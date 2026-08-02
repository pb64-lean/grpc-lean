module

public import Std.Async.TCP
public import Std.Async.Timer
public import Std.Sync.CancellationToken

public import Grpc.CancellationToken
public import Grpc.Http2.Connection
public import Grpc.Tls.Session

public section

namespace Grpc
namespace Http2
namespace Server

open Std
open Std.Net
open Std.Async

structure Config where
  address : SocketAddress := .v4 {
    addr := IPv4Addr.ofParts 127 0 0 1,
    port := 50051
  }
  backlog : UInt32 := 1024
  readSize : UInt64 := 16384
  noDelay : Bool := true
  maxConcurrentStreams : Option Nat := none
  maxHeaderListSize : Option Nat := none
  /-- Milliseconds between server-initiated keepalive PINGs; `none` disables keepalive. -/
  keepaliveIntervalMs : Option Nat := none
  /-- Milliseconds to wait for a keepalive PING ack before closing the connection. -/
  keepaliveTimeoutMs : Nat := 20000
  deriving Inhabited

structure ActiveConnection where
  id : Nat
  client : TCP.Socket.Client
  stateMutex : Std.Mutex Connection.State
  stopToken : Std.CancellationToken

/-- Exact owner of one accepted connection computation.  Retaining the outer
`Async.toIO` handle gives shutdown a joinable ownership boundary for every
accepted socket and the selector continuations serving it. -/
structure ConnectionTask where
  id : Nat
  task : Task (Except IO.Error Unit)

structure Server where
  socket : TCP.Socket.Server
  localAddress : SocketAddress
  config : Config
  shutdownToken : Option Std.CancellationToken := none
  acceptTask : Option (Task (Except IO.Error Unit)) := none
  activeConnections : Option (Std.Mutex (Array ActiveConnection)) := none
  connectionTasks : Option (Std.Mutex (Array ConnectionTask)) := none
  nextConnectionId : Option (IO.Ref Nat) := none

def ipv4Address (a b c d : UInt8) (port : UInt16) : SocketAddress :=
  .v4 { addr := IPv4Addr.ofParts a b c d, port := port }

def loopback (port : UInt16) : SocketAddress :=
  ipv4Address 127 0 0 1 port

def anyIPv4 (port : UInt16) : SocketAddress :=
  ipv4Address 0 0 0 0 port

def bind (config : Config := {}) : IO Server := do
  let socket ← TCP.Socket.Server.mk
  socket.bind config.address
  socket.listen config.backlog
  if config.noDelay then
    socket.noDelay
  let localAddress ← socket.getSockName
  pure { socket := socket, localAddress := localAddress, config := config }

def statusDebugData (status : Status) : ByteArray :=
  status.messageD.toUTF8

def errorGoAwayFrame (state : Connection.State) (status : Status) : Except Status Frame :=
  GoAway.frame state.lastClientStreamId ErrorCode.internalError (statusDebugData status)

def errorGoAwayBytes (state : Connection.State) (status : Status) : Except Status ByteArray := do
  let frame ← errorGoAwayFrame state status
  Frame.encode frame

def gracefulGoAwayFrame (state : Connection.State) : Except Status Frame :=
  GoAway.frame state.lastClientStreamId ErrorCode.noError

def gracefulGoAwayBytes (state : Connection.State) : Except Status ByteArray := do
  let frame ← gracefulGoAwayFrame state
  Frame.encode frame

private def ofStatusExcept (result : Except Status α) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

/-- Connection teardown. Deliberately does NOT call `client.shutdown`: `uv_shutdown`
blocks until queued writes flush, so a peer that has stopped reading (which a gRPC
client does the moment it closes — leaving our GOAWAY stuck in the send buffer) makes
it block forever. Because `.block` parks the worker thread and the stuck `uv_shutdown`
is not cancellable, that would leak a worker per closed connection and hang process exit
(the task manager joins all workers). The socket fd is released by handle finalization
regardless — the same path the graceful shutdown already relied on for the actual close
— so we drop only the redundant TCP FIN; the gRPC GOAWAY already signals shutdown at the
application layer. -/
private def shutdownWrite (_client : TCP.Socket.Client) : IO Unit :=
  pure ()

private def sendBytes (client : TCP.Socket.Client) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then
    pure ()
  else
    (client.send bytes).block

private def sendGoAway (client : TCP.Socket.Client) (state : Connection.State)
    (status : Status) : IO Unit := do
  if state.prefaceReceived then
    match errorGoAwayBytes state status with
    | .ok bytes =>
        try
          sendBytes client bytes
        catch _ =>
          pure ()
    | .error _ => pure ()

private def getConnectionState (stateMutex : Std.Mutex Connection.State) : IO Connection.State :=
  stateMutex.atomically get

private def markGracefulShutdownState (stateMutex : Std.Mutex Connection.State) :
    IO Connection.State :=
  stateMutex.atomically do
    let state ← get
    let state := {
      state with outboundGoAwayLastStreamId := some state.lastClientStreamId
    }
    set state
    pure state

private def sendGracefulGoAway (connection : ActiveConnection) : IO Unit := do
  let state ← markGracefulShutdownState connection.stateMutex
  if state.prefaceReceived then
    match gracefulGoAwayBytes state with
    | .ok bytes =>
        try
          sendBytes connection.client bytes
        catch _ =>
          pure ()
    | .error _ => pure ()

private def initialConnectionState (config : Config) (state : Connection.State) :
    Connection.State :=
  {
    state with
    inboundMaxConcurrentStreams := config.maxConcurrentStreams,
    inboundMaxHeaderListSize := config.maxHeaderListSize
  }

private def newConnectionStateMutex (config : Config) (state : Connection.State) :
    IO (Std.Mutex Connection.State) :=
  Std.Mutex.new (initialConnectionState config state)

private def nextActiveConnectionId (server : Server) : IO Nat := do
  match server.nextConnectionId with
  | none => pure 0
  | some ref =>
      let id ← ref.get
      ref.set (id + 1)
      pure id

private def registerActiveConnection (server : Server) (id : Nat)
    (client : TCP.Socket.Client)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken) :
    IO (Option ActiveConnection) := do
  match server.activeConnections with
  | none => pure none
  | some connectionsMutex =>
      let connection : ActiveConnection := {
        id := id,
        client := client,
        stateMutex := stateMutex,
        stopToken := stopToken
      }
      connectionsMutex.atomically do
        let connections ← get
        set (connections.push connection)
      pure (some connection)

private def unregisterActiveConnection (server : Server)
    (connection? : Option ActiveConnection) : IO Unit := do
  match server.activeConnections, connection? with
  | some connectionsMutex, some connection =>
      connectionsMutex.atomically do
        let connections ← get
        set (connections.filter fun active => active.id != connection.id)
  | _, _ => pure ()

private def activeConnectionSnapshot (server : Server) : IO (Array ActiveConnection) := do
  match server.activeConnections with
  | none => pure #[]
  | some connectionsMutex => connectionsMutex.atomically get

private def retainConnectionTask (server : Server) (owner : ConnectionTask) : IO Unit := do
  match server.connectionTasks with
  | none => pure ()
  | some tasksMutex =>
      tasksMutex.atomically do
        modify fun tasks => tasks.push owner

private def connectionTaskSnapshot (server : Server) : IO (Array ConnectionTask) := do
  match server.connectionTasks with
  | none => pure #[]
  | some tasksMutex => tasksMutex.atomically get

/-- Observe and remove completed owners without ever blocking while holding the
registry mutex.  Connection-level transport failures remain connection-local,
matching the historical detached-task behavior. -/
private def pruneFinishedConnectionTasks (server : Server) : IO Unit := do
  let owners ← connectionTaskSnapshot server
  let mut finishedIds := #[]
  for owner in owners do
    if ← IO.hasFinished owner.task then
      match owner.task.get with
      | .ok () => pure ()
      | .error _ => pure ()
      finishedIds := finishedIds.push owner.id
  unless finishedIds.isEmpty do
    match server.connectionTasks with
    | none => pure ()
    | some tasksMutex =>
        tasksMutex.atomically do
          modify fun tasks => tasks.filter fun owner => !(finishedIds.contains owner.id)

private def waitConnectionTasks (server : Server) : IO Unit := do
  let owners ← connectionTaskSnapshot server
  for owner in owners do
    match owner.task.get with
    | .ok () => pure ()
    | .error _ => pure ()
  match server.connectionTasks with
  | none => pure ()
  | some tasksMutex => tasksMutex.atomically do set (#[] : Array ConnectionTask)

private def signalActiveConnectionsShutdown (server : Server) : IO Unit := do
  let connections ← activeConnectionSnapshot server
  for connection in connections do
    sendGracefulGoAway connection

private def stopDrainedConnection (connection : ActiveConnection) : IO Bool := do
  let state ← getConnectionState connection.stateMutex
  if Connection.isDrainedAfterOutboundGoAway state then
    discard <| Grpc.CancellationToken.cancel connection.stopToken
      (reason := Std.CancellationReason.shutdown)
    pure true
  else
    pure false

private partial def serveClientLoop (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) (stateMutex : Std.Mutex Connection.State) :
    IO Connection.State := do
  let chunk? ← (client.recv? config.readSize).block
  match chunk? with
  | none => Connection.cancelActiveShared stateMutex
  | some chunk =>
      if chunk.isEmpty then
        serveClientLoop registry config client stateMutex
      else
        match (← Connection.processBytesEncodedSharedWith registry stateMutex chunk (sendBytes client)) with
        | .ok () =>
            serveClientLoop registry config client stateMutex
        | .error status =>
            let state ← getConnectionState stateMutex
            sendGoAway client state status
            shutdownWrite client
            Connection.cancelActiveShared stateMutex

private def serveClientWithStateMutex (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) (stateMutex : Std.Mutex Connection.State) :
    IO Connection.State := do
  if config.noDelay then
    client.noDelay
  let serverPreface ← ofStatusExcept
    (Connection.serverPrefaceBytes config.maxConcurrentStreams config.maxHeaderListSize)
  sendBytes client serverPreface
  serveClientLoop registry config client stateMutex

private def keepalivePingPayload : ByteArray :=
  ByteArray.mk #[0x67, 0x72, 0x70, 0x63, 0x6c, 0x65, 0x61, 0x6e]

private def sendKeepalivePing (client : TCP.Socket.Client)
    (stateMutex : Std.Mutex Connection.State) : IO Bool := do
  stateMutex.atomically do
    modify fun state => { state with pendingKeepalivePing := some keepalivePingPayload }
  match Ping.frame keepalivePingPayload with
  | .error _ => pure false
  | .ok ping =>
      match Frame.encode ping with
      | .error _ => pure false
      | .ok bytes =>
          try
            sendBytes client bytes
            pure true
          catch _ =>
            pure false

private inductive KeepaliveEvent where
  | tick
  | stop

/-- Suspend for `ms` milliseconds or until the stop token fires, whichever comes
first. Suspends cooperatively (no parked worker) and reacts to shutdown at once. -/
private def keepaliveWait (stopToken : Std.CancellationToken) (ms : Nat) :
    Std.Async.Async KeepaliveEvent := do
  let sleeper ← Std.Async.Selector.sleep (Std.Time.Millisecond.Offset.ofNat ms)
  Std.Async.Selectable.one #[
    Std.Async.Selectable.case sleeper fun _ =>
      pure KeepaliveEvent.tick,
    Std.Async.Selectable.case stopToken.selector fun _ =>
      pure KeepaliveEvent.stop
  ]

/-- Periodically PING the peer; if an ack does not arrive within the timeout, cancel all
active work and stop the connection. Detects peers that vanished behind NAT/LB idle
timeouts (and clients that never complete the handshake). -/
private partial def keepaliveLoop (client : TCP.Socket.Client)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (intervalMs timeoutMs : Nat) : Std.Async.Async Unit := do
  match ← keepaliveWait stopToken intervalMs with
  | .stop => pure ()
  | .tick =>
    if !(← sendKeepalivePing client stateMutex) then
      pure ()
    else
      match ← keepaliveWait stopToken timeoutMs with
      | .stop => pure ()
      | .tick =>
          let pending ← stateMutex.atomically do
            let state ← get
            pure state.pendingKeepalivePing
          match pending with
          | some payload =>
              if payload == keepalivePingPayload then do
                discard <| Connection.cancelActiveShared stateMutex
                discard <| Grpc.CancellationToken.cancel stopToken
                  (reason := Std.CancellationReason.shutdown)
                shutdownWrite client
              else
                keepaliveLoop client stateMutex stopToken intervalMs timeoutMs
          | none =>
              keepaliveLoop client stateMutex stopToken intervalMs timeoutMs

private def spawnKeepalive (config : Config) (client : TCP.Socket.Client)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken) :
    IO (Option (Task (Except IO.Error Unit))) := do
  match config.keepaliveIntervalMs with
  | none => pure none
  | some intervalMs =>
      let task ← Std.Async.Async.toIO
        (keepaliveLoop client stateMutex stopToken intervalMs config.keepaliveTimeoutMs)
      pure (some task)

private inductive ManagedClientEvent where
  | received (chunk? : Option ByteArray)
  | stop

private def nextManagedClientEvent (config : Config) (client : TCP.Socket.Client)
    (stopToken : Std.CancellationToken) : Std.Async.Async ManagedClientEvent :=
  Std.Async.Selectable.one #[
    Std.Async.Selectable.case (client.recvSelector config.readSize) fun chunk? =>
      pure (ManagedClientEvent.received chunk?),
    Std.Async.Selectable.case stopToken.selector fun _ =>
      pure ManagedClientEvent.stop
  ]

/-- Per-connection event loop. Runs in `Async`: while idle (waiting for bytes or the
stop token) the loop suspends cooperatively instead of parking a worker thread, so
idle connections cost no threads. Frame processing and socket sends inside the body
are ordinary `IO` (a send can briefly block on TCP backpressure). -/
private partial def serveManagedClientLoop (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) (stateMutex : Std.Mutex Connection.State)
    (stopToken : Std.CancellationToken) : Std.Async.Async Connection.State := do
  match ← nextManagedClientEvent config client stopToken with
  | ManagedClientEvent.stop =>
      getConnectionState stateMutex
  | ManagedClientEvent.received none =>
      Connection.cancelActiveShared stateMutex
  | ManagedClientEvent.received (some chunk) =>
      if chunk.isEmpty then
        if Connection.isDrainedAfterOutboundGoAway (← getConnectionState stateMutex) then
          getConnectionState stateMutex
        else
          serveManagedClientLoop registry config client stateMutex stopToken
      else
        match (← Connection.processBytesEncodedSharedWith registry stateMutex chunk (sendBytes client)) with
        | .ok () =>
            if Connection.isDrainedAfterOutboundGoAway (← getConnectionState stateMutex) then
              getConnectionState stateMutex
            else
              serveManagedClientLoop registry config client stateMutex stopToken
        | .error status =>
            let state ← getConnectionState stateMutex
            sendGoAway client state status
            shutdownWrite client
            Connection.cancelActiveShared stateMutex

def serveClientWithState (registry : Registry) (config : Config)
    (client : TCP.Socket.Client)
    (state : Connection.State :=
      Connection.initialState config.maxConcurrentStreams config.maxHeaderListSize) :
    IO Connection.State := do
  let stateMutex ← newConnectionStateMutex config state
  serveClientWithStateMutex registry config client stateMutex

def serveClient (registry : Registry) (config : Config) (client : TCP.Socket.Client) : IO Unit := do
  discard <| serveClientWithState registry config client
  shutdownWrite client

def acceptOne (server : Server) (registry : Registry) : IO Unit := do
  let client ← (server.socket.accept).block
  serveClient registry server.config client

private def waitUntilConnectionTaskRetained (retained : IO.Promise Unit) :
    Std.Async.Async Unit := do
  match ← Std.Async.Async.ofTask retained.result? with
  | some () => pure ()
  | none => throw (IO.userError "connection task owner gate was dropped")

private def finishManagedClient (server : Server) (client : TCP.Socket.Client)
    (stopToken : Std.CancellationToken) (connection? : Option ActiveConnection)
    (keepaliveTask? : Option (Task (Except IO.Error Unit))) : IO Unit := do
  discard <| Grpc.CancellationToken.cancel stopToken
    (reason := Std.CancellationReason.shutdown)
  match keepaliveTask? with
  | none => pure ()
  | some task =>
      match task.get with
      | .ok () => pure ()
      | .error _ => pure ()
  unregisterActiveConnection server connection?
  shutdownWrite client

private def serveManagedClient (server : Server) (registry : Registry)
    (client : TCP.Socket.Client) (stateMutex : Std.Mutex Connection.State)
    (stopToken : Std.CancellationToken) (connection? : Option ActiveConnection)
    (retained : IO.Promise Unit) : Std.Async.Async Unit := do
  waitUntilConnectionTaskRetained retained
  let mut keepaliveTask? := none
  try
    if server.config.noDelay then
      client.noDelay
    let serverPreface ← ofStatusExcept
      (Connection.serverPrefaceBytes server.config.maxConcurrentStreams server.config.maxHeaderListSize)
    sendBytes client serverPreface
    keepaliveTask? ← spawnKeepalive server.config client stateMutex stopToken
    discard <| serveManagedClientLoop registry server.config client stateMutex stopToken
    finishManagedClient server client stopToken connection? keepaliveTask?
  catch err =>
    finishManagedClient server client stopToken connection? keepaliveTask?
    throw err

private def spawnManagedClient (server : Server) (registry : Registry)
    (client : TCP.Socket.Client) (shutdownToken : Std.CancellationToken) : IO Unit := do
  let id ← nextActiveConnectionId server
  let stateMutex ← newConnectionStateMutex server.config
    (Connection.initialState server.config.maxConcurrentStreams server.config.maxHeaderListSize)
  let stopToken ← Std.CancellationToken.new
  let connection? ← registerActiveConnection server id client stateMutex stopToken
  let retained ← IO.Promise.new
  try
    let task ← Std.Async.Async.toIO
      (serveManagedClient server registry client stateMutex stopToken connection? retained)
    retainConnectionTask server { id := id, task := task }
    retained.resolve ()
    -- Registration precedes this check.  Therefore either the shutdown caller's
    -- active snapshot sees this connection, or this side observes the sticky
    -- token transition; an accepted child cannot start behind the drain fence.
    if ← shutdownToken.isCancelled then
      match connection? with
      | none => pure ()
      | some connection => sendGracefulGoAway connection
    pruneFinishedConnectionTasks server
  catch err =>
    -- Release a child that was spawned but could not be published, then roll
    -- back the pre-spawn active registration.  Cleanup operations are
    -- idempotent if the released child races this path.
    retained.resolve ()
    discard <| Grpc.CancellationToken.cancel stopToken
      (reason := Std.CancellationReason.shutdown)
    unregisterActiveConnection server connection?
    shutdownWrite client
    throw err

private inductive AcceptLoopEvent where
  | accepted (client : TCP.Socket.Client)
  | shutdown

private def nextAcceptLoopEvent (server : Server) (token : Std.CancellationToken) :
    Std.Async.Async AcceptLoopEvent :=
  Std.Async.Selectable.one #[
    Std.Async.Selectable.case server.socket.acceptSelector fun client =>
      pure (AcceptLoopEvent.accepted client),
    Std.Async.Selectable.case token.selector fun _ =>
      pure AcceptLoopEvent.shutdown
  ]

partial def serveForever (server : Server) (registry : Registry) : IO Unit := do
  let client ← (server.socket.accept).block
  discard <| IO.asTask (serveClient registry server.config client)
  serveForever server registry

/-- Accept loop as a suspending `Async` computation: between connections it holds no
worker thread, and each accepted connection is spawned as its own `Async` task. -/
private partial def acceptLoop (server : Server) (registry : Registry)
    (token : Std.CancellationToken) : Std.Async.Async Unit := do
  match ← nextAcceptLoopEvent server token with
  | AcceptLoopEvent.shutdown => pure ()
  | AcceptLoopEvent.accepted client =>
      spawnManagedClient server registry client token
      acceptLoop server registry token

partial def serveUntilShutdown (server : Server) (registry : Registry)
    (token : Std.CancellationToken) : IO Unit := do
  let activeConnections ← Std.Mutex.new #[]
  let connectionTasks ← Std.Mutex.new #[]
  let nextConnectionId ← IO.mkRef 0
  let server := {
    server with
    shutdownToken := some token,
    activeConnections := some activeConnections,
    connectionTasks := some connectionTasks,
    nextConnectionId := some nextConnectionId
  }
  Std.Async.Async.block (acceptLoop server registry token)
  signalActiveConnectionsShutdown server
  let connections ← activeConnectionSnapshot server
  for connection in connections do
    discard <| Grpc.CancellationToken.cancel connection.stopToken
      (reason := Std.CancellationReason.shutdown)
  waitConnectionTasks server

def serve (registry : Registry) (config : Config := {}) : IO Server := do
  let server ← bind config
  let token ← Std.CancellationToken.new
  let activeConnections ← Std.Mutex.new #[]
  let connectionTasks ← Std.Mutex.new #[]
  let nextConnectionId ← IO.mkRef 0
  let server := {
    server with
    shutdownToken := some token,
    activeConnections := some activeConnections,
    connectionTasks := some connectionTasks,
    nextConnectionId := some nextConnectionId
  }
  let task ← Std.Async.Async.toIO (acceptLoop server registry token)
  pure { server with acceptTask := some task }

/-! ## TLS

`serveTls` terminates TLS 1.3 and runs gRPC (ALPN "h2") over the encrypted
connection. Static identity (certificate chain + Ed25519 signing key) is shared;
the ephemeral ECDHE scalar and ServerHello random are freshly generated per
connection for forward secrecy. -/

/-- Static TLS server identity and policy. -/
structure TlsConfig where
  /-- DER certificates, leaf first. -/
  certificateChain : Array ByteArray
  /-- Ed25519 private scalar (32 bytes) matching the leaf certificate. -/
  signingKey : ByteArray
  /-- ALPN protocols to offer; gRPC advertises "h2". -/
  alpnProtocols : List String := ["h2"]

/-- Build a fresh per-connection TLS server config with new ECDHE + random. -/
private def freshTlsServerConfig (tlsConfig : TlsConfig) : IO Tls.Server.Config := do
  let entropy ← IO.getRandomBytes 64
  pure {
    serverRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    certificateChain := tlsConfig.certificateChain
    signingKey := tlsConfig.signingKey
    alpnProtocols := tlsConfig.alpnProtocols
  }

private def tlsServerSend (session : Grpc.Tls.ServerSession) (bytes : ByteArray) : IO Unit :=
  session.send bytes

private partial def serveTlsClientLoop (registry : Registry) (config : Config)
    (session : Grpc.Tls.ServerSession) (stateMutex : Std.Mutex Connection.State)
    (stopToken : Std.CancellationToken) : Std.Async.Async Unit := do
  match ← nextManagedClientEvent config session.socket stopToken with
  | ManagedClientEvent.stop => pure ()
  | ManagedClientEvent.received none =>
      discard <| Connection.cancelActiveShared stateMutex
  | ManagedClientEvent.received (some rawChunk) =>
      match ← session.feedInbound rawChunk with
      | none => discard <| Connection.cancelActiveShared stateMutex
      | some plaintext =>
          match ← Connection.processBytesEncodedSharedWith
              registry stateMutex plaintext (tlsServerSend session) with
          | .ok () =>
              if Connection.isDrainedAfterOutboundGoAway (← getConnectionState stateMutex) then
                pure ()
              else
                serveTlsClientLoop registry config session stateMutex stopToken
          | .error status =>
              let state ← getConnectionState stateMutex
              (match errorGoAwayBytes state status with
               | .ok bytes => try session.send bytes catch _ => pure ()
               | .error _ => pure ())
              try session.closeNotify catch _ => pure ()
              discard <| Connection.cancelActiveShared stateMutex

private def serveTlsConnection (registry : Registry) (config : Config)
    (tlsConfig : TlsConfig) (client : TCP.Socket.Client) : Std.Async.Async Unit := do
  try
    if config.noDelay then
      client.noDelay
    let serverConfig ← freshTlsServerConfig tlsConfig
    let session ← Grpc.Tls.ServerSession.establish client serverConfig config.readSize
    let stateMutex ← newConnectionStateMutex config
      (Connection.initialState config.maxConcurrentStreams config.maxHeaderListSize)
    let stopToken ← Std.CancellationToken.new
    let preface ← ofStatusExcept
      (Connection.serverPrefaceBytes config.maxConcurrentStreams config.maxHeaderListSize)
    session.send preface
    serveTlsClientLoop registry config session stateMutex stopToken
  catch _ =>
    pure ()

private partial def acceptTlsLoop (server : Server) (registry : Registry)
    (tlsConfig : TlsConfig) (token : Std.CancellationToken) : Std.Async.Async Unit := do
  match ← nextAcceptLoopEvent server token with
  | AcceptLoopEvent.shutdown => pure ()
  | AcceptLoopEvent.accepted client =>
      discard <| Std.Async.Async.toIO (serveTlsConnection registry server.config tlsConfig client)
      acceptTlsLoop server registry tlsConfig token

/-- Bind, then accept connections and serve gRPC over TLS 1.3 on each. -/
def serveTls (registry : Registry) (tlsConfig : TlsConfig) (config : Config := {}) : IO Server := do
  let server ← bind config
  let token ← Std.CancellationToken.new
  let activeConnections ← Std.Mutex.new #[]
  let nextConnectionId ← IO.mkRef 0
  let server := {
    server with
    shutdownToken := some token,
    activeConnections := some activeConnections,
    nextConnectionId := some nextConnectionId
  }
  let task ← Std.Async.Async.toIO (acceptTlsLoop server registry tlsConfig token)
  pure { server with acceptTask := some task }

def shutdown (server : Server) : IO Unit := do
  match server.shutdownToken with
  | none => signalActiveConnectionsShutdown server
  | some token => do
      let elected ← Grpc.CancellationToken.cancel token
        (reason := Std.CancellationReason.shutdown)
      if elected then
        signalActiveConnectionsShutdown server
      else
        pure ()

private def forceCloseActiveConnections (server : Server) : IO Unit := do
  let connections ← activeConnectionSnapshot server
  for connection in connections do
    discard <| Connection.cancelActiveShared connection.stateMutex
    discard <| Grpc.CancellationToken.cancel connection.stopToken
      (reason := Std.CancellationReason.shutdown)
    shutdownWrite connection.client

private partial def waitActiveConnectionsDrained (server : Server)
    (remainingMs : Option Nat) : IO Unit := do
  let connections ← activeConnectionSnapshot server
  if connections.isEmpty then
    pure ()
  else
    match remainingMs with
    | some 0 => forceCloseActiveConnections server
    | _ =>
        for connection in connections do
          discard <| stopDrainedConnection connection
        IO.sleep 1
        waitActiveConnectionsDrained server (remainingMs.map (· - 1))

/-- Wait for the accept loop and active connections to finish. Connections that have not
drained within `drainTimeoutMs` of graceful shutdown are force-closed; pass `none` to
wait indefinitely. -/
def wait (server : Server) (drainTimeoutMs : Option Nat := some 30000) : IO Unit := do
  let acceptError? ← match server.acceptTask with
    | none => pure none
    | some task =>
        match task.get with
        | .ok () => pure none
        | .error err => pure (some err)
  -- An accept may have won its selector concurrently with shutdown.  Joining
  -- the accept owner closes publication, and this second signal covers every
  -- connection registered by that final accepted event before drain begins.
  let shutdown ← match server.shutdownToken with
    | none => pure false
    | some token => token.isCancelled
  if shutdown then
    signalActiveConnectionsShutdown server
  waitActiveConnectionsDrained server drainTimeoutMs
  waitConnectionTasks server
  match acceptError? with
  | none => pure ()
  | some err => throw err

def isShutdown (server : Server) : IO Bool := do
  match server.shutdownToken with
  | none => pure false
  | some token => token.isCancelled

end Server
end Http2
end Grpc
