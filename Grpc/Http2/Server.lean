module

public import Std.Async.TCP
public import Std.Async.Timer
public import Std.Sync.CancellationToken
public import Std.Sync.Channel

public import Http2.CancellationToken
public import Grpc.Http2.Connection
public import Http2.Tls.Session

public section

namespace Grpc
namespace Http2
namespace Server

private def ofHttp2 {α} (result : Except _root_.Http2.Error α) : Except Status α :=
  match result with
  | .ok value => .ok value
  | .error error => .error (Status.ofHttp2Error error)

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
  /-- Finite default keeps per-stream request bounds compositional at the
  connection level. Set explicitly to `none` only for a trusted deployment
  that supplies an independent admission bound. -/
  maxConcurrentStreams : Option Nat := some 100
  maxHeaderListSize : Option Nat := none
  /-- Milliseconds between server-initiated keepalive PINGs; `none` disables keepalive. -/
  keepaliveIntervalMs : Option Nat := none
  /-- Milliseconds to wait for a keepalive PING ack before closing the connection. -/
  keepaliveTimeoutMs : Nat := 20000
  deriving Inhabited

/-- Why a managed connection is being torn down.  Every teardown path records one,
so a connection that dies is attributable both to the peer (through the GOAWAY the
cause is rendered into) and locally (through `closedConnections`). -/
inductive CloseCause where
  /-- The peer closed its side, or the connection drained after our GOAWAY. -/
  | peerClosed
  /-- Local graceful shutdown; the drain path already sent GOAWAY(NO_ERROR). -/
  | serverShutdown
  /-- The peer never acknowledged a keepalive PING within the timeout. -/
  | keepaliveTimeout
  /-- The connection hit an HTTP/2 or gRPC connection error. -/
  | protocolError (error : Connection.ProcessError)
  /-- The connection task itself failed (socket write, preface encoding, ...). -/
  | transportError (message : String)
  deriving Inhabited, Repr

namespace CloseCause

/-- Whether the peer should be told about this cause with a GOAWAY.  A peer that
already closed cannot read one. -/
def notifiesPeer : CloseCause → Bool
  | .peerClosed => false
  | _ => true

/-- GOAWAY error code for the cause.  A keepalive timeout is not a protocol
violation by either endpoint — RFC 9113 §6.8 has no code for "peer stopped
answering", and NO_ERROR plus debug data says "going away, here is why" without
libelling the peer's framing. -/
def errorCode : CloseCause → _root_.Http2.ErrorCode
  | .peerClosed => _root_.Http2.ErrorCode.noError
  | .serverShutdown => _root_.Http2.ErrorCode.noError
  | .keepaliveTimeout => _root_.Http2.ErrorCode.noError
  | .protocolError error => error.errorCode
  | .transportError _ => _root_.Http2.ErrorCode.internalError

/-- Human-readable cause, carried as GOAWAY debug data and kept in `closedConnections`. -/
def describe : CloseCause → String
  | .peerClosed => "peer closed the connection"
  | .serverShutdown => "server shutdown"
  | .keepaliveTimeout => "keepalive ping timeout"
  | .protocolError error => error.message
  | .transportError message => "connection task failed: " ++ message

end CloseCause

/-- One finished connection and why it finished; kept in a bounded ring so a dying
connection leaves an attributable local record. -/
structure ClosedConnection where
  id : Nat
  cause : CloseCause
  deriving Inhabited, Repr

/-- One FIFO owner of a plaintext connection's write side.  Producers only
enqueue bytes; the `Async` task is the sole socket writer and therefore preserves
HTTP/2 frame order without ever parking an RPC or connection worker on TCP
backpressure. -/
structure SocketWriter where
  outbound : Std.CloseableChannel ByteArray
  task : AsyncTask Unit

structure ActiveConnection where
  id : Nat
  client : TCP.Socket.Client
  stateMutex : Std.Mutex Connection.State
  stopToken : Std.CancellationToken
  /-- Set by whichever teardown path fires first; read by `finishManagedClient`. -/
  closeCause : IO.Ref (Option CloseCause)
  /-- Present for h2c. TLS has its own record writer and leaves this `none`. -/
  plainWriter : Option SocketWriter
  /-- The TLS session, published once its handshake completes.  Teardown bytes for
  such a connection must be sealed through it; writing a GOAWAY straight to the
  socket would put plaintext on an encrypted stream.  Stays `none` for h2c and for
  a TLS connection that died before it had a session — in both cases there is
  nothing to seal and nothing the peer could read. -/
  tlsSession : IO.Ref (Option _root_.Http2.Tls.ServerSession)

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
  /-- Bounded record of the most recently finished connections and their causes. -/
  closedConnections : Option (Std.Mutex (Array ClosedConnection)) := none

def ipv4Address (a b c d : UInt8) (port : UInt16) : SocketAddress :=
  .v4 { addr := IPv4Addr.ofParts a b c d, port := port }

def loopback (port : UInt16) : SocketAddress :=
  ipv4Address 127 0 0 1 port

def anyIPv4 (port : UInt16) : SocketAddress :=
  ipv4Address 0 0 0 0 port

private def validateConfig (config : Config) : IO Unit := do
  if config.readSize == 0 then
    throw (IO.userError "gRPC HTTP/2 readSize must be positive")
  let maximumSettingValue : Nat := 4294967295
  if config.maxConcurrentStreams.any (· > maximumSettingValue) then
    throw (IO.userError "gRPC HTTP/2 maxConcurrentStreams exceeds the SETTINGS wire range")
  if config.maxHeaderListSize.any (· > maximumSettingValue) then
    throw (IO.userError "gRPC HTTP/2 maxHeaderListSize exceeds the SETTINGS wire range")
  if config.keepaliveIntervalMs == some 0 then
    throw (IO.userError "gRPC HTTP/2 keepaliveIntervalMs must be positive")
  if config.keepaliveTimeoutMs == 0 then
    throw (IO.userError "gRPC HTTP/2 keepaliveTimeoutMs must be positive")

private def configuredReceiveLimit (registry : Registry) : Nat :=
  registry.maxReceiveMessageSize.getD Message.defaultMaxDecompressedSize

private def configuredSendLimit (registry : Registry) : Nat :=
  registry.maxSendMessageSize.getD Message.defaultMaxDecompressedSize

private def validateRegistryLimits (registry : Registry) : IO Unit := do
  if Message.prefixLength + configuredReceiveLimit registry >
      _root_.Http2.Connection.maximumWindowSize then
    throw (IO.userError "gRPC receive message limit exceeds the HTTP/2 stream-window range")
  if configuredSendLimit registry > Message.maxWireLength then
    throw (IO.userError "gRPC send message limit exceeds the 32-bit wire-length range")

def bind (config : Config := {}) : IO Server := do
  validateConfig config
  let socket ← TCP.Socket.Server.mk
  socket.bind config.address
  socket.listen config.backlog
  if config.noDelay then
    socket.noDelay
  let localAddress ← socket.getSockName
  pure { socket := socket, localAddress := localAddress, config := config }

def processErrorDebugData (error : Connection.ProcessError) : ByteArray :=
  error.message.toUTF8

def errorGoAwayFrame (state : Connection.State) (error : Connection.ProcessError) :
    Except Status _root_.Http2.Frame :=
  ofHttp2 <| _root_.Http2.GoAway.frame state.protocol.lastPeerStreamId
    error.errorCode (processErrorDebugData error)

def errorGoAwayBytes (state : Connection.State) (error : Connection.ProcessError) :
    Except Status ByteArray := do
  let frame ← errorGoAwayFrame state error
  ofHttp2 <| _root_.Http2.Frame.encode frame

def gracefulGoAwayFrame (state : Connection.State) : Except Status _root_.Http2.Frame :=
  ofHttp2 <| _root_.Http2.GoAway.frame state.protocol.lastPeerStreamId _root_.Http2.ErrorCode.noError

def gracefulGoAwayBytes (state : Connection.State) : Except Status ByteArray := do
  let frame ← gracefulGoAwayFrame state
  ofHttp2 <| _root_.Http2.Frame.encode frame

private def ofStatusExcept (result : Except Status α) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

/-- Milliseconds a connection teardown waits for the write side to drain before it
abandons the attempt and lets the handle go. -/
private def closeFlushTimeoutMs : Nat := 200

/-- Connection teardown uses bounded, asynchronous write-side shutdown.

`Std.Async.TCP` in Lean 4.31 exposes `shutdown` but no full `close` operation.
The internal socket API likewise has no `uv_close` binding, and its handle
layout is not part of the published runtime ABI. Write-side shutdown is
therefore the strongest transport-retirement operation available here.

The shutdown stays in `Async`, so waiting suspends cooperatively without
occupying a worker. Racing it against `closeFlushTimeoutMs` prevents a peer
that has stopped reading from causing an unbounded teardown wait. In the
ordinary case, the peer receives an attributable FIN behind the GOAWAY.

`Async.race` does not cancel its losing branch. If the timer wins, one
`client.shutdown` task per stalled peer can remain suspended until
`uv_shutdown` completes or fails. The task holds the `Client`, so descriptor
release occurs through finalization rather than at the teardown point. The
contract therefore provides bounded cooperative teardown and best-effort FIN,
but not deterministic descriptor release. -/
private def closeConnectionSocket (client : TCP.Socket.Client) : Std.Async.Async Unit := do
  try
    Std.Async.Async.race
      (client.shutdown)
      (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat closeFlushTimeoutMs))
  catch _ =>
    pure ()

private partial def socketWriterLoop (client : TCP.Socket.Client)
    (outbound : Std.CloseableChannel ByteArray) (onError : IO.Error → IO Unit) :
    Std.Async.Async Unit := do
  match ← await (← outbound.recv) with
  | none => pure ()
  | some bytes =>
      try
        client.send bytes
        socketWriterLoop client outbound onError
      catch err =>
        -- Reject future enqueues and wake the connection owner.  The writer owns
        -- the socket send side, so no other task can make forward progress after
        -- this failure.
        discard <| outbound.close.toBaseIO
        onError err

private def startSocketWriter (client : TCP.Socket.Client)
    (onError : IO.Error → IO Unit := fun _ => pure ()) : IO SocketWriter := do
  let outbound ← Std.CloseableChannel.new
  let task ← Std.Async.Async.toIO (socketWriterLoop client outbound onError)
  pure { outbound := outbound, task := task }

/-- Non-blocking producer side of a plaintext connection writer. -/
private def sendBytes (writer : SocketWriter) (bytes : ByteArray) : IO Unit := do
  unless bytes.isEmpty do
    discard <| writer.outbound.send bytes

private def drainSocketWriter (writer : SocketWriter) : Std.Async.Async Unit := do
  discard <| writer.outbound.close.toBaseIO
  let drained ← Std.Async.Async.race
    (do
      try Std.Async.Async.ofAsyncTask writer.task catch _ => pure ()
      pure true)
    (do
      Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat closeFlushTimeoutMs)
      pure false)
  unless drained do
    -- `Std.Async.TCP` exposes no full close/cancel-send operation. Cancelling
    -- the writer owner prevents its Lean continuation from outliving teardown;
    -- the bounded socket shutdown below then makes the best available attempt
    -- to retire the libuv write side.
    IO.cancel writer.task

/-- Put teardown bytes on a connection's wire: through the plaintext FIFO writer
for h2c, sealed through the record writer for TLS. -/
private def sendConnectionBytes (plainWriter? : Option SocketWriter)
    (tls? : Option _root_.Http2.Tls.ServerSession) (bytes : ByteArray) : IO Unit :=
  match tls? with
  | none =>
      match plainWriter? with
      | none => pure ()
      | some writer => sendBytes writer bytes
  | some session => session.send bytes

/-- Retire a connection's transport. For TLS the record queue is closed and its
writer is cooperatively drained first; a short bound cancels a writer stalled on
a non-reading peer before the bounded write-side shutdown. -/
private def retireConnection (plainWriter? : Option SocketWriter)
    (tls? : Option _root_.Http2.Tls.ServerSession)
    (client : TCP.Socket.Client) : Std.Async.Async Unit := do
  match plainWriter?, tls? with
  | some writer, _ => drainSocketWriter writer
  | none, none => pure ()
  | none, some session =>
      try session.closeNotify catch _ => pure ()
      session.drainWriter
  closeConnectionSocket client

private def sendGoAway (writer : SocketWriter) (state : Connection.State)
    (error : Connection.ProcessError) : IO Unit := do
  if state.protocol.prefaceReceived then
    match errorGoAwayBytes state error with
    | .ok bytes =>
        try
          sendBytes writer bytes
        catch _ =>
          pure ()
    | .error _ => pure ()

private def getConnectionState (stateMutex : Std.Mutex Connection.State) : IO Connection.State :=
  stateMutex.atomically get

private def initialConnectionWireBytes (stateMutex : Std.Mutex Connection.State) : IO ByteArray := do
  let state ← getConnectionState stateMutex
  ofStatusExcept (ofHttp2 (_root_.Http2.Connection.initialWireBytes state.protocol))

private def markGracefulShutdownState (stateMutex : Std.Mutex Connection.State) :
    IO (Connection.State × Option _root_.Http2.Frame) :=
  stateMutex.atomically do
    let state ← get
    if state.protocol.localGoAwayLastStream?.isSome then
      pure (state, none)
    else
      match _root_.Http2.Connection.beginGoAway state.protocol with
      | .error _ => pure (state, none)
      | .ok (protocol, frame) =>
          let state := { state with protocol := protocol }
          set state
          pure (state, some frame)

private def sendGracefulGoAway (connection : ActiveConnection) : IO Unit := do
  let (state, frame?) ← markGracefulShutdownState connection.stateMutex
  if state.protocol.prefaceReceived then
    match frame? with
    | none => pure ()
    | some frame =>
      match _root_.Http2.Frame.encode frame with
      | .ok bytes =>
          try
            sendConnectionBytes connection.plainWriter (← connection.tlsSession.get) bytes
          catch _ =>
            pure ()
      | .error _ => pure ()

/-- Tell the peer why this connection is ending, exactly once.  Claiming
the protocol GOAWAY state under the state mutex makes this idempotent and makes it
defer to a GOAWAY that some other path (graceful drain) already sent. -/
private def sendCauseGoAway (plainWriter? : Option SocketWriter)
    (tls? : Option _root_.Http2.Tls.ServerSession)
    (stateMutex : Std.Mutex Connection.State) (cause : CloseCause) : IO Unit := do
  if !cause.notifiesPeer then
    return ()
  let claimed ← stateMutex.atomically do
    let state ← get
    let fatal := cause.errorCode != _root_.Http2.ErrorCode.noError
    let eligible :=
      if fatal then !state.terminalGoAwaySent
      else state.protocol.localGoAwayLastStream?.isNone
    if state.protocol.prefaceReceived && eligible then
      match _root_.Http2.Connection.beginGoAway state.protocol cause.errorCode
          cause.describe.toUTF8 with
      | .error _ => pure none
      | .ok (protocol, frame) =>
          set {
            state with
            protocol := protocol
            terminalGoAwaySent := state.terminalGoAwaySent || fatal
          }
          pure (some frame)
    else
      pure none
  match claimed with
  | none => pure ()
  | some frame =>
      match _root_.Http2.Frame.encode frame with
      | .error _ => pure ()
      | .ok bytes =>
          try
            sendConnectionBytes plainWriter? tls? bytes
          catch _ =>
            pure ()

/-- Record the first cause reported for a connection; later reports lose. -/
private def reportCloseCause (closeCause : IO.Ref (Option CloseCause)) (cause : CloseCause) :
    IO Unit :=
  closeCause.modify fun
    | some existing => some existing
    | none => some cause

/-- How many finished connections `closedConnections` keeps. -/
private def maxRecordedClosedConnections : Nat := 64

private def recordClosedConnection (server : Server) (id : Nat) (cause : CloseCause) :
    IO Unit := do
  match server.closedConnections with
  | none => pure ()
  | some closedMutex =>
      closedMutex.atomically do
        modify fun closed =>
          let closed := closed.push { id := id, cause := cause }
          if closed.size > maxRecordedClosedConnections then
            closed.extract (closed.size - maxRecordedClosedConnections) closed.size
          else
            closed

/-- The most recently finished connections and why each one finished.  A connection
that dies for any reason — protocol error, keepalive timeout, or a failure of the
connection task itself — leaves an entry here. -/
def closedConnectionRecords (server : Server) : IO (Array ClosedConnection) := do
  match server.closedConnections with
  | none => pure #[]
  | some closedMutex => closedMutex.atomically get

private def initialConnectionState (registry : Registry) (config : Config)
    (state : Connection.State) :
    Connection.State :=
  let receiveWindow := Nat.min _root_.Http2.Connection.maximumWindowSize
    (Message.prefixLength + configuredReceiveLimit registry + 65536)
  let protocol := (Connection.initialState config.maxConcurrentStreams
    config.maxHeaderListSize receiveWindow).protocol
  {
    state with
    protocol := protocol,
    maxPendingResponseBytes := Message.prefixLength + configuredSendLimit registry
  }

private def newConnectionStateMutex (registry : Registry) (config : Config)
    (state : Connection.State) :
    IO (Std.Mutex Connection.State) :=
  Std.Mutex.new (initialConnectionState registry config state)

private def installDeadlineScheduler (stateMutex : Std.Mutex Connection.State) : IO Unit := do
  let installed ← stateMutex.atomically do
    pure (← get).deadlineScheduler.isSome
  unless installed do
    let scheduler ← Connection.DeadlineScheduler.new
    stateMutex.atomically do
      modify fun state => { state with deadlineScheduler := some scheduler }

private def nextActiveConnectionId (server : Server) : IO Nat := do
  match server.nextConnectionId with
  | none => pure 0
  | some ref =>
      let id ← ref.get
      ref.set (id + 1)
      pure id

private def registerActiveConnection (server : Server) (id : Nat)
    (client : TCP.Socket.Client)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (closeCause : IO.Ref (Option CloseCause))
    (plainWriter : Option SocketWriter)
    (tlsSession : IO.Ref (Option _root_.Http2.Tls.ServerSession)) :
    IO (Option ActiveConnection) := do
  match server.activeConnections with
  | none => pure none
  | some connectionsMutex =>
      let connection : ActiveConnection := {
        id := id,
        client := client,
        stateMutex := stateMutex,
        stopToken := stopToken,
        closeCause := closeCause,
        plainWriter := plainWriter,
        tlsSession := tlsSession
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
registry mutex. Connection-level transport failures remain connection-local. -/
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

/-- Extra bound after the graceful drain deadline for the exact connection
owners to run their one cleanup path.  TLS teardown can consume two separate
200 ms transport bounds (retiring an in-flight handshake send, then shutting
down the socket), so leave enough scheduling margin for loaded CI workers. -/
private def ownerCleanupTimeoutMs : Nat := 3000

private def waitTaskFinishedWithin (task : Task α) (timeoutMs : Nat) : IO Bool := do
  for _ in [0:timeoutMs] do
    if ← IO.hasFinished task then
      return true
    IO.sleep 1
  IO.hasFinished task

/-- Reap only completed owners while polling; never call `Task.get` on a live
owner.  Thus a finite server wait remains finite even if a transport primitive
does not settle. -/
private def waitConnectionTasksWithin (server : Server) (timeoutMs : Nat) : IO Bool := do
  for _ in [0:timeoutMs] do
    pruneFinishedConnectionTasks server
    if (← connectionTaskSnapshot server).isEmpty then
      return true
    IO.sleep 1
  pruneFinishedConnectionTasks server
  pure (← connectionTaskSnapshot server).isEmpty

private def signalActiveConnectionsShutdown (server : Server) : IO Unit := do
  let connections ← activeConnectionSnapshot server
  for connection in connections do
    try
      sendGracefulGoAway connection
    catch err =>
      -- One broken writer must not prevent shutdown from reaching the rest.
      reportCloseCause connection.closeCause (CloseCause.transportError (toString err))
      Connection.signalCancelActiveShared connection.stateMutex
      discard <| _root_.Http2.CancellationToken.cancel connection.stopToken
        (reason := Std.CancellationReason.shutdown)

private def stopDrainedConnection (connection : ActiveConnection) : IO Bool := do
  let state ← getConnectionState connection.stateMutex
  if Connection.isDrainedAfterOutboundGoAway state then
    reportCloseCause connection.closeCause CloseCause.serverShutdown
    discard <| _root_.Http2.CancellationToken.cancel connection.stopToken
      (reason := Std.CancellationReason.shutdown)
    pure true
  else
    pure false

private inductive ConnectionEvent where
  | received (chunk? : Option ByteArray)
  | stop
  | deadline

private def deadlineMillisecondsFromNow (deadline : Nat) : IO Nat := do
  let now ← IO.monoNanosNow
  if deadline <= now then
    pure 0
  else
    pure ((deadline - now + 999999) / 1000000)

private def nextConnectionEvent (config : Config) (client : TCP.Socket.Client)
    (stopToken : Std.CancellationToken) (deadline? : Option Nat := none) :
    Std.Async.Async ConnectionEvent := do
  let events := #[
    Std.Async.Selectable.case (client.recvSelector config.readSize) fun chunk? =>
      pure (ConnectionEvent.received chunk?),
    Std.Async.Selectable.case stopToken.selector fun _ =>
      pure ConnectionEvent.stop
  ]
  match deadline? with
  | none => Std.Async.Selectable.one events
  | some deadline =>
      let remaining ← deadlineMillisecondsFromNow deadline
      -- Do not race an already-due zero timer with a continuously readable
      -- socket: repeated recv wins could otherwise starve deadline delivery.
      if remaining == 0 then
        pure ConnectionEvent.deadline
      else
        let timer ← Std.Async.Selector.sleep
          (Std.Time.Millisecond.Offset.ofNat remaining)
        Std.Async.Selectable.one <| events.push <|
          Std.Async.Selectable.case timer fun _ => pure ConnectionEvent.deadline

private partial def serveClientLoop (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) (writer : SocketWriter)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken) :
    Std.Async.Async Connection.State := do
  let deadline? := Connection.nextPendingDeadlineFallback? (← getConnectionState stateMutex)
  match ← nextConnectionEvent config client stopToken deadline? with
  | .stop => Connection.cancelActiveSharedOwned stateMutex
  | .received none => Connection.cancelActiveSharedOwned stateMutex
  | .deadline =>
      match ← Connection.expirePendingDeadlinesEncodedSharedWith stateMutex (sendBytes writer) with
      | .ok () => serveClientLoop registry config client writer stateMutex stopToken
      | .error status =>
          let state ← getConnectionState stateMutex
          sendGoAway writer state (.application status)
          Connection.cancelActiveSharedOwned stateMutex
  | .received (some chunk) =>
      if chunk.isEmpty then
        serveClientLoop registry config client writer stateMutex stopToken
      else
        match (← Connection.processBytesEncodedSharedWithOwned
            registry stateMutex chunk (sendBytes writer)) with
        | .ok () =>
            serveClientLoop registry config client writer stateMutex stopToken
        | .error status =>
            let state ← getConnectionState stateMutex
            sendGoAway writer state status
            Connection.cancelActiveSharedOwned stateMutex

private def keepalivePingPayload : ByteArray :=
  ByteArray.mk #[0x67, 0x72, 0x70, 0x63, 0x6c, 0x65, 0x61, 0x6e]

private def sendKeepalivePing (send : ByteArray -> IO Unit)
    (stateMutex : Std.Mutex Connection.State) : IO Bool := do
  stateMutex.atomically do
    modify fun state => { state with pendingKeepalivePing := some keepalivePingPayload }
  match _root_.Http2.Ping.frame keepalivePingPayload with
  | .error _ => pure false
  | .ok ping =>
      match _root_.Http2.Frame.encode ping with
      | .error _ => pure false
      | .ok bytes =>
          try
            send bytes
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
private partial def keepaliveLoop (send : ByteArray -> IO Unit)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (closeCause : IO.Ref (Option CloseCause)) (intervalMs timeoutMs : Nat) :
    Std.Async.Async Unit := do
  match ← keepaliveWait stopToken intervalMs with
  | .stop => pure ()
  | .tick =>
    if !(← sendKeepalivePing send stateMutex) then
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
                -- Record before cancelling: the connection loop wakes on the token and
                -- must find the cause already there to put it in its GOAWAY.
                reportCloseCause closeCause CloseCause.keepaliveTimeout
                Connection.signalCancelActiveShared stateMutex
                discard <| _root_.Http2.CancellationToken.cancel stopToken
                  (reason := Std.CancellationReason.shutdown)
              else
                keepaliveLoop send stateMutex stopToken closeCause intervalMs timeoutMs
          | none =>
              keepaliveLoop send stateMutex stopToken closeCause intervalMs timeoutMs

private def spawnKeepalive (config : Config) (send : ByteArray -> IO Unit)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (closeCause : IO.Ref (Option CloseCause)) :
    IO (Option (Task (Except IO.Error Unit))) := do
  match config.keepaliveIntervalMs with
  | none => pure none
  | some intervalMs =>
      let task ← Std.Async.Async.toIO
        (keepaliveLoop send stateMutex stopToken closeCause intervalMs
          config.keepaliveTimeoutMs)
      pure (some task)

private def serveClientWithStateMutex (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) (stateMutex : Std.Mutex Connection.State) :
    Std.Async.Async Connection.State := do
  let writerFailure ← IO.mkRef (none : Option IO.Error)
  let stopToken ← Std.CancellationToken.new
  let closeCause ← IO.mkRef (none : Option CloseCause)
  let mut keepaliveTask? : Option (Task (Except IO.Error Unit)) := none
  let writer ← startSocketWriter client fun err => do
    writerFailure.set (some err)
    Connection.signalCancelActiveShared stateMutex
    discard <| _root_.Http2.CancellationToken.cancel stopToken
      (reason := Std.CancellationReason.shutdown)
  try
    installDeadlineScheduler stateMutex
    if config.noDelay then
      client.noDelay
    let serverPreface ← initialConnectionWireBytes stateMutex
    sendBytes writer serverPreface
    keepaliveTask? ← spawnKeepalive config (sendBytes writer)
      stateMutex stopToken closeCause
    let state ← serveClientLoop registry config client writer stateMutex stopToken
    discard <| _root_.Http2.CancellationToken.cancel stopToken
      (reason := Std.CancellationReason.shutdown)
    if let some task := keepaliveTask? then
      try Std.Async.Async.ofAsyncTask task catch _ => pure ()
    if let some cause ← closeCause.get then
      sendCauseGoAway (some writer) none stateMutex cause
    drainSocketWriter writer
    match ← writerFailure.get with
    | none => pure state
    | some err => throw err
  catch err =>
    discard <| _root_.Http2.CancellationToken.cancel stopToken
      (reason := Std.CancellationReason.shutdown)
    if let some task := keepaliveTask? then
      try Std.Async.Async.ofAsyncTask task catch _ => pure ()
    -- Setup can fail before the read loop reaches its normal owned-cancel
    -- path; retire the independently spawned deadline scheduler here too.
    discard <| Connection.cancelActiveSharedOwned stateMutex
    drainSocketWriter writer
    throw err

/-- Per-connection event loop. Runs in `Async`: while idle (waiting for bytes or the
stop token) the loop suspends cooperatively instead of parking a worker thread, so
idle connections cost no threads. _root_.Http2.Frame processing only enqueues outbound bytes;
the connection's sole `Async` writer owns all potentially backpressured sends. -/
private partial def serveManagedClientLoop (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) (writer : SocketWriter)
    (stateMutex : Std.Mutex Connection.State)
    (stopToken : Std.CancellationToken) (closeCause : IO.Ref (Option CloseCause)) :
    Std.Async.Async Connection.State := do
  let deadline? := Connection.nextPendingDeadlineFallback? (← getConnectionState stateMutex)
  match ← nextConnectionEvent config client stopToken deadline? with
  | ConnectionEvent.stop =>
      -- Whoever cancelled the token recorded why; a bare shutdown did not.
      reportCloseCause closeCause CloseCause.serverShutdown
      Connection.cancelActiveSharedOwned stateMutex
  | ConnectionEvent.received none =>
      reportCloseCause closeCause CloseCause.peerClosed
      Connection.cancelActiveSharedOwned stateMutex
  | ConnectionEvent.deadline =>
      match ← Connection.expirePendingDeadlinesEncodedSharedWith
          stateMutex (sendBytes writer) with
      | .ok () =>
          serveManagedClientLoop registry config client writer stateMutex stopToken closeCause
      | .error status =>
          reportCloseCause closeCause (CloseCause.protocolError (.application status))
          Connection.cancelActiveSharedOwned stateMutex
  | ConnectionEvent.received (some chunk) =>
      if chunk.isEmpty then
        if Connection.isDrainedAfterOutboundGoAway (← getConnectionState stateMutex) then
          reportCloseCause closeCause CloseCause.peerClosed
          getConnectionState stateMutex
        else
          serveManagedClientLoop registry config client writer stateMutex stopToken closeCause
      else
        match (← Connection.processBytesEncodedSharedWithOwned
            registry stateMutex chunk (sendBytes writer)) with
        | .ok () =>
            if Connection.isDrainedAfterOutboundGoAway (← getConnectionState stateMutex) then
              reportCloseCause closeCause CloseCause.peerClosed
              getConnectionState stateMutex
            else
              serveManagedClientLoop registry config client writer stateMutex stopToken closeCause
        | .error status =>
            -- The GOAWAY naming this status, and the socket close behind it, are
            -- emitted once by `finishManagedClient` for every teardown path.
            reportCloseCause closeCause (CloseCause.protocolError status)
            Connection.cancelActiveSharedOwned stateMutex

private def serveFreshClient (registry : Registry) (config : Config)
    (client : TCP.Socket.Client) : Std.Async.Async Connection.State := do
  validateConfig config
  validateRegistryLimits registry
  let stateMutex ← newConnectionStateMutex registry config
    (Connection.initialState config.maxConcurrentStreams config.maxHeaderListSize)
  serveClientWithStateMutex registry config client stateMutex

def serveClient (registry : Registry) (config : Config) (client : TCP.Socket.Client) :
    Std.Async.Async Unit := do
  discard <| serveFreshClient registry config client
  closeConnectionSocket client

def acceptOne (server : Server) (registry : Registry) : Std.Async.Async Unit := do
  let client ← server.socket.accept
  serveClient registry server.config client

private def waitUntilConnectionTaskRetained (retained : IO.Promise Unit) :
    Std.Async.Async Unit := do
  match ← Std.Async.Async.ofTask retained.result? with
  | some () => pure ()
  | none => throw (IO.userError "connection task owner gate was dropped")

/-- Single teardown point for a managed connection: stop the helpers, tell the peer
why the connection is ending, record that reason locally, then retire the socket.
The GOAWAY precedes the close so the peer attributes the EOF instead of guessing. -/
private def finishManagedClient (server : Server) (id : Nat) (client : TCP.Socket.Client)
    (writer : SocketWriter)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (connection? : Option ActiveConnection) (closeCause : IO.Ref (Option CloseCause))
    (keepaliveTask? : Option (Task (Except IO.Error Unit))) : Std.Async.Async Unit := do
  discard <| _root_.Http2.CancellationToken.cancel stopToken
    (reason := Std.CancellationReason.shutdown)
  match keepaliveTask? with
  | none => pure ()
  | some task =>
      try Std.Async.Async.ofAsyncTask task catch _ => pure ()
  -- Full dispatch and user-stream cancellation runs only here, inside the
  -- retained connection owner. An uncooperative nested task therefore keeps
  -- this exact owner registered and is reported by finite Server.wait.
  discard <| Connection.cancelActiveSharedOwned stateMutex
  let cause := (← closeCause.get).getD CloseCause.peerClosed
  recordClosedConnection server id cause
  sendCauseGoAway (some writer) none stateMutex cause
  unregisterActiveConnection server connection?
  -- The GOAWAY above is queued behind every response byte already accepted for
  -- this connection. Close and cooperatively join the sole writer before the
  -- transport is retired, so no writer task can outlive its connection.
  drainSocketWriter writer
  -- A received EOF is only the peer's read-side half-close; it may still be
  -- waiting for our FIN. Retire the local write side for every cause.
  closeConnectionSocket client

private def serveManagedClient (server : Server) (registry : Registry) (id : Nat)
    (client : TCP.Socket.Client) (writer : SocketWriter)
    (stateMutex : Std.Mutex Connection.State)
    (stopToken : Std.CancellationToken) (connection? : Option ActiveConnection)
    (closeCause : IO.Ref (Option CloseCause))
    (retained : IO.Promise Unit) : Std.Async.Async Unit := do
  let mut keepaliveTask? := none
  let runError? ← try
      -- The publication gate is part of the owned computation.  Even if its
      -- publisher fails, the catch below still reaches the one cleanup owner.
      waitUntilConnectionTaskRetained retained
      installDeadlineScheduler stateMutex
      if server.config.noDelay then
        client.noDelay
      let serverPreface ← initialConnectionWireBytes stateMutex
      sendBytes writer serverPreface
      keepaliveTask? ← spawnKeepalive server.config (sendBytes writer)
        stateMutex stopToken closeCause
      discard <| serveManagedClientLoop registry server.config client writer stateMutex stopToken closeCause
      pure none
    catch err =>
      -- Do not let the connection die anonymously: the failure becomes the
      -- GOAWAY the peer reads and the local close record.
      reportCloseCause closeCause (CloseCause.transportError (toString err))
      pure (some err)
  -- Exactly one path records, unregisters, drains, and retires this connection.
  finishManagedClient server id client writer stateMutex stopToken connection? closeCause keepaliveTask?
  match runError? with
  | none => pure ()
  | some err => throw err

private def spawnManagedClient (server : Server) (registry : Registry)
    (client : TCP.Socket.Client) (shutdownToken : Std.CancellationToken) : IO Unit := do
  let id ← nextActiveConnectionId server
  let stateMutex ← newConnectionStateMutex registry server.config
    (Connection.initialState server.config.maxConcurrentStreams server.config.maxHeaderListSize)
  let stopToken ← Std.CancellationToken.new
  let closeCause ← IO.mkRef (none : Option CloseCause)
  let tlsSession ← IO.mkRef (none : Option _root_.Http2.Tls.ServerSession)
  let writer ← startSocketWriter client fun err => do
    reportCloseCause closeCause (CloseCause.transportError (toString err))
    Connection.signalCancelActiveShared stateMutex
    discard <| _root_.Http2.CancellationToken.cancel stopToken
      (reason := Std.CancellationReason.shutdown)
  let connection? ← registerActiveConnection server id client stateMutex stopToken closeCause
    (some writer) tlsSession
  let retained ← IO.Promise.new
  let task ← try
      Std.Async.Async.toIO <|
        serveManagedClient server registry id client writer stateMutex stopToken connection?
          closeCause retained
    catch err =>
      -- No owner was created, so this is the only synchronous cleanup case.
      retained.resolve ()
      let cause := CloseCause.transportError (toString err)
      reportCloseCause closeCause cause
      recordClosedConnection server id cause
      discard <| _root_.Http2.CancellationToken.cancel stopToken
        (reason := Std.CancellationReason.shutdown)
      unregisterActiveConnection server connection?
      Std.Async.Async.block (retireConnection (some writer) none client)
      throw err
  retainConnectionTask server { id := id, task := task }
  retained.resolve ()
  -- Registration precedes this check.  Therefore either the shutdown caller's
  -- active snapshot sees this connection, or this side observes the sticky
  -- token transition; an accepted child cannot start behind the drain fence.
  if ← shutdownToken.isCancelled then
    match connection? with
    | none => pure ()
    | some connection =>
        try sendGracefulGoAway connection catch err => do
          reportCloseCause closeCause (CloseCause.transportError (toString err))
          discard <| _root_.Http2.CancellationToken.cancel stopToken
            (reason := Std.CancellationReason.shutdown)
  pruneFinishedConnectionTasks server

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

partial def serveForever (server : Server) (registry : Registry) : Std.Async.Async Unit := do
  let client ← server.socket.accept
  discard <| Std.Async.Async.toIO (serveClient registry server.config client)
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
    (token : Std.CancellationToken) : Std.Async.Async Unit := do
  let activeConnections ← Std.Mutex.new #[]
  let connectionTasks ← Std.Mutex.new #[]
  let nextConnectionId ← IO.mkRef 0
  let closedConnections ← Std.Mutex.new #[]
  let server := {
    server with
    shutdownToken := some token,
    activeConnections := some activeConnections,
    connectionTasks := some connectionTasks,
    nextConnectionId := some nextConnectionId,
    closedConnections := some closedConnections
  }
  acceptLoop server registry token
  signalActiveConnectionsShutdown server
  let connections ← activeConnectionSnapshot server
  for connection in connections do
    discard <| _root_.Http2.CancellationToken.cancel connection.stopToken
      (reason := Std.CancellationReason.shutdown)
  waitConnectionTasks server

def serve (registry : Registry) (config : Config := {}) : IO Server := do
  validateRegistryLimits registry
  let server ← bind config
  let token ← Std.CancellationToken.new
  let activeConnections ← Std.Mutex.new #[]
  let connectionTasks ← Std.Mutex.new #[]
  let nextConnectionId ← IO.mkRef 0
  let closedConnections ← Std.Mutex.new #[]
  let server := {
    server with
    shutdownToken := some token,
    activeConnections := some activeConnections,
    connectionTasks := some connectionTasks,
    nextConnectionId := some nextConnectionId,
    closedConnections := some closedConnections
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

private def tlsServerSend (session : _root_.Http2.Tls.ServerSession) (bytes : ByteArray) : IO Unit :=
  session.send bytes

private inductive TlsConnectionEvent where
  | received (chunk? : Option ByteArray)
  | stop
  | writerFailed
  | deadline

private def nextTlsConnectionEvent (config : Config) (session : _root_.Http2.Tls.ServerSession)
    (stopToken : Std.CancellationToken) (deadline? : Option Nat := none) :
    Std.Async.Async TlsConnectionEvent := do
  let events := #[
    Std.Async.Selectable.case (session.socket.recvSelector config.readSize) fun chunk? =>
      pure (TlsConnectionEvent.received chunk?),
    Std.Async.Selectable.case stopToken.selector fun _ =>
      pure TlsConnectionEvent.stop,
    Std.Async.Selectable.case session.writerFailureSelector fun _ =>
      pure TlsConnectionEvent.writerFailed
  ]
  match deadline? with
  | none => Std.Async.Selectable.one events
  | some deadline =>
      let remaining ← deadlineMillisecondsFromNow deadline
      if remaining == 0 then
        pure TlsConnectionEvent.deadline
      else
        let timer ← Std.Async.Selector.sleep
          (Std.Time.Millisecond.Offset.ofNat remaining)
        Std.Async.Selectable.one <| events.push <|
          Std.Async.Selectable.case timer fun _ => pure TlsConnectionEvent.deadline

/-- Observe TLS writer failure independently of the read loop.  Header
authorization intentionally runs outside the connection-state mutex but the
read owner still awaits its exact child; this watcher ensures a failed record
writer can cancel that child immediately rather than waiting for authorization
IO to return. -/
private def watchTlsWriterFailure (session : _root_.Http2.Tls.ServerSession)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (closeCause : IO.Ref (Option CloseCause)) : Std.Async.Async Unit := do
  let failed ← Std.Async.Selectable.one #[
    Std.Async.Selectable.case session.writerFailureSelector fun _ => pure true,
    Std.Async.Selectable.case stopToken.selector fun _ => pure false
  ]
  if failed then
    let message := match ← session.writerFailure? with
      | some err => toString err
      | none => "TLS record writer stopped"
    reportCloseCause closeCause (CloseCause.transportError message)
    Connection.signalCancelActiveShared stateMutex
    discard <| _root_.Http2.CancellationToken.cancel stopToken
      (reason := Std.CancellationReason.shutdown)
  else
    pure ()

/-- Apply one decrypted inbound chunk to the HTTP/2 connection; `true` means the
connection should keep serving.  Shared by the event loop below and by the
handshake leftover — application bytes the peer coalesced behind its TLS
Finished flight — so both paths report causes identically. -/
private def serveTlsInboundPlaintext (registry : Registry)
    (session : _root_.Http2.Tls.ServerSession) (stateMutex : Std.Mutex Connection.State)
    (closeCause : IO.Ref (Option CloseCause)) (plaintext : ByteArray) :
    Std.Async.Async Bool := do
  match ← Connection.processBytesEncodedSharedWithOwned
      registry stateMutex plaintext (tlsServerSend session) with
  | .ok () =>
      if Connection.isDrainedAfterOutboundGoAway (← getConnectionState stateMutex) then
        reportCloseCause closeCause CloseCause.peerClosed
        pure false
      else
        pure true
  | .error status =>
      reportCloseCause closeCause (CloseCause.protocolError status)
      discard <| Connection.cancelActiveSharedOwned stateMutex
      pure false

/-- Per-connection event loop over TLS.  Structurally the same as
`serveManagedClientLoop`, including its cause reporting: every exit records why,
and the GOAWAY naming it is emitted once by `finishManagedTlsClient` rather than
inline here, so a TLS connection dies exactly as attributably as an h2c one. -/
private partial def serveTlsClientLoop (registry : Registry) (config : Config)
    (session : _root_.Http2.Tls.ServerSession) (stateMutex : Std.Mutex Connection.State)
    (stopToken : Std.CancellationToken) (closeCause : IO.Ref (Option CloseCause)) :
    Std.Async.Async Unit := do
  let deadline? := Connection.nextPendingDeadlineFallback? (← getConnectionState stateMutex)
  match ← nextTlsConnectionEvent config session stopToken deadline? with
  | TlsConnectionEvent.stop =>
      reportCloseCause closeCause CloseCause.serverShutdown
      discard <| Connection.cancelActiveSharedOwned stateMutex
  | TlsConnectionEvent.writerFailed =>
      let message := match ← session.writerFailure? with
        | some err => toString err
        | none => "TLS record writer stopped"
      reportCloseCause closeCause (CloseCause.transportError message)
      discard <| Connection.cancelActiveSharedOwned stateMutex
  | TlsConnectionEvent.deadline =>
      match ← Connection.expirePendingDeadlinesEncodedSharedWith
          stateMutex (tlsServerSend session) with
      | .ok () =>
          serveTlsClientLoop registry config session stateMutex stopToken closeCause
      | .error status =>
          reportCloseCause closeCause (CloseCause.protocolError (.application status))
          discard <| Connection.cancelActiveSharedOwned stateMutex
  | TlsConnectionEvent.received none =>
      reportCloseCause closeCause CloseCause.peerClosed
      discard <| Connection.cancelActiveSharedOwned stateMutex
  | TlsConnectionEvent.received (some rawChunk) =>
      match ← session.feedInbound rawChunk with
      | none =>
          -- An authenticated close_notify, or transport EOF: the peer is done.
          reportCloseCause closeCause CloseCause.peerClosed
          discard <| Connection.cancelActiveSharedOwned stateMutex
      | some plaintext =>
          if ← serveTlsInboundPlaintext registry session stateMutex closeCause plaintext then
            serveTlsClientLoop registry config session stateMutex stopToken closeCause

/-- Single teardown point for a managed TLS connection, mirroring
`finishManagedClient`: record the cause, seal the GOAWAY that names it through the
session, unregister, then retire the transport.  `sendCauseGoAway` itself only
emits once the HTTP/2 preface has been seen, which is exactly "far enough along to
carry a GOAWAY" — a connection that died during the TLS handshake has no HTTP/2
framing to say it in, and gets a recorded cause but no frame. -/
private def finishManagedTlsClient (server : Server) (id : Nat)
    (client : TCP.Socket.Client) (session? : Option _root_.Http2.Tls.ServerSession)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (connection? : Option ActiveConnection) (closeCause : IO.Ref (Option CloseCause))
    (keepaliveTask? : Option (Task (Except IO.Error Unit))) :
    Std.Async.Async Unit := do
  discard <| _root_.Http2.CancellationToken.cancel stopToken
    (reason := Std.CancellationReason.shutdown)
  match keepaliveTask? with
  | none => pure ()
  | some task =>
      try Std.Async.Async.ofAsyncTask task catch _ => pure ()
  discard <| Connection.cancelActiveSharedOwned stateMutex
  let cause := (← closeCause.get).getD CloseCause.peerClosed
  recordClosedConnection server id cause
  try
    sendCauseGoAway none session? stateMutex cause
  catch _ =>
    pure ()
  unregisterActiveConnection server connection?
  -- A peer EOF/close_notify is a read-side half-close, not proof the peer cannot
  -- read our close_notify and FIN. Retire the local side for every cause.
  match session? with
  | none => closeConnectionSocket client
  | some session => retireConnection none (some session) client

private def serveManagedTlsClient (server : Server) (registry : Registry) (config : Config)
    (tlsConfig : TlsConfig) (id : Nat) (client : TCP.Socket.Client)
    (stateMutex : Std.Mutex Connection.State) (stopToken : Std.CancellationToken)
    (connection? : Option ActiveConnection) (closeCause : IO.Ref (Option CloseCause))
    (tlsSession : IO.Ref (Option _root_.Http2.Tls.ServerSession))
    (retained : IO.Promise Unit) : Std.Async.Async Unit := do
  let mut writerWatchTask? : Option (Task (Except IO.Error Unit)) := none
  let mut keepaliveTask? : Option (Task (Except IO.Error Unit)) := none
  let runError? ← try
      waitUntilConnectionTaskRetained retained
      installDeadlineScheduler stateMutex
      if config.noDelay then
        client.noDelay
      let serverConfig ← freshTlsServerConfig tlsConfig
      let (session, handshakeLeftover) ←
        _root_.Http2.Tls.ServerSession.establishWithLeftover client serverConfig
        config.readSize (stopToken := some stopToken)
      unless (← session.alpnSelected) == some "h2" do
        throw (IO.userError "gRPC TLS peer did not negotiate the h2 ALPN protocol")
      -- Publish the session before any byte of HTTP/2: from here on every
      -- teardown byte must be sealed instead of written plaintext.
      tlsSession.set (some session)
      writerWatchTask? ← some <$> Std.Async.Async.toIO
        (watchTlsWriterFailure session stateMutex stopToken closeCause)
      let preface ← initialConnectionWireBytes stateMutex
      session.send preface
      keepaliveTask? ← spawnKeepalive config (tlsServerSend session)
        stateMutex stopToken closeCause
      -- A fast client's HTTP/2 preface can ride in the same transport chunk as
      -- its TLS Finished; those bytes were decrypted during the handshake and
      -- must reach the connection before the first socket read.
      let continue? ←
        if handshakeLeftover.isEmpty then
          pure true
        else
          serveTlsInboundPlaintext registry session stateMutex closeCause handshakeLeftover
      if continue? then
        serveTlsClientLoop registry config session stateMutex stopToken closeCause
      pure none
    catch err =>
      -- A handshake that failed has no session and cannot carry HTTP/2 GOAWAY,
      -- but it still has the same one local cause/cleanup owner.
      reportCloseCause closeCause (CloseCause.transportError (toString err))
      pure (some err)
  discard <| _root_.Http2.CancellationToken.cancel stopToken
    (reason := Std.CancellationReason.shutdown)
  match writerWatchTask? with
  | none => pure ()
  | some task =>
      try
        discard <| Std.Async.Async.ofAsyncTask task
      catch _ =>
        pure ()
  finishManagedTlsClient server id client (← tlsSession.get) stateMutex stopToken
    connection? closeCause keepaliveTask?
  match runError? with
  | none => pure ()
  | some err => throw err

private def spawnManagedTlsClient (server : Server) (registry : Registry)
    (tlsConfig : TlsConfig) (client : TCP.Socket.Client)
    (shutdownToken : Std.CancellationToken) : IO Unit := do
  let id ← nextActiveConnectionId server
  let stateMutex ← newConnectionStateMutex registry server.config
    (Connection.initialState server.config.maxConcurrentStreams server.config.maxHeaderListSize)
  let stopToken ← Std.CancellationToken.new
  let closeCause ← IO.mkRef (none : Option CloseCause)
  let tlsSession ← IO.mkRef (none : Option _root_.Http2.Tls.ServerSession)
  -- Registered before the handshake runs, so `shutdown`/`wait` can see and drain a
  -- connection that is still negotiating TLS.  `sendGracefulGoAway` is a no-op
  -- until the HTTP/2 preface has been read, so registering this early cannot put a
  -- frame on a socket that is not carrying HTTP/2 yet.
  let connection? ← registerActiveConnection server id client stateMutex stopToken closeCause
    none tlsSession
  let retained ← IO.Promise.new
  let task ← try
      Std.Async.Async.toIO <|
        serveManagedTlsClient server registry server.config tlsConfig id client stateMutex
          stopToken connection? closeCause tlsSession retained
    catch err =>
      retained.resolve ()
      let cause := CloseCause.transportError (toString err)
      reportCloseCause closeCause cause
      recordClosedConnection server id cause
      discard <| _root_.Http2.CancellationToken.cancel stopToken
        (reason := Std.CancellationReason.shutdown)
      unregisterActiveConnection server connection?
      Std.Async.Async.block (retireConnection none (← tlsSession.get) client)
      throw err
  retainConnectionTask server { id := id, task := task }
  retained.resolve ()
  if ← shutdownToken.isCancelled then
    match connection? with
    | none => pure ()
    | some connection =>
        try sendGracefulGoAway connection catch err => do
          reportCloseCause closeCause (CloseCause.transportError (toString err))
          discard <| _root_.Http2.CancellationToken.cancel stopToken
            (reason := Std.CancellationReason.shutdown)
  pruneFinishedConnectionTasks server

private partial def acceptTlsLoop (server : Server) (registry : Registry)
    (tlsConfig : TlsConfig) (token : Std.CancellationToken) : Std.Async.Async Unit := do
  match ← nextAcceptLoopEvent server token with
  | AcceptLoopEvent.shutdown => pure ()
  | AcceptLoopEvent.accepted client =>
      spawnManagedTlsClient server registry tlsConfig client token
      acceptTlsLoop server registry tlsConfig token

/-- Bind, then accept connections and serve gRPC over TLS 1.3 on each. -/
def serveTls (registry : Registry) (tlsConfig : TlsConfig) (config : Config := {}) : IO Server := do
  unless tlsConfig.alpnProtocols.contains "h2" do
    throw (IO.userError "gRPC TLS server ALPN policy must include h2")
  validateRegistryLimits registry
  let server ← bind config
  let token ← Std.CancellationToken.new
  let activeConnections ← Std.Mutex.new #[]
  let connectionTasks ← Std.Mutex.new #[]
  let nextConnectionId ← IO.mkRef 0
  let closedConnections ← Std.Mutex.new #[]
  let server := {
    server with
    shutdownToken := some token,
    activeConnections := some activeConnections,
    connectionTasks := some connectionTasks,
    nextConnectionId := some nextConnectionId,
    closedConnections := some closedConnections
  }
  let task ← Std.Async.Async.toIO (acceptTlsLoop server registry tlsConfig token)
  pure { server with acceptTask := some task }

def shutdown (server : Server) : IO Unit := do
  match server.shutdownToken with
  | none => signalActiveConnectionsShutdown server
  | some token => do
      let elected ← _root_.Http2.CancellationToken.cancel token
        (reason := Std.CancellationReason.shutdown)
      if elected then
        signalActiveConnectionsShutdown server
      else
        pure ()

private def forceStopActiveConnections (server : Server) : IO Unit := do
  let connections ← activeConnectionSnapshot server
  for connection in connections do
    reportCloseCause connection.closeCause CloseCause.serverShutdown
    Connection.signalCancelActiveShared connection.stateMutex
    discard <| _root_.Http2.CancellationToken.cancel connection.stopToken
      (reason := Std.CancellationReason.shutdown)

private partial def waitActiveConnectionsDrained (server : Server)
    (remainingMs : Option Nat) : IO Bool := do
  let connections ← activeConnectionSnapshot server
  if connections.isEmpty then
    pure true
  else
    match remainingMs with
    | some 0 => pure false
    | _ =>
        for connection in connections do
          discard <| stopDrainedConnection connection
        IO.sleep 1
        waitActiveConnectionsDrained server (remainingMs.map (· - 1))

/-- Wait for the accept loop and active connections to finish.

After shutdown, `drainTimeoutMs` bounds graceful HTTP/2 drain. At its deadline
the stop tokens wake the exact retained connection owners, which get a further
bounded window to run their single dispatch-cancellation, record/unregister,
and transport-retirement path. `wait` never performs a duplicate detached
retirement, never calls `Task.get` on a live owner, and never cancels the owner
that retains nested handler handles. If a handler, user stream-cancel callback,
or transport primitive still cannot settle, `wait` throws while leaving its
owner visibly retained in `connectionTasks`; pass `none` only for an
intentionally unbounded drain. Before shutdown, `wait` remains intentionally
unbounded because it is the serving process's blocking join. -/
def wait (server : Server) (drainTimeoutMs : Option Nat := some 30000) : IO Unit := do
  let shutdownAtEntry ← match server.shutdownToken with
    | none => pure false
    | some token => token.isCancelled
  -- Calling `wait` on a live serving process intentionally remains the main
  -- blocking entry point. Once shutdown is already requested, however, even
  -- closing publication is observed with a finite bound.
  let acceptFinished ← match server.acceptTask with
    | none => pure true
    | some task =>
        if shutdownAtEntry then
          waitTaskFinishedWithin task ownerCleanupTimeoutMs
        else
          match task.get with
          | _ => pure true
  let acceptError? ← match server.acceptTask with
    | some task =>
        if acceptFinished then
          match task.get with
          | .ok () => pure none
          | .error err => pure (some err)
        else
          IO.cancel task
          pure none
    | none => pure none
  -- An accept may have won its selector concurrently with shutdown.  Joining
  -- the accept owner closes publication, and this second signal covers every
  -- connection registered by that final accepted event before drain begins.
  let shutdown ← match server.shutdownToken with
    | none => pure false
    | some token => token.isCancelled
  if shutdown && acceptFinished then
    signalActiveConnectionsShutdown server
  let drained ← if acceptFinished then
      waitActiveConnectionsDrained server drainTimeoutMs
    else
      pure false
  unless drained do
    forceStopActiveConnections server
  let ownersFinished ← waitConnectionTasksWithin server ownerCleanupTimeoutMs
  let activeFinished := (← activeConnectionSnapshot server).isEmpty
  unless acceptFinished do
    throw (IO.userError "server accept owner did not stop within its shutdown bound")
  unless ownersFinished && activeFinished do
    -- The unfinished handles stay in the server registries: the failure is
    -- bounded and observable, never converted into detached cleanup.
    throw (IO.userError "server connection owner did not retire within its shutdown bound")
  match acceptError? with
  | none => pure ()
  | some err => throw err

def isShutdown (server : Server) : IO Bool := do
  match server.shutdownToken with
  | none => pure false
  | some token => token.isCancelled

/-- Non-blocking view of the accept loop: `some err` once it has died.  `wait` reports
the same failure by throwing it, but only after the server has been shut down; a dead
accept loop otherwise presents to clients as connections that hang unaccepted, so a
serving process can poll this and fail instead. -/
def acceptFailure? (server : Server) : IO (Option IO.Error) := do
  match server.acceptTask with
  | none => pure none
  | some task =>
      if ← IO.hasFinished task then
        match task.get with
        | .ok () => pure none
        | .error err => pure (some err)
      else
        pure none

/-- Whether the server is still accepting: bound, not shut down, and with a live
accept loop.  Throws the accept loop's error if it died. -/
def checkAccepting (server : Server) : IO Bool := do
  match ← acceptFailure? server with
  | some err => throw err
  | none => pure !(← isShutdown server)

end Server
end Http2
end Grpc
