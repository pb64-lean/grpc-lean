import Std.Async.TCP

import Grpc

open Grpc

/-! Connection lifecycle: a connection that dies must say why.

Every teardown path records a `CloseCause`; once HTTP/2 is established and the
peer remains readable, it can read that cause as GOAWAY debug data before the
bounded retirement attempt. The server always keeps the local record in
`Grpc.Server.closedConnections`, including peer EOF and pre-HTTP/2 TLS failure.
-/

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def expectEq [BEq α] (actual expected : α) (message : String) : IO Unit := do
  expect (actual == expected) message

def expectStatusOk (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

/-- Generous: only bounds how long a genuine failure takes to report. -/
def observeTimeoutMs : Nat := 5000

partial def waitUntil (message : String) (remainingMs : Nat) (check : IO Bool) : IO Unit := do
  if ← check then
    pure ()
  else if remainingMs == 0 then
    throw (IO.userError message)
  else
    IO.sleep 1
    waitUntil message (remainingMs - 1) check

partial def awaitTaskWithin (task : Task (Except IO.Error α)) (remainingMs : Nat) :
    IO (Option α) := do
  if ← IO.hasFinished task then
    match task.get with
    | .ok value => pure (some value)
    | .error err => throw err
  else if remainingMs == 0 then
    pure none
  else
    IO.sleep 1
    awaitTaskWithin task (remainingMs - 1)

structure ReadHttp2FrameState where
  decoder : Http2.Frame.DecodeState := {}
  frames : Array Http2.Frame := #[]

partial def readFramesUntilFromSocket (client : Std.Async.TCP.Socket.Client)
    (state : ReadHttp2FrameState) (done : Array Http2.Frame -> Bool) :
    IO ReadHttp2FrameState := do
  if done state.frames then
    pure state
  else
    match ← (client.recv? 8192).block with
    | none => pure state
    | some chunk =>
        let decoded ← expectStatusOk (Http2.Frame.decodeChunk state.decoder chunk)
        readFramesUntilFromSocket client
          { decoder := { buffered := decoded.buffered },
            frames := state.frames.append decoded.frames }
          done

def readFramesUntil (client : Std.Async.TCP.Socket.Client) (state : ReadHttp2FrameState)
    (done : Array Http2.Frame -> Bool) (message : String) : IO ReadHttp2FrameState := do
  let readTask ← IO.asTask (readFramesUntilFromSocket client state done)
  match ← awaitTaskWithin readTask observeTimeoutMs with
  | some result =>
      unless done result.frames do
        throw (IO.userError (message ++ " (peer closed first)"))
      pure result
  | none =>
      IO.cancel readTask
      throw (IO.userError message)

partial def drainToEof (client : Std.Async.TCP.Socket.Client) : IO Unit := do
  match ← (client.recv? 8192).block with
  | none => pure ()
  | some _ => drainToEof client

/-- The peer's write side must actually end, not merely go quiet. -/
def expectPeerClosed (client : Std.Async.TCP.Socket.Client) (message : String) : IO Unit := do
  let eofTask ← IO.asTask (drainToEof client)
  match ← awaitTaskWithin eofTask observeTimeoutMs with
  | some _ => pure ()
  | none =>
      IO.cancel eofTask
      throw (IO.userError message)

def hasGoAway (frames : Array Http2.Frame) : Bool :=
  frames.any fun frame => frame.header.frameType == Http2.FrameType.goAway

def firstGoAway (frames : Array Http2.Frame) : IO Http2.GoAway.Decoded := do
  match frames.find? (fun frame => frame.header.frameType == Http2.FrameType.goAway) with
  | none => throw (IO.userError "expected a GOAWAY frame")
  | some frame => expectStatusOk (Http2.GoAway.decode frame)

def goAwayReason (decoded : Http2.GoAway.Decoded) : String :=
  String.fromUTF8! decoded.debugData

def clientSettingsWire (ack : Bool) : IO ByteArray := do
  let frame ← expectStatusOk (Http2.Settings.frame #[] (ack := ack))
  expectStatusOk (Http2.Frame.encode frame)

def connectRaw (server : Grpc.Server.Instance) : IO Std.Async.TCP.Socket.Client := do
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay
  pure client

def closeCauses (server : Grpc.Server.Instance) : IO (Array Http2.Server.CloseCause) := do
  pure ((← Grpc.Server.closedConnections server).map (·.cause))

def activeConnectionCount (server : Grpc.Server.Instance) : IO Nat := do
  match server.activeConnections with
  | none => pure 0
  | some connections => connections.atomically do pure (← get).size

def ownedConnectionCount (server : Grpc.Server.Instance) : IO Nat := do
  match server.connectionTasks with
  | none => pure 0
  | some owners => owners.atomically do pure (← get).size

def isKeepaliveTimeout : Http2.Server.CloseCause → Bool
  | .keepaliveTimeout => true
  | _ => false

def isProtocolError : Http2.Server.CloseCause → Bool
  | .protocolError _ => true
  | _ => false

/-- A connection killed for a known reason emits a GOAWAY naming that reason
before the socket is retired, and the client can attribute the close it then
observes.  The reason here is a keepalive PING the raw peer never acknowledges. -/
def testKeepaliveTimeoutIsAttributable : IO Unit := do
  let server ← Grpc.Server.serve Registry.empty {
    address := Grpc.Server.loopback 0,
    keepaliveIntervalMs := some 25,
    keepaliveTimeoutMs := 50
  }
  let client ← connectRaw server
  -- A complete client preface, then silence: PINGs are never acknowledged.
  (client.send (Http2.connectionPreface.append (← clientSettingsWire false))).block

  let state ← readFramesUntil client {} hasGoAway
    "keepalive timeout did not emit a GOAWAY"
  let goAway ← firstGoAway state.frames
  expectEq (goAwayReason goAway) "keepalive ping timeout"
    "keepalive-timeout GOAWAY must name the keepalive timeout as the cause"
  expectEq goAway.errorCode Http2.ErrorCode.noError
    "a keepalive timeout is not a framing violation by the peer"
  expectPeerClosed client "keepalive timeout did not retire the socket"

  waitUntil "keepalive timeout was not recorded on the server" observeTimeoutMs do
    pure ((← closeCauses server).any isKeepaliveTimeout)
  Grpc.Server.shutdown server
  Grpc.Server.wait server

/-- A connection error kills the connection, and the GOAWAY carries the status
message so the peer knows which of its bytes were fatal.  Here the client
preface is followed by a SETTINGS *ack*, which RFC 9113 §3.4 forbids. -/
def testConnectionErrorIsAttributable : IO Unit := do
  let server ← Grpc.Server.serve Registry.empty { address := Grpc.Server.loopback 0 }
  let client ← connectRaw server
  (client.send (Http2.connectionPreface.append (← clientSettingsWire true))).block

  let state ← readFramesUntil client {} hasGoAway
    "connection error did not emit a GOAWAY"
  let goAway ← firstGoAway state.frames
  expectEq goAway.errorCode Http2.ErrorCode.internalError
    "a connection error GOAWAY must not claim NO_ERROR"
  expect (((goAwayReason goAway).splitOn "SETTINGS").length > 1)
    ("connection-error GOAWAY must carry the failing status, got: " ++ goAwayReason goAway)
  expectPeerClosed client "connection error did not retire the socket"

  waitUntil "connection error was not recorded on the server" observeTimeoutMs do
    pure ((← closeCauses server).any isProtocolError)
  let recorded ← Grpc.Server.closedConnections server
  match recorded.find? (fun closed => isProtocolError closed.cause) with
  | none => throw (IO.userError "expected a recorded protocol-error close")
  | some closed =>
      expectEq closed.cause.describe (goAwayReason goAway)
        "the recorded cause and the cause the peer was told must agree"
  Grpc.Server.shutdown server
  Grpc.Server.wait server

/-- An ordinary peer half-close is attributed too and does not provoke a GOAWAY,
but the server must still finish its own write side so the peer observes EOF. -/
def testPeerCloseIsAttributable : IO Unit := do
  let server ← Grpc.Server.serve Registry.empty { address := Grpc.Server.loopback 0 }
  let client ← connectRaw server
  (client.send (Http2.connectionPreface.append (← clientSettingsWire false))).block
  let _ ← readFramesUntil client {} (fun frames => frames.size > 0)
    "server did not send its preface"
  (client.shutdown).block

  waitUntil "peer close was not recorded on the server" observeTimeoutMs do
    pure (!(← Grpc.Server.closedConnections server).isEmpty)
  let causes ← closeCauses server
  expect (causes.any fun cause => match cause with | .peerClosed => true | _ => false)
    "a peer-initiated close must be recorded as such"
  expectPeerClosed client "server did not answer peer half-close with a local FIN"
  Grpc.Server.shutdown server
  Grpc.Server.wait server

/-- The accept loop is observable while the server runs, so a dead one is a
reportable failure rather than clients hanging on connect. -/
def testAcceptLoopIsObservable : IO Unit := do
  let server ← Grpc.Server.serve Registry.empty { address := Grpc.Server.loopback 0 }
  expect (← Grpc.Server.checkAccepting server) "a fresh server must report that it accepts"
  match ← Grpc.Server.acceptFailure? server with
  | none => pure ()
  | some err => throw (IO.userError s!"live accept loop reported a failure: {err}")

  let client ← connectRaw server
  (client.send (Http2.connectionPreface.append (← clientSettingsWire false))).block
  let _ ← readFramesUntil client {} (fun frames => frames.size > 0)
    "accepting server did not serve the accepted connection"
  (client.shutdown).block

  Grpc.Server.shutdown server
  Grpc.Server.wait server
  expect (!(← Grpc.Server.checkAccepting server)) "a shut-down server must not report accepting"
  match ← Grpc.Server.acceptFailure? server with
  | none => pure ()
  | some err => throw (IO.userError s!"clean shutdown reported an accept failure: {err}")

/-- A plaintext send can fail while the peer deliberately keeps its write side
open, so socket receive alone cannot wake the client reader.  The writer's
sticky failure selector must wake that exact reader, which owns state failure
and bounded transport retirement; both background handles then terminate before
an explicit `Client.close`. -/
def testPlaintextClientWriterFailureWakesReader : IO Unit := do
  let listener ← Std.Async.TCP.Socket.Server.mk
  listener.bind (Grpc.Server.loopback 0)
  listener.listen 8
  let address ← listener.getSockName
  let acceptTask ← Std.Async.Async.toIO listener.accept
  let connection ← Client.connect { address := address }
  let peer ← Std.Async.Async.block (Std.Async.Async.ofAsyncTask acceptTask)

  -- Ensure the initial preface has left the sole writer before making future
  -- sends fail. `shutdown` is local write-side only: `peer` remains open for
  -- writing, so the client's reader cannot observe EOF and must use the token.
  let some preface ← (peer.recv? 4096).block
    | throw (IO.userError "raw peer closed before receiving the client preface")
  expect (!preface.isEmpty) "client emitted an empty HTTP/2 preface"
  (connection.socket.shutdown).block

  match ← Std.Async.Async.block
      (Client.start connection "/lean.example.proto.NoteService/Echo") with
  | .error status =>
      throw (IO.userError s!"call was rejected before exercising writer failure: {status.messageD}")
  | .ok _ => pure ()

  waitUntil "plaintext writer failure did not wake and retire the reader" observeTimeoutMs do
    Client.backgroundTasksFinished connection
  let dead ← connection.state.atomically do pure (← get).dead
  match dead with
  | none => throw (IO.userError "finished reader did not mark the failed writer connection dead")
  | some _ => pure ()
  match ← Std.Async.Async.block
      (Client.start connection "/lean.example.proto.NoteService/Echo") with
  | .ok _ => throw (IO.userError "writer-failed connection accepted a new call")
  | .error _ => pure ()

  Std.Async.Async.block (Client.close connection)
  try (peer.shutdown).block catch _ => pure ()

partial def cooperativeResponseWait (started : IO.Ref Bool) : GrpcM (Option ByteArray) := do
  started.set true
  if ← IO.checkCanceled then
    throw (Status.cancelled "response handler cancelled")
  IO.sleep 1
  cooperativeResponseWait started

partial def uncooperativeResponseWait (started release : IO.Ref Bool) :
    GrpcM (Option ByteArray) := do
  started.set true
  if ← release.get then
    throw (Status.cancelled "test released uncooperative response handler")
  IO.sleep 10
  uncooperativeResponseWait started release

partial def neverReturningStreamCancel (release : IO.Ref Bool) : GrpcM Unit := do
  if ← release.get then
    pure ()
  else
    IO.sleep 10
    neverReturningStreamCancel release

def startStreamingRequest (server : Grpc.Server.Instance) (path : String) :
    IO Client.Connection := do
  let connection ← Client.connect { address := server.localAddress }
  let call ← match ← Std.Async.Async.block (Client.start connection path) with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)
  discard <| expectStatusOk (← Std.Async.Async.block (call.send ByteArray.empty))
  discard <| expectStatusOk (← Std.Async.Async.block call.closeSend)
  pure connection

/-- The ordinary nested-cancellation path invokes a response-stream callback
exactly once, joins its cooperative handler, and retires both public owner
registries before a finite post-shutdown wait returns. -/
def testShutdownOwnsCooperativeStreamCancellation : IO Unit := do
  let method : MethodName := {
    service := "lean.example.proto.LifecycleService",
    method := "CooperativeStream"
  }
  let recvStarted ← IO.mkRef false
  let cancelCount ← IO.mkRef 0
  let registry := Registry.empty.registerServerStreamingStream method fun _ => do
    pure {
      messages := {
        recv? := cooperativeResponseWait recvStarted,
        cancel := cancelCount.modify fun count => count + 1
      },
      status := Status.ok
    }
  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let connection ← startStreamingRequest server method.path
  waitUntil "cooperative response stream did not enter recv" observeTimeoutMs recvStarted.get

  Grpc.Server.shutdown server
  let waitTask ← IO.asTask (Grpc.Server.wait server (drainTimeoutMs := some 0))
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | none =>
      IO.cancel waitTask
      throw (IO.userError "finite shutdown did not join cooperative stream cancellation")
  | some () => pure ()
  expectEq (← cancelCount.get) 1
    "cooperative response cancel callback must be taken exactly once"
  expectEq (← activeConnectionCount server) 0
    "cooperative stream shutdown left an active connection"
  expectEq (← ownedConnectionCount server) 0
    "cooperative stream shutdown left a retained connection owner"
  Std.Async.Async.block (Client.close connection)

/-- Arbitrary user cancellation must never execute inline in `Server.wait` or
be orphaned. Both the never-returning response cancel and its uncooperative
handler remain beneath the exact managed connection task; finite wait reports
the ownership timeout and leaves that task and connection observable. -/
def testFiniteWaitRetainsUncooperativeNestedCancellation : IO Unit := do
  let method : MethodName := {
    service := "lean.example.proto.LifecycleService",
    method := "UncooperativeStream"
  }
  let recvStarted ← IO.mkRef false
  let cancelStarted ← IO.mkRef false
  let cancelCount ← IO.mkRef 0
  let release ← IO.mkRef false
  let registry := Registry.empty.registerServerStreamingStream method fun _ => do
    pure {
      messages := {
        recv? := uncooperativeResponseWait recvStarted release,
        cancel := do
          cancelCount.modify fun count => count + 1
          cancelStarted.set true
          neverReturningStreamCancel release
      },
      status := Status.ok
    }
  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let connection ← startStreamingRequest server method.path
  waitUntil "uncooperative response stream did not enter recv" observeTimeoutMs recvStarted.get

  Grpc.Server.shutdown server
  let waitTask ← IO.asTask do
    try
      Grpc.Server.wait server (drainTimeoutMs := some 0)
      pure (none : Option IO.Error)
    catch err =>
      pure (some err)
  let waitError ← match ← awaitTaskWithin waitTask observeTimeoutMs with
    | none =>
        IO.cancel waitTask
        throw (IO.userError "finite Server.wait synchronously hung in user stream cancellation")
    | some none =>
        throw (IO.userError "finite Server.wait silently retired uncooperative nested work")
    | some (some err) => pure err
  expect (((toString waitError).splitOn "connection owner did not retire").length > 1)
    s!"finite wait reported the wrong ownership failure: {waitError}"
  waitUntil "never-returning response cancel callback did not start" observeTimeoutMs
    cancelStarted.get
  expectEq (← cancelCount.get) 1
    "shutdown races must take a never-returning response cancel callback once"
  expectEq (← activeConnectionCount server) 1
    "uncooperative nested work lost its observable active connection"
  expectEq (← ownedConnectionCount server) 1
    "uncooperative nested work lost its exact registered connection owner"
  -- Release the simulated permanently-blocked user code. The same retained
  -- owner must resume, perform its one cleanup path, and disappear; no detached
  -- rescue task is allowed to do this for it.
  release.set true
  let cleanupTask ← IO.asTask (Grpc.Server.wait server (drainTimeoutMs := some 0))
  match ← awaitTaskWithin cleanupTask observeTimeoutMs with
  | none =>
      IO.cancel cleanupTask
      throw (IO.userError "retained connection owner did not resume after releasing user code")
  | some () => pure ()
  expectEq (← activeConnectionCount server) 0
    "released nested work left an active connection"
  expectEq (← ownedConnectionCount server) 0
    "released nested work left a registered connection owner"
  Std.Async.Async.block (Client.close connection)

/-! ## The same guarantees over TLS

A TLS connection used to die in silence: its error was swallowed, it registered
no `ActiveConnection`, so it took part in neither graceful shutdown nor the
`closedConnections` record, and nothing it sent on the way out was attributable.
These are the h2c tests above, re-run through a real TLS 1.3 session — which also
pins that the teardown bytes are *sealed*: a GOAWAY written straight to the
socket would be plaintext on an encrypted stream, and `feedInbound` below could
not decrypt it. -/

def tlsIdentity : IO Http2.Server.TlsConfig := do
  let certificateDer ← IO.FS.readBinFile "Test/Fixtures/Tls/server_cert.der"
  let signingKey ← IO.FS.readBinFile "Test/Fixtures/Tls/server_key.raw"
  pure { certificateChain := #[certificateDer], signingKey := signingKey }

def rawTlsClientHello : IO ByteArray := do
  let entropy ← IO.getRandomBytes 96
  let config : _root_.Tls.Client.Config := {
    clientRandom := entropy.extract 0 32,
    x25519Private := entropy.extract 32 64,
    legacySessionId := entropy.extract 64 96,
    serverName := some "localhost",
    alpnProtocols := #["h2"]
  }
  match _root_.Tls.Client.start config with
  | .ok output => pure output.wireBytes
  | .error err => throw (IO.userError s!"could not construct raw ClientHello: {repr err}")

/-- A raw TLS peer: a real TLS 1.3 handshake with ALPN "h2", and nothing above it,
so this test drives HTTP/2 by hand exactly as the plaintext tests do. -/
def connectRawTls (server : Grpc.Server.Instance) : IO Grpc.Tls.ClientSession := do
  let socket ← Std.Async.TCP.Socket.Client.mk
  (socket.connect server.localAddress).block
  socket.noDelay
  let entropy ← IO.getRandomBytes 96
  let config : _root_.Tls.Client.Config := {
    clientRandom := entropy.extract 0 32,
    x25519Private := entropy.extract 32 64,
    legacySessionId := entropy.extract 64 96,
    serverName := some "localhost",
    alpnProtocols := #["h2"]
  }
  let (session, handshakeLeftover) ←
    Std.Async.Async.block (Grpc.Tls.ClientSession.establishWithLeftover socket config 16384)
  -- This server never sends 0.5-RTT application data, so callers may treat the
  -- socket as the sole frame source; fail loudly if that ever changes.
  unless handshakeLeftover.isEmpty do
    throw (IO.userError "unexpected TLS application bytes coalesced with the server flight")
  pure session

partial def readTlsFramesUntilFromSession (session : Grpc.Tls.ClientSession)
    (state : ReadHttp2FrameState) (done : Array Http2.Frame -> Bool) :
    IO ReadHttp2FrameState := do
  if done state.frames then
    pure state
  else
    match ← (session.socket.recv? 8192).block with
    | none => pure state
    | some raw =>
        match ← session.feedInbound raw with
        | none => pure state
        | some plaintext =>
            let decoded ← expectStatusOk (Http2.Frame.decodeChunk state.decoder plaintext)
            readTlsFramesUntilFromSession session
              { decoder := { buffered := decoded.buffered },
                frames := state.frames.append decoded.frames }
              done

def readTlsFramesUntil (session : Grpc.Tls.ClientSession) (state : ReadHttp2FrameState)
    (done : Array Http2.Frame -> Bool) (message : String) : IO ReadHttp2FrameState := do
  let readTask ← IO.asTask (readTlsFramesUntilFromSession session state done)
  match ← awaitTaskWithin readTask observeTimeoutMs with
  | some result =>
      unless done result.frames do
        throw (IO.userError (message ++ " (peer closed first)"))
      pure result
  | none =>
      IO.cancel readTask
      throw (IO.userError message)

def expectTlsClientOk {α} (result : Except _root_.Tls.Client.Error α) (message : String) :
    IO α :=
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError s!"{message}: {err}")

/-- Feed server handshake flights until the client is connected, but do NOT send
the final client flight (CCS + Finished): return it with the connected state so
the caller controls what shares its transport chunk. -/
partial def completeTlsHandshakeKeepingFlight (socket : Std.Async.TCP.Socket.Client)
    (state : _root_.Tls.Client.State) : IO (_root_.Tls.Client.State × ByteArray) := do
  let some chunk ← (socket.recv? 8192).block
    | throw (IO.userError "server closed during the coalescing-test handshake")
  let output ← expectTlsClientOk (_root_.Tls.Client.feed state chunk)
    "coalescing-test handshake feed"
  if output.state.connected then
    pure (output.state, output.wireBytes)
  else do
    unless output.wireBytes.isEmpty do
      (socket.send output.wireBytes).block
    completeTlsHandshakeKeepingFlight socket output.state

partial def readCoalescedTestFrames (socket : Std.Async.TCP.Socket.Client)
    (state : _root_.Tls.Client.State) (decode : ReadHttp2FrameState)
    (done : Array Http2.Frame -> Bool) : IO ReadHttp2FrameState := do
  if done decode.frames then
    pure decode
  else
    match ← (socket.recv? 8192).block with
    | none => pure decode
    | some raw =>
        let output ← expectTlsClientOk (_root_.Tls.Client.feed state raw)
          "coalescing-test application feed"
        let decoded ← expectStatusOk (Http2.Frame.decodeChunk decode.decoder output.plaintext)
        readCoalescedTestFrames socket output.state
          { decoder := { buffered := decoded.buffered },
            frames := decode.frames.append decoded.frames }
          done

/-- A fast client's HTTP/2 preface routinely rides in the same transport chunk as
its TLS Finished flight (the kernel coalesces the two back-to-back writes).  The
server decrypts those application bytes while still inside its handshake loop, so
losing them desynchronizes the connection at its very first frame — the failure
surfaces as `invalid HTTP/2 client connection preface`.  Drive the handshake by
hand so Finished, preface, SETTINGS, and a PING are one `send`, then require the
PING ack and no GOAWAY. -/
def testTlsCoalescedPrefaceAfterFinished : IO Unit := do
  let server ← Grpc.Server.serveTls Registry.empty (← tlsIdentity)
    { address := Grpc.Server.loopback 0 }
  let socket ← Std.Async.TCP.Socket.Client.mk
  (socket.connect server.localAddress).block
  socket.noDelay
  let entropy ← IO.getRandomBytes 96
  let config : _root_.Tls.Client.Config := {
    clientRandom := entropy.extract 0 32,
    x25519Private := entropy.extract 32 64,
    legacySessionId := entropy.extract 64 96,
    serverName := some "localhost",
    alpnProtocols := #["h2"]
  }
  let hello ← expectTlsClientOk (_root_.Tls.Client.start config) "coalescing-test ClientHello"
  (socket.send hello.wireBytes).block
  let (state, finishedFlight) ← completeTlsHandshakeKeepingFlight socket hello.state
  let pingPayload := ByteArray.mk (Array.replicate 8 7)
  let ping ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode ping)
  let appBytes := (Http2.connectionPreface.append (← clientSettingsWire false)).append pingWire
  let sealed ← expectTlsClientOk (_root_.Tls.Client.sealApplication state appBytes)
    "coalescing-test seal"
  (socket.send (finishedFlight.append sealed.wireBytes)).block
  let donePingAck (frames : Array Http2.Frame) : Bool :=
    frames.any Http2.Ping.isAck || hasGoAway frames
  let readTask ← IO.asTask (readCoalescedTestFrames socket sealed.state {} donePingAck)
  let frames ← match ← awaitTaskWithin readTask observeTimeoutMs with
    | some result => pure result.frames
    | none =>
        IO.cancel readTask
        -- Half-close so the reader's parked recv observes the server teardown
        -- instead of pinning a worker (and the process) past the failure.
        try (socket.shutdown).block catch _ => pure ()
        try discard <| awaitTaskWithin readTask 1000 catch _ => pure ()
        throw (IO.userError "coalesced preface: no PING ack within the observation window")
  expect (!hasGoAway frames)
    "a preface coalesced behind TLS Finished must not be treated as a protocol error"
  expect (frames.any Http2.Ping.isAck)
    "the server must answer the PING that rode in with the TLS Finished chunk"
  Grpc.Server.shutdown server
  Grpc.Server.wait server

/-- A connection error over TLS kills the connection, and the GOAWAY naming the
status is sealed through the session so the peer can actually read it.  As in the
plaintext case the offending bytes are a SETTINGS *ack* right after the preface,
which RFC 9113 §3.4 forbids. -/
def testTlsConnectionErrorIsAttributable : IO Unit := do
  let server ← Grpc.Server.serveTls Registry.empty (← tlsIdentity)
    { address := Grpc.Server.loopback 0 }
  let session ← connectRawTls server
  expectEq (← session.alpnSelected) (some "h2") "the TLS peer must negotiate h2"
  session.send (Http2.connectionPreface.append (← clientSettingsWire true))

  let state ← readTlsFramesUntil session {} hasGoAway
    "TLS connection error did not emit a GOAWAY"
  let goAway ← firstGoAway state.frames
  expectEq goAway.errorCode Http2.ErrorCode.internalError
    "a TLS connection error GOAWAY must not claim NO_ERROR"
  expect (((goAwayReason goAway).splitOn "SETTINGS").length > 1)
    ("TLS connection-error GOAWAY must carry the failing status, got: " ++ goAwayReason goAway)
  expectPeerClosed session.socket "TLS connection error did not retire the socket"

  waitUntil "TLS connection error was not recorded on the server" observeTimeoutMs do
    pure ((← closeCauses server).any isProtocolError)
  let recorded ← Grpc.Server.closedConnections server
  match recorded.find? (fun closed => isProtocolError closed.cause) with
  | none => throw (IO.userError "expected a recorded protocol-error close over TLS")
  | some closed =>
      expectEq closed.cause.describe (goAwayReason goAway)
        "the recorded TLS cause and the cause the peer was told must agree"
  Grpc.Server.shutdown server
  Grpc.Server.wait server

/-- A TLS peer that closes is attributed as such, exactly as a plaintext one is. -/
def testTlsPeerCloseIsAttributable : IO Unit := do
  let server ← Grpc.Server.serveTls Registry.empty (← tlsIdentity)
    { address := Grpc.Server.loopback 0 }
  let session ← connectRawTls server
  session.send (Http2.connectionPreface.append (← clientSettingsWire false))
  let _ ← readTlsFramesUntil session {} (fun frames => frames.size > 0)
    "TLS server did not send its preface"
  Std.Async.Async.block session.close

  waitUntil "TLS peer close was not recorded on the server" observeTimeoutMs do
    pure (!(← Grpc.Server.closedConnections server).isEmpty)
  let causes ← closeCauses server
  expect (causes.any fun cause => match cause with | .peerClosed => true | _ => false)
    "a peer-initiated TLS close must be recorded as such"
  expectPeerClosed session.socket
    "TLS server did not answer close_notify/peer half-close with a local FIN"
  Grpc.Server.shutdown server
  Grpc.Server.wait server

/-- Shutdown must interrupt a peer that connected but never sent ClientHello;
otherwise the retained handshake task makes `Server.wait` unbounded. -/
def testTlsShutdownCancelsSilentHandshake : IO Unit := do
  let server ← Grpc.Server.serveTls Registry.empty (← tlsIdentity)
    { address := Grpc.Server.loopback 0 }
  let client ← connectRaw server
  -- Give the accept loop time to publish the pre-handshake connection.
  IO.sleep 20
  Grpc.Server.shutdown server
  let waitTask ← IO.asTask (Grpc.Server.wait server)
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | some () => pure ()
  | none =>
      IO.cancel waitTask
      throw (IO.userError "TLS shutdown did not cancel a silent ClientHello peer")
  expectPeerClosed client "silent TLS handshake socket was not retired on shutdown"

/-- A more adversarial handshake peer sends ClientHello but never reads.  A
large (still uint24-valid) certificate flight fills the TCP send path.  The stop
token must win against that exact handshake-send task so `Server.wait` reaches
the one owner cleanup path rather than blocking forever or launching a detached
second retirement. -/
def testTlsShutdownCancelsStalledHandshakeSend : IO Unit := do
  let identity ← tlsIdentity
  let some leaf := identity.certificateChain[0]?
    | throw (IO.userError "TLS fixture identity has no leaf certificate")
  -- 16k * (349-byte cert + framing) is about 5.7 MiB: below TLS's uint24
  -- Certificate limit, but beyond Linux's maximum autotuned send buffer.
  let stalledIdentity := {
    identity with certificateChain := Array.replicate 16000 leaf
  }
  let server ← Grpc.Server.serveTls Registry.empty stalledIdentity
    { address := Grpc.Server.loopback 0 }
  let client ← connectRaw server
  (client.send (← rawTlsClientHello)).block
  waitUntil "TLS handshake connection owner was not published" observeTimeoutMs do
    pure ((← activeConnectionCount server) == 1 && (← ownedConnectionCount server) == 1)
  let owner ← match server.connectionTasks with
    | none => throw (IO.userError "TLS server did not expose its owner registry")
    | some ownersMutex => do
        let owners ← ownersMutex.atomically get
        let some owner := owners[0]?
          | throw (IO.userError "TLS handshake owner disappeared before shutdown")
        pure owner
  -- Let the owner construct and enter the oversized server-flight send.
  IO.sleep 3000

  Grpc.Server.shutdown server
  let waitTask ← IO.asTask (Grpc.Server.wait server (drainTimeoutMs := some 10))
  match ← awaitTaskWithin waitTask 10000 with
  | none =>
      IO.cancel waitTask
      throw (IO.userError "Server.wait hung on an unread TLS handshake flight")
  | some () => pure ()

  expectEq (← activeConnectionCount server) 0
    "bounded TLS shutdown returned with an active handshake connection"
  expectEq (← ownedConnectionCount server) 0
    "bounded TLS shutdown returned with a retained handshake owner"
  let records ← Grpc.Server.closedConnections server
  expectEq records.size 1
    "the single handshake owner must produce exactly one close record"
  match owner.task.get with
  | .ok () => throw (IO.userError "stalled TLS handshake owner unexpectedly succeeded")
  | .error err =>
      expect (((toString err).splitOn "handshake send cancelled").length > 1)
        s!"shutdown cancelled a later receive, not the stalled handshake send: {err}"
  try (client.shutdown).block catch _ => pure ()

/-- A live TLS connection takes part in graceful shutdown: it is registered, so
`shutdown` reaches it with a GOAWAY(NO_ERROR), `wait` drains it rather than
returning vacuously, and it leaves a `serverShutdown` record behind. -/
def testTlsShutdownDrainsConnections : IO Unit := do
  let server ← Grpc.Server.serveTls Registry.empty (← tlsIdentity)
    { address := Grpc.Server.loopback 0 }
  let session ← connectRawTls server
  session.send (Http2.connectionPreface.append (← clientSettingsWire false))
  -- Carry the decoder forward, so a frame split across TLS records is not
  -- re-parsed from the middle by the second read.
  let afterPreface ← readTlsFramesUntil session {} (fun frames => frames.size > 0)
    "TLS server did not send its preface"

  Grpc.Server.shutdown server
  let state ← readTlsFramesUntil session afterPreface hasGoAway
    "TLS graceful shutdown did not reach the connection with a GOAWAY"
  let goAway ← firstGoAway state.frames
  expectEq goAway.errorCode Http2.ErrorCode.noError
    "a graceful TLS shutdown GOAWAY must claim NO_ERROR"
  Grpc.Server.wait server

  let causes ← closeCauses server
  expect (causes.any fun cause => match cause with | .serverShutdown => true | _ => false)
    "a TLS connection drained by shutdown must be recorded as serverShutdown"

def main : IO Unit := do
  IO.println "connection-lifecycle test: cause-carrying teardown"
  IO.println "  keepalive timeout"
  testKeepaliveTimeoutIsAttributable
  IO.println "  plaintext protocol error"
  testConnectionErrorIsAttributable
  IO.println "  plaintext peer close"
  testPeerCloseIsAttributable
  IO.println "  accept-loop observability"
  testAcceptLoopIsObservable
  IO.println "  plaintext writer failure"
  testPlaintextClientWriterFailureWakesReader
  IO.println "  cooperative nested cancellation ownership"
  testShutdownOwnsCooperativeStreamCancellation
  IO.println "  TLS protocol error"
  testTlsConnectionErrorIsAttributable
  IO.println "  TLS peer close"
  testTlsPeerCloseIsAttributable
  IO.println "  TLS coalesced preface after Finished"
  testTlsCoalescedPrefaceAfterFinished
  IO.println "  TLS silent handshake shutdown"
  testTlsShutdownCancelsSilentHandshake
  IO.println "  TLS stalled-send handshake shutdown"
  testTlsShutdownCancelsStalledHandshakeSend
  IO.println "  TLS graceful drain"
  testTlsShutdownDrainsConnections
  IO.println "  bounded wait retains uncooperative nested cancellation"
  testFiniteWaitRetainsUncooperativeNestedCancellation
  IO.println "connection lifecycle ok"
