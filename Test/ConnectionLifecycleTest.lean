import Std.Async.TCP

import Grpc

open Grpc

/-! Connection lifecycle: a connection that dies must say why.

Every teardown path records a `CloseCause`; the peer reads it as GOAWAY debug
data before the socket is retired, and the server keeps it in
`Grpc.Server.closedConnections`.  Before this existed a dying connection was
silent: no GOAWAY, and an EOF whose timing was decided by handle finalization.
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

/-- An ordinary peer close is attributed too, and is the one cause that does not
provoke a GOAWAY: the peer that would read it is already gone. -/
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

def main : IO Unit := do
  IO.println "connection-lifecycle test: cause-carrying teardown"
  testKeepaliveTimeoutIsAttributable
  testConnectionErrorIsAttributable
  testPeerCloseIsAttributable
  testAcceptLoopIsObservable
  IO.println "connection lifecycle ok"
