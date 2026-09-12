import Std.Async.TCP

import Grpc

open Grpc
open Std.Async

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectStatusCode
    (result : Except Status α) (expected : Code) (msg : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"{msg}: unexpectedly succeeded")
  | .error status =>
      expectEq status.code expected
        s!"{msg}: got {repr status.code}, expected {repr expected}"

def echoMethod : MethodName :=
  { service := "lean.example.proto.NoteService", method := "Echo" }

def failMethod : MethodName :=
  { service := "lean.example.proto.NoteService", method := "Fail" }

def bigMethod : MethodName :=
  { service := "lean.example.proto.NoteService", method := "Big" }

def repeatByte (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

private def compressedResponseBody (sizes : Array Nat) : IO ByteArray := do
  let mut body := ByteArray.empty
  for size in sizes do
    let message := Message.gzipped (repeatByte size 0)
    expectEq message.compressed CompressionFlag.compressed
      "decoded-response bound fixture did not use gzip"
    let encoded ← match Message.encode message with
      | .ok encoded => pure encoded
      | .error status => throw (IO.userError status.messageD)
    body := body.append encoded
  pure body

/-- Compressed wire credit cannot expand into an unbounded queued response.
The exact normalized-window boundary is admitted and one production queue pop
releases its exact accounting entry; one additional decoded byte fails the RPC
with RESOURCE_EXHAUSTED and selects ENHANCE_YOUR_CALM for its stream reset. -/
private def testRetainedDecodedResponseBound : IO Unit := do
  let maxReceiveMessageSize := 4096
  let limit := Client.TestSupport.retainedDecodedResponseLimitForTest
    maxReceiveMessageSize
  let exactSizes : Array Nat := (Array.replicate 16 4096).push 4016
  let exactBody ← compressedResponseBody exactSizes
  expect (exactBody.size < limit)
    "exact-boundary gzip fixture did not compress below the decoded limit"
  let exact ← match Client.TestSupport.processResponseDataForTest
      maxReceiveMessageSize true exactBody with
    | .ok observation => pure observation
    | .error status =>
        throw (IO.userError s!"exact decoded response boundary failed: {status.messageD}")
  expectEq exact.messageCount exactSizes.size
    "exact decoded response boundary lost messages"
  expectEq exact.retainedDecodedBytes limit
    "exact decoded response boundary was not admitted"
  expectEq exact.retainedAfterOneReceive (limit - (Message.prefixLength + 4096))
    "receiving one response did not release its decoded-memory budget"

  let overSizes : Array Nat := (Array.replicate 16 4096).push 4017
  let overBody ← compressedResponseBody overSizes
  expect (overBody.size < limit)
    "over-limit gzip fixture did not demonstrate compressed-wire expansion"
  match Client.TestSupport.processResponseDataForTest
      maxReceiveMessageSize true overBody with
  | .ok _ => throw (IO.userError "over-limit decoded response queue was admitted")
  | .error status => do
      expectEq status.code Code.resourceExhausted
        "decoded response queue overflow used the wrong gRPC status"
      expectEq (Client.TestSupport.responseDataFailureResetCodeForTest status)
        _root_.Http2.ErrorCode.enhanceYourCalm
        "decoded response queue overflow used the wrong HTTP/2 reset code"

def testRegistry : Registry :=
  Registry.empty
    |>.registerUnary echoMethod (fun request => do
        pure {
          metadata := _root_.Http2.Headers.empty.insert "handled-by" "lean-http2",
          data := request.data,
          status := Status.ok
        })
    |>.registerUnary failMethod (fun _ => do
        throw (Status.invalidArgument "nope"))
    |>.registerUnary bigMethod (fun _ => do
        pure { metadata := _root_.Http2.Headers.empty, data := repeatByte 200000 7, status := Status.ok })

partial def waitUntil (description : String) (remainingMilliseconds : Nat)
    (condition : IO Bool) : IO Unit := do
  if ← condition then
    pure ()
  else if remainingMilliseconds == 0 then
    throw (IO.userError s!"{description}: watchdog expired")
  else
    IO.sleep 1
    waitUntil description (remainingMilliseconds - 1) condition

def connectRawPeer : IO (Client.Connection × Std.Async.TCP.Socket.Client) := do
  let listener ← Std.Async.TCP.Socket.Server.mk
  listener.bind (Grpc.Server.loopback 0)
  listener.listen 8
  let address ← listener.getSockName
  let acceptTask ← Std.Async.Async.toIO listener.accept
  let connection ← Client.connect { address := address }
  let peer ← Std.Async.Async.block (Std.Async.Async.ofAsyncTask acceptTask)
  let some preface ← (peer.recv? 4096).block
    | throw (IO.userError "raw peer closed before receiving the client preface")
  expect (!preface.isEmpty) "client emitted an empty HTTP/2 preface"
  pure (connection, peer)

def testPeerEofRetiresClient : IO Unit := do
  let (connection, peer) ← connectRawPeer
  (peer.shutdown).block
  waitUntil "peer EOF did not retire client background owners" 5000 do
    Client.backgroundTasksFinished connection
  Async.block (Client.close connection)

def testProtocolErrorRetiresClient : IO Unit := do
  let (connection, peer) ← connectRawPeer
  let malformed : _root_.Http2.Frame := {
    header := {
      length := 0
      frameType := .data
      flags := 0
      streamId := 0
    }
  }
  let wire ← match _root_.Http2.Frame.encode malformed with
    | .ok wire => pure wire
    | .error error => throw (IO.userError error.messageD)
  (peer.send wire).block
  waitUntil "protocol error did not retire client background owners" 5000 do
    Client.backgroundTasksFinished connection
  let dead ← connection.state.atomically do pure (← get).dead
  expect dead.isSome "protocol-error retirement did not mark the client dead"
  Async.block (Client.close connection)
  try (peer.shutdown).block catch _ => pure ()

def main : IO Unit := do
  testRetainedDecodedResponseBound
  IO.println "client retained decoded-response bound ok"

  let zeroReadRejected ← try
    let invalid ← Client.connect { readSize := 0 }
    Async.block (Client.close invalid)
    pure false
  catch error =>
    expect (error.toString.contains "readSize must be positive")
      s!"zero readSize returned the wrong error: {error}"
    pure true
  expect zeroReadRejected "zero readSize unexpectedly opened a client connection"

  let oversizedWindowRejected ← try
    let invalid ← Client.connect {
      maxReceiveMessageSize := _root_.Http2.Connection.maximumWindowSize
    }
    Async.block (Client.close invalid)
    pure false
  catch error =>
    expect (error.toString.contains "largest safe HTTP/2 stream receive window")
      s!"oversized receive window returned the wrong error: {error}"
    pure true
  expect oversizedWindowRejected
    "oversized receive window unexpectedly opened a client connection"
  IO.println "client pre-ownership configuration validation ok"

  testPeerEofRetiresClient
  IO.println "client peer-EOF retirement ok"
  testProtocolErrorRetiresClient
  IO.println "client protocol-error retirement ok"

  let server ← Grpc.Server.serve testRegistry {
    address := Http2.Server.loopback 0
  }
  let port := match server.localAddress with
    | .v4 addr => addr.port
    | .v6 addr => addr.port
  let client ← Client.connect { address := Http2.Server.loopback port }

  -- unary echo
  let payload := repeatByte 64 42
  match ← Async.block (Client.call client "/lean.example.proto.NoteService/Echo" payload) with
  | .error status => throw (IO.userError s!"echo failed: {status.messageD}")
  | .ok (_, response) =>
      expectEq response payload "echo response should match request"
  IO.println "client unary echo ok"

  -- second call on the same connection (stream id advance + HPACK state reuse)
  let payload2 := repeatByte 10 1
  match ← Async.block (Client.call client "/lean.example.proto.NoteService/Echo" payload2) with
  | .error status => throw (IO.userError s!"second echo failed: {status.messageD}")
  | .ok (_, response) =>
      expectEq response payload2 "second echo response should match request"
  IO.println "client connection reuse ok"

  -- The shared stream phase is the source of truth for request half-close, so
  -- repeated closeSend calls are idempotent without parallel client flags.
  let streaming ← Async.block (Client.start client
    "/lean.example.proto.NoteService/Echo")
  let streaming ← match streaming with
    | .ok call => pure call
    | .error status => throw (IO.userError s!"streaming echo start failed: {status.messageD}")
  match ← Async.block (streaming.send payload2) with
  | .ok () => pure ()
  | .error status => throw (IO.userError s!"streaming echo send failed: {status.messageD}")
  match ← Async.block streaming.closeSend with
  | .ok () => pure ()
  | .error status => throw (IO.userError s!"streaming echo close failed: {status.messageD}")
  match ← Async.block streaming.closeSend with
  | .ok () => pure ()
  | .error status => throw (IO.userError s!"repeated closeSend failed: {status.messageD}")
  expectStatusCode (← Async.block (streaming.send payload2)) .internal
    "send after closeSend"
  match ← Async.block streaming.recv? with
  | .ok (some response) =>
      expectEq response payload2 "streaming echo should return its response"
  | .ok none => throw (IO.userError "streaming echo ended before its response")
  | .error status => throw (IO.userError s!"streaming echo receive failed: {status.messageD}")
  match ← Async.block streaming.recv? with
  | .ok none => pure ()
  | .ok (some _) => throw (IO.userError "streaming echo returned an extra response")
  | .error status => throw (IO.userError s!"streaming echo completion failed: {status.messageD}")
  match ← Async.block streaming.finish with
  | .ok (status, _, _) => expectEq status.code Code.ok "streaming echo should finish OK"
  | .error status => throw (IO.userError s!"streaming echo finish failed: {status.messageD}")
  IO.println "client protocol-owned half-close ok"

  -- error status propagation
  match ← Async.block (Client.call client "/lean.example.proto.NoteService/Fail" payload) with
  | .ok _ => throw (IO.userError "expected error status from Fail")
  | .error status => do
      expectEq status.code Code.invalidArgument "Fail should surface INVALID_ARGUMENT"
      expectEq status.message (some "nope") "grpc-message should round-trip"
  IO.println "client error propagation ok"

  -- unimplemented method → trailers-only response
  match ← Async.block (Client.call client "/lean.example.proto.NoteService/Missing" payload) with
  | .ok _ => throw (IO.userError "expected error status for unknown method")
  | .error status =>
      expectEq status.code Code.unimplemented "unknown method should be UNIMPLEMENTED"
  IO.println "client trailers-only ok"

  -- A local cancellation closes the protocol stream through RST_STREAM while
  -- leaving the multiplexed connection available for later calls.
  let cancelled ← Async.block (Client.start client
    "/lean.example.proto.NoteService/Echo")
  let cancelled ← match cancelled with
    | .ok call => pure call
    | .error status => throw (IO.userError s!"cancelled call start failed: {status.messageD}")
  expectEq (← Async.block cancelled.cancelIfActive) true
    "active local cancellation should report its atomic commit"
  expectEq (← Async.block cancelled.cancelIfActive) false
    "a repeated cancellation must not claim another terminal commit"
  Async.block cancelled.cancel
  expectStatusCode (← Async.block cancelled.recv?) .cancelled
    "locally cancelled receive"
  expectStatusCode (← Async.block cancelled.finish) .cancelled
    "locally cancelled finish"
  expectEq (← Async.block cancelled.cancelIfActive) false
    "a retired call must not claim a cancellation commit"
  match ← Async.block (Client.call client
      "/lean.example.proto.NoteService/Echo" payload2) with
  | .error status =>
      throw (IO.userError s!"call after cancellation failed: {status.messageD}")
  | .ok (_, response) =>
      expectEq response payload2 "connection should remain usable after cancellation"
  IO.println "client protocol-owned cancellation ok"

  -- large response (exceeds 65535 connection/stream windows → client must
  -- send WINDOW_UPDATE for the server to finish; response is gzip-compressed)
  match ← Async.block (Client.call client "/lean.example.proto.NoteService/Big" ByteArray.empty) with
  | .error status => throw (IO.userError s!"big response failed: {status.messageD}")
  | .ok (_, response) =>
      expectEq response.size 200000 "large response should arrive complete"
      expectEq response (repeatByte 200000 7) "large response content should match"
  IO.println "client large response + flow control ok"

  -- large request (exceeds windows in the other direction)
  let bigPayload := repeatByte 150000 9
  match ← Async.block (Client.call client "/lean.example.proto.NoteService/Echo" bigPayload) with
  | .error status => throw (IO.userError s!"big request failed: {status.messageD}")
  | .ok (_, response) =>
      expectEq response.size 150000 "large request should echo back complete"
  IO.println "client large request + flow control ok"

  -- Per-connection message caps reject a request before framing and a response
  -- as soon as its declared wire length is available.
  let limited ← Client.connect {
    address := Http2.Server.loopback port
    maxSendMessageSize := 32
    maxReceiveMessageSize := 64
  }
  expectStatusCode
    (← Async.block (Client.call limited
      "/lean.example.proto.NoteService/Echo" (repeatByte 33 1)))
    .resourceExhausted "oversized request"

  let receiveLimited ← Async.block (Client.start limited
    "/lean.example.proto.NoteService/Big")
  let receiveLimited ← match receiveLimited with
    | .ok call => pure call
    | .error status => throw (IO.userError s!"limited response start failed: {status.messageD}")
  match ← Async.block (receiveLimited.send ByteArray.empty) with
  | .ok () => pure ()
  | .error status => throw (IO.userError s!"limited response send failed: {status.messageD}")
  match ← Async.block receiveLimited.closeSend with
  | .ok () => pure ()
  | .error status => throw (IO.userError s!"limited response close failed: {status.messageD}")
  expectStatusCode (← Async.block receiveLimited.recv?)
    .resourceExhausted "oversized response"
  expectStatusCode (← Async.block receiveLimited.finish)
    .resourceExhausted "oversized response finish"

  -- Rejecting one stream must not poison the multiplexed connection.
  let smallPayload := repeatByte 16 3
  match ← Async.block (Client.call limited
      "/lean.example.proto.NoteService/Echo" smallPayload) with
  | .error status =>
      throw (IO.userError s!"call after oversized response failed: {status.messageD}")
  | .ok (_, response) =>
      expectEq response smallPayload
        "connection should remain usable after rejecting an oversized response"
  Async.block (Client.close limited)
  IO.println "client request/response message caps ok"

  let mut closeTasks := #[]
  for _ in [0:16] do
    closeTasks := closeTasks.push (← IO.asTask (Async.block (Client.close client)))
  for task in closeTasks do
    match ← IO.wait task with
    | .ok () => pure ()
    | .error error => throw error
  Async.block (Client.close client)
  expect (← Client.backgroundTasksFinished client)
    "concurrent client close left a background owner running"
  IO.println "client concurrent and repeated close ok"
  Grpc.Server.shutdown server
  IO.println "all client assertions passed"
