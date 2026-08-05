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

def testRegistry : Registry :=
  Registry.empty
    |>.registerUnary echoMethod (fun request => do
        pure {
          metadata := Metadata.empty.insert "handled-by" "lean-http2",
          data := request.data,
          status := Status.ok
        })
    |>.registerUnary failMethod (fun _ => do
        throw (Status.invalidArgument "nope"))
    |>.registerUnary bigMethod (fun _ => do
        pure { metadata := Metadata.empty, data := repeatByte 200000 7, status := Status.ok })

def main : IO Unit := do
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

  Async.block (Client.close client)
  Grpc.Server.shutdown server
  IO.println "all client assertions passed"
