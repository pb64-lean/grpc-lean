import Std.Async.TCP

import Grpc

open Grpc
open Grpc.Services
open Std.Async

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectOk (result : Except Status α) (msg : String) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError s!"{msg}: {status.messageD}")

def expectProtoOk (result : Except Protobuf.Encoding.ProtoError α) (msg : String) : IO α := do
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{msg}: {error}")

def repeatByte (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

def service : String := "lean.test.Streaming"

def methodNamed (m : String) : MethodName := { service := service, method := m }

def pathOf (m : String) : String := s!"/{service}/{m}"

def bigMessageSize : Nat := 100000

def testRegistry : Registry :=
  Registry.empty
    |>.registerUnary (methodNamed "Echo") (fun request => do
        pure { data := request.data, status := Status.ok })
    |>.registerServerStreamingStream (methodNamed "Range") (fun request => do
        let count := (request.data[0]?.getD 0).toNat
        let items := Array.ofFn (n := count) fun i => s!"item-{i.val}".toUTF8
        pure {
          metadata := Metadata.empty.insert "served-by" "range",
          messages := ← MessageStream.ofArray items,
          status := Status.ok
        })
    |>.registerServerStreamingStream (methodNamed "BigRange") (fun _ => do
        let items := Array.ofFn (n := 4) fun i =>
          repeatByte bigMessageSize (UInt8.ofNat (0x40 + i.val))
        pure { messages := ← MessageStream.ofArray items, status := Status.ok })
    |>.registerServerStreamingStream (methodNamed "FailAfterTwo") (fun _ => do
        let items := #["one".toUTF8, "two".toUTF8]
        pure {
          messages := ← MessageStream.ofArray items,
          status := Status.invalidArgument "stream failed mid-way"
        })
    |>.registerClientStreamingStream (methodNamed "Sum") (fun request => do
        let messages ← request.messages.collect
        let total := messages.foldl (fun acc message => acc + message.size) 0
        pure { data := (toString total).toUTF8, status := Status.ok })
    |>.registerBidirectionalStreamingStream (methodNamed "PingPong") (fun request => do
        pure {
          messages := request.messages.mapM fun message =>
            pure ("ack:".toUTF8.append message),
          status := Status.ok
        })

def testServerStreamingBasic (client : Client.Connection) : Async Unit := do
  let result ← Client.serverStreaming client (pathOf "Range") (ByteArray.mk #[5])
  expectEq result.status.code Code.ok "Range should succeed"
  expectEq result.messages.size 5 "Range should stream five messages"
  for i in [0:5] do
    expectEq result.messages[i]! s!"item-{i}".toUTF8 s!"Range message {i} should match"
  expectEq (Metadata.get? result.headers "served-by") (some "range")
    "initial response metadata should arrive"
  IO.println "server-streaming basic ok"

def testServerStreamingLarge (client : Client.Connection) : Async Unit := do
  let result ← Client.serverStreaming client (pathOf "BigRange") ByteArray.empty
  expectEq result.status.code Code.ok "BigRange should succeed"
  expectEq result.messages.size 4 "BigRange should stream four messages"
  for i in [0:4] do
    expectEq result.messages[i]!.size bigMessageSize s!"BigRange message {i} size should match"
    expectEq result.messages[i]! (repeatByte bigMessageSize (UInt8.ofNat (0x40 + i)))
      s!"BigRange message {i} content should match"
  IO.println "server-streaming large + flow control + gzip ok"

def testClientStreamingBasic (client : Client.Connection) : Async Unit := do
  let call ← ofExceptIO (← Client.start client (pathOf "Sum"))
  discard <| expectOk (← call.send "abc".toUTF8) "Sum send 1"
  discard <| expectOk (← call.send "defgh".toUTF8) "Sum send 2"
  discard <| expectOk (← call.send "ij".toUTF8) "Sum send 3"
  discard <| expectOk (← call.closeSend) "Sum closeSend"
  let response ← expectOk (← call.recv?) "Sum recv"
  expectEq response (some "10".toUTF8) "Sum should add message sizes"
  let done ← expectOk (← call.recv?) "Sum recv end"
  expectEq done none "Sum should end after one response"
  let (status, _, _) ← expectOk (← call.finish) "Sum finish"
  expectEq status.code Code.ok "Sum status should be OK"
  IO.println "client-streaming basic ok"
where
  ofExceptIO (result : Except Status Client.Call) : IO Client.Call :=
    match result with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)

def testClientStreamingLarge (client : Client.Connection) : Async Unit := do
  let call ← match ← Client.start client (pathOf "Sum") with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)
  for i in [0:3] do
    discard <| expectOk (← call.send (repeatByte bigMessageSize (UInt8.ofNat i)))
      s!"big Sum send {i}"
  discard <| expectOk (← call.closeSend) "big Sum closeSend"
  let response ← expectOk (← call.recv?) "big Sum recv"
  expectEq response (some (toString (3 * bigMessageSize)).toUTF8)
    "big Sum should add all bytes sent under flow control"
  let (status, _, _) ← expectOk (← call.finish) "big Sum finish"
  expectEq status.code Code.ok "big Sum status should be OK"
  IO.println "client-streaming large + deferred server credit ok"

def testBidiPingPong (client : Client.Connection) : Async Unit := do
  let call ← match ← Client.start client (pathOf "PingPong") with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)
  for i in [0:5] do
    let message := s!"msg-{i}".toUTF8
    discard <| expectOk (← call.send message) s!"PingPong send {i}"
    let response ← expectOk (← call.recv?) s!"PingPong recv {i}"
    expectEq response (some ("ack:".toUTF8.append message))
      s!"PingPong round {i} should echo with prefix before the next send"
  discard <| expectOk (← call.closeSend) "PingPong closeSend"
  let done ← expectOk (← call.recv?) "PingPong recv end"
  expectEq done none "PingPong should end after closeSend"
  let (status, _, _) ← expectOk (← call.finish) "PingPong finish"
  expectEq status.code Code.ok "PingPong status should be OK"
  IO.println "bidi ping-pong interleaved ok"

def testMidStreamError (client : Client.Connection) : Async Unit := do
  let result ← Client.serverStreaming client (pathOf "FailAfterTwo") ByteArray.empty
  expectEq result.messages.size 2 "FailAfterTwo should deliver two messages before failing"
  expectEq result.status.code Code.invalidArgument "FailAfterTwo should surface the error status"
  expectEq result.status.message (some "stream failed mid-way")
    "FailAfterTwo error message should round-trip"
  IO.println "mid-stream error ok"

def testConcurrentCalls (client : Client.Connection) : Async Unit := do
  let streamCall ← match ← Client.start client (pathOf "PingPong") with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)
  discard <| expectOk (← streamCall.send "first".toUTF8) "concurrent stream send"
  let response ← expectOk (← streamCall.recv?) "concurrent stream recv"
  expectEq response (some "ack:first".toUTF8) "stream call should progress"
  -- run a whole unary call while the bidi stream is still open
  match ← Client.call client (pathOf "Echo") "interleaved".toUTF8 with
  | .error status => throw (IO.userError s!"interleaved unary failed: {status.messageD}")
  | .ok (_, data) => expectEq data "interleaved".toUTF8 "interleaved unary should echo"
  discard <| expectOk (← streamCall.send "second".toUTF8) "concurrent stream send 2"
  let response2 ← expectOk (← streamCall.recv?) "concurrent stream recv 2"
  expectEq response2 (some "ack:second".toUTF8) "stream call should still progress"
  discard <| expectOk (← streamCall.closeSend) "concurrent stream closeSend"
  let done ← expectOk (← streamCall.recv?) "concurrent stream recv end"
  expectEq done none "stream call should end"
  let (status, _, _) ← expectOk (← streamCall.finish) "concurrent stream finish"
  expectEq status.code Code.ok "concurrent stream status should be OK"
  IO.println "concurrent calls on one connection ok"

def testCancelMidStream (client : Client.Connection) : Async Unit := do
  let call ← match ← Client.start client (pathOf "PingPong") with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)
  discard <| expectOk (← call.send "before-cancel".toUTF8) "cancel test send"
  let response ← expectOk (← call.recv?) "cancel test recv"
  expectEq response (some "ack:before-cancel".toUTF8) "cancel test should progress first"
  call.cancel
  match ← call.finish with
  | .ok _ => throw (IO.userError "cancelled call should not finish cleanly")
  | .error status =>
      expectEq status.code Code.cancelled "cancelled call should report CANCELLED"
  -- the connection must remain healthy for other calls
  match ← Client.call client (pathOf "Echo") "after-cancel".toUTF8 with
  | .error status => throw (IO.userError s!"post-cancel unary failed: {status.messageD}")
  | .ok (_, data) => expectEq data "after-cancel".toUTF8 "post-cancel unary should echo"
  IO.println "cancel mid-stream ok"

/-- A real client RST_STREAM must release the Health Watch producer retained by
the server, without waiting for a later status transition or connection teardown. -/
def testHealthWatchRst (client : Client.Connection) (health : Health.Service) : Async Unit := do
  let request ← expectProtoOk
    (Health.CheckRequest.encode { service := "svc" }) "encode Health Watch request"
  let call ← expectOk (← Client.start client Health.watchMethodName.path) "start Health Watch"
  discard <| expectOk (← call.send request) "send Health Watch request"
  discard <| expectOk (← call.closeSend) "close Health Watch request"

  let initialBytes? ← expectOk (← call.recv?) "receive initial Health Watch status"
  let initialBytes ← match initialBytes? with
    | some bytes => pure bytes
    | none => throw (IO.userError "Health Watch ended before its initial status")
  let initial ← expectProtoOk
    (Health.CheckResponse.decode initialBytes) "decode initial Health Watch status"
  expectEq initial.status .serving "Health Watch should initially report SERVING"
  expectEq (← health.activeWatcherCount) 1
    "Health Watch should retain one server-side producer"

  call.cancel
  match ← call.finish with
  | .ok _ => throw (IO.userError "cancelled Health Watch should not finish cleanly")
  | .error status =>
      expectEq status.code Code.cancelled "cancelled Health Watch should report CANCELLED"

  -- Client outbound frames are FIFO, and the server awaits each frame's
  -- processing. This same-connection call is therefore a deterministic
  -- barrier proving the preceding RST_STREAM reached the server.
  match ← Client.call client (pathOf "Echo") "health-rst-barrier".toUTF8 with
  | .error status => throw (IO.userError s!"Health Watch RST barrier failed: {status.messageD}")
  | .ok (_, data) =>
      expectEq data "health-rst-barrier".toUTF8 "Health Watch RST barrier should echo"
  expectEq (← health.activeWatcherCount) 0
    "RST_STREAM should release Health Watch ownership before connection teardown"
  IO.println "health watch RST releases server ownership ok"

/-- Many calls in flight at once, composed with `Async.concurrentlyAll` so they
multiplex cooperatively on the worker pool: each suspends (not parks a thread)
while waiting for the reader to deliver its data. With the old IO/blocking API
this many simultaneous waiters would park a thread each. -/
def testConcurrencyStress (client : Client.Connection) : Async Unit := do
  let n := 200
  let calls : Array (Async Unit) := (Array.range n).map fun i =>
    (do
      let result ← Client.serverStreaming client (pathOf "Range") (ByteArray.mk #[6])
      if result.status.code != Code.ok then
        throw (IO.userError s!"stress call {i} failed: {result.status.messageD}")
      if result.messages.size != 6 then
        throw (IO.userError s!"stress call {i} got {result.messages.size} messages, want 6")
      pure ())
  discard <| Async.concurrentlyAll calls
  IO.println s!"concurrency stress ({n} concurrent async calls, multiplexed) ok"

def testTrailersOnlyViaHandle (client : Client.Connection) : Async Unit := do
  let call ← match ← Client.start client (pathOf "Missing") with
    | .ok call => pure call
    | .error status => throw (IO.userError status.messageD)
  discard <| expectOk (← call.closeSend) "missing method closeSend"
  let done ← expectOk (← call.recv?) "missing method recv"
  expectEq done none "unknown method should deliver no messages"
  let (status, _, _) ← expectOk (← call.finish) "missing method finish"
  expectEq status.code Code.unimplemented "unknown method should be UNIMPLEMENTED"
  IO.println "trailers-only via handle ok"

def describeCause : Http2.Server.CloseCause → String
  | .peerClosed => "peerClosed"
  | .serverShutdown => "serverShutdown"
  | .keepaliveTimeout => "keepaliveTimeout"
  | .protocolError status => s!"protocolError({status.messageD})"
  | .transportError message => s!"transportError({message})"

/-- What the server itself says about the connections it closed and about the health
of its accept loop.  A client-side "connection closed by peer" is only half of the
story; this is the other half, and it is why the failure below names a cause. -/
def serverDiagnostics (server : Grpc.Server.Instance) : IO String := do
  let closed ← Grpc.Server.closedConnections server
  let causes := closed.map fun record => s!"#{record.id}:{describeCause record.cause}"
  let accepting ← try
      pure (toString (← Grpc.Server.checkAccepting server))
    catch err =>
      pure s!"threw {err}"
  let failure ← match ← Grpc.Server.acceptFailure? server with
    | none => pure "none"
    | some err => pure (toString err)
  pure s!"accepting={accepting} acceptFailure={failure} \
    closed={closed.size} causes=[{String.intercalate ", " causes.toList}]"

/-- Many simultaneously open connections: with the async server each idle connection
suspends its event loop rather than parking a worker thread, so this should scale on
a small pool. Runs an RPC on all of them concurrently, lets them all sit idle, then
runs a second round to prove the idle loops are still live. -/
def testManyConnections (server : Grpc.Server.Instance) (port : UInt16) : IO Unit := do
  let n := 80
  let clients ← (Array.range n).mapM fun _ =>
    Client.connect { address := Http2.Server.loopback port }
  let round (tag : String) : Async (Array (Option String)) := do
    Async.concurrentlyAll <| clients.map fun client => do
      match ← Client.call client (pathOf "Echo") tag.toUTF8 with
      | .error status => pure (some status.messageD)
      | .ok (_, data) =>
          if data != tag.toUTF8 then
            pure (some "echoed wrong payload")
          else
            pure none
  let runRound (tag : String) : IO Unit := do
    let outcomes := Async.block (round tag)
    let failures := (← outcomes).filterMap id
    unless failures.isEmpty do
      let diagnostics ← serverDiagnostics server
      throw (IO.userError s!"many-connections {tag} failed on \
        {failures.size}/{n} connections: {failures[0]!} [server: {diagnostics}]")
  runRound "round-one"
  runRound "round-two"
  for client in clients do
    Async.block (Client.close client)
  IO.println s!"many connections ({n} open, two concurrent rounds) ok"

def main : IO Unit := do
  let health ← Health.Service.new
  health.setServing "svc"
  let server ← Grpc.Server.serve (health.registerWith testRegistry)
    { address := Http2.Server.loopback 0 }
  let port := match server.localAddress with
    | .v4 addr => addr.port
    | .v6 addr => addr.port
  let client ← Client.connect { address := Http2.Server.loopback port }

  Async.block (testServerStreamingBasic client)
  Async.block (testServerStreamingLarge client)
  Async.block (testClientStreamingBasic client)
  Async.block (testClientStreamingLarge client)
  Async.block (testBidiPingPong client)
  Async.block (testMidStreamError client)
  Async.block (testConcurrentCalls client)
  Async.block (testConcurrencyStress client)
  Async.block (testCancelMidStream client)
  Async.block (testHealthWatchRst client health)
  Async.block (testTrailersOnlyViaHandle client)
  testManyConnections server port

  Async.block (Client.close client)
  Grpc.Server.shutdown server
  IO.println "all streaming assertions passed"
