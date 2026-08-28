import Grpc

open Grpc

namespace Test.DeadlineArbiter

private def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def expectOk (result : Except Status α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status =>
      throw (IO.userError s!"{description}: {status.code}: {status.messageD}")

private def expectStatus (result : Except Status α) (code : Code)
    (description : String) : IO Status :=
  match result with
  | .ok _ => throw (IO.userError s!"{description}: expected {code}")
  | .error status => do
      expect (status.code == code)
        s!"{description}: expected {code}, got {status.code}: {status.messageD}"
      pure status

private def method : MethodName := {
  service := "test.deadline.v1.DeadlineService"
  method := "Check"
}

private def metadata : _root_.Http2.Headers :=
  _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

private def preflight : Headers.RequestPreflight := {
  method := method
  timeout := none
  contentLength := none
  requestUsesGzip := false
  clientAcceptsGzip := false
}

private def requestBody : IO ByteArray :=
  expectOk (Message.encode { data := ByteArray.mk #[1, 2, 3] })
    "encode managed-unary request"

private def scriptedClock (values : Array Nat) : IO (BaseIO Nat × IO (Array Nat)) := do
  let remaining ← IO.mkRef values
  let observed ← IO.mkRef (#[] : Array Nat)
  let now : BaseIO Nat := do
    let value ← remaining.modifyGet fun values =>
      match values[0]? with
      | some value => (value, values.extract 1 values.size)
      | none => (0, #[])
    observed.modify fun seen => seen.push value
    pure value
  pure (now, observed.get)

/-- The inline handler accepts a response only when both exact clock brackets
are strictly before the absolute deadline. -/
private def testInlineSuccessBeforeDeadline : IO Unit := do
  let body ← requestBody
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[99, 99]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata body preflight handler 100 now
  let response ← expectOk result "dispatch before deadline"
  expect (response.data == ByteArray.mk #[1, 2, 3])
    "before-deadline dispatch changed the handler response"
  expect ((← handlerCalls.get) == 1)
    "before-deadline dispatch did not run its handler exactly once"
  expect ((← observed) == #[99, 99])
    "before-deadline dispatch did not bracket the handler with exact clock reads"

/-- A handler that returns at the exact absolute deadline loses locally even
when no scheduler callback has run yet. -/
private def testInlinePostHandlerExactDeadlineSelfExpiry : IO Unit := do
  let body ← requestBody
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[99, 100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata body preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "post-handler exact-deadline self-expiry"
  expect ((← handlerCalls.get) == 1)
    "post-handler self-expiry did not run its handler exactly once"
  expect ((← observed) == #[99, 100])
    "post-handler self-expiry did not observe the scripted deadline crossing"

/-- Reaching the boundary before handler entry suppresses arbitrary user IO. -/
private def testInlineExactDeadlineSuppressesHandler : IO Unit := do
  let body ← requestBody
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata body preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "pre-handler exact-deadline self-expiry"
  expect ((← handlerCalls.get) == 0)
    "exact pre-handler deadline entered arbitrary handler IO"
  expect ((← observed) == #[100])
    "pre-handler exact-deadline path performed an unexpected clock read"

/-- Malformed request decoding remains part of the timed call phase. -/
private def testInlineDecodeErrorAtDeadlineSelfExpires : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun _ => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { status := Status.ok }
  let (now, observed) ← scriptedClock #[100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata ByteArray.empty preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "decode error at exact deadline self-expiry"
  expect ((← handlerCalls.get) == 0)
    "decode-error self-expiry entered arbitrary handler IO"
  expect ((← observed) == #[100])
    "decode-error self-expiry did not read the exact boundary once"

/-- Transport framing errors use the same local boundary rule. -/
private def testTransportFramingErrorAtDeadlineSelfExpires : IO Unit := do
  let malformed := ByteArray.mk #[0xff, 0x00, 0x01]
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun _ => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { status := Status.ok }
  let (now, observed) ← scriptedClock #[100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryTransportBodyInlineUntilAsync
      metadata malformed preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "transport framing error at exact deadline self-expiry"
  expect ((← handlerCalls.get) == 0)
    "transport framing self-expiry entered arbitrary handler IO"
  expect ((← observed) == #[100])
    "transport framing self-expiry did not read the exact boundary once"

def run : IO Unit := do
  testInlineSuccessBeforeDeadline
  testInlinePostHandlerExactDeadlineSelfExpiry
  testInlineExactDeadlineSuppressesHandler
  testInlineDecodeErrorAtDeadlineSelfExpires
  testTransportFramingErrorAtDeadlineSelfExpires
  IO.println "managed-unary inline deadline tests pass"

end Test.DeadlineArbiter

def main : IO Unit :=
  Test.DeadlineArbiter.run
