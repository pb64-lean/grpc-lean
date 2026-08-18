import Grpc

open Grpc

namespace Test.UnaryIdentityDecodeReuse

private def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

private def fail (failure : String) : IO α :=
  throw (IO.userError failure)

private def expectOk (result : Except Status α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => fail s!"{description}: {status.code}: {status.messageD}"

private def method : MethodName := {
  service := "test.decode.v1.DecodeService"
  method := "Unary"
}

private def metadata : Metadata := Metadata.empty

private def preflight (usesGzip : Bool) (contentLength : Option Nat := none) :
    Headers.RequestPreflight := {
  method
  timeout := none
  contentLength
  requestUsesGzip := usesGzip
  clientAcceptsGzip := false
}

private def registryWithLimit : Option Nat → Registry
  | none => Registry.empty
  | some limit => Registry.empty.withMaxReceiveMessageSize limit

private def payload (size : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for i in [0:size] do
    bytes := bytes.push (UInt8.ofNat ((i * 131 + 17) % 256))
  return bytes

private def uint32BE (value : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((value / 16777216) % 256),
    UInt8.ofNat ((value / 65536) % 256),
    UInt8.ofNat ((value / 256) % 256),
    UInt8.ofNat (value % 256)]

private def rawWire (flag : UInt8) (declaredLength : Nat)
    (data : ByteArray) : ByteArray :=
  (ByteArray.empty.push flag).append (uint32BE declaredLength) |>.append data

private def encodeMessage (message : Message) : IO ByteArray :=
  expectOk (Message.encode message) "encode gRPC message"

private def runReference (registry : Registry) (preflight : Headers.RequestPreflight)
    (handler : UnaryHandler) (body : ByteArray) : IO (Except Status UnaryResponse) := do
  match Message.decompressBody preflight.requestUsesGzip
      registry.maxReceiveMessageSize body with
  | .error status => pure (.error status)
  | .ok normalized =>
      Std.Async.Async.block <|
        registry.dispatchManagedUnaryAsync metadata normalized preflight handler none

private def runCandidate (registry : Registry) (preflight : Headers.RequestPreflight)
    (handler : UnaryHandler) (body : ByteArray) : IO (Except Status UnaryResponse) := do
  Std.Async.Async.block <|
    registry.dispatchManagedUnaryTransportBodyAsync metadata body preflight handler none

private inductive Expected where
  | ok (data : ByteArray)
  | error (status : Status)

private def resultEq : Except Status UnaryResponse → Except Status UnaryResponse → Bool
  | .error left, .error right => decide (left = right)
  | .ok left, .ok right =>
      decide (left.status = right.status)
        && left.data == right.data
        && decide (left.metadata = right.metadata)
        && decide (left.trailers = right.trailers)
  | _, _ => false

private def matchesExpected : Except Status UnaryResponse → Expected → Bool
  | .ok response, .ok data =>
      response.status == Status.ok && response.data == data
  | .error status, .error expected => decide (status = expected)
  | _, _ => false

private def validateCase (label : String) (body : ByteArray)
    (requestPreflight : Headers.RequestPreflight) (maxDataSize? : Option Nat)
    (expected : Expected) (expectedHandlerCalls : Nat) : IO Unit := do
  let referenceCalls ← IO.mkRef 0
  let candidateCalls ← IO.mkRef 0
  let referenceHandler : UnaryHandler := fun request => do
    referenceCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let candidateHandler : UnaryHandler := fun request => do
    candidateCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let registry := registryWithLimit maxDataSize?
  let reference ← runReference registry requestPreflight referenceHandler body
  let candidate ← runCandidate registry requestPreflight candidateHandler body
  expect (resultEq reference candidate)
    s!"{label}: prepared identity path differs from body reference"
  expect (matchesExpected reference expected)
    s!"{label}: reference differs from expected result"
  expect ((← referenceCalls.get) == expectedHandlerCalls)
    s!"{label}: reference handler call count changed"
  expect ((← candidateCalls.get) == expectedHandlerCalls)
    s!"{label}: candidate handler call count changed"

private def validateDispatchCorpus : IO Nat := do
  let mut cases := 0
  for size in [0, 1, 64, 1024] do
    let data := payload size
    let wire ← encodeMessage { data := data }
    validateCase s!"identity-{size}" wire (preflight false) none (.ok data) 1
    cases := cases + 1

  validateCase "empty-body" ByteArray.empty (preflight false) none
    (.error (Status.invalidArgument "unary request expected one message, got 0")) 0
  cases := cases + 1

  let data1 := payload 1
  let data64 := payload 64
  let wire1 ← encodeMessage { data := data1 }
  let wire64 ← encodeMessage { data := data64 }
  validateCase "two-identity-messages" (wire1 ++ wire64) (preflight false) none
    (.error (Status.invalidArgument "unary request expected one message, got 2")) 0
  cases := cases + 1

  let incomplete := rawWire 0 5 (payload 2)
  validateCase "valid-plus-incomplete" (wire1 ++ incomplete) (preflight false) none
    (.error (Status.internal "incomplete gRPC message")) 0
  cases := cases + 1
  validateCase "invalid-flag" (rawWire 7 0 ByteArray.empty) (preflight false) none
    (.error (Status.internal "invalid gRPC compression flag 7")) 0
  cases := cases + 1

  validateCase "size-limit-exact" wire64 (preflight false) (some 64) (.ok data64) 1
  cases := cases + 1
  validateCase "size-limit-exceeded" wire64 (preflight false) (some 63)
    (.error (Status.resourceExhausted
      "gRPC message exceeds configured size limit 63")) 0
  cases := cases + 1

  validateCase "content-length-exact" wire64
    (preflight false (some wire64.size)) none (.ok data64) 1
  cases := cases + 1
  validateCase "content-length-mismatch" wire64
    (preflight false (some (wire64.size + 1))) none
    (.error (Status.invalidArgument
      s!"content-length {wire64.size + 1} does not match request body size {wire64.size}")) 0
  cases := cases + 1

  -- A gzip declaration still permits an identity-flag message and therefore
  -- uses the retained identity array.
  validateCase "gzip-header-identity-message" wire64 (preflight true) none
    (.ok data64) 1
  cases := cases + 1

  let large := payload 4096
  let compressedMessage := Message.gzipped large
  let compressedWire ← encodeMessage compressedMessage
  validateCase "valid-gzip" compressedWire (preflight true) none (.ok large) 1
  cases := cases + 1
  validateCase "compressed-without-encoding" compressedWire (preflight false) none
    (.error (Status.internal
      "gRPC message has the compressed flag set without a message encoding")) 0
  cases := cases + 1

  let corruptWire ← encodeMessage {
    compressed := .compressed
    data := ByteArray.mk #[0xde, 0xad, 0xbe, 0xef]
  }
  validateCase "corrupt-gzip" corruptWire (preflight true) none
    (.error (Status.internal "failed to decompress gzip gRPC message")) 0
  cases := cases + 1
  validateCase "late-framing-before-gzip" (corruptWire ++ incomplete) (preflight true) none
    (.error (Status.internal "incomplete gRPC message")) 0
  cases := cases + 1
  validateCase "late-gzip-before-cardinality" (compressedWire ++ corruptWire)
    (preflight true) none
    (.error (Status.internal "failed to decompress gzip gRPC message")) 0
  cases := cases + 1
  validateCase "mixed-valid-before-cardinality" (wire1 ++ compressedWire)
    (preflight true) none
    (.error (Status.invalidArgument "unary request expected one message, got 2")) 0
  cases := cases + 1

  -- Preserve the current normalized-body content-length contract for gzip.
  let normalized ← expectOk (Message.decompressBody true none compressedWire)
    "normalize gzip content-length fixture"
  validateCase "gzip-normalized-content-length" compressedWire
    (preflight true (some normalized.size)) none (.ok large) 1
  cases := cases + 1
  validateCase "gzip-wire-content-length-control" compressedWire
    (preflight true (some compressedWire.size)) none
    (.error (Status.invalidArgument
      s!"content-length {compressedWire.size} does not match request body size {normalized.size}")) 0
  cases := cases + 1
  pure cases

private def scriptedClock (samples : Array Nat) : IO (BaseIO Nat × IO (Array Nat)) := do
  let remaining ← IO.mkRef samples
  let observed ← IO.mkRef (#[] : Array Nat)
  let now : BaseIO Nat := do
    let sample? ← remaining.modifyGet fun values =>
      match values[0]? with
      | none => (none, values)
      | some sample => (some sample, values.extract 1 values.size)
    match sample? with
    | none => pure 0
    | some sample =>
        observed.modify (fun values => values.push sample)
        pure sample
  pure (now, observed.get)

private def validateInlineDeadlineBoundary : IO Unit := do
  let data := payload 64
  let body ← encodeMessage { data := data }
  let calls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    calls.modify (fun count => count + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[99, 99]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryTransportBodyInlineUntilAsync
      metadata body (preflight false) handler 100 now
  match result with
  | .ok response => expect (response.data == data) "inline identity payload changed"
  | .error status => fail s!"inline identity dispatch failed: {status.messageD}"
  expect ((← calls.get) == 1) "inline identity handler call count changed"
  expect ((← observed) == #[99, 99]) "inline identity clock brackets changed"

  let (lateNow, lateObserved) ← scriptedClock #[100]
  let late ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryTransportBodyInlineUntilAsync
      metadata ByteArray.empty (preflight false) handler 100 lateNow
  match late with
  | .error status =>
      expect (status.code == .deadlineExceeded)
        "inline cardinality error did not yield to exact deadline"
  | .ok _ => fail "inline empty identity body unexpectedly succeeded"
  expect ((← calls.get) == 1) "late inline decode entered the handler"
  expect ((← lateObserved) == #[100]) "late inline decode clock reads changed"

def run : IO Unit := do
  let cases ← validateDispatchCorpus
  validateInlineDeadlineBoundary
  IO.println s!"unary identity decode reuse: {cases} differential cases and deadline gate passed"

end Test.UnaryIdentityDecodeReuse

def main : IO Unit :=
  Test.UnaryIdentityDecodeReuse.run
