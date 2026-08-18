import Grpc

open Grpc

/-!
# Unary identity framing reuse benchmark

The reference is the exact former successful preprocessing topology:
`decompressBody` validates the aggregate and returns its unchanged identity
wire, then unary decoding parses that wire again. The candidate retains the
first all-identity message array from `prepareBody` and applies the same unary
cardinality/flag checks without the second parse.

Only framing and unary payload selection are measured. Header validation,
authorization, protobuf codecs, handlers, HTTP/2, networking, and response
work are deliberately excluded.
-/

private def finishUnary (messages : Array Message) : Except Status ByteArray := do
  if messages.size != 1 then
    throw (Status.invalidArgument s!"unary request expected one message, got {messages.size}")
  let message := messages[0]!
  if message.compressed != .identity then
    throw (Status.unimplemented "compressed requests are not supported")
  pure message.data

@[noinline] private def decodeReference (maxDataSize? : Option Nat)
    (body : ByteArray) : Except Status ByteArray := do
  let normalized ← Message.decompressBody false maxDataSize? body
  let messages ← Message.decodeAllWithLimit maxDataSize? normalized
  finishUnary messages

@[noinline] private def decodeCandidate (maxDataSize? : Option Nat)
    (body : ByteArray) : Except Status ByteArray := do
  match ← Message.prepareBody false maxDataSize? body with
  | .identity messages => finishUnary messages
  | .rewritten normalized =>
      finishUnary (← Message.decodeAllWithLimit maxDataSize? normalized)

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

private def encodeMessage (message : Message) : IO ByteArray := do
  match Message.encode message with
  | .ok wire => pure wire
  | .error status => throw (IO.userError status.messageD)

private def exactResultEq : Except Status ByteArray → Except Status ByteArray → Bool
  | .error left, .error right => decide (left = right)
  | .ok left, .ok right => left == right
  | _, _ => false

private def validateCase (label : String) (maxDataSize? : Option Nat)
    (body : ByteArray) : IO Unit := do
  let reference := decodeReference maxDataSize? body
  let candidate := decodeCandidate maxDataSize? body
  unless exactResultEq reference candidate do
    throw (IO.userError s!"{label}: reference and candidate differ")

private def validateCorpus : IO Nat := do
  let mut cases := 0
  validateCase "empty" none ByteArray.empty
  cases := cases + 1
  for size in [0, 1, 16, 64, 128, 1024] do
    let wire ← encodeMessage { data := payload size }
    validateCase s!"identity-{size}" none wire
    cases := cases + 1
  let wire1 ← encodeMessage { data := payload 1 }
  let wire64 ← encodeMessage { data := payload 64 }
  validateCase "two-messages" none (wire1 ++ wire64)
  cases := cases + 1
  validateCase "valid-plus-incomplete" none (wire1 ++ rawWire 0 5 (payload 2))
  cases := cases + 1
  validateCase "invalid-flag" none (rawWire 7 0 ByteArray.empty)
  cases := cases + 1
  validateCase "limit-exact" (some 64) wire64
  cases := cases + 1
  validateCase "limit-exceeded" (some 63) wire64
  cases := cases + 1
  pure cases

private structure Fixture where
  label : String
  body : ByteArray
  payloadBytes : Nat

private def fixture? (name : String) : IO (Option Fixture) := do
  let size ← match name with
    | "small" => pure 32
    | "acme" => pure 128
    | "large" => pure 1024
    | _ => pure 0
  if name != "small" && name != "acme" && name != "large" then
    pure none
  else
    let body ← encodeMessage { data := payload size }
    pure (some { label := name, body, payloadBytes := size })

@[inline] private def resultDigest : Except Status ByteArray → UInt64
  | .error status => UInt64.ofNat status.code.toNat + 1
  | .ok data =>
      let first := data[0]?.getD 0
      let last := data[data.size - 1]?.getD 0
      UInt64.ofNat data.size * 1099511628211
        + UInt64.ofNat first.toNat * 257
        + UInt64.ofNat last.toNat + 17

private inductive Mode where
  | redecode
  | reuse

@[noinline] private def runRedecode (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (decodeReference none fixture.body)
  return checksum

@[noinline] private def runReuse (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (decodeCandidate none fixture.body)
  return checksum

private def runIterations (mode : Mode) (fixture : @& Fixture)
    (iterations : Nat) : UInt64 :=
  match mode with
  | .redecode => runRedecode fixture iterations
  | .reuse => runReuse fixture iterations

private def parsePositive (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a positive decimal integer")
  unless parsed > 0 do
    throw (IO.userError s!"{label} must be positive")
  pure parsed

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

def main (args : List String) : IO Unit := do
  let (modeName, fixtureName, iterations, warmup) ← match args with
    | [mode, fixture, iterations, warmup] =>
      pure (mode, fixture,
        ← parsePositive "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: unary_identity_decode_reuse_benchmark (redecode|reuse) " ++
          "(small|acme|large) iterations warmup")
  let mode ← match modeName with
    | "redecode" => pure Mode.redecode
    | "reuse" => pure Mode.reuse
    | _ => throw (IO.userError "mode must be redecode or reuse")
  let some fixture ← fixture? fixtureName
    | throw (IO.userError "fixture must be small, acme, or large")

  let semanticCases ← validateCorpus
  let digest := resultDigest (decodeCandidate none fixture.body)
  unless digest != 0 do
    throw (IO.userError s!"{fixture.label}: selected fixture digest is zero")
  let warmupChecksum := runIterations mode fixture warmup
  unless warmupChecksum == digest * UInt64.ofNat warmup do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let checksum := runIterations mode fixture iterations
  unless checksum == digest * UInt64.ofNat iterations do
    throw (IO.userError s!"{fixture.label}: measured checksum mismatch")
  IO.println <| s!"benchmark=grpc_unary_identity_decode_reuse_v1 mode={modeName} " ++
    s!"fixture={fixture.label} payload_bytes={fixture.payloadBytes} " ++
    s!"wire_bytes={fixture.body.size} iterations={iterations} warmup={warmup} " ++
    s!"checksum={checksum}"
  IO.println <| s!"unary_identity_decode_reuse_validation=pass cases={semanticCases} " ++
    "result=exact reference=candidate"
