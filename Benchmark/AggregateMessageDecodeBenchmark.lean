import Grpc

open Grpc

/-!
# Aggregate gRPC-message decode benchmark

Focused differential and counter harness for `Message.decodeAllWithLimit`.
The reference reproduces the former aggregate composition through
`decodeChunkWithLimit` and an empty state.  The candidate is the public
aggregate decoder, which parses its complete input directly.

Every invocation first compares the complete `Except Status (Array Message)`
for valid identity/compressed messages, every incomplete prefix of a 64-byte
message, invalid flags, declared-length mismatches, exact and exceeded size
limits, concatenated messages, and invalid trailing frames.  Only the
single-message `small` and `large` fixtures are measured; their wires are
constructed before warmup and the repeated loop is pure.
-/

@[noinline] private def decodeReference (maxDataSize? : Option Nat)
    (bytes : ByteArray) : Except Status (Array Message) := do
  let state ← Message.decodeChunkWithLimit maxDataSize? {} bytes
  if state.buffered.isEmpty then
    pure state.messages
  else
    throw (Status.internal "incomplete gRPC message")

@[noinline] private def decodeCandidate (maxDataSize? : Option Nat)
    (bytes : ByteArray) : Except Status (Array Message) :=
  Message.decodeAllWithLimit maxDataSize? bytes

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

private def exactResultEq : Except Status (Array Message) →
    Except Status (Array Message) → Bool
  | .error left, .error right => decide (left = right)
  | .ok left, .ok right => decide (left = right)
  | _, _ => false

private def validateCase (label : String) (maxDataSize? : Option Nat)
    (wire : ByteArray) (expected : Except Status (Array Message)) : IO Unit := do
  let reference := decodeReference maxDataSize? wire
  let candidate := decodeCandidate maxDataSize? wire
  unless exactResultEq reference expected do
    throw (IO.userError s!"{label}: reference differs from expected")
  unless exactResultEq candidate expected do
    throw (IO.userError s!"{label}: candidate differs from expected")
  unless exactResultEq reference candidate do
    throw (IO.userError s!"{label}: reference and candidate differ")

private def incomplete : Except Status (Array Message) :=
  .error (Status.internal "incomplete gRPC message")

private def validateCorpus : IO Nat := do
  let mut cases := 0
  validateCase "empty" none ByteArray.empty (.ok #[])
  cases := cases + 1

  for size in [0, 1, 64, 1024] do
    let message : Message := { data := payload size }
    let wire ← encodeMessage message
    validateCase s!"identity-{size}" none wire (.ok #[message])
    cases := cases + 1

  for size in [0, 1, 64] do
    let message : Message := { compressed := .compressed, data := payload size }
    let wire ← encodeMessage message
    validateCase s!"compressed-{size}" none wire (.ok #[message])
    cases := cases + 1

  let message64 : Message := { data := payload 64 }
  let wire64 ← encodeMessage message64
  for split in [1:wire64.size] do
    validateCase s!"identity-64-prefix-{split}" none (wire64.extract 0 split) incomplete
    cases := cases + 1

  for flag in [2, 255] do
    validateCase s!"invalid-flag-{flag}" none
      (rawWire (UInt8.ofNat flag) 0 ByteArray.empty)
      (.error (Status.internal s!"invalid gRPC compression flag {flag}"))
    cases := cases + 1

  validateCase "declared-shorter-than-body" none
    (rawWire 0 3 (payload 4)) incomplete
  cases := cases + 1
  validateCase "declared-longer-than-body" none
    (rawWire 0 5 (payload 4)) incomplete
  cases := cases + 1

  validateCase "size-limit-equal" (some 64) wire64 (.ok #[message64])
  cases := cases + 1
  validateCase "size-limit-exceeded" (some 63) wire64
    (.error (Status.resourceExhausted
      "gRPC message exceeds configured size limit 63"))
  cases := cases + 1

  let identity0 : Message := { data := payload 0 }
  let identity1 : Message := { data := payload 1 }
  let compressed64 : Message := { compressed := .compressed, data := payload 64 }
  let wire0 ← encodeMessage identity0
  let wire1 ← encodeMessage identity1
  let compressedWire64 ← encodeMessage compressed64
  validateCase "two-messages" none (wire0 ++ wire1) (.ok #[identity0, identity1])
  cases := cases + 1
  validateCase "three-messages" none (wire0 ++ wire1 ++ compressedWire64)
    (.ok #[identity0, identity1, compressed64])
  cases := cases + 1

  validateCase "valid-plus-incomplete" none
    (wire1 ++ rawWire 0 4 (payload 2)) incomplete
  cases := cases + 1
  validateCase "valid-plus-invalid" none
    (wire1 ++ rawWire 7 0 ByteArray.empty)
    (.error (Status.internal "invalid gRPC compression flag 7"))
  cases := cases + 1
  pure cases

private structure Fixture where
  label : String
  wire : ByteArray
  payloadBytes : Nat

private def fixture? (name : String) : IO (Option Fixture) := do
  let size ← match name with
    | "small" => pure 64
    | "large" => pure 1024
    | _ => pure 0
  if name != "small" && name != "large" then
    pure none
  else
    let wire ← encodeMessage { data := payload size }
    pure (some { label := name, wire := wire, payloadBytes := size })

@[inline] private def resultDigest : Except Status (Array Message) → UInt64
  | .error _ => 1
  | .ok messages => Id.run do
      let mut digest := UInt64.ofNat messages.size + 1469598103934665603
      for message in messages do
        digest := digest * 1099511628211 +
          match message.compressed with
          | .identity => 2
          | .compressed => 3
        digest := digest * 1099511628211 + UInt64.ofNat message.data.size
        for byte in message.data do
          digest := digest * 1099511628211 + UInt64.ofNat byte.toNat + 1
      return digest

private inductive Mode where
  | reference
  | candidate

@[noinline] private def runReference (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (decodeReference none fixture.wire)
  return checksum

@[noinline] private def runCandidate (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (decodeCandidate none fixture.wire)
  return checksum

private def runIterations (mode : Mode) (fixture : @& Fixture)
    (iterations : Nat) : UInt64 :=
  match mode with
  | .reference => runReference fixture iterations
  | .candidate => runCandidate fixture iterations

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
        "usage: aggregate_message_decode_benchmark (reference|candidate) " ++
          "(small|large) iterations warmup")
  let mode ← match modeName with
    | "reference" => pure Mode.reference
    | "candidate" => pure Mode.candidate
    | _ => throw (IO.userError "mode must be reference or candidate")
  let some fixture ← fixture? fixtureName
    | throw (IO.userError "fixture must be small or large")

  let semanticCases ← validateCorpus
  let digest := resultDigest (decodeCandidate none fixture.wire)
  unless digest != 0 do
    throw (IO.userError s!"{fixture.label}: selected fixture digest is zero")
  let warmupChecksum := runIterations mode fixture warmup
  unless warmupChecksum == digest * UInt64.ofNat warmup do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let checksum := runIterations mode fixture iterations
  unless checksum == digest * UInt64.ofNat iterations do
    throw (IO.userError s!"{fixture.label}: measured checksum mismatch")
  IO.println <| s!"benchmark=grpc_aggregate_message_decode_v1 mode={modeName} " ++
    s!"fixture={fixture.label} payload_bytes={fixture.payloadBytes} " ++
    s!"wire_bytes={fixture.wire.size} iterations={iterations} warmup={warmup} " ++
    s!"checksum={checksum}"
  IO.println <| s!"aggregate_message_decode_validation=pass cases={semanticCases} " ++
    "result=exact reference=candidate expected=pass"
