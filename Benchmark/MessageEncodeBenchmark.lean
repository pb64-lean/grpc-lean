import Grpc

open Grpc

/-!
# gRPC message encode benchmark

The reference is the exact former compositional encoder: create the flag byte,
create a separate four-byte length array, append it, then append the payload.
The candidate is the production `Message.encode`, which reserves the exact
wire size, writes the five prefix bytes directly, and appends the payload once.

Only message framing is measured.  Protobuf codecs, compression, HTTP/2,
networking, handlers, and service work are deliberately excluded.
-/

private def payload (size : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for index in [0:size] do
    bytes := bytes.push (UInt8.ofNat ((index * 131 + size * 17 + 29) % 256))
  return bytes

private def uint32BE (value : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((value / 16777216) % 256),
    UInt8.ofNat ((value / 65536) % 256),
    UInt8.ofNat ((value / 256) % 256),
    UInt8.ofNat (value % 256)]

/- Frozen exact copy of the former public `Message.encode` body. -/
@[noinline] private def encodeReference (message : Message) : Except Status ByteArray :=
  let len := message.data.size
  if len > Message.maxWireLength then
    .error (Status.internal "gRPC message exceeds 32-bit wire length")
  else
    .ok <| ByteArray.empty
      |>.push message.compressed.toUInt8
      |>.append (uint32BE len)
      |>.append message.data

@[noinline] private def encodeCandidate (message : Message) : Except Status ByteArray :=
  Message.encode message

private def exactResultEq : Except Status ByteArray → Except Status ByteArray → Bool
  | .error left, .error right => decide (left = right)
  | .ok left, .ok right => left == right
  | _, _ => false

private def validateCase (label : String) (message : Message) : IO Unit := do
  let reference := encodeReference message
  let candidate := encodeCandidate message
  unless exactResultEq reference candidate do
    throw (IO.userError s!"{label}: reference and candidate differ")
  match candidate with
  | .error status => throw (IO.userError s!"{label}: unexpected error: {status.messageD}")
  | .ok wire =>
      unless wire.size == Message.prefixLength + message.data.size
          && wire[0]? == some message.compressed.toUInt8
          && wire.extract Message.prefixLength wire.size == message.data do
        throw (IO.userError s!"{label}: candidate wire shape changed")

private def validateCorpus : IO Nat := do
  let mut cases := 0
  for size in [0, 1, 32, 128, 255, 256, 1024, 65535, 65536] do
    let data := payload size
    validateCase s!"identity-{size}" { compressed := .identity, data := data }
    cases := cases + 1
    validateCase s!"compressed-{size}" { compressed := .compressed, data := data }
    cases := cases + 1
  pure cases

private structure Fixture where
  label : String
  message : Message
  payloadBytes : Nat

private def fixture? (name : String) : Option Fixture :=
  let size := match name with
    | "small" => 32
    | "acme" => 128
    | "large" => 1024
    | _ => 0
  if name != "small" && name != "acme" && name != "large" then
    none
  else
    some {
      label := name
      message := { compressed := .identity, data := payload size }
      payloadBytes := size
    }

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

/- Consume a fixed number of bytes, independent of payload size. -/
@[inline] private def resultDigest : Except Status ByteArray → UInt64
  | .error status => mix 1469598103934665603 (UInt64.ofNat status.code.toNat)
  | .ok wire =>
      let digest := mix 1469598103934665603 (UInt64.ofNat wire.size)
      let digest := mix digest (UInt64.ofNat (wire[0]?.getD 0).toNat)
      let digest := mix digest (UInt64.ofNat (wire[1]?.getD 0).toNat)
      let digest := mix digest (UInt64.ofNat (wire[2]?.getD 0).toNat)
      let digest := mix digest (UInt64.ofNat (wire[3]?.getD 0).toNat)
      let digest := mix digest (UInt64.ofNat (wire[4]?.getD 0).toNat)
      mix digest (UInt64.ofNat (wire[wire.size - 1]?.getD 0).toNat)

private inductive Mode where
  | reference
  | candidate

@[noinline] private def runReference (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (encodeReference fixture.message)
  return checksum

@[noinline] private def runCandidate (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (encodeCandidate fixture.message)
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
        "usage: message_encode_benchmark (reference|candidate) " ++
          "(small|acme|large) iterations warmup")
  let mode ← match modeName with
    | "reference" => pure Mode.reference
    | "candidate" => pure Mode.candidate
    | _ => throw (IO.userError "mode must be reference or candidate")
  let some fixture := fixture? fixtureName
    | throw (IO.userError "fixture must be small, acme, or large")

  let semanticCases ← validateCorpus
  validateCase fixture.label fixture.message
  let digest := resultDigest (encodeCandidate fixture.message)
  unless digest != 0 do
    throw (IO.userError s!"{fixture.label}: selected fixture digest is zero")
  let warmupChecksum := runIterations mode fixture warmup
  unless warmupChecksum == digest * UInt64.ofNat warmup do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let checksum := runIterations mode fixture iterations
  unless checksum == digest * UInt64.ofNat iterations do
    throw (IO.userError s!"{fixture.label}: measured checksum mismatch")
  IO.println <| s!"benchmark=grpc_message_encode_v1 mode={modeName} " ++
    s!"fixture={fixture.label} payload_bytes={fixture.payloadBytes} " ++
    s!"wire_bytes={Message.prefixLength + fixture.payloadBytes} " ++
    s!"iterations={iterations} warmup={warmup} checksum={checksum}"
  IO.println <| s!"message_encode_validation=pass cases={semanticCases} " ++
    "result=exact reference=candidate"
