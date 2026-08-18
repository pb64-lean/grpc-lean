import Grpc

open Grpc

namespace Test.MessageEncode

private def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

private def fail (failure : String) : IO α :=
  throw (IO.userError failure)

private def expectOk (result : Except Status α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => fail s!"{description}: {status.code}: {status.messageD}"

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

private def roundTrips (wire : ByteArray) (message : Message) : Bool :=
  match Message.decodeAll wire with
  | .error _ => false
  | .ok messages =>
      match messages[0]? with
      | none => false
      | some decoded =>
          messages.size == 1
            && decide (decoded.compressed = message.compressed)
            && decoded.data == message.data

private def validateMessage (label : String) (message : Message) : IO Unit := do
  let reference := encodeReference message
  let candidate := encodeCandidate message
  expect (exactResultEq reference candidate)
    s!"{label}: candidate differs from the former encoder"
  let wire ← expectOk candidate s!"{label}: encode"
  let len := message.data.size
  expect (wire.size == Message.prefixLength + len)
    s!"{label}: total wire size changed"
  expect (wire[0]? == some message.compressed.toUInt8)
    s!"{label}: compression flag changed"
  expect (wire[1]? == some (UInt8.ofNat ((len / 16777216) % 256)))
    s!"{label}: most-significant length byte changed"
  expect (wire[2]? == some (UInt8.ofNat ((len / 65536) % 256)))
    s!"{label}: second length byte changed"
  expect (wire[3]? == some (UInt8.ofNat ((len / 256) % 256)))
    s!"{label}: third length byte changed"
  expect (wire[4]? == some (UInt8.ofNat (len % 256)))
    s!"{label}: least-significant length byte changed"
  expect (wire.extract Message.prefixLength wire.size == message.data)
    s!"{label}: payload bytes changed"
  expect (roundTrips wire message)
    s!"{label}: encoded message did not round-trip"

/- Compile-time coverage of the exact over-limit status.  Constructing a real
payload of this size would require more than 4 GiB, so the universal production
law is the safe boundary test. -/
private theorem maxWireErrorCoverage (message : Message)
    (h : message.data.size > Message.maxWireLength) :
    Message.encode message =
      .error (Status.internal "gRPC message exceeds 32-bit wire length") :=
  Message.encode_exceeds_maxWireLength message h

private def validateCorpus : IO Nat := do
  let sizes := [0, 1, 32, 128, 255, 256, 1024, 65535, 65536]
  let mut cases := 0
  for size in sizes do
    let data := payload size
    validateMessage s!"identity-{size}" { compressed := .identity, data := data }
    cases := cases + 1
    validateMessage s!"compressed-{size}" { compressed := .compressed, data := data }
    cases := cases + 1

  let arbitraryCompressed := ByteArray.mk #[0x00, 0xff, 0x1f, 0x8b, 0x00, 0x80]
  validateMessage "compressed-arbitrary-bytes" {
    compressed := .compressed
    data := arbitraryCompressed
  }
  cases := cases + 1

  let defaultMessage : Message := { data := payload 128 }
  let explicitIdentity : Message := { compressed := .identity, data := payload 128 }
  expect (exactResultEq (encodeCandidate defaultMessage) (encodeCandidate explicitIdentity))
    "default compression flag no longer means identity"
  cases := cases + 1
  pure cases

def run : IO Unit := do
  let cases ← validateCorpus
  IO.println s!"message encode: {cases} exact differential cases passed; max-wire error proved"

end Test.MessageEncode

def main : IO Unit :=
  Test.MessageEncode.run
