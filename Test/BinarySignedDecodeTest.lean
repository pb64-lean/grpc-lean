import Binary.Get
import Binary.Put

open Binary

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectSuccess (name : String) (toInt : α → Int) (expected : Int)
    (data : ByteArray) (offset : Nat) (result : DecodeResult α) : IO Unit := do
  match result with
  | .success value decoder =>
      expect (toInt value == expected) s!"{name}: expected {expected}, got {toInt value}"
      expect (decoder.offset == offset) s!"{name}: incorrect consumed byte count"
      expect (decoder.data == data) s!"{name}: input buffer changed"
  | .error error _ => throw (IO.userError s!"{name}: unexpected error {error}")
  | .pending _ => throw (IO.userError s!"{name}: unexpectedly pending")

private def expectEOI (name : String) (data : ByteArray) (offset : Nat)
    (result : DecodeResult α) : IO Unit := do
  match result with
  | .error .eoi decoder =>
      expect (decoder.offset == offset) s!"{name}: short input consumed bytes"
      expect (decoder.data == data) s!"{name}: short input changed the buffer"
  | .error error _ => throw (IO.userError s!"{name}: expected EOI, got {error}")
  | .success .. => throw (IO.userError s!"{name}: short input succeeded")
  | .pending _ => throw (IO.userError s!"{name}: expected EOI, got pending")

private def expectPending (name : String) (result : DecodeResult α) : IO Unit := do
  match result with
  | .pending _ => pure ()
  | .error error _ => throw (IO.userError s!"{name}: expected pending, got {error}")
  | .success .. => throw (IO.userError s!"{name}: succeeded before all bytes arrived")

private def checkRoundTrip [Encode α] [Decode α] (name : String)
    (toInt : α → Int) (width : Nat) (value : α) : IO Unit := do
  let encoded := (put value).run
  expect (encoded.size == width) s!"{name}: incorrect encoded width"
  expectSuccess s!"{name}, round trip" toInt (toInt value) encoded width
    (Get.run (getThe α) encoded)

private def checkCase [Encode α] [Decode α] (name : String)
    (ofInt : Int → α) (toInt : α → Int) (wire : ByteArray) (expected : Int) : IO Unit := do
  let name := s!"{name} {repr wire.data}"
  expectSuccess name toInt expected wire wire.size (Get.run (getThe α) wire)
  expect ((put (ofInt expected)).run == wire) s!"{name}: incorrect encoded bytes"
  checkRoundTrip name toInt wire.size (ofInt expected)

  let suffix : ByteArray := ⟨#[0xa5, 0x5a]⟩
  -- Exercise both the initial offset and a decoder following another field.
  for prefixBytes in (#[(⟨#[]⟩ : ByteArray), ⟨#[0x12, 0x34]⟩]) do
    let data := prefixBytes ++ wire ++ suffix
    let offset := prefixBytes.size
    expectSuccess s!"{name}, offset {offset}" toInt expected data (offset + wire.size)
      ((getThe α) { data, offset })

    -- Every two-fragment split, including empty first/last fragments. Before
    -- completion, direct decoding and terminating a pending decode must both
    -- report EOI without advancing the offset or discarding buffered bytes.
    for split in [0:wire.size + 1] do
      let first := prefixBytes ++ wire.extract 0 split
      let decoder : Decoder := { data := first, offset }
      let result := (pending (getThe α)) decoder
      if split < wire.size then
        expectEOI s!"{name}, truncated at {split}" first offset ((getThe α) decoder)
        expectPending s!"{name}, split {split}" result
        expectEOI s!"{name}, terminated at {split}" first offset result.terminate
        expectPending s!"{name}, empty feed at {split}" (result.feed ⟨#[]⟩)
      let rest := wire.extract split wire.size ++ suffix
      expectSuccess s!"{name}, split {split}" toInt expected data (offset + wire.size)
        ((result.feed ⟨#[]⟩).feed rest)

    -- Multiple retries must work too, not just a single continuation.
    let mut result := (pending (getThe α)) { data := prefixBytes, offset }
    for byte in wire.data do
      expectPending s!"{name}, byte-at-a-time" result
      result := result.feed ⟨#[byte]⟩
    expectSuccess s!"{name}, byte-at-a-time" toInt expected data (offset + wire.size)
      (result.feed suffix)

private def cases16 : Array (Array UInt8 × Int) := #[
  (#[0x00, 0x00], 0),
  (#[0x00, 0x7f], 127),
  (#[0x00, 0x80], 128),
  (#[0x01, 0xff], 511),
  (#[0x7f, 0xff], 32767),
  (#[0x80, 0x00], -32768),
  (#[0xff, 0xff], -1),
  (#[0x80, 0x80], -32640)
]

private def cases32 : Array (Array UInt8 × Int) := #[
  (#[0x00, 0x00, 0x00, 0x00], 0),
  (#[0x00, 0x00, 0x00, 0x7f], 127),
  (#[0x00, 0x00, 0x00, 0x80], 128),
  (#[0x00, 0x00, 0x01, 0xff], 511),
  (#[0x7f, 0xff, 0xff, 0xff], 2147483647),
  (#[0x80, 0x00, 0x00, 0x00], -2147483648),
  (#[0xff, 0xff, 0xff, 0xff], -1),
  (#[0x01, 0x80, 0xfe, 0xff], 25231103),
  (#[0x80, 0x00, 0x00, 0x80], -2147483520)
]

private def cases64 : Array (Array UInt8 × Int) := #[
  (#[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], 0),
  (#[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x7f], 127),
  (#[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80], 128),
  (#[0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0xff], 511),
  (#[0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], 9223372036854775807),
  (#[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00], -9223372036854775808),
  (#[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff], -1),
  (#[0x01, 0x80, 0xfe, 0xff, 0x00, 0x00, 0x00, 0x80], 108366762227007616),
  (#[0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x80], -9223372036854775680)
]

private def checkWidth [Encode α] [Decode α] (name : String) (le : Bool)
    (ofInt : Int → α) (toInt : α → Int) (width : Nat)
    (cases : Array (Array UInt8 × Int)) : IO Unit := do
  for (bytes, expected) in cases do
    checkCase name ofInt toInt ⟨if le then bytes.reverse else bytes⟩ expected
  -- Put a high-bit boundary byte in every position, so a bug in any shift
  -- cannot hide behind the least-significant-byte reproducer.
  for position in [0:width] do
    for byte in (#[0x7f, 0x80, 0xff] : Array UInt8) do
      let bytes := (Array.replicate width (0 : UInt8)).set! position byte
      let magnitude := byte.toNat * 256 ^ (width - 1 - position)
      let expected : Int := if position == 0 && byte.toNat >= 128 then
          (magnitude : Int) - (256 ^ width : Nat)
        else magnitude
      checkCase name ofInt toInt ⟨if le then bytes.reverse else bytes⟩ expected

private def checkConversions : IO Unit := do
  let byte : UInt8 := 0x80
  expect (byte.toInt8.toInt == -128) "UInt8.toInt8 must preserve the 8-bit pattern"
  expect (byte.toInt8.toInt16.toUInt16 == 0xff80) "Int8.toInt16 must sign-extend"
  expect (byte.toInt8.toInt32.toUInt32 == 0xffffff80) "Int8.toInt32 must sign-extend"
  expect (byte.toInt8.toInt64.toUInt64 == 0xffffffffffffff80) "Int8.toInt64 must sign-extend"
  expect ((byte.toInt8.toInt16 <<< 8).toUInt16 == 0x8000) "signed shift semantics changed"
  expect ((((0 : Int16) <<< 8) ||| (byte.toInt8.toInt16 <<< 0)).toInt == -128)
    "signed OR must retain the sign-extended bits"
  expect ((byte.toUInt16 <<< 0).toInt16.toInt == 128) "full-width reinterpretation failed"

section
open Binary.Primitive.BE

private def checkBE16 : IO Unit := do
  checkWidth "Int16 BE" false Int16.ofInt Int16.toInt 2 cases16
  for bits in [0:65536] do
    checkRoundTrip "Int16 BE exhaustive" Int16.toInt 2 bits.toUInt16.toInt16

private def checkBE32 : IO Unit :=
  checkWidth "Int32 BE" false Int32.ofInt Int32.toInt 4 cases32

private def checkBE64 : IO Unit :=
  checkWidth "Int64 BE" false Int64.ofInt Int64.toInt 8 cases64

end

section
open Binary.Primitive.LE

private def checkLE16 : IO Unit := do
  checkWidth "Int16 LE" true Int16.ofInt Int16.toInt 2 cases16
  for bits in [0:65536] do
    checkRoundTrip "Int16 LE exhaustive" Int16.toInt 2 bits.toUInt16.toInt16

private def checkLE32 : IO Unit :=
  checkWidth "Int32 LE" true Int32.ofInt Int32.toInt 4 cases32

private def checkLE64 : IO Unit :=
  checkWidth "Int64 LE" true Int64.ofInt Int64.toInt 8 cases64

end

def main : IO Unit := do
  checkConversions
  let mut failures := 0
  for (name, test) in #[
      ("Int16 BE", checkBE16), ("Int16 LE", checkLE16),
      ("Int32 BE", checkBE32), ("Int32 LE", checkLE32),
      ("Int64 BE", checkBE64), ("Int64 LE", checkLE64)] do
    try
      test
      IO.println s!"PASS: {name}"
    catch error =>
      failures := failures + 1
      IO.eprintln s!"FAIL: {error}"
  expect (failures == 0) s!"{failures} signed decoder test groups failed"
