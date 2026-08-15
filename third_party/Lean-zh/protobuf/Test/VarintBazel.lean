import Protobuf.Encoding.Unwire

open Binary
open Protobuf.Encoding

@[always_inline]
private partial def referenceGetVarintBytes : Get ((bs : ByteArray) ×' bs.size > 0) := do
  let rec go (acc : ByteArray) : Get ((bs : ByteArray) ×' bs.size > 0) := do
    if acc.size ≥ 10 then
      throw (.userError "protobuf: varint too long")
    let b ← getThe UInt8
    let acc := acc.push b
    if !b.toBitVec.msb then
      return ⟨acc, by simp [acc, ByteArray.push]; unfold ByteArray.size; simp⟩
    go acc
  go (ByteArray.emptyWithCapacity 10)

@[always_inline]
private partial def referenceGetVarint : Get Nat := do
  let ⟨bs, h⟩ ← referenceGetVarintBytes
  let rec go (acc : Nat) (shift : Nat) (idx : USize) (h : idx.toNat < bs.size) : Nat :=
    let b := bs.uget idx h
    let j := idx + 1
    let acc := acc ||| ((b &&& 0x7F).toNat <<< shift)
    if h' : j.toNat < bs.size then
      go acc (shift + 7) j h'
    else
      acc
  let n := go 0 0 0 h
  if n < UInt64.size then
    return n
  else
    throw (.userError "protobuf: varint overflows uint64")

@[always_inline]
private partial def referencePutVarint (n : Nat) : Put := do
  let rec go (acc : ByteArray) (v : UInt64) : ByteArray :=
    let byte : UInt8 := UInt8.ofNat ((v &&& (0x7F : UInt64)).toNat)
    let v := v >>> 7
    if v = 0 then
      acc.push byte
    else
      go (acc.push (byte ||| (0x80 : UInt8))) v
  let bs := go (ByteArray.emptyWithCapacity 10) (UInt64.ofNat n)
  put_bytes bs

private def repeatByte (count : Nat) (byte : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity count
  for _ in [0:count] do
    out := out.push byte
  return out

private def observe : DecodeResult Nat → String
  | .success value decoder => s!"success:{value}:{decoder.offset}"
  | .error err decoder => s!"error:{err}:{decoder.offset}"
  | .pending _ => "pending"

private def expectEq [BEq α] (actual expected : α) (label : String) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError label

private def compareDecodeAt (bytes : ByteArray) (offset : Nat) (label : String) : IO Unit := do
  let decoder : Decoder := { data := bytes, offset }
  expectEq (observe (get_varint decoder)) (observe (referenceGetVarint decoder)) label

private def boundaryValues : Array Nat := #[
  0,
  1,
  2,
  0x7F,
  0x80,
  0x81,
  0x3FFF,
  0x4000,
  (1 : Nat) <<< 21,
  ((1 : Nat) <<< 28) - 1,
  (1 : Nat) <<< 28,
  ((1 : Nat) <<< 35) + 17,
  ((1 : Nat) <<< 56) - 1,
  (1 : Nat) <<< 56,
  (1 : Nat) <<< 63,
  UInt64.size - 1,
  UInt64.size,
  UInt64.size + 127,
  UInt64.size * 3 + 150
]

private def testWriterCompatibility : IO Unit := do
  let initial : ByteArray := ⟨#[0xA5, 0x5A]⟩
  for value in boundaryValues do
    let (_, expected) := referencePutVarint value initial
    let (_, actual) := put_varint value initial
    expectEq actual expected s!"writer compatibility for {value}"

private def testReaderDifferential : IO Unit := do
  for value in boundaryValues do
    let encoded := Binary.Put.run (referencePutVarint value)
    compareDecodeAt encoded 0 s!"boundary decode for {value}"
    for cut in [0:encoded.size] do
      compareDecodeAt (encoded.extract 0 cut) 0 s!"truncated boundary {value} at {cut}"
    let prefixed := (⟨#[0xA5, 0x5A]⟩ : ByteArray).append encoded |>.push 0xCC
    compareDecodeAt prefixed 2 s!"nonzero decoder offset for {value}"
  for continuationCount in [0:11] do
    let continuationPrefix := repeatByte continuationCount 0x80
    for finalByte in [0:256] do
      let bytes := continuationPrefix.push (UInt8.ofNat finalByte)
      compareDecodeAt bytes 0 s!"continuations={continuationCount}, final={finalByte}"
  compareDecodeAt ⟨#[0x00]⟩ 2 "decoder offset beyond input"

private def expectObservation (bytes : ByteArray) (expected label : String) : IO Unit :=
  let actual := observe (Binary.Get.run get_varint bytes)
  expectEq actual expected s!"{label}: expected {expected}, got {actual}"

private def classify (bytes : ByteArray) : Except ProtoError Nat :=
  protoDecodeParseResultExcept (Binary.Get.run get_varint bytes).toExcept

private def expectTruncated (bytes : ByteArray) (label : String) : IO Unit := do
  match classify bytes with
  | .error .truncated => pure ()
  | .error err => throw <| IO.userError s!"{label}: expected truncated, got {err}"
  | .ok value => throw <| IO.userError s!"{label}: expected truncated, got {value}"

private def expectInvalidVarint (bytes : ByteArray) (label : String) : IO Unit := do
  match classify bytes with
  | .error .invalidVarint => pure ()
  | .error err => throw <| IO.userError s!"{label}: expected invalidVarint, got {err}"
  | .ok value => throw <| IO.userError s!"{label}: expected invalidVarint, got {value}"

private def testExactErrorsAndOffsets : IO Unit := do
  let nineContinuations := repeatByte 9 0x80
  let tenContinuations := repeatByte 10 0x80
  let tenthByteOverflow := nineContinuations.push 0x02
  let noncanonicalZero := nineContinuations.push 0x00
  let maxUInt64 := (repeatByte 9 0xFF).push 0x01
  expectObservation ByteArray.empty "error:EOI:0" "empty input"
  expectObservation nineContinuations "error:EOI:9" "nine-byte truncated prefix"
  expectObservation tenContinuations
    "error:protobuf: varint too long:10" "consumed tenth continuation byte"
  expectObservation tenthByteOverflow
    "error:protobuf: varint overflows uint64:10" "terminating tenth-byte overflow"
  expectObservation noncanonicalZero "success:0:10" "noncanonical ten-byte zero"
  expectObservation maxUInt64 s!"success:{UInt64.size - 1}:10" "maximum uint64"
  expectTruncated nineContinuations "truncated classification"
  expectInvalidVarint tenContinuations "too-long classification"
  expectInvalidVarint tenthByteOverflow "overflow classification"

def main : IO Unit := do
  testWriterCompatibility
  testReaderDifferential
  testExactErrorsAndOffsets
