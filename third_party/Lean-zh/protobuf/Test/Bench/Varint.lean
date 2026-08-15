import Protobuf.Encoding.Binary

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

private def seeds : Array Nat := #[
  0, 1, 2, 3, 4, 5, 7, 8, 10, 15, 16, 31, 32, 63, 64, 100, 126, 127,
  128, 150, 255, 300, 1024, 4096, 0x3FFF, 0x4000,
  (1 : Nat) <<< 21, ((1 : Nat) <<< 28) - 1,
  ((1 : Nat) <<< 35) + 17, ((1 : Nat) <<< 56) - 1,
  (1 : Nat) <<< 63, UInt64.size - 1
]

private def benchmarkValues : Array Nat := Id.run do
  let mut out := Array.emptyWithCapacity (seeds.size * 64)
  for round in [0:64] do
    for value in seeds do
      out := out.push (value ^^^ (round % 4))
  return out

private def encodeOnce (putOne : Nat → Put) (values : Array Nat) : ByteArray :=
  Binary.Put.run (values.forM putOne) (values.size * 10)

private def decodeOnce (getOne : Get Nat) (count : Nat) (bytes : ByteArray) : Except String Nat := do
  let result := Binary.Get.run (do
    let mut checksum := 0
    for _ in [0:count] do
      checksum := checksum + (← getOne)
    return checksum) bytes
  result.toExceptString

private def encodeRepeated (putOne : Nat → Put) (values : Array Nat)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    checksum := checksum + (encodeOnce putOne values).size
  return checksum

private def decodeRepeated (getOne : Get Nat) (count : Nat) (bytes : ByteArray)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match decodeOnce getOne count bytes with
    | .ok value => checksum := checksum + value
    | .error err => throw <| IO.userError err
  return checksum

private def timed (action : IO Nat) : IO (Nat × Nat) := do
  let started ← IO.monoNanosNow
  let checksum ← action
  let elapsed := (← IO.monoNanosNow) - started
  return (elapsed, checksum)

private def parseIterations (args : List String) : IO Nat := do
  match args with
  | [] => pure 10000
  | [raw] =>
      match raw.toNat? with
      | some value => pure value
      | none => throw <| IO.userError s!"invalid iteration count: {raw}"
  | _ => throw <| IO.userError "usage: varint_benchmark [iterations]"

private def rate (operations elapsed : Nat) : Nat :=
  if elapsed == 0 then 0 else operations * 1000000000 / elapsed

private def speedupTimes100 (reference direct : Nat) : Nat :=
  if direct == 0 then 0 else reference * 100 / direct

private def twoDigits (value : Nat) : String :=
  if value < 10 then s!"0{value}" else toString value

private def printResult (name : String) (operations referenceElapsed directElapsed : Nat) : IO Unit := do
  let speedup := speedupTimes100 referenceElapsed directElapsed
  IO.println s!"{name}: operations={operations}"
  IO.println s!"reference_ns={referenceElapsed} reference_varints_s={rate operations referenceElapsed}"
  IO.println s!"direct_ns={directElapsed} direct_varints_s={rate operations directElapsed}"
  IO.println s!"speedup={speedup / 100}.{twoDigits (speedup % 100)}x"

def main (args : List String) : IO Unit := do
  let iterations ← parseIterations args
  let values := benchmarkValues
  let referenceBytes := encodeOnce referencePutVarint values
  let directBytes := encodeOnce put_varint values
  unless referenceBytes == directBytes do
    throw <| IO.userError "reference and direct encoders produced different bytes"
  let .ok referenceChecksum := decodeOnce referenceGetVarint values.size referenceBytes
    | throw <| IO.userError "reference decoder rejected the benchmark corpus"
  let .ok directChecksum := decodeOnce get_varint values.size referenceBytes
    | throw <| IO.userError "direct decoder rejected the benchmark corpus"
  unless referenceChecksum == directChecksum do
    throw <| IO.userError "reference and direct decoders produced different checksums"
  let warmupIterations := 20
  discard <| encodeRepeated referencePutVarint values warmupIterations
  discard <| encodeRepeated put_varint values warmupIterations
  discard <| decodeRepeated referenceGetVarint values.size referenceBytes warmupIterations
  discard <| decodeRepeated get_varint values.size referenceBytes warmupIterations
  let (referenceEncodeNs, referenceEncodeChecksum) ←
    timed <| encodeRepeated referencePutVarint values iterations
  let (directEncodeNs, directEncodeChecksum) ←
    timed <| encodeRepeated put_varint values iterations
  let (referenceDecodeNs, referenceDecodeChecksum) ←
    timed <| decodeRepeated referenceGetVarint values.size referenceBytes iterations
  let (directDecodeNs, directDecodeChecksum) ←
    timed <| decodeRepeated get_varint values.size referenceBytes iterations
  unless referenceEncodeChecksum == directEncodeChecksum do
    throw <| IO.userError "encode benchmark checksums differ"
  unless referenceDecodeChecksum == directDecodeChecksum do
    throw <| IO.userError "decode benchmark checksums differ"
  let operations := values.size * iterations
  IO.println s!"varint corpus: values={values.size} encoded_bytes={referenceBytes.size} iterations={iterations}"
  printResult "encode" operations referenceEncodeNs directEncodeNs
  printResult "decode" operations referenceDecodeNs directDecodeNs
