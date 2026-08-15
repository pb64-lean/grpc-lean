import Protobuf.Encoding
import Protobuf.Notation

open Protobuf Encoding
open scoped Protobuf.Notation

namespace DirectEncodeBenchmark

message Widget {
  uint64 id = 1;
  string name = 2;
  string sku = 3;
  string description = 4;
  uint32 quantity = 5;
  uint64 owner_id = 6;
}

message ListWidgetsResponse {
  repeated Widget widgets = 1;
}

def corpus : ListWidgetsResponse :=
  { widgets := Array.range 55 |>.map fun i =>
      { id := UInt64.ofNat (i * 16384 + 128)
      , name := s!"widget-{i}-café"
      , sku := s!"SKU-{100000 + i}"
      , description := s!"inventory widget {i}: nested protobuf payload 🚀"
      , quantity := UInt32.ofNat (i * 97 + 1)
      , owner_id := UInt64.ofNat (9_000_000 + i * 1024)
      }
  }

/-- The pre-PB-02 generated encoding path, retained here as the benchmark
oracle after `ListWidgetsResponse.encode` adopts direct encoding. -/
def legacyEncode (value : ListWidgetsResponse) : Except ProtoError ByteArray := do
  return Binary.Put.run (Binary.put (← ListWidgetsResponse.toMessage value))

def encodeRepeated (encoder : ListWidgetsResponse → Except ProtoError ByteArray)
    (value : ListWidgetsResponse) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match encoder value with
    | .ok bytes => checksum := checksum + bytes.size
    | .error err => throw (IO.userError err.toString)
  return checksum

def timed (action : IO Nat) : IO (Nat × Nat) := do
  let started ← IO.monoNanosNow
  let checksum ← action
  let elapsed := (← IO.monoNanosNow) - started
  return (elapsed, checksum)

/-- Lean heartbeats are a runtime proxy for small allocations on the current
execution thread. -/
def allocationHeartbeats (action : IO Nat) : IO (Nat × Nat) := do
  IO.setNumHeartbeats 0
  let checksum ← action
  let allocations ← IO.getNumHeartbeats
  return (allocations, checksum)

def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.mergeSort (· < ·)
  sorted[samples.size / 2]!

def speedupTimes100 (legacy direct : Nat) : Nat :=
  if direct == 0 then 0 else legacy * 100 / direct

def ratioTimes100 (larger smaller : Nat) : Nat :=
  if smaller == 0 then 0 else larger * 100 / smaller

def twoDigits (value : Nat) : String :=
  if value < 10 then s!"0{value}" else toString value

def formatRatio (ratio : Nat) : String :=
  s!"{ratio / 100}.{twoDigits (ratio % 100)}x"

def parseIterations : List String → IO Nat
  | [] => pure 2000
  | [raw] =>
      match raw.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"invalid iteration count: {raw}")
  | _ => throw (IO.userError "usage: direct_encode_benchmark [iterations]")

def main (args : List String) : IO Unit := do
  let iterations ← parseIterations args
  let value := corpus
  let .ok legacyBytes := legacyEncode value
    | throw (IO.userError "legacy encoder rejected benchmark corpus")
  let .ok directBytes := ListWidgetsResponse.encode value
    | throw (IO.userError "direct encoder rejected benchmark corpus")
  unless legacyBytes == directBytes do
    throw (IO.userError "legacy and direct benchmark bytes differ")
  let .ok explicitDirectBytes := ListWidgetsResponse.encodeDirect value
    | throw (IO.userError "explicit direct encoder rejected benchmark corpus")
  unless directBytes == explicitDirectBytes do
    throw (IO.userError "adopted and explicit direct encoders differ")

  let warmupIterations := 200
  discard <| encodeRepeated legacyEncode value warmupIterations
  discard <| encodeRepeated ListWidgetsResponse.encode value warmupIterations

  let mut legacySamples := #[]
  let mut directSamples := #[]
  let mut expectedChecksum? : Option Nat := none
  for sample in [0:9] do
    let (firstName, firstEncoder, secondName, secondEncoder) :=
      if sample % 2 == 0 then
        ("legacy", legacyEncode, "direct", ListWidgetsResponse.encode)
      else
        ("direct", ListWidgetsResponse.encode, "legacy", legacyEncode)
    let (firstElapsed, firstChecksum) ← timed <| encodeRepeated firstEncoder value iterations
    let (secondElapsed, secondChecksum) ← timed <| encodeRepeated secondEncoder value iterations
    unless firstChecksum == secondChecksum do
      throw (IO.userError s!"sample {sample} checksums differ")
    match expectedChecksum? with
    | some expected =>
        unless firstChecksum == expected do
          throw (IO.userError s!"sample {sample} checksum changed")
    | none => expectedChecksum? := some firstChecksum
    if firstName == "legacy" then
      legacySamples := legacySamples.push firstElapsed
      directSamples := directSamples.push secondElapsed
    else
      directSamples := directSamples.push firstElapsed
      legacySamples := legacySamples.push secondElapsed
    IO.println s!"sample={sample} {firstName}_ns={firstElapsed} {secondName}_ns={secondElapsed}"

  let allocationIterations := 200
  let (legacyAllocations, legacyAllocationChecksum) ← allocationHeartbeats <|
    encodeRepeated legacyEncode value allocationIterations
  let (directAllocations, directAllocationChecksum) ← allocationHeartbeats <|
    encodeRepeated ListWidgetsResponse.encode value allocationIterations
  unless legacyAllocationChecksum == directAllocationChecksum do
    throw (IO.userError "allocation benchmark checksums differ")

  let legacyMedian := median legacySamples
  let directMedian := median directSamples
  let speedup := speedupTimes100 legacyMedian directMedian
  let allocationReduction := ratioTimes100 legacyAllocations directAllocations
  let allocationSavedPercent :=
    if legacyAllocations == 0 then 0
    else (legacyAllocations - directAllocations) * 100 / legacyAllocations
  IO.println s!"corpus_widgets={value.widgets.size} encoded_bytes={legacyBytes.size} iterations={iterations}"
  IO.println s!"legacy_samples_ns={legacySamples}"
  IO.println s!"direct_samples_ns={directSamples}"
  IO.println s!"legacy_median_ns={legacyMedian} direct_median_ns={directMedian} speedup={formatRatio speedup}"
  IO.println s!"allocation_proxy_iterations={allocationIterations} legacy_heartbeats={legacyAllocations} direct_heartbeats={directAllocations} reduction={formatRatio allocationReduction} saved_percent={allocationSavedPercent}%"
  unless speedup >= 150 do
    throw (IO.userError s!"direct encoding gate failed: {formatRatio speedup} < 1.50x")
  unless directAllocations * 10 <= legacyAllocations * 7 do
    throw (IO.userError s!"direct encoding allocation-proxy gate failed: saved {allocationSavedPercent}% < 30%")

end DirectEncodeBenchmark

def main (args : List String) : IO Unit := DirectEncodeBenchmark.main args
