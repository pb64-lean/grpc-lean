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

message WidgetResponse {
  Widget widget = 1;
}

message ListWidgetsResponse {
  repeated Widget widgets = 1;
}

message DeleteWidgetResponse {
  bool deleted = 1;
}

def widgetAt (i : Nat) : Widget :=
  { id := UInt64.ofNat (i * 16384 + 128)
  , name := s!"widget-{i}-café"
  , sku := s!"SKU-{100000 + i}"
  , description := s!"inventory widget {i}: nested protobuf payload 🚀"
  , quantity := UInt32.ofNat (i * 97 + 1)
  , owner_id := UInt64.ofNat (9_000_000 + i * 1024)
  }

def widgetResponseCorpus : WidgetResponse :=
  { widget := some (widgetAt 17) }

def listResponseCorpus : ListWidgetsResponse :=
  { widgets := Array.range 55 |>.map widgetAt }

def deleteResponseCorpus : Array DeleteWidgetResponse :=
  #[{ deleted := false }, { deleted := true }]

inductive ResponseCase where
  | widget (value : WidgetResponse)
  | list (value : ListWidgetsResponse)
  | delete (value : DeleteWidgetResponse)

/-- One hundred response calls matching the Acme 55/20/15/8/2 operation mix.
Get, update, and create all return `WidgetResponse`; list returns 55 widgets. -/
def weightedResponseCorpus : Array ResponseCase :=
  Array.range 100 |>.map fun i =>
    if i < 55 then
      .widget { widget := some (widgetAt i) }
    else if i < 75 then
      .list listResponseCorpus
    else if i < 90 then
      .widget { widget := some (widgetAt (100 + i)) }
    else if i < 98 then
      .widget { widget := some (widgetAt (200 + i)) }
    else
      .delete { deleted := i % 2 == 1 }

/-- The pre-PB-02 generated encoding path, retained as the benchmark oracle. -/
def legacyEncode {α} (toMessage : α → Except ProtoError Message)
    (value : α) : Except ProtoError ByteArray := do
  return Binary.Put.run (Binary.put (← toMessage value))

def legacyWidgetResponse : WidgetResponse → Except ProtoError ByteArray :=
  legacyEncode WidgetResponse.toMessage

def legacyListResponse : ListWidgetsResponse → Except ProtoError ByteArray :=
  legacyEncode ListWidgetsResponse.toMessage

def legacyDeleteResponse : DeleteWidgetResponse → Except ProtoError ByteArray :=
  legacyEncode DeleteWidgetResponse.toMessage

def legacyResponseCase : ResponseCase → Except ProtoError ByteArray
  | .widget value => legacyWidgetResponse value
  | .list value => legacyListResponse value
  | .delete value => legacyDeleteResponse value

def directResponseCase : ResponseCase → Except ProtoError ByteArray
  | .widget value => WidgetResponse.encode value
  | .list value => ListWidgetsResponse.encode value
  | .delete value => DeleteWidgetResponse.encode value

def requireSameOutcome (context : String) (legacy direct : Except ProtoError ByteArray) :
    IO Unit := do
  match legacy, direct with
  | .ok legacyBytes, .ok directBytes =>
      unless legacyBytes == directBytes do
        throw (IO.userError s!"{context}: legacy and direct bytes differ")
  | .error legacyError, .error directError =>
      unless legacyError.toString == directError.toString do
        throw (IO.userError s!"{context}: legacy and direct errors differ")
  | .ok _, .error directError =>
      throw (IO.userError s!"{context}: direct failed unexpectedly: {directError}")
  | .error legacyError, .ok _ =>
      throw (IO.userError s!"{context}: direct accepted legacy error: {legacyError}")

def encodeRepeated {α} (encoder : α → Except ProtoError ByteArray)
    (value : α) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match encoder value with
    | .ok bytes => checksum := checksum + bytes.size
    | .error err => throw (IO.userError err.toString)
  return checksum

def encodeArrayRepeated {α} (encoder : α → Except ProtoError ByteArray)
    (values : Array α) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    for value in values do
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

def runComparison (label : String) (legacyAction directAction : Nat → IO Nat)
    (iterations allocationIterations : Nat) (enforceGate : Bool) : IO Unit := do
  let warmupIterations := min 200 (max 1 (iterations / 10))
  discard <| legacyAction warmupIterations
  discard <| directAction warmupIterations

  let mut legacySamples := #[]
  let mut directSamples := #[]
  let mut expectedChecksum? : Option Nat := none
  for sample in [0:9] do
    let (firstName, firstAction, secondName, secondAction) :=
      if sample % 2 == 0 then
        ("legacy", legacyAction, "direct", directAction)
      else
        ("direct", directAction, "legacy", legacyAction)
    let (firstElapsed, firstChecksum) ← timed <| firstAction iterations
    let (secondElapsed, secondChecksum) ← timed <| secondAction iterations
    unless firstChecksum == secondChecksum do
      throw (IO.userError s!"{label} sample {sample}: checksums differ")
    match expectedChecksum? with
    | some expected =>
        unless firstChecksum == expected do
          throw (IO.userError s!"{label} sample {sample}: checksum changed")
    | none => expectedChecksum? := some firstChecksum
    if firstName == "legacy" then
      legacySamples := legacySamples.push firstElapsed
      directSamples := directSamples.push secondElapsed
    else
      directSamples := directSamples.push firstElapsed
      legacySamples := legacySamples.push secondElapsed
    IO.println s!"corpus={label} sample={sample} {firstName}_ns={firstElapsed} {secondName}_ns={secondElapsed}"

  let (legacyAllocations, legacyAllocationChecksum) ← allocationHeartbeats <|
    legacyAction allocationIterations
  let (directAllocations, directAllocationChecksum) ← allocationHeartbeats <|
    directAction allocationIterations
  unless legacyAllocationChecksum == directAllocationChecksum do
    throw (IO.userError s!"{label}: allocation benchmark checksums differ")

  let legacyMedian := median legacySamples
  let directMedian := median directSamples
  let speedup := speedupTimes100 legacyMedian directMedian
  let allocationReduction := ratioTimes100 legacyAllocations directAllocations
  let allocationSavedPercent :=
    if legacyAllocations == 0 then 0
    else (legacyAllocations - directAllocations) * 100 / legacyAllocations
  IO.println s!"corpus={label} iterations={iterations} legacy_samples_ns={legacySamples}"
  IO.println s!"corpus={label} iterations={iterations} direct_samples_ns={directSamples}"
  IO.println s!"corpus={label} legacy_median_ns={legacyMedian} direct_median_ns={directMedian} speedup={formatRatio speedup}"
  IO.println s!"corpus={label} allocation_proxy_iterations={allocationIterations} legacy_heartbeats={legacyAllocations} direct_heartbeats={directAllocations} reduction={formatRatio allocationReduction} saved_percent={allocationSavedPercent}%"
  if enforceGate then
    unless speedup >= 150 do
      throw (IO.userError s!"{label}: direct encoding gate failed: {formatRatio speedup} < 1.50x")
    unless directAllocations * 10 <= legacyAllocations * 7 do
      throw (IO.userError s!"{label}: allocation-proxy gate failed: saved {allocationSavedPercent}% < 30%")

def parseIterations : List String → IO Nat
  | [] => pure 2000
  | [raw] =>
      match raw.toNat? with
      | some n => pure n
      | none => throw (IO.userError s!"invalid iteration count: {raw}")
  | _ => throw (IO.userError "usage: direct_encode_benchmark [iterations]")

def main (args : List String) : IO Unit := do
  let iterations ← parseIterations args

  requireSameOutcome "widget response oracle"
    (legacyWidgetResponse widgetResponseCorpus)
    (WidgetResponse.encode widgetResponseCorpus)
  for (value, i) in deleteResponseCorpus.toList.zipIdx do
    requireSameOutcome s!"delete response oracle {i}"
      (legacyDeleteResponse value) (DeleteWidgetResponse.encode value)
  for (value, i) in weightedResponseCorpus.toList.zipIdx do
    requireSameOutcome s!"weighted response oracle {i}"
      (legacyResponseCase value) (directResponseCase value)

  let .ok widgetBytes := WidgetResponse.encode widgetResponseCorpus
    | throw (IO.userError "direct widget-response encoder rejected benchmark corpus")
  let .ok listBytes := ListWidgetsResponse.encode listResponseCorpus
    | throw (IO.userError "direct list-response encoder rejected benchmark corpus")
  IO.println s!"widget_response_bytes={widgetBytes.size} list_widgets={listResponseCorpus.widgets.size} list_response_bytes={listBytes.size} weighted_response_calls={weightedResponseCorpus.size}"

  let widgetIterations := iterations * 25
  runComparison "widget_response"
    (encodeRepeated legacyWidgetResponse widgetResponseCorpus)
    (encodeRepeated WidgetResponse.encode widgetResponseCorpus)
    widgetIterations 200 true

  runComparison "delete_response"
    (encodeArrayRepeated legacyDeleteResponse deleteResponseCorpus)
    (encodeArrayRepeated DeleteWidgetResponse.encode deleteResponseCorpus)
    (iterations * 10) 200 false

  let weightedIterations := max 1 (iterations / 20)
  runComparison "weighted_55_20_15_8_2"
    (encodeArrayRepeated legacyResponseCase weightedResponseCorpus)
    (encodeArrayRepeated directResponseCase weightedResponseCorpus)
    weightedIterations 10 true

end DirectEncodeBenchmark

def main (args : List String) : IO Unit := DirectEncodeBenchmark.main args
