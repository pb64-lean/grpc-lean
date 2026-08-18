import Grpc

/-!
# HPACK dynamic-table size-accounting benchmark

The reference retains the former temporary-`ByteArray` formula and the
candidate reads cached UTF-8 byte sizes.  Both noinline paths otherwise use
the same insertion algorithm and digest only the resulting state, so each
timed iteration performs exactly one production-shaped insertion.  All-fixture
semantic validation and the bounded warmup precede the selected loop, but a
whole-process counter includes both: validation is fixed, while warmup uses
the selected mode and fixture for `min iterations 1000`.  Metadata entry-size
equality is checked during validation; this benchmark does not measure a
header-list fold.
-/

namespace Grpc.HeaderSizeAccountingBenchmarkHarness

@[noinline] private def referenceEntrySize (header : Header) : Nat :=
  header.name.toUTF8.size + header.value.toUTF8.size + 32

@[noinline] private def candidateEntrySize (header : Header) : Nat :=
  header.name.utf8ByteSize + header.value.utf8ByteSize + 32

private def referenceDynamicSize (entries : Array Header) : Nat :=
  entries.foldl (fun total header => total + referenceEntrySize header) 0

private def referenceEvictTo (maxSize : Nat) (entries : Array Header) : Array Header :=
  if referenceDynamicSize entries <= maxSize then
    entries
  else if _hempty : entries.isEmpty then
    entries
  else
    referenceEvictTo maxSize entries.pop
  termination_by entries.size
  decreasing_by
    simp only [Array.isEmpty, decide_eq_true_eq] at _hempty
    simp only [Array.size_pop]
    omega

private def prepend (header : Header) (entries : Array Header) : Array Header :=
  entries.foldl (fun result entry => result.push entry) #[header]

@[noinline] private def referenceInsert
    (state : Http2.Hpack.State) (header : Header) : Http2.Hpack.State :=
  if referenceEntrySize header > state.maxSize then
    { state with dynamic := #[] }
  else
    { state with dynamic :=
        referenceEvictTo state.maxSize (prepend header state.dynamic) }

private def headersOfDepth (depth : Nat) : Array Header :=
  (Array.range depth).map fun index =>
    Header.of s!"x-accounting-{index}" s!"value-{index}"

private def unicodeHeadersOfDepth (depth : Nat) : Array Header :=
  (Array.range depth).map fun index =>
    { name := s!"é-{index}", value := s!"雪-😀-{index}" }

private structure Fixture where
  name : String
  state : Http2.Hpack.State
  header : Header
  expectedDynamicCount : Nat

private def exactDepthFixture (depth : Nat) : Fixture :=
  let dynamic := headersOfDepth depth
  let header := Header.of "x-accounting-new" "candidate"
  let maxSize := referenceDynamicSize dynamic + referenceEntrySize header
  {
    name := s!"depth_{depth}"
    state := { dynamic := dynamic, maxSize := maxSize, maxAllowedSize := maxSize }
    header := header
    expectedDynamicCount := depth + 1
  }

private def forcedEvictionFixture : Fixture :=
  let dynamic := headersOfDepth 48
  let header := Header.of "x-accounting-new" "forced-eviction"
  let retained := dynamic.extract 0 3
  let maxSize := referenceEntrySize header + referenceDynamicSize retained
  {
    name := "forced_eviction"
    state := { dynamic := dynamic, maxSize := maxSize, maxAllowedSize := maxSize }
    header := header
    expectedDynamicCount := 4
  }

private def oversizedFixture : Fixture := {
  name := "oversized"
  state := {
    dynamic := headersOfDepth 16
    maxSize := 33
    maxAllowedSize := 4096
    pendingSizeUpdate := some 33
  }
  header := { name := "超", value := "😀-oversized" }
  expectedDynamicCount := 0
}

private def unicodeFixture : Fixture :=
  let dynamic := unicodeHeadersOfDepth 16
  let header : Header := { name := "ключ", value := "😀\u0000雪" }
  let maxSize := referenceDynamicSize dynamic + referenceEntrySize header
  {
    name := "unicode"
    state := { dynamic := dynamic, maxSize := maxSize, maxAllowedSize := maxSize }
    header := header
    expectedDynamicCount := 17
  }

private def fixtures : Array Fixture := #[
  exactDepthFixture 1,
  exactDepthFixture 4,
  exactDepthFixture 16,
  exactDepthFixture 48,
  forcedEvictionFixture,
  oversizedFixture,
  unicodeFixture
]

private def sameState (left right : Http2.Hpack.State) : Bool :=
  left.dynamic == right.dynamic &&
    left.maxSize == right.maxSize &&
    left.maxAllowedSize == right.maxAllowedSize &&
    left.pendingSizeUpdate == right.pendingSizeUpdate

private def validateFixture (fixture : @& Fixture) : IO Unit := do
  let referenceSize := referenceEntrySize fixture.header
  let candidateSize := candidateEntrySize fixture.header
  unless referenceSize == candidateSize &&
      Http2.Hpack.entrySize fixture.header == referenceSize &&
      Metadata.headerListEntrySize fixture.header == referenceSize do
    throw (IO.userError s!"{fixture.name}: exact entry sizes differ")
  let reference := referenceInsert fixture.state fixture.header
  let candidate := Http2.Hpack.insert fixture.state fixture.header
  unless sameState reference candidate do
    throw (IO.userError s!"{fixture.name}: resulting insert states differ")
  unless candidate.dynamic.size == fixture.expectedDynamicCount do
    throw (IO.userError <|
      s!"{fixture.name}: resulting dynamic count {candidate.dynamic.size} != " ++
        s!"{fixture.expectedDynamicCount}")

private def findFixture? (name : String) : Option Fixture :=
  fixtures.find? fun fixture => fixture.name == name

@[noinline] private def stateDigest (state : @& Http2.Hpack.State) : Nat :=
  let base := state.dynamic.size * 65537 + state.maxSize * 257 + state.maxAllowedSize
  match state.dynamic[0]?, state.dynamic.back? with
  | some first, some last =>
      base + first.name.utf8ByteSize * 17 + first.value.utf8ByteSize * 19 +
        last.name.utf8ByteSize * 23 + last.value.utf8ByteSize * 29
  | _, _ => base + 1

@[noinline] private def runReference (fixture : @& Fixture) (iterations : Nat) : Nat :=
  Id.run do
    let mut checksum := 0
    for _ in [0:iterations] do
      let result := referenceInsert fixture.state fixture.header
      checksum := checksum + stateDigest result
    return checksum

@[noinline] private def runCandidate (fixture : @& Fixture) (iterations : Nat) : Nat :=
  Id.run do
    let mut checksum := 0
    for _ in [0:iterations] do
      let result := Http2.Hpack.insert fixture.state fixture.header
      checksum := checksum + stateDigest result
    return checksum

private def parsePositive (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a positive decimal integer")
  unless parsed > 0 do
    throw (IO.userError s!"{label} must be positive")
  pure parsed

def main (args : List String) : IO Unit := do
  let (mode, fixtureName, iterations) ← match args with
    | [mode, fixtureName, iterations] =>
        pure (mode, fixtureName, ← parsePositive "iterations" iterations)
    | _ => throw (IO.userError <|
        "usage: header_size_accounting_benchmark (reference|candidate) " ++
          "(depth_1|depth_4|depth_16|depth_48|forced_eviction|oversized|unicode) " ++
          "iterations")
  for fixture in fixtures do
    validateFixture fixture
  let some fixture := findFixture? fixtureName
    | throw (IO.userError s!"unknown fixture: {fixtureName}")
  let referenceResult := referenceInsert fixture.state fixture.header
  let contribution := stateDigest referenceResult
  let expected := contribution * iterations
  let warmupIterations := Nat.min iterations 1000
  let warmupExpected := contribution * warmupIterations
  let warmupChecksum ← match mode with
    | "reference" => pure (runReference fixture warmupIterations)
    | "candidate" => pure (runCandidate fixture warmupIterations)
    | _ => throw (IO.userError "mode must be reference or candidate")
  unless warmupChecksum == warmupExpected do
    throw (IO.userError s!"{fixture.name}: warmup checksum mismatch")
  let checksum ← match mode with
    | "reference" => pure (runReference fixture iterations)
    | "candidate" => pure (runCandidate fixture iterations)
    | _ => throw (IO.userError "mode must be reference or candidate")
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != expected {expected}")
  IO.println <|
    s!"benchmark=header_size_accounting mode={mode} fixture={fixture.name} " ++
      s!"dynamic_depth={fixture.state.dynamic.size} iterations={iterations} " ++
      s!"entry_bytes={referenceEntrySize fixture.header} checksum={checksum}"

end Grpc.HeaderSizeAccountingBenchmarkHarness

def main (args : List String) : IO Unit :=
  Grpc.HeaderSizeAccountingBenchmarkHarness.main args
