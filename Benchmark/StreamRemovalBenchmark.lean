import Grpc

open Grpc

/-!
# HTTP/2 stream-state removal benchmark

Measures the production `Connection.removeStream` operation in the
remove-and-reinsert shape used by stream updates.  The benchmark-local
reference path is the pre-change `Array.filter` implementation; fixtures,
full-array equivalence checks, warmup, and final validation stay outside the
reported samples.  A constant-size state digest remains inside every measured
iteration.

The rotating target order removes the first logical stream on every step and
restores the original order after a complete cycle.  It models streams closing
or being updated in admission order while keeping every iteration at the same
depth.  Separate absent-target cases expose the allocation cost of a defensive
no-op removal without making it part of the common-path claim.
-/

private inductive Algorithm where
  | reference
  | production

private structure Fixture where
  label : String
  streams : Array Http2.Connection.StreamState
  targetIds : Array Nat
  reinsert : Bool
  expectedDigest : Nat

private def stream (streamId : Nat) : Http2.Connection.StreamState :=
  { streamId }

private def streamsOfDepth (depth : Nat) : Array Http2.Connection.StreamState := Id.run do
  let mut streams := #[]
  for index in [0:depth] do
    streams := streams.push (stream (index * 2 + 1))
  return streams

private def referenceRemove (streams : Array Http2.Connection.StreamState)
    (streamId : Nat) : Array Http2.Connection.StreamState :=
  streams.filter (fun stream => stream.streamId != streamId)

@[inline] private def stateDigest
    (streams : @& Array Http2.Connection.StreamState) : Nat :=
  let first := (streams[0]?).map (·.streamId) |>.getD 0
  let middle := (streams[streams.size / 2]?).map (·.streamId) |>.getD 0
  let last := (streams[streams.size - 1]?).map (·.streamId) |>.getD 0
  streams.size * 1000003 + first * 1009 + middle * 101 + last

private def removeWith (algorithm : Algorithm)
    (streams : Array Http2.Connection.StreamState) (streamId : Nat) :
    Array Http2.Connection.StreamState :=
  match algorithm with
  | .reference => referenceRemove streams streamId
  | .production => Http2.Connection.removeStream streams streamId

private def cycleOnce (algorithm : Algorithm) (reinsert : Bool)
    (streams : Array Http2.Connection.StreamState) (targetId : Nat) :
    Array Http2.Connection.StreamState :=
  let streams := removeWith algorithm streams targetId
  if reinsert then streams.push (stream targetId) else streams

private def makeFixture (label : String) (depth : Nat)
    (absent : Bool := false) : IO Fixture := do
  let streams := streamsOfDepth depth
  let targetIds :=
    if absent then #[depth * 2 + 101]
    else streams.map (·.streamId)
  unless !targetIds.isEmpty do
    throw (IO.userError s!"{label}: target sequence is empty")
  let mut reference := streams
  let mut production := streams
  for targetId in targetIds do
    reference := cycleOnce .reference (!absent) reference targetId
    production := cycleOnce .production (!absent) production targetId
  unless production.map (·.streamId) == reference.map (·.streamId) do
    throw (IO.userError s!"{label}: production cycle differs from reference")
  unless reference.size == depth do
    throw (IO.userError s!"{label}: cycle changed stream depth")
  unless reference.map (·.streamId) == streams.map (·.streamId) do
    throw (IO.userError s!"{label}: cycle did not preserve the expected stream order")
  pure {
    label, streams, targetIds, reinsert := !absent,
    expectedDigest := stateDigest reference
  }

@[noinline] private def runRepeated (algorithm : Algorithm) (fixture : @& Fixture)
    (iterations : Nat) : IO Nat := do
  let mut streams := fixture.streams
  let mut checksum := 0
  for iteration in [0:iterations] do
    let targetId := fixture.targetIds[iteration % fixture.targetIds.size]!
    streams := cycleOnce algorithm fixture.reinsert streams targetId
    checksum := checksum + stateDigest streams
  pure (checksum + stateDigest streams)

private def expectedChecksum (fixture : @& Fixture) (iterations : Nat) : Nat := Id.run do
  let mut streams := fixture.streams
  let mut checksum := 0
  for iteration in [0:iterations] do
    let targetId := fixture.targetIds[iteration % fixture.targetIds.size]!
    streams := cycleOnce .reference fixture.reinsert streams targetId
    checksum := checksum + stateDigest streams
  return checksum + stateDigest streams

private def measureFixture (algorithm : Algorithm) (fixture : @& Fixture)
    (iterations : Nat) : IO (Nat × Nat) := do
  let expected := expectedChecksum fixture iterations
  let warmupIterations := Nat.min iterations 1000
  let warmup ← runRepeated algorithm fixture warmupIterations
  unless warmup == expectedChecksum fixture warmupIterations do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let started ← IO.monoNanosNow
  let checksum ← runRepeated algorithm fixture iterations
  let elapsed := (← IO.monoNanosNow) - started
  unless checksum == expected do
    throw (IO.userError s!"{fixture.label}: measured checksum mismatch")
  pure (elapsed, checksum)

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
    if value <= head then value :: head :: tail else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def parsePositive (name : String) (value? : Option String)
    (fallback : Nat) : IO Nat := do
  let value := (value? >>= String.toNat?).getD fallback
  unless value > 0 do throw (IO.userError s!"{name} must be positive")
  pure value

private def algorithmName : Algorithm → String
  | .reference => "reference"
  | .production => "production"

private def parseAlgorithm : String → Option Algorithm
  | "reference" => some .reference
  | "production" => some .production
  | _ => none

def main (args : List String) : IO Unit := do
  let iterations ← parsePositive "iterations" args[0]? 100000
  let rounds ← parsePositive "rounds" args[1]? 7
  unless rounds >= 3 && rounds % 2 == 1 do
    throw (IO.userError "rounds must be an odd integer of at least 3")
  let algorithmText := args[2]?.getD "production"
  let some algorithm := parseAlgorithm algorithmText
    | throw (IO.userError s!"unknown algorithm: {algorithmText}")
  let selection := args[3]?.getD "all"
  unless #["all", "depth_1", "depth_4", "depth_48", "absent_48"].contains selection do
    throw (IO.userError s!"unknown benchmark selection: {selection}")
  unless args.length <= 4 do
    throw (IO.userError <|
      "usage: stream_removal_benchmark [iterations] [rounds] " ++
        "[reference|production] [all|depth_1|depth_4|depth_48|absent_48]")

  let fixtures := #[
    ← makeFixture "depth_1" 1,
    ← makeFixture "depth_4" 4,
    ← makeFixture "depth_48" 48,
    ← makeFixture "absent_48" 48 true
  ]
  IO.println <| "benchmark=http2_stream_removal_v1 " ++
    s!"algorithm={algorithmName algorithm} selection={selection} validation=pass"
  for fixture in fixtures do
    if selection == "all" || selection == fixture.label then
      let mut samples := #[]
      let mut checksum := 0
      for _ in [0:rounds] do
        let (elapsed, roundChecksum) ← measureFixture algorithm fixture iterations
        samples := samples.push elapsed
        checksum := roundChecksum
      let perOperation := median samples * 100 / iterations
      IO.println <| s!"case={fixture.label} depth={fixture.streams.size} " ++
        s!"iterations={iterations} checksum={checksum} expected_digest={fixture.expectedDigest}"
      IO.println s!"case={fixture.label} samples_ns={formatSamples samples}"
      IO.println s!"case={fixture.label} median_ns_per_operation={formatHundredths perOperation}"
  IO.println "HTTP/2 stream-removal benchmark completed"
