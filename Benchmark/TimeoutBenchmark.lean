import Grpc

open Grpc

private abbrev Parser := String → Option Timeout

private def unitChecksum : TimeoutUnit → Nat
  | .hour => 1
  | .minute => 2
  | .second => 3
  | .millisecond => 4
  | .microsecond => 5
  | .nanosecond => 6

private def timeoutChecksum : Option Timeout → Nat
  | none => 1
  | some timeout => timeout.value * 7 + unitChecksum timeout.unit

private def runRepeated (parser : Parser) (inputs : Array String)
    (iterations : Nat) : Nat :=
  Id.run do
    let mut checksum := 0
    for _ in [0:iterations] do
      for raw in inputs do
        checksum := checksum + timeoutChecksum (parser raw)
    pure checksum

private def measureParser (sink : IO.Ref Nat) (parser : Parser) (inputs : Array String)
    (iterations : Nat) : IO (Nat × Nat) := do
  let warmupChecksum := runRepeated parser inputs (Nat.min iterations 1000)
  if warmupChecksum == 0 then
    throw (IO.userError "timeout benchmark warmup checksum was zero")
  let started ← IO.monoNanosNow
  -- Publishing the checksum through an observable IO reference forces all
  -- parser work to finish before the ending timestamp is sampled.
  sink.set (runRepeated parser inputs iterations)
  let ended ← IO.monoNanosNow
  let checksum ← sink.get
  pure (ended - started, checksum)

private def measurePair (sink : IO.Ref Nat) (inputs : Array String) (iterations : Nat)
    (reverse : Bool) : IO (Nat × Nat) := do
  let (reference, candidate) ← if reverse then
      let candidate ← measureParser sink Timeout.parseByteIndexed? inputs iterations
      let reference ← measureParser sink Timeout.parseReference? inputs iterations
      pure (reference, candidate)
    else
      let reference ← measureParser sink Timeout.parseReference? inputs iterations
      let candidate ← measureParser sink Timeout.parseByteIndexed? inputs iterations
      pure (reference, candidate)
  unless reference.2 == candidate.2 do
    let message := s!"timeout benchmark checksum mismatch: reference={reference.2}, " ++
      s!"byte_indexed={candidate.2}"
    throw (IO.userError message)
  pure (reference.1, candidate.1)

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value ≤ head then value :: head :: tail
      else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def printCorpus (label : String) (inputs : Array String) (iterations : Nat)
    (referenceSamples candidateSamples : Array Nat) : IO Unit := do
  let reference := median referenceSamples
  let candidate := median candidateSamples
  let operations := iterations * inputs.size
  let referenceNs := if operations == 0 then 0 else reference * 100 / operations
  let candidateNs := if operations == 0 then 0 else candidate * 100 / operations
  let speedup := if candidate == 0 then "n/a" else formatHundredths (reference * 100 / candidate)
  let improvement := if reference == 0 then
      "n/a"
    else if candidate ≤ reference then
      formatHundredths ((reference - candidate) * 10000 / reference)
    else
      s!"-{formatHundredths ((candidate - reference) * 10000 / reference)}"
  IO.println s!"{label}_reference_samples_ns={formatSamples referenceSamples}"
  IO.println s!"{label}_byte_indexed_samples_ns={formatSamples candidateSamples}"
  IO.println s!"{label}_reference_median_ns_per_parse={formatHundredths referenceNs}"
  IO.println s!"{label}_byte_indexed_median_ns_per_parse={formatHundredths candidateNs}"
  IO.println s!"{label}_byte_indexed_speedup_x={speedup} improvement_pct={improvement}"

private def parseIterations (args : List String) : Nat :=
  match args.head? >>= String.toNat? with
  | some n => Nat.max 1 n
  | none => 100000

private def parseRounds (args : List String) : Nat :=
  match (args.drop 1).head? >>= String.toNat? with
  | some n => Nat.max 1 n
  | none => 7

private def commonInputs : Array String := #[
  "1H", "3S", "250m", "10u", "00000001n", "99999999H"
]

private def mixedInputs : Array String := #[
  "1H", "3S", "250m", "00000001n", "99999999H", "", "H", "0n", "123456789S",
  "1x", "1.5S", "+1S", " 1S", "éH", "1é", "１２S"
]

def main (args : List String) : IO Unit := do
  let iterations := parseIterations args
  let rounds := parseRounds args
  -- Keep the corpora behind an IO boundary so whole-program optimization
  -- cannot precompute parses of the closed string literals.
  let corporaRef ← IO.mkRef (commonInputs, mixedInputs)
  let corpora ← corporaRef.get
  let commonInputs := corpora.1
  let mixedInputs := corpora.2
  let checksumSink ← IO.mkRef 0
  IO.println s!"timeout parser: {rounds} alternating rounds x {iterations} corpus sweeps"
  let mut commonReference := #[]
  let mut commonCandidate := #[]
  let mut mixedReference := #[]
  let mut mixedCandidate := #[]
  for round in [0:rounds] do
    let reverse := round % 2 == 1
    let common ← measurePair checksumSink commonInputs iterations reverse
    commonReference := commonReference.push common.1
    commonCandidate := commonCandidate.push common.2
    let mixed ← measurePair checksumSink mixedInputs iterations reverse
    mixedReference := mixedReference.push mixed.1
    mixedCandidate := mixedCandidate.push mixed.2
  printCorpus "common_valid" commonInputs iterations commonReference commonCandidate
  printCorpus "mixed_valid_invalid" mixedInputs iterations mixedReference mixedCandidate
  IO.println s!"timeout_benchmark_checksum={← checksumSink.get}"
