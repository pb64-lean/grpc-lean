import Grpc

open Grpc

/-!
# Header-name normalization benchmark

Measures the production `Header.of` path while varying the input to
`Header.normalizeName`. Fixture construction, exact `String.toLower`
comparison, pointer-identity observation, warmup, and final checksum validation
stay outside the reported samples. The measured checksum reads a fixed set of
bytes from every normalized name so the result remains live without adding a
length-proportional traversal.

Lowercase ASCII fixtures model ordinary HTTP/2 and gRPC metadata. Uppercase and
Unicode fixtures are correctness/performance controls for the fallback path,
not common-path optimization claims.
-/

private structure Fixture where
  label : String
  names : Array String
  expectedDigestPerSweep : Nat

@[noinline] private def runtimeCopy (value : String) : String :=
  String.ofList value.toList

@[inline] private def nameDigest (name : String) : Nat :=
  if h : name.utf8ByteSize > 0 then
    let first := name.getUTF8Byte ⟨0⟩ (by
      simpa only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using h)
    name.utf8ByteSize * 257 + first.toNat * 17
  else
    1

private unsafe def makeFixture (label : String) (rawNames : Array String) : IO Fixture := do
  unless !rawNames.isEmpty do
    throw (IO.userError s!"{label}: fixture is empty")
  let mut names := #[]
  let mut expectedDigestPerSweep := 0
  let mut reused := 0
  for raw in rawNames do
    let input := runtimeCopy raw
    let expected := input.toLower
    let header := Header.of input "benchmark"
    unless header.name == expected && header.value == "benchmark" do
      throw (IO.userError <|
        s!"{label}: Header.of/String.toLower disagreement for {repr raw}: " ++
          s!"expected={repr expected}, actual={repr header.name}")
    if ptrEq input header.name then
      reused := reused + 1
    names := names.push input
    expectedDigestPerSweep := expectedDigestPerSweep + nameDigest expected
  IO.println <| s!"case={label} preflight_reused_names={reused}/{names.size}"
  pure { label, names, expectedDigestPerSweep }

@[noinline] private def normalizeRepeated (fixture : @& Fixture)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    for name in fixture.names do
      let header := Header.of name "benchmark"
      checksum := checksum + nameDigest header.name
  pure checksum

private def expectedChecksum (fixture : @& Fixture) (iterations : Nat) : Nat :=
  fixture.expectedDigestPerSweep * iterations

private def measureFixture (fixture : @& Fixture) (iterations : Nat) : IO (Nat × Nat) := do
  let warmupIterations := Nat.min iterations 1000
  let warmup ← normalizeRepeated fixture warmupIterations
  unless warmup == expectedChecksum fixture warmupIterations do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let started ← IO.monoNanosNow
  let checksum ← normalizeRepeated fixture iterations
  let elapsed := (← IO.monoNanosNow) - started
  unless checksum == expectedChecksum fixture iterations do
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

private def report (fixture : @& Fixture) (iterations : Nat)
    (samples : Array Nat) (checksum : Nat) : IO Unit := do
  let operations := iterations * fixture.names.size
  let perName := median samples * 100 / operations
  IO.println <| s!"case={fixture.label} names_per_sweep={fixture.names.size} " ++
    s!"iterations={iterations} operations={operations} checksum={checksum}"
  IO.println s!"case={fixture.label} samples_ns={formatSamples samples}"
  IO.println <| s!"case={fixture.label} median_ns_per_name={formatHundredths perName}"

private def repeatCharacter (character : Char) (count : Nat) : String := Id.run do
  let mut value := ""
  for _ in [0:count] do
    value := value.push character
  pure value

unsafe def main (args : List String) : IO Unit := do
  let iterations ← parsePositive "iterations" args[0]? 500000
  let rounds ← parsePositive "rounds" args[1]? 7
  unless rounds >= 3 && rounds % 2 == 1 do
    throw (IO.userError "rounds must be an odd integer of at least 3")
  let selection := args[2]?.getD "all"
  unless #["all", "lowercase_typical", "lowercase_lengths", "uppercase_controls",
      "unicode_controls"].contains selection do
    throw (IO.userError s!"unknown benchmark selection: {selection}")
  unless args.length <= 3 do
    throw (IO.userError <|
      "usage: header_normalize_name_benchmark [iterations] [rounds] " ++
        "[all|lowercase_typical|lowercase_lengths|uppercase_controls|unicode_controls]")

  let lowercaseTypical ← makeFixture "lowercase_typical" #[
    "content-type", "te", "grpc-timeout", "authorization", "user-agent",
    "x-request-id", "x-tenant", "grpc-accept-encoding"
  ]
  let lowercaseLengths ← makeFixture "lowercase_lengths" #[
    "a", "x-id", "grpc-timeout", "x-custom-metadata-name-012345",
    repeatCharacter 'a' 64, repeatCharacter 'z' 128
  ]
  let uppercaseControls ← makeFixture "uppercase_controls" #[
    "Content-Type", "CONTENT-TYPE", "content-TypE", "A", "grpc-timeouT",
    (repeatCharacter 'a' 63).push 'Z'
  ]
  let unicodeControls ← makeFixture "unicode_controls" #[
    "é", "É", "Straße", "STRAẞE", "ΜΕΤΑ", "μετα", "Σίσυφος", "İ",
    "Key", "１-name", "😀-meta", "e\u0301"
  ]
  let fixtures := #[lowercaseTypical, lowercaseLengths, uppercaseControls, unicodeControls]

  IO.println <| "benchmark=header_normalize_name_v1 path=Header.of " ++
    s!"selection={selection} validation=pass"
  for fixture in fixtures do
    if selection == "all" || selection == fixture.label then
      let mut samples := #[]
      let mut checksum := 0
      for _ in [0:rounds] do
        let measured ← measureFixture fixture iterations
        samples := samples.push measured.1
        checksum := measured.2
      report fixture iterations samples checksum
  IO.println "header-name normalization benchmark completed"
