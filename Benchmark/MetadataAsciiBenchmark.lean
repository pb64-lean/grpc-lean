import Grpc

open Grpc

/-!
# Metadata ASCII-validation benchmark

Measures the production `Metadata.validateHeader` path for ordinary non-binary
metadata.  The benchmark-local reference retains the pre-change `String.all`
predicates; fixture construction, exact result comparison, warmup, and final
validation stay outside the reported samples.  A constant-size result digest
remains inside every measured validation.

The valid fixtures separate header-name scans from representative value
lengths while `typical` models one request-sized metadata set.  Invalid inputs
are correctness controls for early, middle, and late failures, not a
common-path performance claim.
-/

private structure Fixture where
  label : String
  headers : Array Header
  expectedDigestPerSweep : Nat

private def referenceHeaderName (name : String) : Bool :=
  !name.isEmpty && name.all fun character =>
    character.isLower || character.isDigit ||
      character == '-' || character == '_' || character == '.'

private def referenceVisibleValue (value : String) : Bool :=
  value.all fun character =>
    0x20 <= character.toNat && character.toNat <= 0x7e

private def referenceValidateHeader (header : Header) : Except Status Unit := do
  if !referenceHeaderName header.name then
    throw (Status.invalidArgument s!"invalid gRPC metadata name {header.name}")
  if referenceVisibleValue header.value then
    pure ()
  else
    throw (Status.invalidArgument s!"invalid ASCII gRPC metadata value for {header.name}")

private def sameResult (left right : Except Status Unit) : Bool :=
  match left, right with
  | .ok (), .ok () => true
  | .error left, .error right => left.code == right.code && left.message == right.message
  | _, _ => false

@[inline] private def resultDigest : Except Status Unit → Nat
  | .ok () => 1
  | .error status => 17 + status.messageD.utf8ByteSize

private def header (name value : String) : Header := { name, value }

private def visibleValue (size seed : Nat) : String := Id.run do
  let mut value := ""
  for index in [0:size] do
    value := value.push (Char.ofNat (0x20 + (index * 37 + seed) % 0x5f))
  return value

private def withCharacter (before : String) (character : Char)
    (after : String := "") : String :=
  (before.push character).append after

private def makeFixture (label : String) (headers : Array Header) : IO Fixture := do
  unless !headers.isEmpty do
    throw (IO.userError s!"{label}: fixture is empty")
  let mut expectedDigestPerSweep := 0
  for current in headers do
    if current.name.startsWith ":" || current.name.endsWith "-bin" ||
        (#["connection", "keep-alive", "proxy-connection", "transfer-encoding", "upgrade"]
          |>.contains current.name) then
      throw (IO.userError s!"{label}: fixture escaped the ordinary metadata path")
    let expected := referenceValidateHeader current
    let actual := Metadata.validateHeader current
    unless sameResult actual expected do
      throw (IO.userError <|
        s!"{label}: production/reference disagreement for " ++
          s!"name={repr current.name} value={repr current.value}")
    expectedDigestPerSweep := expectedDigestPerSweep + resultDigest expected
  pure { label, headers, expectedDigestPerSweep }

@[noinline] private def validateRepeated (fixture : @& Fixture)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    for current in fixture.headers do
      checksum := checksum + resultDigest (Metadata.validateHeader current)
  pure checksum

private def expectedChecksum (fixture : @& Fixture) (iterations : Nat) : Nat :=
  fixture.expectedDigestPerSweep * iterations

private def measureFixture (fixture : @& Fixture) (iterations : Nat) : IO (Nat × Nat) := do
  let warmupIterations := Nat.min iterations 1000
  let warmup ← validateRepeated fixture warmupIterations
  unless warmup == expectedChecksum fixture warmupIterations do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let started ← IO.monoNanosNow
  let checksum ← validateRepeated fixture iterations
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
  let operations := iterations * fixture.headers.size
  let perValidation := median samples * 100 / operations
  IO.println <| s!"case={fixture.label} headers_per_sweep={fixture.headers.size} " ++
    s!"iterations={iterations} operations={operations} checksum={checksum}"
  IO.println s!"case={fixture.label} samples_ns={formatSamples samples}"
  IO.println <|
    s!"case={fixture.label} median_ns_per_validation={formatHundredths perValidation}"

def main (args : List String) : IO Unit := do
  let iterations ← parsePositive "iterations" args[0]? 200000
  let rounds ← parsePositive "rounds" args[1]? 7
  unless rounds >= 3 && rounds % 2 == 1 do
    throw (IO.userError "rounds must be an odd integer of at least 3")
  let selection := args[2]?.getD "all"
  unless #["all", "typical", "names", "values_8", "values_32", "values_128",
      "invalid_controls"].contains selection do
    throw (IO.userError s!"unknown benchmark selection: {selection}")
  unless args.length <= 3 do
    throw (IO.userError <|
      "usage: metadata_ascii_benchmark [iterations] [rounds] " ++
        "[all|typical|names|values_8|values_32|values_128|invalid_controls]")

  let typical ← makeFixture "typical" #[
    header "content-type" "application/grpc",
    header "te" "trailers",
    header "grpc-timeout" "250m",
    header "authorization" "BenchmarkScheme local-token",
    header "user-agent" "grpc-python/1.67.0",
    header "x-request-id" "0123456789abcdef",
    header "x-tenant" "acme",
    header "grpc-accept-encoding" "identity,gzip"
  ]
  let names ← makeFixture "names" #[
    header "a" "",
    header "te" "",
    header "x-id" "",
    header "content-type" "",
    header "grpc-timeout" "",
    header "grpc-accept-encoding" "",
    header "x-long-custom-metadata-name-012345" ""
  ]
  let values8 ← makeFixture "values_8" #[
    header "x-a" (visibleValue 8 1),
    header "x-b" (visibleValue 8 7),
    header "x-c" (visibleValue 8 19),
    header "x-d" (visibleValue 8 31)
  ]
  let values32 ← makeFixture "values_32" #[
    header "x-a" (visibleValue 32 1),
    header "x-b" (visibleValue 32 7),
    header "x-c" (visibleValue 32 19),
    header "x-d" (visibleValue 32 31)
  ]
  let values128 ← makeFixture "values_128" #[
    header "x-a" (visibleValue 128 1),
    header "x-b" (visibleValue 128 7),
    header "x-c" (visibleValue 128 19),
    header "x-d" (visibleValue 128 31)
  ]
  let invalidControls ← makeFixture "invalid_controls" #[
    header "Bad" "visible",
    header (withCharacter "bad" (Char.ofNat 0x1f)) "visible",
    header "x-value" (withCharacter "" (Char.ofNat 0x1f) "visible"),
    header "x-value" (withCharacter "visi" (Char.ofNat 0x1f) "ble"),
    header "x-value" (withCharacter "visible" (Char.ofNat 0x1f)),
    header "x-value" (withCharacter "visible" (Char.ofNat 0x7f)),
    header "x-value" "visiblé"
  ]
  let fixtures := #[typical, names, values8, values32, values128, invalidControls]

  IO.println <| "benchmark=metadata_ascii_validation_v1 " ++
    s!"path=Metadata.validateHeader selection={selection} validation=pass"
  for fixture in fixtures do
    if selection == "all" || selection == fixture.label then
      let mut samples := #[]
      let mut checksum := 0
      for _ in [0:rounds] do
        let measured ← measureFixture fixture iterations
        samples := samples.push measured.1
        checksum := measured.2
      report fixture iterations samples checksum
  IO.println "metadata ASCII-validation benchmark completed"
