import Grpc

open Grpc

/-!
# HPACK name-lookup normalization benchmark

Compares the legacy lookup, which normalizes the query at every table probe,
with the production lookup that normalizes once before the static and dynamic
scans. Fixture construction, exact comparison, and the selected mode's warmup
stay outside the repeated measurement loop but remain in whole-process
counters. Run one mode and fixture per process under deterministic counters.
-/

private def findNameInLegacy (entries : Array Header) (name : String)
    (i start : Nat) : Option Nat :=
  if i >= entries.size then
    none
  else
    let entry := entries[i]!
    if entry.name == Header.normalizeName name then
      some (start + i)
    else
      findNameInLegacy entries name (i + 1) start
  termination_by entries.size - i
  decreasing_by omega

private def findNameLegacy (state : Http2.Hpack.State) (name : String) : Option Nat :=
  match findNameInLegacy Http2.Hpack.staticEntries name 0 1 with
  | some index => some index
  | none =>
      findNameInLegacy state.dynamic name 0 (Http2.Hpack.staticEntries.size + 1)

private def findNameInHoisted (entries : Array Header) (key : String)
    (i start : Nat) : Option Nat :=
  if i >= entries.size then
    none
  else
    let entry := entries[i]!
    if entry.name == key then
      some (start + i)
    else
      findNameInHoisted entries key (i + 1) start
  termination_by entries.size - i
  decreasing_by omega

private def findNameHoisted (state : Http2.Hpack.State) (name : String) : Option Nat :=
  let key := Header.normalizeName name
  match findNameInHoisted Http2.Hpack.staticEntries key 0 1 with
  | some index => some index
  | none =>
      findNameInHoisted state.dynamic key 0 (Http2.Hpack.staticEntries.size + 1)

private structure Fixture where
  state : Http2.Hpack.State
  query : String

private def dynamicState : Http2.Hpack.State :=
  Http2.Hpack.insert
    (Http2.Hpack.insert ({} : Http2.Hpack.State)
      (Header.of "x-dynamic-last" "last"))
    (Header.of "x-dynamic-first" "first")

private def fixture? : String → Option Fixture
  | "early_static" => some ⟨{}, ":authority"⟩
  | "middle_static" => some ⟨{}, "content-type"⟩
  | "late_static" => some ⟨{}, "www-authenticate"⟩
  | "missing_lower" => some ⟨{}, "x-acme-custom"⟩
  | "missing_upper" => some ⟨{}, "X-ACME-CUSTOM"⟩
  | "missing_unicode" => some ⟨{}, "É-META"⟩
  | "dynamic_first" => some ⟨dynamicState, "x-dynamic-first"⟩
  | "dynamic_last_upper" => some ⟨dynamicState, "X-DYNAMIC-LAST"⟩
  | _ => none

@[inline] private def resultDigest : Option Nat → Nat
  | none => 1
  | some index => index * 257 + 17

@[noinline] private def runLegacy (state : @& Http2.Hpack.State)
    (query : @& String) (iterations : Nat) : Nat := Id.run do
  let mut checksum := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (findNameLegacy state query)
  return checksum

@[noinline] private def runProduction (state : @& Http2.Hpack.State)
    (query : @& String) (iterations : Nat) : Nat := Id.run do
  let mut checksum := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (Http2.Hpack.findName? state query)
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
        "usage: hpack_name_lookup_benchmark (legacy|production) " ++
          "(early_static|middle_static|late_static|missing_lower|missing_upper|" ++
          "missing_unicode|dynamic_first|dynamic_last_upper) iterations")
  let some fixture := fixture? fixtureName
    | throw (IO.userError s!"unknown fixture: {fixtureName}")
  let expectedResult := findNameLegacy fixture.state fixture.query
  unless findNameHoisted fixture.state fixture.query == expectedResult &&
      Http2.Hpack.findName? fixture.state fixture.query == expectedResult do
    throw (IO.userError s!"{fixtureName}: production/legacy result mismatch")
  let expected := resultDigest expectedResult * iterations
  let warmupIterations := Nat.min iterations 1000
  let warmupExpected := resultDigest expectedResult * warmupIterations
  let warmupChecksum ← match mode with
    | "legacy" => pure (runLegacy fixture.state fixture.query warmupIterations)
    | "production" => pure (runProduction fixture.state fixture.query warmupIterations)
    | _ => throw (IO.userError "mode must be legacy or production")
  unless warmupChecksum == warmupExpected do
    throw (IO.userError s!"{fixtureName}: warmup checksum mismatch")
  let checksum ← match mode with
    | "legacy" => pure (runLegacy fixture.state fixture.query iterations)
    | "production" => pure (runProduction fixture.state fixture.query iterations)
    | _ => throw (IO.userError "mode must be legacy or production")
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != expected {expected}")
  IO.println <| s!"benchmark=hpack_name_lookup mode={mode} fixture={fixtureName} " ++
    s!"static_entries={Http2.Hpack.staticEntries.size} " ++
    s!"dynamic_entries={fixture.state.dynamic.size} iterations={iterations} " ++
    s!"checksum={checksum}"
