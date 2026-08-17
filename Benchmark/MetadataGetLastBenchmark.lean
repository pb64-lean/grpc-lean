import Grpc

open Grpc

/-!
# Last metadata lookup benchmark

Compares the former `getAll`/`back?` composition with `Metadata.getLast?`.
The primary cases put authorization last, matching ordinary Acme requests;
first-match and missing cases force the reverse search to scan the complete
array and guard against repeating the earlier isolated-getter regression.
Fixture construction, exact result comparison, and warmup remain outside the
externally counted region.
-/

private def referenceGetLast? (metadata : Metadata) (name : String) : Option String :=
  (metadata.getAll name).back?

@[inline] private def resultDigest : Option String → Nat
  | none => 1
  | some value =>
      if h : value.utf8ByteSize > 0 then
        let first := value.getUTF8Byte ⟨0⟩ (by
          simpa only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using h)
        value.utf8ByteSize * 257 + first.toNat * 17
      else
        3

private def fillerMetadata (count : Nat) : Metadata := Id.run do
  let mut metadata := #[]
  for index in [0:count] do
    metadata := metadata.push (Header.of s!"x-benchmark-{index}" s!"value-{index}")
  return metadata

private def lastFixture (size : Nat) : Metadata :=
  (fillerMetadata (size - 1)).push (Header.of "authorization" "Bearer acme-editor-8")

private def firstFixture (size : Nat) : Metadata :=
  (fillerMetadata (size - 1)).foldl (fun metadata header => metadata.push header)
    #[Header.of "authorization" "Bearer acme-editor-8"]

private def fixture (name : String) : Option Metadata :=
  match name with
  | "last_1" => some (lastFixture 1)
  | "last_4" => some (lastFixture 4)
  | "last_16" => some (lastFixture 16)
  | "first_16" => some (firstFixture 16)
  | "missing_16" => some (fillerMetadata 16)
  | "duplicate_last_malformed_16" =>
      some <| ((#[Header.of "authorization" "Bearer acme-editor-8"] : Metadata).append
        (fillerMetadata 14)).push (Header.of "authorization" "Basic malformed")
  | _ => none

@[noinline] private def runReference (metadata : @& Metadata)
    (iterations : Nat) : Nat := Id.run do
  let mut checksum := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (referenceGetLast? metadata "authorization")
  return checksum

@[noinline] private def runDirect (metadata : @& Metadata)
    (iterations : Nat) : Nat := Id.run do
  let mut checksum := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest (metadata.getLast? "authorization")
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
        "usage: metadata_get_last_benchmark (reference|direct) " ++
          "(last_1|last_4|last_16|first_16|missing_16|duplicate_last_malformed_16) " ++
          "iterations")
  let some metadata := fixture fixtureName
    | throw (IO.userError s!"unknown fixture: {fixtureName}")
  let expectedValue := referenceGetLast? metadata "authorization"
  unless metadata.getLast? "authorization" == expectedValue do
    throw (IO.userError s!"{fixtureName}: direct/reference result mismatch")
  let expected := resultDigest expectedValue * iterations
  let warmupIterations := Nat.min iterations 1000
  let warmupExpected := resultDigest expectedValue * warmupIterations
  unless runReference metadata warmupIterations == warmupExpected &&
      runDirect metadata warmupIterations == warmupExpected do
    throw (IO.userError s!"{fixtureName}: warmup checksum mismatch")
  let checksum ← match mode with
    | "reference" => pure (runReference metadata iterations)
    | "direct" => pure (runDirect metadata iterations)
    | _ => throw (IO.userError "mode must be reference or direct")
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != expected {expected}")
  IO.println <| s!"benchmark=metadata_get_last mode={mode} fixture={fixtureName} " ++
    s!"metadata_headers={metadata.size} iterations={iterations} checksum={checksum}"
