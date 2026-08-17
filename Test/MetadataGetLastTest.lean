import Grpc

open Grpc

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def referenceGetLast? (metadata : Metadata) (name : String) : Option String :=
  (metadata.getAll name).back?

private def expectSame (label : String) (metadata : Metadata) (name : String) : IO Unit := do
  let expected := referenceGetLast? metadata name
  let actual := metadata.getLast? name
  expect (actual == expected) <|
    s!"{label}: getLast? disagreed for {repr name}: " ++
      s!"expected={repr expected}, actual={repr actual}"

private def directedCases : Array (String × Metadata × Array String) := #[
  ("empty", #[], #["authorization", "Authorization", "x-meta"]),
  ("no match", #[Header.of "x-meta" "one", Header.of "te" "trailers"],
    #["authorization", "x-missing"]),
  ("one match", #[Header.of "authorization" "first"],
    #["authorization", "Authorization", "AUTHORIZATION"]),
  ("last duplicate", #[
      Header.of "authorization" "first",
      Header.of "x-meta" "middle",
      Header.of "authorization" "last"],
    #["authorization", "Authorization"]),
  ("trailing nonmatch", #[
      Header.of "authorization" "first",
      Header.of "authorization" "last",
      Header.of "x-meta" "trailing"],
    #["authorization", "x-meta"]),
  ("unicode query", #[
      Header.of "É" "normalized-unicode",
      { name := "É", value := "raw-uppercase" }],
    #["É", "é"]),
  ("raw stored names", #[
      { name := "Authorization", value := "raw" },
      { name := "authorization", value := "normalized" }],
    #["authorization", "Authorization"])
]

private def testDirected : IO Unit := do
  for (label, metadata, names) in directedCases do
    for name in names do
      expectSame label metadata name

private def extendPatterns (patterns : Array (Array Nat)) : Array (Array Nat) := Id.run do
  let mut next := #[]
  for pattern in patterns do
    for choice in [0:3] do
      next := next.push (pattern.push choice)
  return next

private def metadataForPattern (pattern : Array Nat) : Metadata := Id.run do
  let mut metadata := #[]
  for index in [0:pattern.size] do
    let header := match pattern[index]! with
      | 0 => Header.of "authorization" s!"auth-{index}"
      | 1 => Header.of "x-meta" s!"meta-{index}"
      | _ => Header.of "te" s!"te-{index}"
    metadata := metadata.push header
  return metadata

private def testExhaustivePatterns : IO Unit := do
  let mut patterns := #[#[]]
  let mut checked := 0
  for length in [0:7] do
    for pattern in patterns do
      let metadata := metadataForPattern pattern
      expectSame s!"exhaustive-{length}-{checked}" metadata "authorization"
      expectSame s!"exhaustive-case-{length}-{checked}" metadata "AUTHORIZATION"
      expectSame s!"exhaustive-missing-{length}-{checked}" metadata "x-missing"
    checked := checked + patterns.size
    if length < 6 then
      patterns := extendPatterns patterns
  expect (checked == 1093)
    s!"getLast? checked {checked} patterns instead of 1,093"

def main : IO Unit := do
  testDirected
  testExhaustivePatterns
  IO.println "Metadata.getLast? matches getAll/back? on directed and 1,093 exhaustive patterns"
