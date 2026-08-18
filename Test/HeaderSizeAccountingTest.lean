import Grpc

open Grpc

/-!
# Header-size accounting differential and boundaries

The local reference retains the former `String.toUTF8.size` formula.  These
cases compare it with both production consumers and the allocation-free
`utf8ByteSize` expression, then exercise the exact HPACK table and HTTP/2
header-list boundaries whose decisions depend on that size.
-/

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def referenceEntrySize (header : Header) : Nat :=
  header.name.toUTF8.size + header.value.toUTF8.size + 32

private def directEntrySize (header : Header) : Nat :=
  header.name.utf8ByteSize + header.value.utf8ByteSize + 32

private structure SizeCase where
  label : String
  header : Header
  expected : Nat

private def sizeCases : Array SizeCase := #[
  { label := "empty", header := { name := "", value := "" }, expected := 32 },
  { label := "ascii", header := { name := "x", value := "v" }, expected := 34 },
  { label := "unicode", header := { name := "é", value := "😀" }, expected := 38 },
  { label := "embedded-nul", header := { name := "x\u0000", value := "\u0000v" },
    expected := 36 },
  { label := "decomposed-unicode", header := { name := "e\u0301", value := "雪" },
    expected := 38 }
]

private def testExactSizes : IO Unit := do
  for fixture in sizeCases do
    let reference := referenceEntrySize fixture.header
    let direct := directEntrySize fixture.header
    let hpack := Http2.Hpack.entrySize fixture.header
    let headerList := Metadata.headerListEntrySize fixture.header
    expect (reference == fixture.expected) <|
      s!"{fixture.label}: reference size {reference} != {fixture.expected}"
    expect (direct == reference && hpack == reference && headerList == reference) <|
      s!"{fixture.label}: accounting mismatch: reference={reference}, " ++
        s!"direct={direct}, hpack={hpack}, header-list={headerList}"

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

private def referencePrepend (header : Header) (entries : Array Header) : Array Header :=
  entries.foldl (fun result entry => result.push entry) #[header]

private def referenceInsert (state : Http2.Hpack.State) (header : Header) :
    Http2.Hpack.State :=
  if referenceEntrySize header > state.maxSize then
    { state with dynamic := #[] }
  else
    { state with dynamic :=
        referenceEvictTo state.maxSize (referencePrepend header state.dynamic) }

private def sameState (left right : Http2.Hpack.State) : Bool :=
  left.dynamic == right.dynamic &&
    left.maxSize == right.maxSize &&
    left.maxAllowedSize == right.maxAllowedSize &&
    left.pendingSizeUpdate == right.pendingSizeUpdate

private def sameValidation (left right : Except Status Unit) : Bool :=
  match left, right with
  | .ok (), .ok () => true
  | .error leftStatus, .error rightStatus =>
      leftStatus.code == rightStatus.code &&
        leftStatus.message == rightStatus.message
  | _, _ => false

private structure TableCase where
  label : String
  state : Http2.Hpack.State
  header : Header
  expectedDynamic : Array Header

private def tableCases : Array TableCase :=
  let a := Header.of "a" "1"
  let b := Header.of "b" "2"
  let c := Header.of "c" "3"
  let unicode : Header := { name := "é", value := "😀" }
  let empty : Header := { name := "", value := "" }
  #[
    { label := "exact-entry-boundary",
      state := { maxSize := 34 }, header := c, expectedDynamic := #[c] },
    { label := "exact-table-boundary",
      state := { dynamic := #[a, b], maxSize := 102 },
      header := c, expectedDynamic := #[c, a, b] },
    { label := "one-below-table-boundary",
      state := { dynamic := #[a, b], maxSize := 101 },
      header := c, expectedDynamic := #[c, a] },
    { label := "forced-multiple-eviction",
      state := { dynamic := #[a, b], maxSize := 67 },
      header := c, expectedDynamic := #[c] },
    { label := "oversized-clears-existing",
      state := { dynamic := #[a, b], maxSize := 33,
                 maxAllowedSize := 777, pendingSizeUpdate := some 123 },
      header := c, expectedDynamic := #[] },
    { label := "unicode-exact-boundary",
      state := { maxSize := 38 }, header := unicode, expectedDynamic := #[unicode] },
    { label := "empty-exact-boundary",
      state := { maxSize := 32 }, header := empty, expectedDynamic := #[empty] }
  ]

private def testDynamicTableBoundaries : IO Unit := do
  for fixture in tableCases do
    let reference := referenceInsert fixture.state fixture.header
    let actual := Http2.Hpack.insert fixture.state fixture.header
    expect (sameState actual reference) <|
      s!"{fixture.label}: production insert differs from the former accounting path"
    expect (actual.dynamic == fixture.expectedDynamic) <|
      s!"{fixture.label}: expected dynamic={repr fixture.expectedDynamic}, " ++
        s!"actual={repr actual.dynamic}"
    expect (Http2.Hpack.dynamicSize actual.dynamic ==
        referenceDynamicSize actual.dynamic) <|
      s!"{fixture.label}: resulting dynamic-table size differs"
    expect (actual.maxSize == fixture.state.maxSize &&
        actual.maxAllowedSize == fixture.state.maxAllowedSize &&
        actual.pendingSizeUpdate == fixture.state.pendingSizeUpdate) <|
      s!"{fixture.label}: insertion changed non-table state"

private def testHeaderListBoundaries : IO Unit := do
  let metadata : Metadata := sizeCases.map (·.header)
  let expected := sizeCases.foldl (fun total fixture => total + fixture.expected) 0
  expect (Metadata.headerListSize metadata == expected) <|
    s!"header-list total {Metadata.headerListSize metadata} != {expected}"
  expect (Metadata.headerListSize #[] == 0) "empty header-list size was not zero"
  expect (sameValidation (Metadata.validateHeaderListSize none metadata) (.ok ()))
    "an absent header-list limit rejected metadata"
  expect (sameValidation
      (Metadata.validateHeaderListSize (some expected) metadata) (.ok ()))
    "the exact header-list limit rejected metadata"
  expect (sameValidation
      (Metadata.validateHeaderListSize (some (expected + 1)) metadata) (.ok ()))
    "a header-list limit above the exact total rejected metadata"
  let below := expected - 1
  let expectedError : Except Status Unit := .error <|
    Status.resourceExhausted
      s!"HTTP/2 header list exceeds configured size limit {below}"
  expect (sameValidation
      (Metadata.validateHeaderListSize (some below) metadata) expectedError)
    "one byte below the header-list boundary did not return the exact status"

def main : IO Unit := do
  testExactSizes
  testDynamicTableBoundaries
  testHeaderListBoundaries
  IO.println <|
    "header accounting matches the former UTF-8 byte-array formula across " ++
      "Unicode/NUL cases and exact HPACK/header-list boundaries"
