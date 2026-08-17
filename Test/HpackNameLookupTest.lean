import Grpc

open Grpc

/-!
# HPACK name-lookup normalization differential

The production lookup historically normalized the query inside every static
and dynamic table probe.  This local candidate normalizes it once and keeps
the exact static-first, lowest-index, raw-stored-name behavior.
-/

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

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

private def expectSame (label : String) (state : Http2.Hpack.State)
    (name : String) : IO Unit := do
  let expected := findNameLegacy state name
  let production := Http2.Hpack.findName? state name
  let candidate := findNameHoisted state name
  expect (production == expected && candidate == expected) <|
    s!"{label}: hoisted lookup disagreed for {repr name}: " ++
      s!"expected={repr expected}, production={repr production}, " ++
      s!"candidate={repr candidate}"

private def testStaticAndFallbackNames : IO Unit := do
  let state : Http2.Hpack.State := {}
  for header in Http2.Hpack.staticEntries do
    expectSame "static-lowercase" state header.name
  for name in #[
      "", ":authority", ":path", "authorization", "content-type",
      "www-authenticate", "x-acme-custom", "X-ACME-CUSTOM",
      "Authorization", "CONTENT-TYPE", "é-meta", "É-META", "Straße",
      "Σίσυφος", "İ", "e\u0301", "bad name", "x\u0000meta"
    ] do
    expectSame "directed" state name
  for (name, index) in #[
      (":method", 2), (":path", 4), (":scheme", 6), (":status", 8)
    ] do
    expect (Http2.Hpack.findName? state name == some index)
      s!"{name}: first static duplicate was not index {index}"

private def testDynamicOrderingAndRawNames : IO Unit := do
  let dynamicState :=
    Http2.Hpack.insert
      (Http2.Hpack.insert ({} : Http2.Hpack.State)
        (Header.of "x-dynamic-last" "last"))
      (Header.of "x-dynamic-first" "first")
  for name in #[
      "x-dynamic-first", "X-DYNAMIC-FIRST", "x-dynamic-last",
      "X-DYNAMIC-LAST", "x-dynamic-missing", "É-DYNAMIC"
    ] do
    expectSame "dynamic" dynamicState name

  let duplicateState : Http2.Hpack.State := {
    dynamic := #[
      Header.of "content-type" "dynamic-static-duplicate",
      Header.of "x-duplicate" "first",
      Header.of "x-duplicate" "second"
    ]
  }
  expectSame "static-before-dynamic" duplicateState "Content-Type"
  expectSame "first-dynamic-duplicate" duplicateState "X-DUPLICATE"
  expect (Http2.Hpack.findName? duplicateState "content-type" == some 31)
    "static content-type entry did not retain priority"
  expect (Http2.Hpack.findName? duplicateState "x-duplicate" ==
      some (Http2.Hpack.staticEntries.size + 2))
    "first dynamic duplicate did not retain priority"

  let rawStoredState : Http2.Hpack.State := {
    dynamic := #[{ name := "X-RAW-STORED", value := "raw" }]
  }
  expectSame "raw-stored-uppercase" rawStoredState "X-RAW-STORED"
  expect (Http2.Hpack.findName? rawStoredState "X-RAW-STORED" == none)
    "lookup unexpectedly normalized a raw stored dynamic name"

def main : IO Unit := do
  testStaticAndFallbackNames
  testDynamicOrderingAndRawNames
  IO.println <|
    "HPACK hoisted name normalization matches legacy static/dynamic lookup semantics"
