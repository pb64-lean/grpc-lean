import Grpc

open Grpc

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def referenceHeaderName (name : String) : Bool :=
  !name.isEmpty && name.all fun character =>
    character.isLower || character.isDigit ||
      character == '-' || character == '_' || character == '.'

private def referenceVisibleString (value : String) : Bool :=
  value.all fun character =>
    let code := character.toNat
    0x20 <= code && code <= 0x7e

private def expectPredicatesAgree (raw : String) : IO Unit := do
  let expectedName := referenceHeaderName raw
  let byteName := Ascii.validHeaderNameByteIndexed raw
  let publicName := Ascii.validHeaderName raw
  unless byteName == expectedName do
    throw (IO.userError <|
      s!"byte-indexed header-name predicate disagreed for {repr raw}: " ++
        s!"reference={expectedName}, byte_indexed={byteName}")
  unless publicName == expectedName do
    throw (IO.userError <|
      s!"public header-name predicate disagreed for {repr raw}: " ++
        s!"reference={expectedName}, public={publicName}")

  let expectedVisible := referenceVisibleString raw
  let byteVisible := Ascii.isVisibleStringByteIndexed raw
  let publicVisible := Ascii.isVisibleString raw
  unless byteVisible == expectedVisible do
    throw (IO.userError <|
      s!"byte-indexed visible-string predicate disagreed for {repr raw}: " ++
        s!"reference={expectedVisible}, byte_indexed={byteVisible}")
  unless publicVisible == expectedVisible do
    throw (IO.userError <|
      s!"public visible-string predicate disagreed for {repr raw}: " ++
        s!"reference={expectedVisible}, public={publicVisible}")

private def expectHeaderName (raw : String) (expected : Bool) : IO Unit := do
  expectPredicatesAgree raw
  expect (Ascii.validHeaderNameByteIndexed raw == expected)
    s!"unexpected header-name result for {repr raw}"

private def expectVisibleString (raw : String) (expected : Bool) : IO Unit := do
  expectPredicatesAgree raw
  expect (Ascii.isVisibleStringByteIndexed raw == expected)
    s!"unexpected visible-string result for {repr raw}"

private def withCharacter (before : String) (character : Char)
    (after : String := "") : String :=
  (before.push character).append after

private def testDirectedBoundaries : IO Unit := do
  for (raw, expected) in #[("", false), ("a", true), ("z", true), ("0", true),
      ("9", true), ("-", true), ("_", true), (".", true),
      ("content-type", true), ("grpc_timeout.2", true), ("A", false),
      ("bad name", false), ("bad~name", false), ("é", false), ("λ", false),
      ("１", false)] do
    expectHeaderName raw expected

  for raw in #[
      withCharacter "" (Char.ofNat 0x1f) "name",
      withCharacter "na" (Char.ofNat 0x1f) "me",
      withCharacter "name" (Char.ofNat 0x1f),
      withCharacter "" (Char.ofNat 0x20) "name",
      withCharacter "name" (Char.ofNat 0x7e),
      withCharacter "name" (Char.ofNat 0x7f),
      withCharacter "na" 'é' "me",
      withCharacter "name" (Char.ofNat 0)
    ] do
    expectHeaderName raw false

  for (raw, expected) in #[("", true), (" ", true), ("~", true),
      ("visible ASCII 09 !@#$%^&*()", true)] do
    expectVisibleString raw expected

  for raw in #[
      withCharacter "" (Char.ofNat 0x1f) "visible",
      withCharacter "visi" (Char.ofNat 0x1f) "ble",
      withCharacter "visible" (Char.ofNat 0x1f),
      withCharacter "" (Char.ofNat 0x7f) "visible",
      withCharacter "visi" (Char.ofNat 0x7f) "ble",
      withCharacter "visible" (Char.ofNat 0x7f),
      withCharacter "" 'é' "visible",
      withCharacter "visi" 'é' "ble",
      withCharacter "visible" 'é',
      withCharacter "visible" '\n',
      withCharacter "visible" (Char.ofNat 0)
    ] do
    expectVisibleString raw false

private def sameValidation (left right : Except Status Unit) : Bool :=
  match left, right with
  | .ok (), .ok () => true
  | .error left, .error right => left.code == right.code && left.message == right.message
  | _, _ => false

private def referenceValidateOrdinary (header : Header) : Except Status Unit := do
  if !referenceHeaderName header.name then
    throw (Status.invalidArgument s!"invalid gRPC metadata name {header.name}")
  if referenceVisibleString header.value then
    pure ()
  else
    throw (Status.invalidArgument s!"invalid ASCII gRPC metadata value for {header.name}")

private def testValidationRouting : IO Unit := do
  let cases : Array Header := #[
    { name := "x-meta", value := "" },
    { name := "x-meta", value := " " },
    { name := "x-meta", value := "~" },
    { name := "x-meta", value := withCharacter "good" (Char.ofNat 0x1f) "value" },
    { name := "x-meta", value := withCharacter "good" (Char.ofNat 0x7f) "value" },
    { name := "x-meta", value := "unicodé" },
    { name := "Bad", value := withCharacter "" (Char.ofNat 0x1f) }
  ]
  for current in cases do
    let expected := referenceValidateOrdinary current
    let actual := Metadata.validateHeader current
    expect (sameValidation actual expected)
      s!"validateHeader changed result or rejection precedence for {repr current}"

private def testAllSingleByteValues : IO Unit := do
  for code in [0:256] do
    expectPredicatesAgree (String.singleton (Char.ofNat code))

private def extendLevel (level : Array String) (alphabet : Array Char) : Array String :=
  Id.run do
    let mut next := #[]
    for base in level do
      for symbol in alphabet do
        next := next.push (base.push symbol)
    pure next

private def testCompactAlphabetExhaustive : IO Unit := do
  let alphabet := #[
    'a', 'z', '0', '9', '-', '_', '.', 'A', Char.ofNat 0x1f, ' ', '~',
    Char.ofNat 0x7f, Char.ofNat 0, 'é'
  ]
  let mut level := #[""]
  let mut checked := 0
  for length in [0:5] do
    for raw in level do
      expectPredicatesAgree raw
    checked := checked + level.size
    if length < 4 then
      level := extendLevel level alphabet
  expect (checked == 41371)
    s!"compact metadata ASCII differential checked {checked} inputs instead of 41371"

private def advanceRandom (state : Nat) : Nat :=
  (state * 1664525 + 1013904223) % 4294967296

private def randomString (initial : Nat) (alphabet : Array Char) : Nat × String :=
  Id.run do
    let mut state := advanceRandom initial
    let length := state % 33
    let mut raw := ""
    for _ in [0:length] do
      state := advanceRandom state
      raw := raw.push alphabet[state % alphabet.size]!
    pure (state, raw)

private def testDeterministicRandomDifferential : IO Unit := do
  let alphabet := #[
    'a', 'm', 'z', '0', '5', '9', '-', '_', '.', 'A', 'Z', ' ', '~',
    Char.ofNat 0x1f, Char.ofNat 0x7f, Char.ofNat 0, '\n', 'é', 'λ', '１'
  ]
  let mut state := 0x5eed4a11
  for _ in [0:20000] do
    let generated := randomString state alphabet
    state := generated.1
    expectPredicatesAgree generated.2

def main : IO Unit := do
  testDirectedBoundaries
  IO.println "metadata ASCII directed boundaries agree"
  testValidationRouting
  IO.println "metadata validation routing and precedence agree"
  testAllSingleByteValues
  IO.println "metadata ASCII single-code-point differential agrees for 0..255"
  testCompactAlphabetExhaustive
  IO.println "metadata ASCII compact differential agrees on 41,371 inputs"
  testDeterministicRandomDifferential
  IO.println "metadata ASCII deterministic differential agrees on 20,000 inputs"
