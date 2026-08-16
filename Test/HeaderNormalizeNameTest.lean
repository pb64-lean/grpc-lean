import Grpc

open Grpc

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

@[noinline] private def runtimeCopy (value : String) : String :=
  String.ofList value.toList

private def expectNormalization (raw : String) : IO Unit := do
  let input := runtimeCopy raw
  let expected := input.toLower
  let actual := Header.normalizeName input
  expect (actual == expected) <|
    s!"normalizeName disagreed with String.toLower for {repr raw}: " ++
      s!"expected={repr expected}, actual={repr actual}"
  let header := Header.of input "value"
  expect (header.name == expected && header.value == "value") <|
    s!"Header.of changed normalization or value for {repr raw}: {repr header}"

private def testDirectedCases : IO Unit := do
  for raw in #[
      "", "a", "content-type", ":method", "grpc-timeout", "x_request.id",
      "Content-Type", "CONTENT-TYPE", "content-TypE", "A", "Z",
      "bad name", "bad\tname", "bad\nname", "bad~name",
      "é", "É", "Straße", "STRAẞE", "ΜΕΤΑ", "μετα", "Σίσυφος",
      "İ", "ı", "Key", "１-name", "😀-meta", "e\u0301"
    ] do
    expectNormalization raw

private def testAllSingleCodePoints : IO Unit := do
  for code in [0:256] do
    expectNormalization (String.singleton (Char.ofNat code))

private def extendLevel (level : Array String) (alphabet : Array Char) : Array String :=
  Id.run do
    let mut next := #[]
    for base in level do
      for symbol in alphabet do
        next := next.push (base.push symbol)
    pure next

private def testCompactAlphabetExhaustive : IO Unit := do
  let alphabet := #[
    'a', 'z', '0', '-', '_', '.', ':', 'A', 'Z', ' ', '~', 'é', 'É', 'Σ'
  ]
  let mut level := #[""]
  let mut checked := 0
  for length in [0:5] do
    for raw in level do
      expectNormalization raw
    checked := checked + level.size
    if length < 4 then
      level := extendLevel level alphabet
  expect (checked == 41371)
    s!"header normalization differential checked {checked} inputs instead of 41,371"

private def advanceRandom (state : Nat) : Nat :=
  (state * 1664525 + 1013904223) % 4294967296

private def randomString (initial : Nat) (alphabet : Array Char) : Nat × String :=
  Id.run do
    let mut state := advanceRandom initial
    let length := state % 49
    let mut raw := ""
    for _ in [0:length] do
      state := advanceRandom state
      raw := raw.push alphabet[state % alphabet.size]!
    pure (state, raw)

private def testDeterministicRandomDifferential : IO Unit := do
  let alphabet := #[
    'a', 'm', 'z', '0', '5', '9', '-', '_', '.', ':', 'A', 'M', 'Z',
    ' ', '~', Char.ofNat 0, '\t', '\n', 'é', 'É', 'ß', 'ẞ', 'Σ', 'ς', 'İ',
    '１', '😀', Char.ofNat 0x0301
  ]
  let mut state := 0x14eadead
  for _ in [0:20000] do
    let generated := randomString state alphabet
    state := generated.1
    expectNormalization generated.2

private unsafe def testLowercaseIdentityObservation : IO Unit := do
  let cases := #[
    runtimeCopy "content-type",
    runtimeCopy "te",
    runtimeCopy "grpc-timeout",
    runtimeCopy "authorization",
    runtimeCopy "user-agent",
    runtimeCopy "x-request-id",
    runtimeCopy "grpc-accept-encoding"
  ]
  let mut reused := 0
  for raw in cases do
    let normalized := Header.normalizeName raw
    expect (normalized == raw) s!"lowercase identity value changed for {repr raw}"
    if ptrEq raw normalized then
      reused := reused + 1
  expect (reused == cases.size) <|
    s!"normalized lowercase names reused {reused}/{cases.size} input objects"
  IO.println <| s!"header normalization lowercase identity observation: " ++
    s!"reused={reused}/{cases.size}"

unsafe def main : IO Unit := do
  testDirectedCases
  IO.println "header normalization directed differential agrees"
  testAllSingleCodePoints
  IO.println "header normalization single-code-point differential agrees for 0..255"
  testCompactAlphabetExhaustive
  IO.println "header normalization compact differential agrees on 41,371 inputs"
  testDeterministicRandomDifferential
  IO.println "header normalization deterministic differential agrees on 20,000 inputs"
  testLowercaseIdentityObservation
