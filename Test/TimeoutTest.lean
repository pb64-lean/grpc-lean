import Grpc

open Grpc

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def expectParsersAgree (raw : String) : IO Unit := do
  let reference := Timeout.parseReference? raw
  let byteIndexed := Timeout.parseByteIndexed? raw
  let publicResult := Timeout.parse? raw
  unless reference == byteIndexed do
    let message := s!"timeout parsers disagreed for {repr raw}: " ++
      s!"reference={repr reference}, byte_indexed={repr byteIndexed}"
    throw (IO.userError message)
  unless publicResult == byteIndexed do
    let message := s!"public timeout parser differed for {repr raw}: " ++
      s!"public={repr publicResult}, byte_indexed={repr byteIndexed}"
    throw (IO.userError message)

private def expectParsed (raw : String) (expected : Timeout) : IO Unit := do
  expectParsersAgree raw
  expect (Timeout.parseByteIndexed? raw == some expected)
    (s!"timeout parser returned {repr (Timeout.parseByteIndexed? raw)} " ++
      s!"for {repr raw}, expected {repr expected}")

private def expectRejected (raw : String) : IO Unit := do
  expectParsersAgree raw
  expect (Timeout.parseByteIndexed? raw).isNone
    s!"timeout parser accepted invalid input {repr raw}"

private def testDirectedCases : IO Unit := do
  for (raw, expected) in #[
      ("1H", { value := 1, unit := TimeoutUnit.hour }),
      ("2M", { value := 2, unit := TimeoutUnit.minute }),
      ("3S", { value := 3, unit := TimeoutUnit.second }),
      ("4m", { value := 4, unit := TimeoutUnit.millisecond }),
      ("5u", { value := 5, unit := TimeoutUnit.microsecond }),
      ("6n", { value := 6, unit := TimeoutUnit.nanosecond }),
      ("00000001S", { value := 1, unit := TimeoutUnit.second }),
      ("00000100m", { value := 100, unit := TimeoutUnit.millisecond }),
      ("99999999H", { value := 99999999, unit := TimeoutUnit.hour })
    ] do
    expectParsed raw expected

  for raw in #[
      "", "H", "1", "0n", "00000000H", "123456789S", "000000000S",
      "12345678", "1x", "1.5S", "+1S", "-1S", " 1S", "1S ", "1\nS",
      "é", "éH", "1é", "１２S", "٠S", ("1".push (Char.ofNat 0)).push 'S'
    ] do
    expectRejected raw

private def extendLevel (level : Array String) (alphabet : Array Char) : Array String :=
  Id.run do
    let mut next := #[]
    for base in level do
      for symbol in alphabet do
        next := next.push (base.push symbol)
    pure next

private def testCompactAlphabetExhaustive : IO Unit := do
  let alphabet :=
    #['0', '1', '9', 'H', 'S', 'm', 'n', 'x', '+', ' ', Char.ofNat 0, 'é']
  let mut level := #[""]
  let mut checked := 0
  for length in [0:5] do
    for raw in level do
      expectParsersAgree raw
    checked := checked + level.size
    if length < 4 then
      level := extendLevel level alphabet
  expect (checked == 22621)
    s!"compact timeout differential checked {checked} inputs instead of 22621"

private def advanceRandom (state : Nat) : Nat :=
  (state * 1664525 + 1013904223) % 4294967296

private def randomString (initial : Nat) (alphabet : Array Char) : Nat × String :=
  Id.run do
    let mut state := advanceRandom initial
    let length := state % 13
    let mut raw := ""
    for _ in [0:length] do
      state := advanceRandom state
      raw := raw.push alphabet[state % alphabet.size]!
    pure (state, raw)

private def testDeterministicRandomDifferential : IO Unit := do
  let alphabet := #[
    '0', '1', '5', '9', 'H', 'M', 'S', 'm', 'u', 'n', 'x', '+', '-', ' ', '.',
    '/', Char.ofNat 0, '\n', 'é', '٠', '１'
  ]
  let mut state := 0x5eed1234
  for _ in [0:20000] do
    let generated := randomString state alphabet
    state := generated.1
    expectParsersAgree generated.2

def main : IO Unit := do
  testDirectedCases
  IO.println "timeout parser directed cases agree"
  testCompactAlphabetExhaustive
  IO.println "timeout parser compact differential agrees on 22,621 inputs"
  testDeterministicRandomDifferential
  IO.println "timeout parser deterministic differential agrees on 20,000 inputs"
