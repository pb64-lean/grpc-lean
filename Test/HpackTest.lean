import Grpc

open Grpc

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectStatusOk (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def bytes (xs : List Nat) : ByteArray :=
  xs.foldl (fun out n => out.push (UInt8.ofNat n)) ByteArray.empty

def byteArrayEq (a b : ByteArray) : Bool :=
  a.data == b.data

def testHuffmanKnownVector : IO Unit := do
  let expected := bytes [0x8c, 0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff]
  let encoded ← expectStatusOk (Http2.Hpack.encodeString "www.example.com")
  expect (byteArrayEq encoded expected)
    "encodeString should produce the RFC 7541 Appendix C.4 Huffman bytes for www.example.com"
  let decoded ← expectStatusOk (Http2.Hpack.decodeString encoded 0)
  expectEq decoded.value "www.example.com" "Huffman-encoded string should decode back"

def testHuffmanRoundTrip : IO Unit := do
  let samples := [
    "www.example.com",
    "no-cache",
    "application/grpc",
    "custom-key custom-value",
    "0123456789 abcdefghijklmnopqrstuvwxyz ABCDEFGHIJKLMNOPQRSTUVWXYZ",
    "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~",
    ""
  ]
  for sample in samples do
    let raw := sample.toUTF8
    let encoded := Http2.Hpack.encodeHuffman raw
    let decoded ← expectStatusOk (Http2.Hpack.decodeHuffman encoded)
    expect (byteArrayEq decoded raw) s!"Huffman round trip should preserve: {sample}"
    -- encodeString/decodeString round trip regardless of which form is chosen
    let string ← expectStatusOk (Http2.Hpack.encodeString sample)
    let stringDecoded ← expectStatusOk (Http2.Hpack.decodeString string 0)
    expectEq stringDecoded.value sample s!"encodeString round trip should preserve: {sample}"

def testHuffmanShorterFormChosen : IO Unit := do
  -- "www.example.com" Huffman form is 12 bytes vs 15 raw, so the H bit must be set
  let encoded ← expectStatusOk (Http2.Hpack.encodeString "www.example.com")
  expect (encoded[0]!.toNat >= 128) "Huffman form should be used when strictly shorter"
  -- A string of rare characters is longer in Huffman form, so raw must be used
  let rare := "\\\\\\\\"
  let rareEncoded ← expectStatusOk (Http2.Hpack.encodeString rare)
  expect (rareEncoded[0]!.toNat < 128) "raw form should be used when Huffman is not shorter"
  expectEq rareEncoded.size (1 + rare.toUTF8.size) "raw form should carry the raw octets"
  let rareDecoded ← expectStatusOk (Http2.Hpack.decodeString rareEncoded 0)
  expectEq rareDecoded.value rare "raw fallback should decode back"

def testDynamicTableRoundTrip : IO Unit := do
  let firstBlockHeaders := #[
    Header.of ":status" "200",
    Header.of "content-type" "application/grpc",
    Header.of "grpc-encoding" "identity",
    Header.of "x-request-id" "abc123"
  ]
  let secondBlockHeaders := #[
    Header.of ":status" "200",
    Header.of "content-type" "application/grpc",
    Header.of "grpc-encoding" "identity",
    Header.of "x-request-id" "abc123"
  ]
  let thirdBlockHeaders := #[
    Header.of "grpc-status" "0",
    Header.of "x-request-id" "abc123"
  ]

  let encoder : Http2.Hpack.State := {}
  let firstBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock encoder firstBlockHeaders)
  let secondBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock firstBlock.2 secondBlockHeaders)
  let thirdBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock secondBlock.2 thirdBlockHeaders)

  expect (!firstBlock.2.dynamic.isEmpty)
    "encoder should insert literal headers into its dynamic table"
  expect (secondBlock.1.size < firstBlock.1.size)
    "repeated header block should compress via the dynamic table"
  -- second block should be all single-byte indexed representations
  expectEq secondBlock.1.size secondBlockHeaders.size
    "fully repeated block should use one indexed byte per header"

  let decoder : Http2.Hpack.State := {}
  let firstDecoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock decoder firstBlock.1)
  expectEq firstDecoded.headers firstBlockHeaders "first block should round trip"
  let secondDecoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock firstDecoded.state secondBlock.1)
  expectEq secondDecoded.headers secondBlockHeaders "second block should round trip via decoder dynamic table"
  let thirdDecoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock secondDecoded.state thirdBlock.1)
  expectEq thirdDecoded.headers thirdBlockHeaders "third block should round trip"
  expectEq thirdDecoded.state.dynamic thirdBlock.2.dynamic
    "decoder dynamic table should match encoder dynamic table after three blocks"

def testEncoderDecoderTablesStayInSync : IO Unit := do
  let encoder : Http2.Hpack.State := {}
  let decoder : Http2.Hpack.State := {}
  let blocks := [
    #[Header.of "a-header" "one", Header.of "b-header" "two"],
    #[Header.of "a-header" "one", Header.of "c-header" "three"],
    #[Header.of "b-header" "two", Header.of "c-header" "three", Header.of "a-header" "changed"],
    #[Header.of "a-header" "changed", Header.of "a-header" "one"]
  ]
  let mut encoderState := encoder
  let mut decoderState := decoder
  for headers in blocks do
    let encoded ← expectStatusOk (Http2.Hpack.encodeHeaderBlock encoderState headers)
    encoderState := encoded.2
    let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock decoderState encoded.1)
    decoderState := decoded.state
    expectEq decoded.headers headers "sequential header block should round trip"
    expectEq decoderState.dynamic encoderState.dynamic
      "decoder dynamic table should mirror encoder dynamic table"

def testEviction : IO Unit := do
  -- max size that fits roughly one small entry (name+value+32)
  let encoder := Http2.Hpack.setMaxAllowedSize {} 70
  let decoder := Http2.Hpack.setMaxAllowedSize {} 70
  let blocks := [
    #[Header.of "header-aa" "value-aa"],
    #[Header.of "header-bb" "value-bb"],
    #[Header.of "header-aa" "value-aa", Header.of "header-bb" "value-bb"]
  ]
  let mut encoderState := encoder
  let mut decoderState := decoder
  for headers in blocks do
    let encoded ← expectStatusOk (Http2.Hpack.encodeHeaderBlock encoderState headers)
    encoderState := encoded.2
    let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock decoderState encoded.1)
    decoderState := decoded.state
    expectEq decoded.headers headers "header block with eviction should round trip"
    expect (Http2.Hpack.dynamicSize encoderState.dynamic <= 70)
      "encoder dynamic table should stay within max size"
    expectEq decoderState.dynamic encoderState.dynamic
      "tables should stay in sync under eviction"

def testDynamicTableSizeUpdateEmitted : IO Unit := do
  let encoder : Http2.Hpack.State := {}
  let firstHeaders := #[Header.of "x-first" "one"]
  let first ← expectStatusOk (Http2.Hpack.encodeHeaderBlock encoder firstHeaders)
  -- peer announces a smaller SETTINGS_HEADER_TABLE_SIZE
  let resized := Http2.Hpack.setMaxAllowedSize first.2 128
  expectEq resized.pendingSizeUpdate (some 128)
    "encoder should record a pending dynamic table size update"
  let secondHeaders := #[Header.of "x-second" "two"]
  let second ← expectStatusOk (Http2.Hpack.encodeHeaderBlock resized secondHeaders)
  expectEq second.2.pendingSizeUpdate (none : Option Nat)
    "pending size update should be cleared after emission"
  -- first byte must be a dynamic table size update (0b001xxxxx)
  expect (second.1[0]!.toNat >= 32 && second.1[0]!.toNat < 64)
    "next header block should start with a dynamic table size update"

  let decoder : Http2.Hpack.State := {}
  let firstDecoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock decoder first.1)
  let decoderResized := Http2.Hpack.setMaxAllowedSize firstDecoded.state 128
  let secondDecoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock decoderResized second.1)
  expectEq secondDecoded.headers secondHeaders
    "block with leading size update should decode"
  expectEq secondDecoded.state.maxSize 128
    "decoder should apply the emitted dynamic table size update"
  expectEq secondDecoded.state.dynamic second.2.dynamic
    "tables should stay in sync across a size update"

def testAuthorizationIsNeverIndexed : IO Unit := do
  let authorization := Header.of "authorization" "Bearer production-secret"
  let ordinary := Header.of "x-request-id" "request-1"
  let encoder : Http2.Hpack.State := {}
  let encoded ← expectStatusOk
    (Http2.Hpack.encodeHeaderBlock encoder #[authorization, ordinary])
  -- The first representation must use the 0001xxxx never-indexed prefix.
  expect (!encoded.1.isEmpty &&
      encoded.1[0]!.toNat >= 16 && encoded.1[0]!.toNat < 32)
    "authorization should use HPACK's never-indexed literal representation"
  expect (!encoded.2.dynamic.contains authorization)
    "authorization should not enter the encoder dynamic table"
  expect (encoded.2.dynamic.contains ordinary)
    "ordinary metadata should remain eligible for dynamic indexing"

  let decoded ← expectStatusOk
    (Http2.Hpack.decodeHeaderBlock ({} : Http2.Hpack.State) encoded.1)
  expectEq decoded.headers #[authorization, ordinary]
    "never-indexed authorization should round trip"
  expect (!decoded.state.dynamic.contains authorization)
    "authorization should not enter the decoder dynamic table"

def main : IO Unit := do
  testHuffmanKnownVector
  testHuffmanRoundTrip
  testHuffmanShorterFormChosen
  testDynamicTableRoundTrip
  testEncoderDecoderTablesStayInSync
  testEviction
  testDynamicTableSizeUpdateEmitted
  testAuthorizationIsNeverIndexed
  IO.println "hpack tests passed"
