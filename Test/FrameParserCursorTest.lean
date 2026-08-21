import Grpc

open Grpc

namespace Test.FrameParserCursor

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    fail message

private def payloadOfSize (size : Nat) (seed : Nat := 0) : ByteArray := Id.run do
  let mut payload := ByteArray.emptyWithCapacity size
  for index in [0:size] do
    payload := payload.push (UInt8.ofNat (index * 37 + seed * 17 + 11))
  return payload

private def frame (frameType : Http2.FrameType) (streamId : Nat)
    (payload : ByteArray) (flags : UInt8 := 0) : Http2.Frame :=
  { header := { length := payload.size, frameType, flags, streamId }, payload }

private def rawHeader (length : Nat) (frameType flags : UInt8)
    (streamWord : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((length / 65536) % 256),
    UInt8.ofNat ((length / 256) % 256),
    UInt8.ofNat (length % 256),
    frameType,
    flags,
    UInt8.ofNat ((streamWord / 16777216) % 256),
    UInt8.ofNat ((streamWord / 65536) % 256),
    UInt8.ofNat ((streamWord / 256) % 256),
    UInt8.ofNat (streamWord % 256)]

private def encodeFrame (value : Http2.Frame) : IO ByteArray := do
  match Http2.Frame.encode value with
  | .ok wire => pure wire
  | .error status => fail s!"valid frame failed to encode: {status.messageD}"

private def encodeFrames (values : Array Http2.Frame) : IO ByteArray := do
  match Http2.Frame.encodeBatch values with
  | .ok wire => pure wire
  | .error status => fail s!"valid frame batch failed to encode: {status.messageD}"

private def sameState (left right : Http2.Frame.DecodeState) : Bool :=
  left.buffered == right.buffered && left.frames == right.frames

/- Compare both complete public projections. If either implementation ever gains
an input-dependent error, the exact `Status` remains part of the differential. -/
private def compareDecode (context : String) (state : Http2.Frame.DecodeState)
    (chunk : ByteArray) : IO (Except Status Http2.Frame.DecodeState) := do
  let reference :=
    Http2.Frame.TestSupport.decodeChunkReferenceForBenchmark state chunk
  let candidate :=
    Http2.Frame.TestSupport.decodeChunkCandidateForBenchmark state chunk
  match reference, candidate with
  | .ok expected, .ok actual =>
      expect (sameState actual expected)
        s!"{context}: candidate DecodeState projections diverged"
  | .error expected, .error actual =>
      expect (actual == expected)
        s!"{context}: candidate returned a different exact Status"
  | .ok _, .error actual =>
      fail s!"{context}: candidate rejected reference success: {actual.messageD}"
  | .error expected, .ok _ =>
      fail s!"{context}: candidate accepted reference error: {expected.messageD}"
  return candidate

private def requireOk (context : String)
    (result : Except Status Http2.Frame.DecodeState) : IO Http2.Frame.DecodeState := do
  match result with
  | .ok state => pure state
  | .error status => fail s!"{context}: unexpected parser error: {status.messageD}"

private def decodeOk (context : String) (state : Http2.Frame.DecodeState)
    (chunk : ByteArray) : IO Http2.Frame.DecodeState := do
  requireOk context (← compareDecode context state chunk)

private def testEmpty : IO Unit := do
  let decoded ← decodeOk "empty/default" {} ByteArray.empty
  expect decoded.buffered.isEmpty "empty/default: retained bytes"
  expect decoded.frames.isEmpty "empty/default: produced frames"

  let residue := ByteArray.mk #[0x00, 0x01, 0x02]
  let prior := frame .ping 99 (payloadOfSize 2 1) 0xff
  let state : Http2.Frame.DecodeState := { buffered := residue, frames := #[prior] }
  let retained ← decodeOk "empty/existing-residue-and-prior-frames" state ByteArray.empty
  expect (retained.buffered == residue)
    "empty/existing-residue-and-prior-frames: changed buffered bytes"
  expect retained.frames.isEmpty
    "empty/existing-residue-and-prior-frames: prior frames were not ignored"

private def testHeaderPrefixes (wire : ByteArray) : IO Unit := do
  for size in [0:Http2.frameHeaderSize] do
    let fragment := wire.extract 0 size
    let decoded ← decodeOk s!"header-prefix/{size}" {} fragment
    expect (decoded.buffered == fragment)
      s!"header-prefix/{size}: changed the exact retained prefix"
    expect decoded.frames.isEmpty
      s!"header-prefix/{size}: emitted a frame below the header boundary"

private def testIncompletePayloads (wire : ByteArray) (payloadSize : Nat) : IO Unit := do
  for present in [0:payloadSize] do
    let size := Http2.frameHeaderSize + present
    let fragment := wire.extract 0 size
    let decoded ← decodeOk s!"incomplete-payload/{present}-of-{payloadSize}" {} fragment
    expect (decoded.buffered == fragment)
      s!"incomplete-payload/{present}-of-{payloadSize}: changed retained bytes"
    expect decoded.frames.isEmpty
      s!"incomplete-payload/{present}-of-{payloadSize}: emitted an incomplete frame"

private def testCompleteBatch (label : String) (frames : Array Http2.Frame) : IO ByteArray := do
  let wire ← encodeFrames frames
  let decoded ← decodeOk s!"complete/{label}" {} wire
  expect decoded.buffered.isEmpty s!"complete/{label}: retained residue"
  expect (decoded.frames == frames) s!"complete/{label}: frame sequence changed"
  return wire

private def testNextHeaderResidues (complete : Array Http2.Frame)
    (completeWire nextWire : ByteArray) : IO Unit := do
  for size in [0:Http2.frameHeaderSize] do
    let residue := nextWire.extract 0 size
    let decoded ← decodeOk s!"next-header-residue/{size}" {}
      (completeWire.append residue)
    expect (decoded.frames == complete)
      s!"next-header-residue/{size}: changed completed frames"
    expect (decoded.buffered == residue)
      s!"next-header-residue/{size}: changed exact next-header residue"

private def testNextPayloadResidues (complete : Array Http2.Frame)
    (completeWire nextWire : ByteArray) (nextPayloadSize : Nat) : IO Unit := do
  for present in [0:nextPayloadSize] do
    let residueSize := Http2.frameHeaderSize + present
    let residue := nextWire.extract 0 residueSize
    let decoded ← decodeOk s!"next-payload-residue/{present}-of-{nextPayloadSize}" {}
      (completeWire.append residue)
    expect (decoded.frames == complete)
      s!"next-payload-residue/{present}-of-{nextPayloadSize}: changed completed frames"
    expect (decoded.buffered == residue)
      s!"next-payload-residue/{present}-of-{nextPayloadSize}: changed exact residue"

private def testTwoCallSplits (label : String) (wire : ByteArray)
    (expected : Array Http2.Frame) : IO Unit := do
  for split in [0:wire.size + 1] do
    let first ← decodeOk s!"two-call/{label}/{split}/first" {}
      (wire.extract 0 split)
    let second ← decodeOk s!"two-call/{label}/{split}/second" first
      (wire.extract split wire.size)
    expect (first.frames.append second.frames == expected)
      s!"two-call/{label}/{split}: changed the aggregate frame sequence"
    expect second.buffered.isEmpty
      s!"two-call/{label}/{split}: retained residue after the complete second chunk"

private def testPriorFramesIgnored (wire : ByteArray) (expected : Array Http2.Frame) : IO Unit := do
  let stale : Array Http2.Frame := #[
    frame .data 71 (payloadOfSize 1 3),
    frame (.unknown 0xe7) 73 (payloadOfSize 2 5) 0xa5]
  let decoded ← decodeOk "prior-frames/complete-chunk" { frames := stale } wire
  expect (decoded.frames == expected)
    "prior-frames/complete-chunk: output retained or prepended prior state.frames"
  expect decoded.buffered.isEmpty "prior-frames/complete-chunk: retained residue"

  let split := Nat.min 7 wire.size
  let first ← decodeOk "prior-frames/fragment-first" { frames := stale }
    (wire.extract 0 split)
  expect first.frames.isEmpty
    "prior-frames/fragment-first: output retained prior state.frames"
  let second ← decodeOk "prior-frames/fragment-second"
    { first with frames := stale } (wire.extract split wire.size)
  expect (second.frames == expected)
    "prior-frames/fragment-second: output retained prior state.frames"
  expect second.buffered.isEmpty "prior-frames/fragment-second: retained residue"

private def testAllTypeBytes : IO Unit := do
  for value in [0:256] do
    let byte := UInt8.ofNat value
    let wire := rawHeader 0 byte 0 1
    let decoded ← decodeOk s!"type-byte/{value}" {} wire
    expect decoded.buffered.isEmpty s!"type-byte/{value}: retained residue"
    expect (decoded.frames.size == 1) s!"type-byte/{value}: wrong frame count"
    let parsed := decoded.frames[0]!
    expect (parsed.header.frameType == Http2.FrameType.ofUInt8 byte)
      s!"type-byte/{value}: changed canonical frame type"
    expect parsed.payload.isEmpty s!"type-byte/{value}: created payload bytes"

private def testAllFlagBytes : IO Unit := do
  for value in [0:256] do
    let flags := UInt8.ofNat value
    let wire := rawHeader 0 Http2.FrameType.headers.toUInt8 flags 3
    let decoded ← decodeOk s!"flag-byte/{value}" {} wire
    expect (decoded.frames.size == 1) s!"flag-byte/{value}: wrong frame count"
    expect (decoded.frames[0]!.header.flags == flags)
      s!"flag-byte/{value}: parser normalized opaque flags"

private def testStreamIds : IO Unit := do
  let streamIds : Array Nat := #[
    0, 1, 127, 128, 255, 256, 65535, 65536,
    16777215, 16777216, Http2.maxStreamId - 1, Http2.maxStreamId]
  for streamId in streamIds do
    let wire := rawHeader 0 Http2.FrameType.data.toUInt8 0 streamId
    let decoded ← decodeOk s!"stream-id/{streamId}" {} wire
    expect (decoded.frames.size == 1) s!"stream-id/{streamId}: wrong frame count"
    expect (decoded.frames[0]!.header.streamId == streamId)
      s!"stream-id/{streamId}: changed a valid 31-bit stream id"

  -- The high bit is reserved on the wire. `decodeHeader` deliberately masks it
  -- by reduction modulo 2^31; retain that established behavior exactly.
  let reservedCases : Array (Nat × Nat) := #[
    (Http2.maxStreamId + 1, 0),
    (Http2.maxStreamId + 2, 1),
    (4294967295, Http2.maxStreamId)]
  for (wireId, expectedId) in reservedCases do
    let wire := rawHeader 0 Http2.FrameType.headers.toUInt8 0xff wireId
    let decoded ← decodeOk s!"reserved-stream-bit/{wireId}" {} wire
    expect (decoded.frames.size == 1)
      s!"reserved-stream-bit/{wireId}: wrong frame count"
    expect (decoded.frames[0]!.header.streamId == expectedId)
      s!"reserved-stream-bit/{wireId}: changed reserved-bit masking"

private def testLengthBoundaries : IO Unit := do
  let completeLengths : Array Nat := #[
    0, 1, 2, 7, 8, 9, 127, 128, 255, 256, 257,
    16383, 16384, 16385, 65535, 65536]
  for length in completeLengths do
    let payload := payloadOfSize length (length % 251)
    let wire := (rawHeader length Http2.FrameType.data.toUInt8 0x5a 5).append payload
    let decoded ← decodeOk s!"length-complete/{length}" {} wire
    expect decoded.buffered.isEmpty s!"length-complete/{length}: retained residue"
    expect (decoded.frames.size == 1) s!"length-complete/{length}: wrong frame count"
    let parsed := decoded.frames[0]!
    expect (parsed.header.length == length)
      s!"length-complete/{length}: changed decoded length"
    expect (parsed.payload == payload)
      s!"length-complete/{length}: changed payload bytes"

  -- Exercise the full 24-bit header boundary without allocating a 16 MiB test
  -- payload. Both parsers must retain the exact header and available payload.
  let maxPrefix := (rawHeader Http2.maxFramePayloadLength 0xff 0xff 0xffffffff)
    |>.append (payloadOfSize 31 19)
  let decoded ← decodeOk "length-incomplete/24-bit-max" {} maxPrefix
  expect decoded.frames.isEmpty "length-incomplete/24-bit-max: emitted an incomplete frame"
  expect (decoded.buffered == maxPrefix)
    "length-incomplete/24-bit-max: changed retained bytes"

private def testNoncanonicalConstructors : IO Unit := do
  -- `unknown` constructors in the named 0..9 range encode to a canonical named
  -- constructor. This is intentional and must not be mistaken for parser drift.
  for value in [0:10] do
    let source := frame (.unknown (UInt8.ofNat value)) 1 ByteArray.empty 0xcc
    let wire ← encodeFrame source
    let decoded ← decodeOk s!"noncanonical-unknown/{value}" {} wire
    expect (decoded.frames.size == 1)
      s!"noncanonical-unknown/{value}: wrong frame count"
    expect (decoded.frames[0]!.header.frameType ==
      Http2.FrameType.ofUInt8 (UInt8.ofNat value))
      s!"noncanonical-unknown/{value}: did not canonicalize by wire type byte"

private def testMalformedFramingBoundaries : IO Unit := do
  -- Frame parsing is deliberately structural. SETTINGS semantics (stream zero,
  -- ACK shape, and six-byte entries) are checked later, so this malformed
  -- SETTINGS frame must still be returned byte-for-byte at this layer.
  let settingsPayload := ByteArray.empty.push 0x7f
  let settingsWire :=
    (rawHeader 1 Http2.FrameType.settings.toUInt8 0x1 1).append settingsPayload
  let settings ← decodeOk "malformed/semantic-settings" {} settingsWire
  let expectedSettings := frame .settings 1 settingsPayload 0x1
  expect settings.buffered.isEmpty "malformed/semantic-settings: retained residue"
  expect (settings.frames == #[expectedSettings])
    "malformed/semantic-settings: framing layer changed semantic-invalid input"

  -- A declared frame that is longer than the available bytes is not an error;
  -- the entire unconsumed frame prefix is retained for the next decode call.
  let shortPayload := ByteArray.mk #[0x10, 0x20, 0x30]
  let truncatedWire :=
    (rawHeader 1024 Http2.FrameType.data.toUInt8 0x3d 7).append shortPayload
  let truncated ← decodeOk "malformed/truncated-declared-payload" {} truncatedWire
  expect truncated.frames.isEmpty
    "malformed/truncated-declared-payload: emitted an incomplete frame"
  expect (truncated.buffered == truncatedWire)
    "malformed/truncated-declared-payload: changed the retained frame prefix"

def run : IO Unit := do
  let emptyData := frame .data 0 ByteArray.empty
  let one := frame .headers 1 (payloadOfSize 23 1) Http2.FrameFlag.endHeaders
  let three : Array Http2.Frame := #[
    frame .headers 1 (payloadOfSize 11 2) Http2.FrameFlag.endHeaders,
    frame .data 1 (payloadOfSize 257 3) 0xa9,
    frame .continuation Http2.maxStreamId (payloadOfSize 7 4)
      (Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream])]
  let sixtyFour := Array.range 64 |>.map fun index =>
    frame (Http2.FrameType.ofUInt8 (UInt8.ofNat (index % 17)))
      (if index % 3 == 0 then 0 else index * 8191 % (Http2.maxStreamId + 1))
      (payloadOfSize (index % 19) index) (UInt8.ofNat (index * 29))
  let next := frame .pushPromise 17 (payloadOfSize 37 7) 0xed

  let oneWire ← encodeFrame one
  let threeWire ← encodeFrames three
  let nextWire ← encodeFrame next

  testEmpty
  testHeaderPrefixes oneWire
  testIncompletePayloads oneWire one.payload.size
  discard <| testCompleteBatch "zero-length" #[emptyData]
  discard <| testCompleteBatch "one-frame" #[one]
  discard <| testCompleteBatch "three-frame" three
  discard <| testCompleteBatch "sixty-four-frame" sixtyFour
  testNextHeaderResidues three threeWire nextWire
  testNextPayloadResidues three threeWire nextWire next.payload.size
  testTwoCallSplits "one-frame" oneWire #[one]
  testTwoCallSplits "three-frame" threeWire three
  testPriorFramesIgnored threeWire three
  testAllTypeBytes
  testAllFlagBytes
  testStreamIds
  testLengthBoundaries
  testNoncanonicalConstructors
  testMalformedFramingBoundaries

  IO.println "HTTP/2 frame parser cursor differential passed"

end Test.FrameParserCursor

unsafe def main : IO Unit :=
  Test.FrameParserCursor.run
