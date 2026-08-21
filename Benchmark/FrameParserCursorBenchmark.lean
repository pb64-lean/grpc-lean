import Grpc

/-!
# HTTP/2 frame-parser cursor differential benchmark

The reference seam is the exact former suffix-recursive `Frame.decodeChunk`
implementation; the candidate seam is the proved-equal cursor implementation.
Both seams include the production decoder's unchanged buffered-input append.
An opaque selector chooses one noinline seam before either scaling run, leaving
the loop with the same indirect call and error-unwrapping shape in both modes.

The fixed preflight compares exact frames, exact residual bytes, and exact
errors.  It covers every split point of the measured complete wires plus
structurally malformed inputs whose framing behavior is intentionally distinct
from later HTTP/2 semantic validation.  The measured digest visits every frame
header, every payload byte, and every residual byte.

This executable reports no wall time.  It is intended for whole-process
`perf stat` instruction and branch counters.  Fixture construction, exact
semantic validation, selector construction, requested warmup, checksum checks,
and output are fixed process work; only the selected decode/digest recurrence
scales with `iterations`.
-/

namespace Grpc.Http2.FrameParserCursorBenchmarkHarness

private abbrev ChunkDecoder :=
  Frame.DecodeState → ByteArray → Except Status Frame.DecodeState

private inductive Mode where
  | reference
  | candidate

private structure DecoderBox where
  decode : ChunkDecoder
  /-- Keep selection nontrivial across the opaque boundary. -/
  candidateSelected : Bool

/-- Select once; neither a `Mode` value nor a mode branch enters the recurrence. -/
@[noinline] private opaque selectDecoderBox (mode : Mode) : DecoderBox :=
  match mode with
  | .reference => {
      decode := Frame.TestSupport.decodeChunkReferenceForBenchmark
      candidateSelected := false
    }
  | .candidate => {
      decode := Frame.TestSupport.decodeChunkCandidateForBenchmark
      candidateSelected := true
    }

private def payload (size seed : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for index in [0:size] do
    bytes := bytes.push (UInt8.ofNat ((index * 131 + seed * 29 + 17) % 251))
  return bytes

private def frame (frameType : FrameType) (streamId : Nat)
    (bytes : ByteArray := ByteArray.empty) (flags : UInt8 := 0) : Frame := {
  header := {
    length := bytes.size
    frameType
    flags
    streamId
  }
  payload := bytes
}

private def encodeFrames (label : String) (frames : Array Frame) : IO ByteArray := do
  match Frame.encodeBatch frames with
  | .ok wire => pure wire
  | .error status =>
      throw (IO.userError s!"{label}: frame encoding failed: {status.messageD}")

private def oneFrame : Array Frame :=
  #[frame .data 1 (payload 128 11) FrameFlag.endStream]

private def unaryFrames : Array Frame :=
  let headers := frame .headers 1 (payload 21 3) FrameFlag.endHeaders
  let data := frame .data 1 (payload 128 11)
  let trailers := frame .headers 1 (payload 13 19)
    (FrameFlag.combine #[FrameFlag.endHeaders, FrameFlag.endStream])
  #[headers, data, trailers]

private def frames16 : Array Frame := Id.run do
  let mut frames := #[]
  for index in [0:16] do
    frames := frames.push <| frame .data (index % 4 * 2 + 1)
      (payload (16 + index % 5) (index + 31))
      (if index == 15 then FrameFlag.endStream else 0)
  return frames

private def tinyFrames64 : Array Frame := Id.run do
  let mut frames := #[]
  for index in [0:64] do
    frames := frames.push <| frame .data (index * 2 + 1)
      (ByteArray.empty.push (UInt8.ofNat (index * 29 + 5)))
      (if index == 63 then FrameFlag.endStream else 0)
  return frames

private def sameState (left right : Frame.DecodeState) : Bool :=
  left.buffered == right.buffered && left.frames == right.frames

private def sameResult : Except Status Frame.DecodeState →
    Except Status Frame.DecodeState → Bool
  | .error left, .error right => left == right
  | .ok left, .ok right => sameState left right
  | _, _ => false

private def expectExact (label : String) (state : Frame.DecodeState)
    (chunk : ByteArray) (expected : Except Status Frame.DecodeState) : IO Unit := do
  let reference := Frame.TestSupport.decodeChunkReferenceForBenchmark state chunk
  let candidate := Frame.TestSupport.decodeChunkCandidateForBenchmark state chunk
  unless sameResult reference expected do
    throw (IO.userError s!"{label}: reference result differs from the independent expectation")
  unless sameResult candidate expected do
    throw (IO.userError s!"{label}: candidate result differs from the independent expectation")
  unless sameResult reference candidate do
    throw (IO.userError s!"{label}: reference and candidate results differ")

private def frameWireSize (value : Frame) : Nat :=
  frameHeaderSize + value.payload.size

/-- Independent boundary oracle for an encoded frame batch cut at `split`. -/
private def expectedAtSplit (frames : Array Frame) (wire : ByteArray) (split : Nat) :
    Frame.DecodeState × Frame.DecodeState := Id.run do
  let mut count := 0
  let mut consumed := 0
  let mut scanning := true
  for index in [0:frames.size] do
    if scanning then
      let next := consumed + frameWireSize frames[index]!
      if next ≤ split then
        count := count + 1
        consumed := next
      else
        scanning := false
  let first : Frame.DecodeState := {
    buffered := wire.extract consumed split
    frames := frames.extract 0 count
  }
  let second : Frame.DecodeState := {
    buffered := ByteArray.empty
    frames := frames.extract count frames.size
  }
  return (first, second)

private def validateAllSplits (label : String) (frames : Array Frame)
    (wire : ByteArray) : IO Nat := do
  for split in [0:wire.size + 1] do
    let expected := expectedAtSplit frames wire split
    let firstChunk := wire.extract 0 split
    let secondChunk := wire.extract split wire.size

    let referenceFirst :=
      Frame.TestSupport.decodeChunkReferenceForBenchmark {} firstChunk
    let candidateFirst :=
      Frame.TestSupport.decodeChunkCandidateForBenchmark {} firstChunk
    unless sameResult referenceFirst (.ok expected.1) &&
        sameResult candidateFirst (.ok expected.1) &&
        sameResult referenceFirst candidateFirst do
      throw (IO.userError s!"{label}/split-{split}: first decode differs")

    let referenceSecond := Frame.TestSupport.decodeChunkReferenceForBenchmark
      { buffered := expected.1.buffered } secondChunk
    let candidateSecond := Frame.TestSupport.decodeChunkCandidateForBenchmark
      { buffered := expected.1.buffered } secondChunk
    unless sameResult referenceSecond (.ok expected.2) &&
        sameResult candidateSecond (.ok expected.2) &&
        sameResult referenceSecond candidateSecond do
      throw (IO.userError s!"{label}/split-{split}: second decode differs")
  pure (wire.size + 1)

private def uint24BE (value : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (value / 65536),
    UInt8.ofNat (value / 256),
    UInt8.ofNat value]

private def uint32BE (value : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat (value / 16777216),
    UInt8.ofNat (value / 65536),
    UInt8.ofNat (value / 256),
    UInt8.ofNat value]

/-- Raw construction deliberately bypasses `Frame.encode` for malformed cases. -/
private def rawFrame (declaredLength : Nat) (frameType flags : UInt8)
    (rawStreamId : Nat) (fragment : ByteArray) : ByteArray :=
  uint24BE declaredLength
    |>.push frameType
    |>.push flags
    |>.append (uint32BE rawStreamId)
    |>.append fragment

private def validateMalformed : IO Nat := do
  let invalidSettingsPayload := ByteArray.empty.push 0x7f
  let invalidSettingsWire := rawFrame 1 0x4 0 1 invalidSettingsPayload
  let invalidSettings := frame .settings 1 invalidSettingsPayload
  expectExact "semantic-invalid-settings" {} invalidSettingsWire
    (.ok { buffered := ByteArray.empty, frames := #[invalidSettings] })

  let unknownPayload := (ByteArray.empty.push 0x51).push 0xa7
  let unknownWire := rawFrame 2 0xfe 0xa5 (maxStreamId + 8) unknownPayload
  let unknown := frame (.unknown 0xfe) 7 unknownPayload 0xa5
  expectExact "unknown-type-reserved-stream-bit" {} unknownWire
    (.ok { buffered := ByteArray.empty, frames := #[unknown] })

  let truncatedPayload := (ByteArray.empty.push 0x10).push 0x20 |>.push 0x30
  let truncatedWire := rawFrame 1024 0x0 0 3 truncatedPayload
  expectExact "declared-length-truncated" {} truncatedWire
    (.ok { buffered := truncatedWire, frames := #[] })

  let shortHeader := (uint24BE 7).push 0x0 |>.push 0x1
  expectExact "short-header" {} shortHeader
    (.ok { buffered := shortHeader, frames := #[] })
  pure 4

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

@[inline] private def bytesDigest (digest : UInt64) (bytes : @& ByteArray) : UInt64 := Id.run do
  let mut digest := mix digest (UInt64.ofNat bytes.size)
  for byte in bytes do
    digest := mix digest (UInt64.ofNat byte.toNat + 1)
  return digest

@[inline] private def frameDigest (digest : UInt64) (value : @& Frame) : UInt64 :=
  let digest := mix digest (UInt64.ofNat value.header.length)
  let digest := mix digest (UInt64.ofNat value.header.frameType.toUInt8.toNat)
  let digest := mix digest (UInt64.ofNat value.header.flags.toNat)
  let digest := mix digest (UInt64.ofNat value.header.streamId)
  bytesDigest digest value.payload

/-- Full ordered observation of every decoded frame and every residual byte. -/
@[noinline] private def decodeStateDigest (state : @& Frame.DecodeState) : UInt64 := Id.run do
  let mut digest := mix 1469598103934665603 (UInt64.ofNat state.frames.size)
  for value in state.frames do
    digest := frameDigest digest value
  return bytesDigest digest state.buffered

private structure Fixture where
  label : String
  frames : Array Frame
  chunks : Array ByteArray
  expectedDigests : Array UInt64
  wireBytes : Nat
  payloadBytes : Nat

private def totalBytes (chunks : Array ByteArray) : Nat :=
  chunks.foldl (fun total chunk => total + chunk.size) 0

private def totalPayloadBytes (frames : Array Frame) : Nat :=
  frames.foldl (fun total value => total + value.payload.size) 0

private def makeFixture (label : String) (frames : Array Frame)
    (chunks : Array ByteArray) : IO Fixture := do
  unless !chunks.isEmpty do
    throw (IO.userError s!"{label}: fixture must have at least one chunk")
  let mut referenceState : Frame.DecodeState := {}
  let mut candidateState : Frame.DecodeState := {}
  let mut referenceFrames : Array Frame := #[]
  let mut candidateFrames : Array Frame := #[]
  let mut expectedDigests := #[]
  for chunk in chunks do
    let reference ← match
        Frame.TestSupport.decodeChunkReferenceForBenchmark referenceState chunk with
      | .ok decoded => pure decoded
      | .error status =>
          throw (IO.userError s!"{label}: reference fixture decode failed: {status.messageD}")
    let candidate ← match
        Frame.TestSupport.decodeChunkCandidateForBenchmark candidateState chunk with
      | .ok decoded => pure decoded
      | .error status =>
          throw (IO.userError s!"{label}: candidate fixture decode failed: {status.messageD}")
    unless sameState reference candidate do
      throw (IO.userError s!"{label}: reference and candidate fixture states differ")
    referenceFrames := referenceFrames.append reference.frames
    candidateFrames := candidateFrames.append candidate.frames
    expectedDigests := expectedDigests.push (decodeStateDigest reference)
    referenceState := { buffered := reference.buffered }
    candidateState := { buffered := candidate.buffered }
  unless referenceState.buffered.isEmpty && candidateState.buffered.isEmpty do
    throw (IO.userError s!"{label}: fixture chunk cycle leaves residual bytes")
  unless referenceFrames == frames && candidateFrames == frames do
    throw (IO.userError s!"{label}: fixture chunk cycle changed decoded frames")
  pure {
    label
    frames
    chunks
    expectedDigests
    wireBytes := totalBytes chunks
    payloadBytes := totalPayloadBytes frames
  }

private def makeFixtures : IO (Array Fixture) := do
  let oneWire ← encodeFrames "one_frame" oneFrame
  let unaryWire ← encodeFrames "unary_three" unaryFrames
  let wire16 ← encodeFrames "frames_16" frames16
  let tinyWire ← encodeFrames "tiny_64" tinyFrames64

  let tail := frame .data 3 (payload 37 211) FrameFlag.endStream
  let tailWire ← encodeFrames "incomplete_tail/tail" #[tail]
  let tailSplit := frameHeaderSize + 3
  let firstTailChunk := unaryWire.append (tailWire.extract 0 tailSplit)
  let secondTailChunk := tailWire.extract tailSplit tailWire.size

  pure #[
    ← makeFixture "one_frame" oneFrame #[oneWire],
    ← makeFixture "unary_three" unaryFrames #[unaryWire],
    ← makeFixture "frames_16" frames16 #[wire16],
    ← makeFixture "tiny_64" tinyFrames64 #[tinyWire],
    ← makeFixture "incomplete_tail" (unaryFrames.push tail)
      #[firstTailChunk, secondTailChunk]
  ]

private def validateSemantics (fixtures : Array Fixture) : IO Nat := do
  let mut cases := 0
  expectExact "empty" {} ByteArray.empty
    (.ok { buffered := ByteArray.empty, frames := #[] })
  cases := cases + 1

  for fixture in fixtures do
    let wire := fixture.chunks.foldl (init := ByteArray.empty) ByteArray.append
    cases := cases + (← validateAllSplits fixture.label fixture.frames wire)

  cases := cases + (← validateMalformed)
  pure cases

private def expectedChecksum (digests : Array UInt64) (iterations : Nat) : UInt64 :=
  let cycle := digests.foldl (fun total digest => total + digest) 0
  let remainder := (digests.extract 0 (iterations % digests.size)).foldl
    (fun total digest => total + digest) 0
  cycle * UInt64.ofNat (iterations / digests.size) + remainder

/-- Linear recurrence with one common indirect selected call in either mode. -/
@[noinline] private def runRepeated (decode : @& ChunkDecoder) (fixture : @& Fixture)
    (iterations : Nat) : Except Status UInt64 := do
  let mut state : Frame.DecodeState := {}
  let mut checksum : UInt64 := 0
  for iteration in [0:iterations] do
    let chunk := fixture.chunks[iteration % fixture.chunks.size]!
    let decoded ← decode state chunk
    checksum := checksum + decodeStateDigest decoded
    state := { buffered := decoded.buffered }
  pure checksum

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

private def parsePositive (label value : String) : IO Nat := do
  let parsed ← parseNatural label value
  unless parsed > 0 do
    throw (IO.userError s!"{label} must be positive")
  pure parsed

private def parseMode : String → Option Mode
  | "reference" => some .reference
  | "candidate" => some .candidate
  | _ => none

private def modeName : Mode → String
  | .reference => "reference"
  | .candidate => "candidate"

private def modeIsCandidate : Mode → Bool
  | .reference => false
  | .candidate => true

def runMain (args : List String) : IO Unit := do
  let (modeText, selection, iterations, warmup) ← match args with
    | [mode, fixture, iterations, warmup] =>
        pure (mode, fixture,
          ← parsePositive "iterations" iterations,
          ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: frame_parser_cursor_benchmark (reference|candidate) " ++
          "(one_frame|unary_three|frames_16|tiny_64|incomplete_tail) " ++
          "iterations warmup")
  let some mode := parseMode modeText
    | throw (IO.userError "mode must be reference or candidate")

  let fixtures ← makeFixtures
  let semanticCases ← validateSemantics fixtures
  let some fixture := fixtures.find? fun fixture => fixture.label == selection
    | throw (IO.userError s!"unknown fixture: {selection}")

  let decoderBox := selectDecoderBox mode
  unless decoderBox.candidateSelected == modeIsCandidate mode do
    throw (IO.userError "opaque decoder selection metadata mismatch")
  let selected := decoderBox.decode

  let warmupChecksum ← match runRepeated selected fixture warmup with
    | .ok checksum => pure checksum
    | .error status =>
        throw (IO.userError s!"warmup decode failed: {status.messageD}")
  let expectedWarmup := expectedChecksum fixture.expectedDigests warmup
  unless warmupChecksum == expectedWarmup do
    throw (IO.userError
      s!"warmup checksum {warmupChecksum} != reference checksum {expectedWarmup}")

  let checksum ← match runRepeated selected fixture iterations with
    | .ok checksum => pure checksum
    | .error status =>
        throw (IO.userError s!"measured decode failed: {status.messageD}")
  let expected := expectedChecksum fixture.expectedDigests iterations
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != reference checksum {expected}")

  IO.println <| s!"benchmark=grpc_http2_frame_parser_cursor_v1 mode={modeName mode} " ++
    s!"fixture={fixture.label} frames_per_cycle={fixture.frames.size} " ++
    s!"chunks_per_cycle={fixture.chunks.size} wire_bytes={fixture.wireBytes} " ++
    s!"payload_bytes={fixture.payloadBytes} iterations={iterations} warmup={warmup} " ++
    s!"checksum={checksum}"
  IO.println <|
    s!"frame_parser_cursor_validation=pass cases={semanticCases} " ++
      "result=exact_reference_candidate_expected digest=all_frames_payloads_residue"
  IO.println <|
    "counter_scope=whole_process fixed=fixture_construction+exact_semantic_validation+" ++
      "selector+requested_warmup+checksum_checks+output " ++
      "scaling=selected_decodeChunk_with_existing_append+full_result_digest " ++
      "excluded=tls+socket+network+hpack+grpc_message_decode+handler+service"

end Grpc.Http2.FrameParserCursorBenchmarkHarness

def main (args : List String) : IO Unit :=
  Grpc.Http2.FrameParserCursorBenchmarkHarness.runMain args
