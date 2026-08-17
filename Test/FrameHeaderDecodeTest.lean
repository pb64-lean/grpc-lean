import Grpc

open Grpc

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def payloadOfSize (size : Nat) (seed : Nat := 0) : ByteArray := Id.run do
  let mut payload := ByteArray.empty
  for index in [0:size] do
    payload := payload.push (UInt8.ofNat (index * 37 + seed))
  pure payload

private def frame (frameType : Http2.FrameType) (streamId : Nat)
    (payload : ByteArray) (flags : UInt8 := 0) : Http2.Frame :=
  {
    header := { length := payload.size, frameType, flags, streamId }
    payload
  }

private def encodeFrame (value : Http2.Frame) : IO ByteArray := do
  match Http2.Frame.encode value with
  | .ok wire => pure wire
  | .error status => throw (IO.userError status.messageD)

private def encodeFrames (values : Array Http2.Frame) : IO ByteArray := do
  match Http2.Frame.encodeBatch values with
  | .ok wire => pure wire
  | .error status => throw (IO.userError status.messageD)

/- The exact pre-change parser, retained as a differential oracle. -/
private partial def legacyParseBuffered (buffered : ByteArray)
    (frames : Array Http2.Frame) : Except Status Http2.Frame.DecodeState :=
  if buffered.size < Http2.frameHeaderSize then
    .ok { buffered, frames }
  else
    match Http2.Frame.decodeHeader
        (buffered.extract 0 Http2.frameHeaderSize) with
    | .error status => .error status
    | .ok header =>
        if buffered.size < Http2.frameHeaderSize + header.length then
          .ok { buffered, frames }
        else
          let next : Http2.Frame := {
            header
            payload := buffered.extract Http2.frameHeaderSize
              (Http2.frameHeaderSize + header.length)
          }
          let rest := buffered.extract (Http2.frameHeaderSize + header.length)
            buffered.size
          legacyParseBuffered rest (frames.push next)

private def legacyDecodeChunk (state : Http2.Frame.DecodeState)
    (chunk : ByteArray) : Except Status Http2.Frame.DecodeState :=
  legacyParseBuffered (state.buffered.append chunk) #[]

private def sameState (left right : Http2.Frame.DecodeState) : Bool :=
  left.buffered == right.buffered && left.frames == right.frames

private def compareDecode (context : String) (state : Http2.Frame.DecodeState)
    (chunk : ByteArray) : IO Http2.Frame.DecodeState := do
  let expected := legacyDecodeChunk state chunk
  let actual := Http2.Frame.decodeChunk state chunk
  match actual, expected with
  | .ok actual, .ok expected =>
      expect (sameState actual expected)
        s!"{context}: decoded frame state diverged from the nine-byte-extract oracle"
      pure actual
  | .error actual, .error expected =>
      expect (actual == expected)
        s!"{context}: exact decoder status diverged from the nine-byte-extract oracle"
      throw (IO.userError s!"{context}: decoder unexpectedly rejected the fixture")
  | _, _ =>
      throw (IO.userError s!"{context}: decoder success/error shape diverged from the oracle")

private def validateAllSplits (label : String) (wire : ByteArray)
    (expected : Array Http2.Frame) : IO Unit := do
  for split in [0:wire.size + 1] do
    let first ← compareDecode s!"{label}/split-{split}/first" {}
      (wire.extract 0 split)
    let second ← compareDecode s!"{label}/split-{split}/second" first
      (wire.extract split wire.size)
    expect (first.frames.append second.frames == expected)
      s!"{label}/split-{split}: split decode changed the completed frame sequence"
    expect second.buffered.isEmpty
      s!"{label}/split-{split}: split decode retained unexpected residue"

private def testIncompleteHeaders (wire : ByteArray) : IO Unit := do
  for size in [0:Http2.frameHeaderSize] do
    let decoded ← compareDecode s!"incomplete-header/{size}" {} (wire.extract 0 size)
    expect (decoded.frames.isEmpty && decoded.buffered == wire.extract 0 size)
      s!"incomplete-header/{size}: bytes below the nine-byte boundary changed"

private def testIncompletePayloads (wire : ByteArray) (payloadSize : Nat) : IO Unit := do
  for present in [0:payloadSize] do
    let size := Http2.frameHeaderSize + present
    let fragment := wire.extract 0 size
    let decoded ← compareDecode s!"incomplete-payload/{present}" {} fragment
    expect (decoded.frames.isEmpty && decoded.buffered == fragment)
      s!"incomplete-payload/{present}: complete header/incomplete payload state changed"

private def testMultipleFramesWithResidue (complete : Array Http2.Frame)
    (completeWire nextWire : ByteArray) : IO Unit := do
  for residueSize in [0:nextWire.size] do
    let residue := nextWire.extract 0 residueSize
    let decoded ← compareDecode s!"multiple-with-residue/{residueSize}" {}
      (completeWire.append residue)
    expect (decoded.frames == complete && decoded.buffered == residue)
      s!"multiple-with-residue/{residueSize}: frame or residue parity changed"

def main : IO Unit := do
  let headers := frame .headers 1 (payloadOfSize 21 3) Http2.FrameFlag.endHeaders
  let data := frame .data 1 (payloadOfSize 128 11) Http2.FrameFlag.endStream
  let trailers := frame .headers 1 (payloadOfSize 13 19)
    (Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream])
  let unary := #[headers, data, trailers]
  let unknown := frame (.unknown 0xc8) 17 (payloadOfSize 7 23) 0xa5
  let next := frame .data 3 (payloadOfSize 4 29)

  let headersWire ← encodeFrame headers
  let dataWire ← encodeFrame data
  let unaryWire ← encodeFrames unary
  let unknownWire ← encodeFrame unknown
  let nextWire ← encodeFrame next

  validateAllSplits "headers" headersWire #[headers]
  validateAllSplits "data-128" dataWire #[data]
  validateAllSplits "unary-three-frame" unaryWire unary
  validateAllSplits "unknown-type" unknownWire #[unknown]
  testIncompleteHeaders dataWire
  testIncompletePayloads dataWire data.payload.size
  testMultipleFramesWithResidue unary unaryWire nextWire

  IO.println <| "HTTP/2 frame-header decode differential passed: " ++
    s!"all_splits={headersWire.size + dataWire.size + unaryWire.size + unknownWire.size + 4} " ++
    s!"short_headers={Http2.frameHeaderSize} incomplete_payloads={data.payload.size} " ++
    s!"multi_frame_residues={nextWire.size}"
