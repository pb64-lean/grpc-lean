import Grpc

open Grpc

namespace Test.DataFrames

def fail (message : String) : IO α :=
  throw (IO.userError message)

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do fail message

def payloadOfSize (size : Nat) : ByteArray :=
  (List.range size).foldl (fun payload value =>
    payload.push (UInt8.ofNat ((value * 37 + 11) % 251))) ByteArray.empty

def legacyDataFrame (streamId : Nat) (payload : ByteArray) : Http2.Frame := {
  header := {
    length := payload.size
    frameType := .data
    flags := 0
    streamId := streamId
  }
  payload := payload
}

/-- The pre-fast-path implementation, retained here as a differential oracle. -/
def legacyDataFrames (streamId : Nat) (payload : ByteArray) (maxSize : Nat) :
    Except Status (Array Http2.Frame) := do
  if maxSize == 0 then
    throw (Status.internal "HTTP/2 DATA frame max size must be positive")
  else
    pure <| Id.run do
      let mut frames := #[]
      let mut offset := 0
      while offset < payload.size do
        let stop := Nat.min payload.size (offset + maxSize)
        let chunk := payload.extract offset stop
        frames := frames.push (legacyDataFrame streamId chunk)
        offset := stop
      return frames

def sameResult (left right : Except Status (Array Http2.Frame)) : Bool :=
  match left, right with
  | .error left, .error right => left == right
  | .ok left, .ok right => left == right
  | _, _ => false

def joinedPayload (frames : Array Http2.Frame) : ByteArray :=
  frames.foldl (fun payload frame => payload.append frame.payload) ByteArray.empty

def testPositiveCase (size streamId maxSize : Nat) : IO Unit := do
  let payload := payloadOfSize size
  let actual := Http2.Transport.dataFrames streamId payload maxSize
  let expected := legacyDataFrames streamId payload maxSize
  let context := s!"size={size}, stream={streamId}, max={maxSize}"
  expect (sameResult actual expected) s!"{context}: result diverged from legacy splitter"
  match actual with
  | .error status => fail s!"{context}: unexpected error: {status.messageD}"
  | .ok frames =>
      let expectedCount := if size == 0 then 0 else (size + maxSize - 1) / maxSize
      expect (frames.size == expectedCount) s!"{context}: wrong frame count"
      for frame in frames do
        expect (frame.header.frameType == .data) s!"{context}: emitted a non-DATA frame"
        expect (frame.header.flags == 0) s!"{context}: emitted unexpected DATA flags"
        expect (frame.header.streamId == streamId) s!"{context}: changed the stream id"
        expect (frame.header.length == frame.payload.size)
          s!"{context}: frame header length disagrees with its payload"
        expect (frame.payload.size > 0) s!"{context}: emitted an empty DATA chunk"
        expect (frame.payload.size <= maxSize) s!"{context}: chunk exceeds max size"
      expect (joinedPayload frames == payload) s!"{context}: framing changed the payload"

/-- Native-runtime contract for the allocation-eliding branch itself. -/
unsafe def testExactFitReusesPayload : IO Unit := do
  let maxSize := Http2.defaultMaxFramePayloadLength
  let payload := payloadOfSize maxSize
  match Http2.Transport.dataFrames Http2.maxStreamId payload maxSize with
  | .error status => fail s!"exact-fit reuse: unexpected error: {status.messageD}"
  | .ok frames =>
      expect (frames.size == 1) "exact-fit reuse: expected one DATA frame"
      expect (ptrEq payload frames[0]!.payload)
        "exact-fit reuse: DATA frame did not retain the original ByteArray"

def testBoundaryMatrix : IO Unit := do
  let maxSize := Http2.defaultMaxFramePayloadLength
  let cases : List (Nat × Nat) := [
    (0, 1),
    (1, 3),
    (maxSize - 1, 7),
    (maxSize, 11),
    (maxSize + 1, 13),
    (2 * maxSize, 17),
    (2 * maxSize + 1, Http2.maxStreamId)
  ]
  for (size, streamId) in cases do
    testPositiveCase size streamId maxSize

def testZeroMax : IO Unit := do
  let cases : List (Nat × Nat) := [
    (0, 1),
    (1, 3),
    (Http2.defaultMaxFramePayloadLength + 1, Http2.maxStreamId)
  ]
  for (size, streamId) in cases do
    let payload := payloadOfSize size
    let actual := Http2.Transport.dataFrames streamId payload 0
    let expected := legacyDataFrames streamId payload 0
    let context := s!"zero max, size={size}, stream={streamId}"
    expect (sameResult actual expected) s!"{context}: result diverged from legacy splitter"
    match actual with
    | .ok _ => fail s!"{context}: expected an internal error"
    | .error status =>
        expect (status.code == .internal) s!"{context}: wrong status code"
        expect (status.messageD == "HTTP/2 DATA frame max size must be positive")
          s!"{context}: wrong status message"

unsafe def main : IO Unit := do
  testBoundaryMatrix
  testZeroMax
  testExactFitReusesPayload
  IO.println "DATA frame fast-path differential tests passed"

end Test.DataFrames

unsafe def main : IO Unit :=
  Test.DataFrames.main
