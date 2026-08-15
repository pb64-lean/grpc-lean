import Grpc

open Grpc

namespace Grpc.Http2.Connection.OutboundQueueTest

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

def expectStatusOk (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def bytes (values : List Nat) : ByteArray :=
  values.foldl (fun out value => out.push (UInt8.ofNat value)) ByteArray.empty

def frame (frameType : FrameType) (streamId : Nat) (payload : ByteArray := ByteArray.empty)
    (flags : UInt8 := 0) (length : Option Nat := none) : Frame := {
  header := {
    length := length.getD payload.size
    frameType := frameType
    flags := flags
    streamId := streamId
  }
  payload := payload
}

def data (streamId : Nat) (payload : ByteArray) (flags : UInt8 := 0)
    (length : Option Nat := none) : Frame :=
  frame .data streamId payload flags length

def headers (streamId : Nat) (endStream : Bool := false) : Frame :=
  frame .headers streamId (bytes [streamId, 0x48])
    (if endStream then FrameFlag.endStream else 0)

def stateWith (connectionWindow initialStreamWindow : Nat)
    (windows : Array OutboundStreamWindow := #[])
    (pending : Array Frame := #[]) : State := {
  ({} : State) with
  outboundConnectionWindow := connectionWindow
  outboundInitialStreamWindow := initialStreamWindow
  outboundStreamWindows := windows
  pendingOutbound := pending
}

def testNormalBatch : IO Unit := do
  let payload := bytes [1, 2, 3]
  let frames := #[headers 1, data 1 payload, headers 1 true]
  let result := queueOutbound (stateWith 20 20) frames
  expect (decide (result.2 = frames))
    "normal batch should emit the ordered batch without changing frame contents"
  expect result.1.pendingOutbound.isEmpty "normal batch should leave no pending frames"
  expect (result.1.outboundConnectionWindow == 17)
    "normal batch should debit exactly its DATA bytes"
  expect result.1.outboundStreamWindows.isEmpty
    "terminal response headers should retire the stream window"

unsafe def testExactFit : IO Unit := do
  let payload := bytes [4, 5, 6]
  let frames := #[headers 1, data 1 payload, headers 1 true]
  let state := stateWith 3 3 #[{ streamId := 1, window := (3 : Int) }]
  let result := queueOutbound state frames
  expect (result.1.outboundConnectionWindow == 0)
    "exact-fit DATA should consume all connection credit"
  expect result.1.pendingOutbound.isEmpty "exact-fit DATA should not be buffered"
  expect result.1.outboundStreamWindows.isEmpty
    "exact-fit terminal batch should clean up its stream window"
  expect (ptrEq payload result.2[1]!.payload)
    "exact-fit DATA should retain the original payload allocation"

def testOneByteShortConnection : IO Unit := do
  let payload := bytes [7, 8, 9]
  let frames := #[headers 1, data 1 payload FrameFlag.endStream]
  let state := stateWith 2 3 #[{ streamId := 1, window := (3 : Int) }]
  let result := queueOutbound state frames
  expect (result.2.size == 2) "connection-limited batch should emit HEADERS and a DATA prefix"
  expect (result.2[1]!.payload.size == 2)
    "connection-limited DATA prefix should consume exactly available credit"
  expect (!FrameFlag.has result.2[1]!.header.flags FrameFlag.endStream)
    "a partial connection-limited DATA prefix must not end the stream"
  expect (result.1.pendingOutbound.size == 1)
    "connection-limited batch should retain exactly its DATA suffix"
  expect (FrameFlag.has result.1.pendingOutbound[0]!.header.flags FrameFlag.endStream)
    "the queued connection-limited DATA suffix must retain END_STREAM"

  let update ← expectStatusOk (WindowUpdate.frame 0 1)
  let processed ← processFrame Registry.empty result.1 update
  let flushed ← expectStatusOk processed
  expect (flushed.2.size == 1)
    "connection WINDOW_UPDATE should emit the terminal DATA suffix"
  expect (FrameFlag.has flushed.2[0]!.header.flags FrameFlag.endStream)
    "the final connection-limited DATA suffix must end the stream"
  expect flushed.1.pendingOutbound.isEmpty
    "connection WINDOW_UPDATE should drain the terminal DATA suffix"
  expect flushed.1.outboundStreamWindows.isEmpty
    "terminal DATA suffix should clean up stream state after connection credit"

def testOneByteShortStream : IO Unit := do
  let payload := bytes [10, 11, 12]
  let frames := #[headers 1, data 1 payload FrameFlag.endStream]
  let state := stateWith 3 3 #[{ streamId := 1, window := (2 : Int) }]
  let result := queueOutbound state frames
  expect (result.2.size == 2) "stream-limited batch should emit HEADERS and a DATA prefix"
  expect (result.2[1]!.payload.size == 2)
    "stream-limited DATA prefix should consume exactly available credit"
  expect (!FrameFlag.has result.2[1]!.header.flags FrameFlag.endStream)
    "a partial stream-limited DATA prefix must not end the stream"
  expect (result.1.pendingOutbound.size == 1)
    "stream-limited batch should retain exactly its DATA suffix"
  expect (FrameFlag.has result.1.pendingOutbound[0]!.header.flags FrameFlag.endStream)
    "the queued stream-limited DATA suffix must retain END_STREAM"

  let update ← expectStatusOk (WindowUpdate.frame 1 1)
  let processed ← processFrame Registry.empty result.1 update
  let flushed ← expectStatusOk processed
  expect (flushed.2.size == 1)
    "stream WINDOW_UPDATE should emit the terminal DATA suffix"
  expect (FrameFlag.has flushed.2[0]!.header.flags FrameFlag.endStream)
    "the final stream-limited DATA suffix must end the stream"
  expect flushed.1.pendingOutbound.isEmpty
    "stream WINDOW_UPDATE should drain the terminal DATA suffix"
  expect flushed.1.outboundStreamWindows.isEmpty
    "terminal DATA suffix should clean up stream state after stream credit"

def testNegativeStreamWindow : IO Unit := do
  let frames := #[headers 1, data 1 (bytes [13]), headers 1 true]
  let state := stateWith 5 5 #[{ streamId := 1, window := (-1 : Int) }]
  let result := queueOutbound state frames
  expect (result.2.size == 1) "negative stream debt should stop before DATA"
  expect (result.2[0]!.header.frameType == .headers)
    "negative stream debt should preserve the leading HEADERS"
  expect (result.1.pendingOutbound.size == 2)
    "negative stream debt should preserve DATA-before-trailers ordering"

def testZeroLengthData : IO Unit := do
  let zeroData := data 1 ByteArray.empty
  let frames := #[zeroData, headers 1 true]
  let zeroResult := queueOutbound
    (stateWith 0 1 #[{ streamId := 1, window := (1 : Int) }]) frames
  expect zeroResult.2.isEmpty "zero-length DATA must retain zero-window blocking"
  expect (zeroResult.1.pendingOutbound.size == 2)
    "blocked zero-length DATA should retain following trailers"

  let positiveResult := queueOutbound
    (stateWith 1 1 #[{ streamId := 1, window := (1 : Int) }]) frames
  expect (positiveResult.2.size == 2)
    "zero-length DATA with positive credit should emit with its trailers"
  expect (positiveResult.1.outboundConnectionWindow == 1)
    "zero-length DATA should not debit positive connection credit"
  expect positiveResult.1.outboundStreamWindows.isEmpty
    "terminal headers after zero-length DATA should clean up the stream"

def testExistingPendingOrdering : IO Unit := do
  let pending := data 3 (bytes [21])
  let incoming := #[headers 1, data 1 (bytes [22]), headers 1 true]
  let state := stateWith 8 8
    #[{ streamId := 3, window := (8 : Int) }, { streamId := 1, window := (8 : Int) }]
    #[pending]
  let result := queueOutbound state incoming
  expect (result.2.size == 4) "existing pending frame and incoming batch should all emit"
  expect (decide (result.2[0]! = pending))
    "new frames must never leapfrog an existing pending frame"

def testLaterDataBlocksAfterEarlierEmission : IO Unit := do
  let first := data 1 (bytes [23])
  let blocked := data 1 (bytes [24])
  let frames := #[first, blocked, headers 1 true]
  let state := stateWith 3 1 #[{ streamId := 1, window := (1 : Int) }]
  let result := queueOutbound state frames
  expect (result.2.size == 1)
    "queue flush should emit the first DATA before the blocked DATA"
  expect (decide (result.2[0]! = first))
    "queue flush should preserve the original DATA ordering"
  expect (result.1.outboundConnectionWindow == 2)
    "the emitted first DATA frame should be debited exactly once"
  expect (result.1.pendingOutbound.size == 2)
    "blocked DATA and its trailers should remain queued"

def testMultipleAndInterleavedData : IO Unit := do
  let sameStream := #[
    data 1 (bytes [31, 32]),
    data 1 (bytes [33, 34, 35]),
    headers 1 true
  ]
  let sameResult := queueOutbound
    (stateWith 5 5 #[{ streamId := 1, window := (5 : Int) }]) sameStream
  expect (sameResult.1.outboundConnectionWindow == 0)
    "multiple exact-fit DATA frames should debit their cumulative size"
  expect sameResult.1.outboundStreamWindows.isEmpty
    "multiple DATA terminal batch should clean up its stream"

  let interleaved := #[
    data 1 (bytes [41, 42]),
    data 3 (bytes [43, 44]),
    headers 1 true,
    headers 3 true
  ]
  let interleavedResult := queueOutbound (stateWith 4 4 #[
      { streamId := 1, window := (2 : Int) },
      { streamId := 3, window := (2 : Int) }
    ]) interleaved
  expect (interleavedResult.1.outboundConnectionWindow == 0)
    "interleaved DATA should share connection credit exactly"
  expect interleavedResult.1.outboundStreamWindows.isEmpty
    "terminal interleaved streams should both be retired"

def testDataEndStreamCleanup : IO Unit := do
  let terminalData := data 1 (bytes [51, 52]) FrameFlag.endStream
  let result := queueOutbound
    (stateWith 2 2 #[{ streamId := 1, window := (2 : Int) }]) #[terminalData]
  expect (result.2.size == 1) "terminal exact-fit DATA should emit"
  expect result.1.outboundStreamWindows.isEmpty
    "DATA END_STREAM should retire its outbound stream window"

def testEndStreamThenSameStreamUsesInitialWindow : IO Unit := do
  let terminal := data 1 (bytes [53]) FrameFlag.endStream
  let later := data 1 (bytes [54, 55])
  let frames := #[terminal, later, headers 1 true]
  let state := stateWith 3 2 #[{ streamId := 1, window := (1 : Int) }]
  let result := queueOutbound state frames
  expect (result.2.size == 3)
    "later same-stream DATA should use the initial window after END_STREAM cleanup"
  expect (result.1.outboundConnectionWindow == 0)
    "END_STREAM cleanup must not lose or duplicate later connection-window debit"
  expect result.1.outboundStreamWindows.isEmpty
    "the later terminal headers should retire the recreated stream window"

def testMismatchedHeaderNormalization : IO Unit := do
  let malformed := data 1 (bytes [61, 62]) 0 (some 99)
  let result := queueOutbound
    (stateWith 2 2 #[{ streamId := 1, window := (2 : Int) }]) #[malformed]
  expect (result.2.size == 1) "mismatched internal DATA should still be emitted"
  expect (result.2[0]!.header.length == 2)
    "the flush path should normalize a mismatched DATA header length"
  expect (result.2[0]!.payload.size == 2)
    "header normalization should preserve the complete exact-fit payload"

unsafe def main : IO Unit := do
  testNormalBatch
  testExactFit
  testOneByteShortConnection
  testOneByteShortStream
  testNegativeStreamWindow
  testZeroLengthData
  testExistingPendingOrdering
  testLaterDataBlocksAfterEarlierEmission
  testMultipleAndInterleavedData
  testDataEndStreamCleanup
  testEndStreamThenSameStreamUsesInitialWindow
  testMismatchedHeaderNormalization
  IO.println "outbound queue and flow-control tests passed"

end Grpc.Http2.Connection.OutboundQueueTest

unsafe def main : IO Unit :=
  Grpc.Http2.Connection.OutboundQueueTest.main
