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

structure StreamProjection where
  streamId : Nat
  frames : Array Frame
  requestMetadata : Option Metadata
  requestPreflight : Option Headers.RequestPreflight
  authorized : Bool
  endHeadersReceivedAt : Option Nat
  deadline : Option Nat
  deriving DecidableEq

/-- A deliberately explicit pure projection of connection state.  The outbound
queue is allowed to change only connection credit, stream credit, and the
pending queue, but retaining the surrounding fields here makes the
differential corpus catch accidental record-update damage as well.  Opaque IO
owners are represented by their ordered stream ids and scheduler presence. -/
structure StateProjection where
  closing : Bool
  prefaceReceived : Bool
  clientSettingsReceived : Bool
  prefaceBuffer : ByteArray
  decoderBuffered : ByteArray
  decoderFrames : Array Frame
  hpackDynamic : Array Header
  hpackMaxSize : Nat
  hpackMaxAllowedSize : Nat
  hpackPendingSizeUpdate : Option Nat
  outboundHpackDynamic : Array Header
  outboundHpackMaxSize : Nat
  outboundHpackMaxAllowedSize : Nat
  outboundHpackPendingSizeUpdate : Option Nat
  lastClientStreamId : Nat
  outboundGoAwayLastStreamId : Option Nat
  outboundConnectionWindow : Nat
  outboundInitialStreamWindow : Nat
  outboundMaxFramePayloadLength : Nat
  inboundMaxFramePayloadLength : Nat
  inboundConnectionWindow : Nat
  inboundInitialStreamWindow : Nat
  inboundMaxConcurrentStreams : Option Nat
  inboundMaxHeaderListSize : Option Nat
  inboundStreamWindows : Array (Nat × Nat)
  outboundStreamWindows : Array (Nat × Int)
  pendingOutbound : Array Frame
  streams : Array StreamProjection
  ignoredInboundStreams : Array Nat
  resetInboundStreams : Array Nat
  resetHeaderBlock : Option Frame
  refusedInboundStreams : Array Nat
  activeRequestStreamIds : Array Nat
  activeDispatchStreamIds : Array Nat
  activeAuthorizationStreamIds : Array Nat
  pendingDispatchPublications : Array Nat
  pendingKeepalivePing : Option ByteArray
  deadlineSchedulerPresent : Bool
  deriving DecidableEq

def projectStream (stream : StreamState) : StreamProjection := {
  streamId := stream.streamId
  frames := stream.frames
  requestMetadata := stream.requestMetadata
  requestPreflight := stream.requestPreflight
  authorized := stream.authorizedEntry?.isSome
  endHeadersReceivedAt := stream.endHeadersReceivedAt
  deadline := stream.deadline
}

def projectState (state : State) : StateProjection := {
  closing := state.closing
  prefaceReceived := state.prefaceReceived
  clientSettingsReceived := state.clientSettingsReceived
  prefaceBuffer := state.prefaceBuffer
  decoderBuffered := state.decoder.buffered
  decoderFrames := state.decoder.frames
  hpackDynamic := state.hpack.dynamic
  hpackMaxSize := state.hpack.maxSize
  hpackMaxAllowedSize := state.hpack.maxAllowedSize
  hpackPendingSizeUpdate := state.hpack.pendingSizeUpdate
  outboundHpackDynamic := state.outboundHpack.dynamic
  outboundHpackMaxSize := state.outboundHpack.maxSize
  outboundHpackMaxAllowedSize := state.outboundHpack.maxAllowedSize
  outboundHpackPendingSizeUpdate := state.outboundHpack.pendingSizeUpdate
  lastClientStreamId := state.lastClientStreamId
  outboundGoAwayLastStreamId := state.outboundGoAwayLastStreamId
  outboundConnectionWindow := state.outboundConnectionWindow
  outboundInitialStreamWindow := state.outboundInitialStreamWindow
  outboundMaxFramePayloadLength := state.outboundMaxFramePayloadLength
  inboundMaxFramePayloadLength := state.inboundMaxFramePayloadLength
  inboundConnectionWindow := state.inboundConnectionWindow
  inboundInitialStreamWindow := state.inboundInitialStreamWindow
  inboundMaxConcurrentStreams := state.inboundMaxConcurrentStreams
  inboundMaxHeaderListSize := state.inboundMaxHeaderListSize
  inboundStreamWindows := state.inboundStreamWindows.map fun entry =>
    (entry.streamId, entry.window)
  outboundStreamWindows := state.outboundStreamWindows.map fun entry =>
    (entry.streamId, entry.window)
  pendingOutbound := state.pendingOutbound
  streams := state.streams.map projectStream
  ignoredInboundStreams := state.ignoredInboundStreams
  resetInboundStreams := state.resetInboundStreams
  resetHeaderBlock := state.resetHeaderBlock
  refusedInboundStreams := state.refusedInboundStreams
  activeRequestStreamIds := state.activeRequestStreams.map (fun stream => stream.streamId)
  activeDispatchStreamIds := state.activeDispatches.map (fun dispatch => dispatch.streamId)
  activeAuthorizationStreamIds := state.activeAuthorizations.map (fun authorization =>
    authorization.streamId)
  pendingDispatchPublications := state.pendingDispatchPublications
  pendingKeepalivePing := state.pendingKeepalivePing
  deadlineSchedulerPresent := state.deadlineScheduler.isSome
}

/-- Populate unrelated fields with non-default sentinels so that a malformed
whole-state update cannot pass merely because all of those fields were empty. -/
def differentialStateWith (connectionWindow initialStreamWindow : Nat)
    (windows : Array OutboundStreamWindow := #[])
    (pending : Array Frame := #[]) : State := {
  (stateWith connectionWindow initialStreamWindow windows pending) with
  closing := true
  prefaceReceived := true
  clientSettingsReceived := true
  prefaceBuffer := bytes [0x50, 0x52, 0x45]
  decoder := {
    buffered := bytes [0x44, 0x45, 0x43]
    frames := #[frame .settings 0 (bytes [0x01])]
  }
  hpack := {
    dynamic := #[Header.of "x-inbound-sentinel" "keep"]
    maxSize := 31
    maxAllowedSize := 63
    pendingSizeUpdate := some 7
  }
  outboundHpack := {
    dynamic := #[Header.of "x-outbound-sentinel" "keep"]
    maxSize := 17
    maxAllowedSize := 33
    pendingSizeUpdate := some 5
  }
  lastClientStreamId := 91
  outboundGoAwayLastStreamId := some 89
  outboundMaxFramePayloadLength := 8192
  inboundMaxFramePayloadLength := 4096
  inboundConnectionWindow := 777
  inboundInitialStreamWindow := 555
  inboundMaxConcurrentStreams := some 13
  inboundMaxHeaderListSize := some 2048
  inboundStreamWindows := #[{ streamId := 91, window := 444 }]
  streams := #[{
    streamId := 91
    frames := #[headers 91]
    requestMetadata := some #[Header.of "x-stream-sentinel" "keep"]
    endHeadersReceivedAt := some 123
    deadline := some 456
  }]
  ignoredInboundStreams := #[81, 83]
  resetInboundStreams := #[85]
  resetHeaderBlock := some (frame .continuation 85 (bytes [0x52]))
  refusedInboundStreams := #[87]
  pendingDispatchPublications := #[91, 93]
  pendingKeepalivePing := some (bytes [0x50, 0x49, 0x4e, 0x47])
}

structure DifferentialCase where
  name : String
  state : State
  incoming : Array Frame

def controlFrames (count : Nat) : Array Frame :=
  (List.range count).foldl (init := #[]) fun controls index =>
    let frameType := if index % 2 == 0 then FrameType.ping else FrameType.settings
    controls.push (frame frameType 0 (bytes [index, index + 1]))

def differentialCases : List DifferentialCase := [
  {
    name := "empty pending and incoming"
    state := differentialStateWith 8 8
    incoming := #[]
  },
  {
    name := "pending-only control"
    state := differentialStateWith 8 8 #[] #[frame .ping 0 (bytes [1])]
    incoming := #[]
  },
  {
    name := "common HEADERS DATA trailers"
    state := differentialStateWith 20 20
    incoming := #[headers 1, data 1 (bytes [1, 2, 3]), headers 1 true]
  },
  {
    name := "sixty-four control frames"
    state := differentialStateWith 8 8
    incoming := controlFrames 64
  },
  {
    name := "ACK-bit controls and unknown extension"
    state := differentialStateWith 8 8 #[
      { streamId := 0, window := (3 : Int) },
      { streamId := 0, window := (5 : Int) },
      { streamId := 1, window := (7 : Int) }
    ]
    incoming := #[
      frame .settings 0 ByteArray.empty 0x1,
      frame .ping 0 (bytes [1, 2, 3, 4, 5, 6, 7, 8]) 0x1,
      frame (.unknown 0xfe) 0 (bytes [0xfe, 0xed]) 0x1
    ]
  },
  {
    name := "trailers followed by controls"
    state := differentialStateWith 8 8 #[{ streamId := 1, window := (8 : Int) }]
    incoming := #[headers 1, data 1 (bytes [4, 5]), headers 1 true] ++ controlFrames 8
  },
  {
    name := "exact-fit DATA"
    state := differentialStateWith 3 3 #[{ streamId := 1, window := (3 : Int) }]
    incoming := #[data 1 (bytes [6, 7, 8]) FrameFlag.endStream]
  },
  {
    name := "connection-partial DATA"
    state := differentialStateWith 2 8 #[{ streamId := 1, window := (8 : Int) }]
    incoming := #[data 1 (bytes [9, 10, 11, 12]) FrameFlag.endStream, headers 1 true]
  },
  {
    name := "stream-partial DATA"
    state := differentialStateWith 8 8 #[{ streamId := 1, window := (2 : Int) }]
    incoming := #[data 1 (bytes [13, 14, 15, 16]) FrameFlag.endStream, headers 1 true]
  },
  {
    name := "zero connection window blocks"
    state := differentialStateWith 0 8 #[{ streamId := 1, window := (8 : Int) }]
    incoming := #[data 1 (bytes [17]), headers 1 true]
  },
  {
    name := "zero stream window blocks"
    state := differentialStateWith 8 8 #[{ streamId := 1, window := (0 : Int) }]
    incoming := #[data 1 (bytes [18]), headers 1 true]
  },
  {
    name := "negative stream window blocks"
    state := differentialStateWith 8 8 #[{ streamId := 1, window := (-3 : Int) }]
    incoming := #[headers 1, data 1 (bytes [19]), headers 1 true]
  },
  {
    name := "zero-length DATA blocks at zero credit"
    state := differentialStateWith 0 8 #[{ streamId := 1, window := (8 : Int) }]
    incoming := #[data 1 ByteArray.empty, headers 1 true]
  },
  {
    name := "zero-length DATA emits at positive credit"
    state := differentialStateWith 1 1 #[{ streamId := 1, window := (1 : Int) }]
    incoming := #[data 1 ByteArray.empty, headers 1 true]
  },
  {
    name := "existing pending preserves FIFO"
    state := differentialStateWith 12 12
      #[{ streamId := 3, window := (12 : Int) }, { streamId := 1, window := (12 : Int) }]
      #[headers 3, data 3 (bytes [20, 21])]
    incoming := #[headers 1, data 1 (bytes [22, 23]), headers 1 true]
  },
  {
    name := "blocked existing pending retains incoming suffix"
    state := differentialStateWith 12 12
      #[{ streamId := 3, window := (0 : Int) }]
      #[data 3 (bytes [24])]
    incoming := controlFrames 4
  },
  {
    name := "mismatched exact DATA header length"
    state := differentialStateWith 2 2 #[{ streamId := 1, window := (2 : Int) }]
    incoming := #[data 1 (bytes [25, 26]) 0 (some 99)]
  },
  {
    name := "mismatched partial DATA header length"
    state := differentialStateWith 2 4 #[{ streamId := 1, window := (4 : Int) }]
    incoming := #[data 1 (bytes [27, 28, 29, 30]) FrameFlag.endStream (some 99)]
  },
  {
    name := "interleaved stream DATA"
    state := differentialStateWith 8 8 #[
      { streamId := 1, window := (4 : Int) },
      { streamId := 3, window := (4 : Int) }
    ]
    incoming := #[
      data 1 (bytes [31, 32]),
      data 3 (bytes [33, 34]),
      data 1 (bytes [35, 36]),
      data 3 (bytes [37, 38]),
      headers 1 true,
      headers 3 true
    ]
  },
  {
    name := "END_STREAM then same stream"
    state := differentialStateWith 3 2 #[{ streamId := 1, window := (1 : Int) }]
    incoming := #[
      data 1 (bytes [39]) FrameFlag.endStream,
      data 1 (bytes [40, 41]),
      headers 1 true
    ]
  },
  {
    name := "duplicate stream windows"
    state := differentialStateWith 8 8 #[
      { streamId := 1, window := (3 : Int) },
      { streamId := 1, window := (7 : Int) },
      { streamId := 3, window := (2 : Int) }
    ]
    incoming := #[data 1 (bytes [42, 43]), data 3 (bytes [44, 45])]
  },
  {
    name := "duplicate windows with END_STREAM reuse"
    state := differentialStateWith 3 2 #[
      { streamId := 1, window := (1 : Int) },
      { streamId := 1, window := (9 : Int) }
    ]
    incoming := #[
      data 1 (bytes [46]) FrameFlag.endStream,
      data 1 (bytes [47, 48]),
      headers 1 true
    ]
  }
]

def testDifferentialCorpus : IO Unit := do
  for testCase in differentialCases do
    let reference :=
      TestSupport.queueOutboundReferenceForBenchmark testCase.state testCase.incoming
    let candidate :=
      TestSupport.queueOutboundCandidateForBenchmark testCase.state testCase.incoming
    expect (decide (projectState reference.1 = projectState candidate.1))
      s!"outbound cursor state mismatch: {testCase.name}"
    expect (decide (reference.2 = candidate.2))
      s!"outbound cursor emitted-frame mismatch: {testCase.name}"

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

/-- A queue blocked before its first DATA frame must be returned by identity.
This guards the cursor boundary against turning the reference path's O(1)
backpressure result into a full `Array.extract 0 size` copy. -/
unsafe def testBlockedPendingIdentity : IO Unit := do
  let pending := #[
    data 1 (bytes [61, 62, 63]),
    headers 1 true,
    frame (.unknown 0xfe) 1 (bytes [64])
  ]
  let result := flushOutbound <|
    stateWith 0 8 #[{ streamId := 1, window := (8 : Int) }] pending
  expect result.2.isEmpty "zero-credit direct flush should emit no frames"
  expect (ptrEq pending result.1.pendingOutbound)
    "zero-credit direct flush should retain the original pending array"

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
  testDifferentialCorpus
  testNormalBatch
  testExactFit
  testOneByteShortConnection
  testOneByteShortStream
  testNegativeStreamWindow
  testZeroLengthData
  testBlockedPendingIdentity
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
