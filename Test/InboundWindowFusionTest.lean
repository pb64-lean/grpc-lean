import Grpc

open Grpc

namespace Grpc.Http2.Connection.InboundWindowFusionTest

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    throw (IO.userError message)

private def payloadOfSize (size : Nat) (seed : Nat := 0) : ByteArray := Id.run do
  let mut payload := ByteArray.empty
  for index in [0:size] do
    payload := payload.push (UInt8.ofNat (index * 37 + seed))
  pure payload

private def dataFrame (streamId size : Nat) (flags : UInt8 := 0) : Frame := {
  header := {
    length := size
    frameType := .data
    flags := flags
    streamId := streamId
  }
  payload := payloadOfSize size streamId
}

private def inboundPairs (state : State) : Array (Nat × Nat) :=
  state.inboundStreamWindows.map fun entry => (entry.streamId, entry.window)

private def streamFramePairs (state : State) : Array (Nat × Array Frame) :=
  state.streams.map fun stream => (stream.streamId, stream.frames)

/- Keep unrelated, equality-friendly state in the differential comparison.  The
fusion is allowed to alter only the two receive-window fields; including these
sentinels catches an accidental broad record reconstruction at the public seam. -/
private structure StateProjection where
  closing : Bool
  prefaceReceived : Bool
  clientSettingsReceived : Bool
  prefaceBuffer : ByteArray
  decoderBuffered : ByteArray
  decoderFrames : Array Frame
  hpackDynamic : Array Header
  hpackMaxSize : Nat
  outboundHpackDynamic : Array Header
  outboundHpackMaxSize : Nat
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
  streams : Array (Nat × Array Frame)
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

private def projectState (state : State) : StateProjection := {
  closing := state.closing
  prefaceReceived := state.prefaceReceived
  clientSettingsReceived := state.clientSettingsReceived
  prefaceBuffer := state.prefaceBuffer
  decoderBuffered := state.decoder.buffered
  decoderFrames := state.decoder.frames
  hpackDynamic := state.hpack.dynamic
  hpackMaxSize := state.hpack.maxSize
  outboundHpackDynamic := state.outboundHpack.dynamic
  outboundHpackMaxSize := state.outboundHpack.maxSize
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
  inboundStreamWindows := inboundPairs state
  outboundStreamWindows := state.outboundStreamWindows.map fun entry =>
    (entry.streamId, entry.window)
  pendingOutbound := state.pendingOutbound
  streams := streamFramePairs state
  ignoredInboundStreams := state.ignoredInboundStreams
  resetInboundStreams := state.resetInboundStreams
  resetHeaderBlock := state.resetHeaderBlock
  refusedInboundStreams := state.refusedInboundStreams
  activeRequestStreamIds := state.activeRequestStreams.map fun stream => stream.streamId
  activeDispatchStreamIds := state.activeDispatches.map fun dispatch => dispatch.streamId
  activeAuthorizationStreamIds := state.activeAuthorizations.map fun authorization =>
    authorization.streamId
  pendingDispatchPublications := state.pendingDispatchPublications
  pendingKeepalivePing := state.pendingKeepalivePing
  deadlineSchedulerPresent := state.deadlineScheduler.isSome
}

private def stateWith (connectionWindow initialStreamWindow : Nat)
    (windows : Array InboundStreamWindow) : State := {
  (initialState (some 13) (some 2048) initialStreamWindow) with
  closing := true
  prefaceReceived := true
  clientSettingsReceived := true
  prefaceBuffer := payloadOfSize 3 0x50
  decoder := {
    buffered := payloadOfSize 4 0x44
    frames := #[dataFrame 91 1]
  }
  hpack := {
    dynamic := #[Header.of "x-inbound-window-sentinel" "keep"]
    maxSize := 31
    maxAllowedSize := 63
    pendingSizeUpdate := some 7
  }
  outboundHpack := {
    dynamic := #[Header.of "x-outbound-window-sentinel" "keep"]
    maxSize := 17
    maxAllowedSize := 33
    pendingSizeUpdate := some 5
  }
  lastClientStreamId := 91
  outboundGoAwayLastStreamId := some 89
  outboundConnectionWindow := 777
  outboundInitialStreamWindow := 555
  outboundMaxFramePayloadLength := 8192
  inboundMaxFramePayloadLength := 4096
  inboundConnectionWindow := connectionWindow
  inboundStreamWindows := windows
  outboundStreamWindows := #[{ streamId := 91, window := (444 : Int) }]
  pendingOutbound := #[dataFrame 91 2]
  ignoredInboundStreams := #[81, 83]
  resetInboundStreams := #[85]
  resetHeaderBlock := some (dataFrame 85 1)
  refusedInboundStreams := #[87]
  pendingDispatchPublications := #[91, 93]
  pendingKeepalivePing := some (payloadOfSize 8 0x60)
}

private def compareWindowTransition (label : String) (state : State) (frame : Frame) :
    IO (Except Status State) := do
  let reference :=
    TestSupport.consumeAndReplenishInboundDataWindowReferenceForBenchmark state frame
  let candidate :=
    TestSupport.consumeAndReplenishInboundDataWindowCandidateForBenchmark state frame
  match reference, candidate with
  | .ok reference, .ok candidate =>
      expect (decide (projectState reference = projectState candidate))
        s!"{label}: fused receive-window state differs from the former composition"
      pure (.ok candidate)
  | .error reference, .error candidate =>
      expect (reference == candidate)
        s!"{label}: fused receive-window error differs from the former composition"
      pure (.error candidate)
  | .ok _, .error status =>
      throw (IO.userError s!"{label}: candidate rejected reference success: {status.messageD}")
  | .error status, .ok _ =>
      throw (IO.userError s!"{label}: candidate accepted reference error: {status.messageD}")

private def expectSuccess (label : String) (state : State) (frame : Frame)
    (expectedWindows : Array (Nat × Nat)) : IO State := do
  match ← compareWindowTransition label state frame with
  | .error status =>
      throw (IO.userError s!"{label}: unexpected error: {status.messageD}")
  | .ok result =>
      expect (result.inboundConnectionWindow == state.inboundConnectionWindow)
        s!"{label}: the immediate connection credit was not restored"
      expect (inboundPairs result == expectedWindows)
        s!"{label}: unexpected restored stream-window ordering/value"
      pure result

private def expectError (label : String) (state : State) (frame : Frame)
    (expectedMessage : String) : IO Unit := do
  match ← compareWindowTransition label state frame with
  | .ok _ => throw (IO.userError s!"{label}: expected an error")
  | .error status =>
      expect (status.code == .internal && status.messageD == expectedMessage)
        s!"{label}: wrong exact flow-control error: {repr status}"

private def deepWindows : Array InboundStreamWindow := Id.run do
  let mut windows := #[]
  for index in [0:64] do
    windows := windows.push {
      streamId := index * 2 + 3
      window := index + 20
    }
  pure (windows.push { streamId := 1, window := 97 })

private unsafe def testDifferentialWindowCorpus : IO Unit := do
  let duplicateZero := #[
    { streamId := 1, window := 0 },
    { streamId := 3, window := 7 },
    { streamId := 1, window := 11 }
  ]
  let zeroState := stateWith 0 0 duplicateZero
  let zeroResult ← expectSuccess "zero-size/duplicates" zeroState (dataFrame 1 0)
    (inboundPairs zeroState)
  expect (decide (projectState zeroResult = projectState zeroState))
    "zero-size DATA must leave every projected state field unchanged"
  expect (ptrEq zeroState zeroResult)
    "zero-size DATA must return the exact input state object"

  discard <| expectSuccess "exact-bounds/absent"
    (stateWith 4 4 #[{ streamId := 3, window := 19 }]) (dataFrame 1 4)
    #[(3, 19), (1, 4)]

  discard <| expectSuccess "exact-bounds/present"
    (stateWith 4 99 #[
      { streamId := 3, window := 19 },
      { streamId := 1, window := 4 },
      { streamId := 5, window := 23 }
    ]) (dataFrame 1 4) #[(3, 19), (5, 23), (1, 4)]

  let deepExpected := (deepWindows.extract 0 64).map fun entry =>
    (entry.streamId, entry.window)
  discard <| expectSuccess "present/depth-64" (stateWith 128 128 deepWindows)
    (dataFrame 1 17) (deepExpected.push (1, 97))

  discard <| expectSuccess "duplicate-targets/first-value-wins"
    (stateWith 32 99 #[
      { streamId := 1, window := 9 },
      { streamId := 3, window := 8 },
      { streamId := 1, window := 27 },
      { streamId := 5, window := 7 },
      { streamId := 1, window := 31 }
    ]) (dataFrame 1 4) #[(3, 8), (5, 7), (1, 9)]

  expectError "connection-overrun-precedes-stream-overrun"
    (stateWith 2 1 #[{ streamId := 1, window := 1 }]) (dataFrame 1 3)
    "HTTP/2 DATA frame exceeds connection flow-control window"
  expectError "present-stream-overrun"
    (stateWith 10 99 #[{ streamId := 1, window := 2 }]) (dataFrame 1 3)
    "HTTP/2 DATA frame exceeds stream flow-control window"
  expectError "absent-stream-overrun"
    (stateWith 10 2 #[{ streamId := 3, window := 99 }]) (dataFrame 1 3)
    "HTTP/2 DATA frame exceeds stream flow-control window"
  expectError "duplicate-first-overrun-despite-later-credit"
    (stateWith 10 99 #[
      { streamId := 1, window := 2 },
      { streamId := 3, window := 7 },
      { streamId := 1, window := 9 }
    ]) (dataFrame 1 3)
    "HTTP/2 DATA frame exceeds stream flow-control window"

private def unaryMethod : MethodName := {
  service := "acme.widgets.InboundWindowFusion"
  method := "Unary"
}

private def registeredEntry : IO MethodEntry := do
  let registry := Registry.empty.registerUnary unaryMethod fun request =>
    pure { data := request.data, status := Status.ok }
  match registry.findEntry? unaryMethod with
  | some entry => pure entry
  | none => throw (IO.userError "focused unary entry was not registered")

private def headersFrame : Frame := {
  header := {
    length := 0
    frameType := .headers
    flags := FrameFlag.endHeaders
    streamId := 1
  }
}

private def unaryState (entry : MethodEntry) : State := {
  (stateWith 16 16 #[
    { streamId := 3, window := 12 },
    { streamId := 1, window := 9 },
    { streamId := 5, window := 11 },
    { streamId := 1, window := 27 }
  ]) with
  closing := false
  pendingOutbound := #[]
  streams := #[{
    streamId := 1
    frames := #[headersFrame]
    requestMetadata := some Metadata.empty
    requestPreflight := some {
      method := unaryMethod
      timeout := none
      contentLength := none
      requestUsesGzip := false
      clientAcceptsGzip := false
    }
    authorizedEntry? := some entry
  }]
  ignoredInboundStreams := #[]
  resetInboundStreams := #[]
  resetHeaderBlock := none
  refusedInboundStreams := #[]
  pendingDispatchPublications := #[]
}

private def expectUnaryOk (label : String)
    (result : Except Status (State × SharedFrameResult)) : IO (State × SharedFrameResult) := do
  match result with
  | .ok result => pure result
  | .error status => throw (IO.userError s!"{label}: {status.messageD}")

private def testUnaryNonterminalAndDetach : IO Unit := do
  let entry ← registeredEntry
  let nonterminalPayload := payloadOfSize 3 0x31
  let nonterminalFrame : Frame := {
    header := {
      length := nonterminalPayload.size
      frameType := .data
      streamId := 1
    }
    payload := nonterminalPayload
  }
  let (buffered, bufferedResult) ← expectUnaryOk "nonterminal unary DATA"
    (processUnaryRequestData (unaryState entry) nonterminalFrame)
  expect bufferedResult.detached.isNone
    "nonterminal unary DATA unexpectedly detached the request"
  expect (bufferedResult.emitted.size == 2)
    "nonterminal unary DATA did not emit both immediate WINDOW_UPDATE frames"
  expect (buffered.inboundConnectionWindow == 16)
    "nonterminal unary DATA did not restore connection credit"
  expect (inboundPairs buffered == #[(3, 12), (5, 11), (1, 9)])
    "nonterminal unary DATA did not restore the first stream credit and collapse duplicates"
  let some retained := buffered.streams.find? fun stream => stream.streamId == 1
    | throw (IO.userError "nonterminal unary DATA removed its stream")
  expect (retained.frames.size == 2 && retained.frames[1]!.payload == nonterminalPayload)
    "nonterminal unary DATA did not append the exact body frame"
  expect buffered.pendingDispatchPublications.isEmpty
    "nonterminal unary DATA published a detached-dispatch ownership token"

  let terminalPayload := payloadOfSize 5 0x71
  let terminalFrame : Frame := {
    header := {
      length := terminalPayload.size
      frameType := .data
      flags := FrameFlag.endStream
      streamId := 1
    }
    payload := terminalPayload
  }
  let (detachedState, detachedResult) ← expectUnaryOk "terminal unary DATA"
    (processUnaryRequestData (unaryState entry) terminalFrame)
  expect (detachedResult.emitted.size == 2)
    "terminal unary DATA did not emit both immediate WINDOW_UPDATE frames"
  expect detachedState.streams.isEmpty
    "terminal unary DATA retained its buffered stream after detach"
  expect (inboundPairs detachedState == #[(3, 12), (5, 11)])
    "terminal unary DATA did not retire every duplicate receive-window entry"
  expect (detachedState.pendingDispatchPublications == #[1])
    "terminal unary DATA did not publish exactly one detach ownership token"
  match detachedResult.detached with
  | none => throw (IO.userError "terminal unary DATA did not detach a request")
  | some detached =>
      expect (detached.request.streamId == 1 && detached.request.body == terminalPayload)
        "terminal unary DATA changed the detached stream id or body"
      expect detached.request.authorizedEntry?.isSome
        "terminal unary DATA dropped its authorized handler"
      expect detached.request.preflight?.isSome
        "terminal unary DATA dropped its validated request preflight"

unsafe def run : IO Unit := do
  testDifferentialWindowCorpus
  testUnaryNonterminalAndDetach

end Grpc.Http2.Connection.InboundWindowFusionTest

unsafe def main : IO Unit :=
  Grpc.Http2.Connection.InboundWindowFusionTest.run
