import Grpc

/-!
# HTTP/2 unary inbound-window round-trip differential benchmark

The reference seam performs the former unary DATA receive-window debit and
matching refund.  The candidate seam validates the same bounds but writes the
canonical stream-window entry only once.  An opaque selector chooses one
`noinline` seam before either scaling loop, leaving the loop with the same
indirect call and error-unwrapping shape in both modes.

Every successful output state becomes the next iteration's input.  The
depth-48 fixtures cycle target ids chosen from the current first or middle
position, or repeatedly choose the last position, so the lookup position and
array depth remain stable instead of benchmarking independent disposable
states.  Fixed preflight compares complete pure projections and exact errors
over zero, absent, present, duplicate, exact-bound, and invalid-bound cases.

This executable reports no wall time.  It is intended for whole-process
`perf stat` instruction and branch counters: construction, exact semantic
preflight, selector creation, requested warmup, and output are fixed process
work; only the selected recurrence scales with `iterations`.
-/

namespace Grpc.Http2.InboundWindowRoundTripBenchmarkHarness

open Connection

private abbrev WindowRoundTrip := State → Frame → Except Status State

private inductive Mode where
  | reference
  | candidate

private structure WindowRoundTripBox where
  run : WindowRoundTrip
  /-- Preserve observable selector metadata across the opaque boundary. -/
  candidateSelected : Bool

/-- Select once; neither a `Mode` value nor a mode branch enters the recurrence. -/
@[noinline] private opaque selectWindowRoundTripBox (mode : Mode) : WindowRoundTripBox :=
  match mode with
  | .reference => {
      run := Connection.TestSupport.consumeAndReplenishInboundDataWindowReferenceForBenchmark
      candidateSelected := false
    }
  | .candidate => {
      run := Connection.TestSupport.consumeAndReplenishInboundDataWindowCandidateForBenchmark
      candidateSelected := true
    }

private def bytes (size seed : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for index in [0:size] do
    result := result.push (UInt8.ofNat ((index * 131 + seed * 29 + 17) % 251))
  return result

private def dataFrame (streamId size : Nat) : Frame :=
  let payload := bytes size (streamId + size)
  {
    header := {
      length := payload.size
      frameType := .data
      flags := 0
      streamId
    }
    payload
  }

private def window (streamId value : Nat) : InboundStreamWindow := {
  streamId
  window := value
}

private def windowsOfDepth (depth value : Nat) : Array InboundStreamWindow :=
  (Array.range depth).map fun index => window (index * 2 + 1) value

/-- Sentinels make whole-record projection catch accidental damage outside the
three fields the round trip is allowed to inspect or rewrite. -/
private def stateWith (connectionWindow initialStreamWindow : Nat)
    (windows : Array InboundStreamWindow) : State := {
  (default : State) with
  closing := true
  prefaceReceived := true
  clientSettingsReceived := true
  prefaceBuffer := bytes 3 11
  decoder := {
    buffered := bytes 4 13
    frames := #[dataFrame 77 3]
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
    maxAllowedSize := 29
    pendingSizeUpdate := some 5
  }
  lastClientStreamId := 97
  outboundGoAwayLastStreamId := some 95
  outboundConnectionWindow := 31337
  outboundInitialStreamWindow := 8192
  outboundMaxFramePayloadLength := 16385
  inboundMaxFramePayloadLength := 16386
  inboundConnectionWindow := connectionWindow
  inboundInitialStreamWindow := initialStreamWindow
  inboundMaxConcurrentStreams := some 47
  inboundMaxHeaderListSize := some 65537
  inboundStreamWindows := windows
  ignoredInboundStreams := #[71, 73]
  resetInboundStreams := #[75]
  refusedInboundStreams := #[79, 81]
  pendingDispatchPublications := #[83]
  pendingKeepalivePing := some (bytes 8 19)
}

private structure StreamProjection where
  streamId : Nat
  frames : Array Frame
  requestMetadata : Option Metadata
  requestPreflight : Option Headers.RequestPreflight
  authorized : Bool
  endHeadersReceivedAt : Option Nat
  deadline : Option Nat
  deriving DecidableEq

/-- Complete pure projection of `State`; opaque IO owners retain ordered ids
and scheduler presence. -/
private structure StateProjection where
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

private def projectStream (stream : StreamState) : StreamProjection := {
  streamId := stream.streamId
  frames := stream.frames
  requestMetadata := stream.requestMetadata
  requestPreflight := stream.requestPreflight
  authorized := stream.authorizedEntry?.isSome
  endHeadersReceivedAt := stream.endHeadersReceivedAt
  deadline := stream.deadline
}

private def projectState (state : State) : StateProjection := {
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
  activeRequestStreamIds := state.activeRequestStreams.map fun stream => stream.streamId
  activeDispatchStreamIds := state.activeDispatches.map fun dispatch => dispatch.streamId
  activeAuthorizationStreamIds := state.activeAuthorizations.map fun authorization =>
    authorization.streamId
  pendingDispatchPublications := state.pendingDispatchPublications
  pendingKeepalivePing := state.pendingKeepalivePing
  deadlineSchedulerPresent := state.deadlineScheduler.isSome
}

private def projectResult : Except Status State → Except Status StateProjection
  | .error status => .error status
  | .ok state => .ok (projectState state)

private def sameProjectedResult
    (left right : Except Status StateProjection) : Bool :=
  match left, right with
  | .error leftStatus, .error rightStatus => decide (leftStatus = rightStatus)
  | .ok leftState, .ok rightState => decide (leftState = rightState)
  | _, _ => false

/-- Freshen the only nested array the selected operation can consume in place. -/
@[noinline] private def ownedState (state : @& State) : State := {
  state with inboundStreamWindows := state.inboundStreamWindows.map id
}

/-- Independent exact oracle for the debit-plus-refund result. -/
private def expectedRoundTrip (state : State) (frame : Frame) : Except Status State :=
  let size := frame.payload.size
  if size == 0 then
    .ok state
  else if size > state.inboundConnectionWindow then
    .error (Status.internal "HTTP/2 DATA frame exceeds connection flow-control window")
  else
    let streamId := frame.header.streamId
    let streamWindow :=
      match state.inboundStreamWindows.find? fun entry => entry.streamId == streamId with
      | some entry => entry.window
      | none => state.inboundInitialStreamWindow
    if size > streamWindow then
      .error (Status.internal "HTTP/2 DATA frame exceeds stream flow-control window")
    else
      .ok {
        state with
        inboundStreamWindows :=
          (state.inboundStreamWindows.filter fun entry => entry.streamId != streamId).push
            (window streamId streamWindow)
      }

private structure SemanticCase where
  label : String
  state : State
  frame : Frame

private def semanticCases : Array SemanticCase :=
  let depth48 := windowsOfDepth 48 128
  let adjacentDuplicates := #[
    window 1 512, window 3 128, window 3 17, window 3 900, window 5 256
  ]
  let separatedDuplicates := #[
    window 3 128, window 1 512, window 3 17, window 5 256, window 3 900
  ]
  #[
    {
      label := "zero_empty"
      state := stateWith 0 0 #[]
      frame := dataFrame 99 0
    },
    {
      label := "zero_preserves_duplicates"
      state := stateWith 0 0 separatedDuplicates
      frame := dataFrame 3 0
    },
    {
      label := "absent_exact_depth48"
      state := stateWith 128 128 depth48
      frame := dataFrame 199 128
    },
    {
      label := "present_first_exact_depth48"
      state := stateWith 128 128 depth48
      frame := dataFrame 1 128
    },
    {
      label := "present_middle_exact_depth48"
      state := stateWith 128 128 depth48
      frame := dataFrame 49 128
    },
    {
      label := "present_last_exact_depth48"
      state := stateWith 128 128 depth48
      frame := dataFrame 95 128
    },
    {
      label := "adjacent_duplicates_first_wins"
      state := stateWith 128 128 adjacentDuplicates
      frame := dataFrame 3 128
    },
    {
      label := "separated_duplicates_first_wins"
      state := stateWith 128 128 separatedDuplicates
      frame := dataFrame 3 128
    },
    {
      label := "connection_overrun_precedes_stream"
      state := stateWith 127 0 #[window 3 0]
      frame := dataFrame 3 128
    },
    {
      label := "present_stream_overrun"
      state := stateWith 128 128 #[window 3 127]
      frame := dataFrame 3 128
    },
    {
      label := "absent_stream_overrun"
      state := stateWith 128 127 depth48
      frame := dataFrame 199 128
    }
  ]

private def validateSemanticCase (fixture : @& SemanticCase) : IO Unit := do
  let reference :=
    Connection.TestSupport.consumeAndReplenishInboundDataWindowReferenceForBenchmark
      (ownedState fixture.state) fixture.frame
  let candidate :=
    Connection.TestSupport.consumeAndReplenishInboundDataWindowCandidateForBenchmark
      (ownedState fixture.state) fixture.frame
  let expected := expectedRoundTrip fixture.state fixture.frame
  unless sameProjectedResult (projectResult reference) (projectResult candidate) do
    throw (IO.userError s!"{fixture.label}: reference and candidate results differ")
  unless sameProjectedResult (projectResult reference) (projectResult expected) do
    throw (IO.userError s!"{fixture.label}: result differs from the exact oracle")

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

@[inline] private def windowDigest (digest : UInt64) (entry : @& InboundStreamWindow) : UInt64 :=
  mix (mix digest (UInt64.ofNat entry.streamId)) (UInt64.ofNat entry.window)

/-- Constant-size borrowed observation of every field the operation may change. -/
@[noinline] private def stateDigest (state : @& State) : UInt64 :=
  let digest := mix 1469598103934665603 (UInt64.ofNat state.inboundConnectionWindow)
  let digest := mix digest (UInt64.ofNat state.inboundInitialStreamWindow)
  let digest := mix digest (UInt64.ofNat state.inboundStreamWindows.size)
  if state.inboundStreamWindows.isEmpty then
    digest
  else
    let digest := windowDigest digest state.inboundStreamWindows[0]!
    let digest := windowDigest digest
      state.inboundStreamWindows[state.inboundStreamWindows.size / 2]!
    windowDigest digest state.inboundStreamWindows[state.inboundStreamWindows.size - 1]!

private structure PerfFixture where
  label : String
  state : State
  frames : Array Frame
  expectedDigests : Array UInt64
  depth : Nat
  payloadBytes : Nat
  lookup : String

private def expectOk (label : String) : Except Status State → IO State
  | .ok state => pure state
  | .error status =>
      throw (IO.userError s!"{label}: unexpected preflight error: {status.messageD}")

/-- Prove one complete reference/candidate recurrence and its return to the
initial pure state before the fixture can enter a scaling loop. -/
private def makePerfFixture (label lookup : String) (state : State)
    (targetIds : Array Nat) (payloadBytes : Nat) : IO PerfFixture := do
  unless !targetIds.isEmpty do
    throw (IO.userError s!"{label}: recurrence requires at least one target id")
  let frames := targetIds.map fun streamId => dataFrame streamId payloadBytes
  let mut referenceState := ownedState state
  let mut candidateState := ownedState state
  let mut expectedDigests := #[]
  for frame in frames do
    let nextReference ← expectOk label <|
      Connection.TestSupport.consumeAndReplenishInboundDataWindowReferenceForBenchmark
        referenceState frame
    let nextCandidate ← expectOk label <|
      Connection.TestSupport.consumeAndReplenishInboundDataWindowCandidateForBenchmark
        candidateState frame
    unless decide (projectState nextReference = projectState nextCandidate) do
      throw (IO.userError s!"{label}: recurrence step differs")
    expectedDigests := expectedDigests.push (stateDigest nextReference)
    referenceState := nextReference
    candidateState := nextCandidate
  unless decide (projectState referenceState = projectState state) do
    throw (IO.userError s!"{label}: reference recurrence did not close its cycle")
  unless decide (projectState candidateState = projectState state) do
    throw (IO.userError s!"{label}: candidate recurrence did not close its cycle")
  pure {
    label
    state
    frames
    expectedDigests
    depth := state.inboundStreamWindows.size
    payloadBytes
    lookup
  }

private def makePerfFixtures : IO (Array PerfFixture) := do
  let windows1 := windowsOfDepth 1 128
  let windows48 := windowsOfDepth 48 128
  let ids48 := windows48.map fun entry => entry.streamId
  let first1 ← makePerfFixture "present_first_1_exact" "first"
    (stateWith 128 128 windows1) (windows1.map fun entry => entry.streamId) 128
  let first48 ← makePerfFixture "present_first_48_exact" "first"
    (stateWith 128 128 windows48) ids48 128
  let middle48 ← makePerfFixture "present_middle_48_exact" "middle"
    (stateWith 128 128 windows48)
    ((windows48.extract (windows48.size / 2) windows48.size).map fun entry => entry.streamId)
    128
  let last48 ← makePerfFixture "present_last_48_exact" "last"
    (stateWith 128 128 windows48) #[windows48[windows48.size - 1]!.streamId] 128
  let absentZero48 ← makePerfFixture "absent_zero_48" "absent-zero"
    (stateWith 0 0 windows48) #[199] 0
  pure #[first1, first48, middle48, last48, absentZero48]

private def expectedChecksum (digests : Array UInt64) (iterations : Nat) : UInt64 :=
  let cycle := digests.foldl (fun total digest => total + digest) 0
  let remainder := (digests.extract 0 (iterations % digests.size)).foldl
    (fun total digest => total + digest) 0
  cycle * UInt64.ofNat (iterations / digests.size) + remainder

/-- Linear recurrence with one common indirect selected call in either mode. -/
@[noinline] private def runRepeated (run : @& WindowRoundTrip) (fixture : @& PerfFixture)
    (iterations : Nat) : Except Status UInt64 := do
  let mut state := ownedState fixture.state
  let mut checksum : UInt64 := 0
  for iteration in [0:iterations] do
    let frame := fixture.frames[iteration % fixture.frames.size]!
    let next ← run state frame
    checksum := checksum + stateDigest next
    state := next
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
    | [mode, selection, iterations, warmup] =>
        pure (mode, selection,
          ← parsePositive "iterations" iterations,
          ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: inbound_window_round_trip_benchmark (reference|candidate) " ++
          "(present_first_1_exact|present_first_48_exact|present_middle_48_exact|" ++
          "present_last_48_exact|absent_zero_48) iterations warmup")
  let some mode := parseMode modeText
    | throw (IO.userError "mode must be reference or candidate")

  for fixture in semanticCases do
    validateSemanticCase fixture
  let fixtures ← makePerfFixtures
  let some fixture := fixtures.find? fun fixture => fixture.label == selection
    | throw (IO.userError s!"unknown fixture: {selection}")

  let selectedBox := selectWindowRoundTripBox mode
  unless selectedBox.candidateSelected == modeIsCandidate mode do
    throw (IO.userError "opaque selector metadata mismatch")
  let selected := selectedBox.run

  let warmupChecksum ← match runRepeated selected fixture warmup with
    | .ok checksum => pure checksum
    | .error status => throw (IO.userError s!"warmup failed: {status.messageD}")
  let expectedWarmup := expectedChecksum fixture.expectedDigests warmup
  unless warmupChecksum == expectedWarmup do
    throw (IO.userError
      s!"warmup checksum {warmupChecksum} != reference checksum {expectedWarmup}")

  let checksum ← match runRepeated selected fixture iterations with
    | .ok checksum => pure checksum
    | .error status => throw (IO.userError s!"measurement failed: {status.messageD}")
  let expected := expectedChecksum fixture.expectedDigests iterations
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != reference checksum {expected}")

  IO.println <| s!"benchmark=grpc_inbound_window_round_trip_v1 mode={modeName mode} " ++
    s!"fixture={fixture.label} lookup={fixture.lookup} depth={fixture.depth} " ++
    s!"payload_bytes={fixture.payloadBytes} cycle={fixture.frames.size} " ++
    s!"iterations={iterations} warmup={warmup} checksum={checksum}"
  IO.println <| s!"semantic_cases={semanticCases.size} exact_preflight=true " ++
    "selector=opaque_once recurrence=linear timing=external"

end Grpc.Http2.InboundWindowRoundTripBenchmarkHarness

def main (args : List String) : IO Unit :=
  Grpc.Http2.InboundWindowRoundTripBenchmarkHarness.runMain args
