import Grpc

/-!
# HTTP/2 outbound-flush differential benchmark

The reference seam is the exact former recursive queue-prefix implementation;
the candidate seam is the proved-equal cursor implementation used by compiled
production.  Both are selected once through an opaque two-field box, so the
scaling loop makes the same indirect call in either mode.

Every iteration owns one connection state and one frame array.  After the
selected queue operation, a constant-size borrowed digest observes the result.
One common noinline helper then restores flow-control credit, reconstructs the
logical input as `emitted ++ pending`, and clears the pending queue.  Fixed
validation proves that reconstruction is exactly the original fixture for both
implementations before warmup or measurement begins.

This executable reports no wall time.  It is intended for whole-process
`perf stat` instruction and branch counters: fixture construction, unary HPACK
encoding, semantic validation, selector construction, requested warmup, and
output are fixed process work; only the selected queue/digest/recycle loop
scales with `iterations`.
-/

namespace Grpc.Http2.OutboundFlushBenchmarkHarness

open Connection

private abbrev Flusher := State → Array Frame → State × Array Frame

private inductive Mode where
  | reference
  | candidate

private structure FlusherBox where
  flush : Flusher
  /-- Keep selection nontrivial across the opaque boundary. -/
  candidateSelected : Bool

/-- Select exactly once, while preserving one indirect call shape in the loop. -/
@[noinline] private opaque selectFlusherBox (mode : Mode) : FlusherBox :=
  match mode with
  | .reference => {
      flush := Connection.TestSupport.queueOutboundReferenceForBenchmark
      candidateSelected := false
    }
  | .candidate => {
      flush := Connection.TestSupport.queueOutboundCandidateForBenchmark
      candidateSelected := true
    }

private structure Fixture where
  label : String
  state : State
  frames : Array Frame
  resetConnectionWindow : Nat
  expectedEmitted : Nat
  expectedPending : Nat
  expectedConnectionWindow : Nat
  payloadBytes : Nat
  dataBytes : Nat

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

private def dataPayloadBytes (frames : Array Frame) : Nat :=
  frames.foldl (fun total next =>
    if next.header.frameType == .data then total + next.payload.size else total) 0

private def payloadBytes (frames : Array Frame) : Nat :=
  frames.foldl (fun total next => total + next.payload.size) 0

private def baseState (connectionWindow : Nat) : State := {
  (default : State) with
  outboundConnectionWindow := connectionWindow
  outboundInitialStreamWindow := initialFlowControlWindow
  outboundStreamWindows := #[]
  pendingOutbound := #[]
}

private def makeUnaryFixture (label : String) (bodySize : Nat) : IO Fixture := do
  let state := baseState initialFlowControlWindow
  let encoded ← match Transport.encodeUnaryResponseFrames state.outboundHpack 1
      { data := payload bodySize (bodySize + 7) } with
    | .ok encoded => pure encoded
    | .error status =>
        throw (IO.userError s!"{label}: unary response encoding failed: {status.messageD}")
  let frames := encoded.1
  let dataBytes := dataPayloadBytes frames
  unless dataBytes <= initialFlowControlWindow do
    throw (IO.userError s!"{label}: fixture exceeds the initial flow-control window")
  pure {
    label
    state
    frames
    resetConnectionWindow := initialFlowControlWindow
    expectedEmitted := frames.size
    expectedPending := 0
    expectedConnectionWindow := initialFlowControlWindow - dataBytes
    payloadBytes := payloadBytes frames
    dataBytes
  }

private def controlType (index : Nat) : FrameType :=
  match index % 8 with
  | 0 => .headers
  | 1 => .continuation
  | 2 => .settings
  | 3 => .ping
  | 4 => .windowUpdate
  | 5 => .rstStream
  | 6 => .priority
  | _ => .unknown (UInt8.ofNat (0xa + index % 6))

private def controlFrame (index : Nat) : Frame :=
  let kind := controlType index
  let streamId :=
    match kind with
    | .settings | .ping | .goAway => 0
    | _ => index * 2 + 1
  let flags :=
    match kind with
    | .headers | .continuation => FrameFlag.endHeaders
    | _ => 0
  frame kind streamId (payload (index % 7 + 1) (index + 31)) flags

private def makeControlsFixture : Fixture :=
  let frames := (Array.range 32).map controlFrame
  {
    label := "controls_32"
    state := baseState initialFlowControlWindow
    frames
    resetConnectionWindow := initialFlowControlWindow
    expectedEmitted := 32
    expectedPending := 0
    expectedConnectionWindow := initialFlowControlWindow
    payloadBytes := payloadBytes frames
    dataBytes := 0
  }

private def makeBlockedFixture : Fixture :=
  let initial := frame .headers 1 (payload 19 101) FrameFlag.endHeaders
  let blocked := frame .data 1 (payload 128 103)
  let trailers := frame .headers 1 (payload 17 107)
    (FrameFlag.combine #[FrameFlag.endHeaders, FrameFlag.endStream])
  let frames := #[initial, blocked, trailers]
  {
    label := "blocked_after_header"
    state := baseState 0
    frames
    resetConnectionWindow := 0
    expectedEmitted := 1
    expectedPending := 2
    expectedConnectionWindow := 0
    payloadBytes := payloadBytes frames
    dataBytes := blocked.payload.size
  }

/-- Fresh outer state and queue wrappers keep the first selected call owned. -/
@[noinline] private def ownedState (state : @& State) : State := {
  state with
  outboundStreamWindows := state.outboundStreamWindows.map id
  pendingOutbound := state.pendingOutbound.map id
}

@[noinline] private def ownedFrames (frames : @& Array Frame) : Array Frame :=
  frames.map id

private def windowSignatures (windows : Array OutboundStreamWindow) : Array (Nat × Int) :=
  windows.map fun window => (window.streamId, window.window)

private def sameRelevantState (left : @& State) (right : @& State) : Bool :=
  left.outboundConnectionWindow == right.outboundConnectionWindow &&
    left.outboundInitialStreamWindow == right.outboundInitialStreamWindow &&
    decide (windowSignatures left.outboundStreamWindows =
      windowSignatures right.outboundStreamWindows) &&
    decide (left.pendingOutbound = right.pendingOutbound)

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

@[inline] private def byteSample (bytes : @& ByteArray) (index : Nat) : UInt64 :=
  UInt64.ofNat ((bytes[index]?).map UInt8.toNat |>.getD 0)

@[inline] private def frameDigest (digest : UInt64) (value : @& Frame) : UInt64 :=
  let digest := mix digest (UInt64.ofNat value.header.length)
  let digest := mix digest (UInt64.ofNat value.header.frameType.toUInt8.toNat)
  let digest := mix digest (UInt64.ofNat value.header.flags.toNat)
  let digest := mix digest (UInt64.ofNat value.header.streamId)
  let digest := mix digest (UInt64.ofNat value.payload.size)
  if value.payload.isEmpty then
    mix digest 0
  else
    let digest := mix digest (byteSample value.payload 0)
    let digest := mix digest (byteSample value.payload (value.payload.size / 2))
    mix digest (byteSample value.payload (value.payload.size - 1))

@[inline] private def frameEnvelopeDigest
    (digest : UInt64) (frames : @& Array Frame) : UInt64 :=
  let digest := mix digest (UInt64.ofNat frames.size)
  if frames.isEmpty then
    digest
  else
    let digest := frameDigest digest frames[0]!
    let digest := frameDigest digest frames[frames.size / 2]!
    frameDigest digest frames[frames.size - 1]!

/-- Constant-size borrowed observation of every result component the flush may change. -/
@[noinline] private def flushDigest
    (state : @& State) (emitted : @& Array Frame) : UInt64 :=
  let digest := mix 1469598103934665603 (UInt64.ofNat state.outboundConnectionWindow)
  let digest := mix digest (UInt64.ofNat state.outboundInitialStreamWindow)
  let digest := mix digest (UInt64.ofNat state.outboundStreamWindows.size)
  let digest := frameEnvelopeDigest digest state.pendingOutbound
  frameEnvelopeDigest digest emitted

/-- Restore the bounded fixture while preserving the emitted-prefix ownership path. -/
@[noinline] private def recreditAndRecycle (connectionWindow : Nat)
    (state : State) (emitted : Array Frame) : State × Array Frame :=
  let frames := emitted.append state.pendingOutbound
  let state := {
    state with
    outboundConnectionWindow := connectionWindow
    outboundStreamWindows := #[]
    pendingOutbound := #[]
  }
  (state, frames)

private def validateFixture (fixture : @& Fixture) : IO UInt64 := do
  let (referenceState, referenceEmitted) :=
    Connection.TestSupport.queueOutboundReferenceForBenchmark
      (ownedState fixture.state) (ownedFrames fixture.frames)
  let (candidateState, candidateEmitted) :=
    Connection.TestSupport.queueOutboundCandidateForBenchmark
      (ownedState fixture.state) (ownedFrames fixture.frames)

  unless sameRelevantState referenceState candidateState &&
      decide (referenceEmitted = candidateEmitted) do
    throw (IO.userError s!"{fixture.label}: reference and candidate results differ")
  unless referenceEmitted.size == fixture.expectedEmitted do
    throw (IO.userError s!"{fixture.label}: unexpected emitted-frame count")
  unless referenceState.pendingOutbound.size == fixture.expectedPending do
    throw (IO.userError s!"{fixture.label}: unexpected pending-frame count")
  unless referenceState.outboundConnectionWindow == fixture.expectedConnectionWindow do
    throw (IO.userError s!"{fixture.label}: unexpected connection-window debit")
  unless referenceState.outboundStreamWindows.isEmpty do
    throw (IO.userError s!"{fixture.label}: terminal/reset-free fixture retained a stream window")

  let referenceDigest := flushDigest referenceState referenceEmitted
  let (referenceReset, referenceFrames) := recreditAndRecycle
    fixture.resetConnectionWindow referenceState referenceEmitted
  let (candidateReset, candidateFrames) := recreditAndRecycle
    fixture.resetConnectionWindow candidateState candidateEmitted
  unless sameRelevantState referenceReset fixture.state &&
      decide (referenceFrames = fixture.frames) do
    throw (IO.userError s!"{fixture.label}: reference recycle did not restore the fixture")
  unless sameRelevantState candidateReset fixture.state &&
      decide (candidateFrames = fixture.frames) do
    throw (IO.userError s!"{fixture.label}: candidate recycle did not restore the fixture")
  pure referenceDigest

/-- No `Mode` value or branch occurs in this scaling loop. -/
@[noinline] private def runRepeated (flush : @& Flusher) (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut state := ownedState fixture.state
  let mut frames := ownedFrames fixture.frames
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    let (nextState, emitted) := flush state frames
    checksum := checksum + flushDigest nextState emitted
    let recycled := recreditAndRecycle fixture.resetConnectionWindow nextState emitted
    state := recycled.1
    frames := recycled.2
  return checksum

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
        "usage: outbound_flush_benchmark (reference|candidate) " ++
          "(unary_128|unary_6144|controls_32|blocked_after_header) " ++
          "iterations warmup")
  let some mode := parseMode modeText
    | throw (IO.userError "mode must be reference or candidate")

  let unary128 ← makeUnaryFixture "unary_128" 128
  let unary6144 ← makeUnaryFixture "unary_6144" 6144
  let fixtures := #[unary128, unary6144, makeControlsFixture, makeBlockedFixture]
  let some fixture := fixtures.find? fun fixture => fixture.label == selection
    | throw (IO.userError s!"unknown fixture: {selection}")

  let mut expectedIterationDigest? : Option UInt64 := none
  for semanticFixture in fixtures do
    let digest ← validateFixture semanticFixture
    if semanticFixture.label == selection then
      expectedIterationDigest? := some digest
  let some expectedIterationDigest := expectedIterationDigest?
    | throw (IO.userError "selected fixture was not semantically validated")

  let flusherBox := selectFlusherBox mode
  unless flusherBox.candidateSelected == modeIsCandidate mode do
    throw (IO.userError "opaque flusher selection metadata mismatch")
  let selected := flusherBox.flush

  let warmupChecksum := runRepeated selected fixture warmup
  let expectedWarmup := expectedIterationDigest * UInt64.ofNat warmup
  unless warmupChecksum == expectedWarmup do
    throw (IO.userError
      s!"warmup checksum {warmupChecksum} != reference checksum {expectedWarmup}")
  let checksum := runRepeated selected fixture iterations
  let expected := expectedIterationDigest * UInt64.ofNat iterations
  unless checksum == expected do
    throw (IO.userError s!"checksum {checksum} != reference checksum {expected}")

  IO.println <| s!"benchmark=grpc_outbound_flush_v1 mode={modeName mode} " ++
    s!"fixture={fixture.label} frames={fixture.frames.size} " ++
    s!"payload_bytes={fixture.payloadBytes} data_bytes={fixture.dataBytes} " ++
    s!"iterations={iterations} warmup={warmup} checksum={checksum}"
  IO.println <|
    "outbound_flush_validation=pass cases=4 result=exact_reference_candidate " ++
      "recycle=emitted_plus_pending_restores_fixture"
  IO.println <|
    "counter_scope=whole_process fixed=fixture_construction+unary_hpack_encoding+" ++
      "semantic_validation+selector+requested_warmup+output " ++
      "scaling=selected_queue_flush+borrowed_digest+recredit_recycle " ++
      "excluded=socket+network+protobuf+handler+service"

end Grpc.Http2.OutboundFlushBenchmarkHarness

def main (args : List String) : IO Unit :=
  Grpc.Http2.OutboundFlushBenchmarkHarness.runMain args
