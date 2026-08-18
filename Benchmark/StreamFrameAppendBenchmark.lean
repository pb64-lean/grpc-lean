import Grpc

/-!
# HTTP/2 stream-frame append differential and benchmark

The reference is the former remove-then-find definition.  The candidate is
the lookup-first implementation used by compiled production.  Directed cases
compare every observable `StreamState` field across missing, first/middle/last,
and duplicate ids.  Present-id cases model the consuming whole-state transfer.
The absent case models the ownership asymmetry at HEADERS: the former caller
retained its state while the reference ran, whereas the candidate consumes the
state before appending.  Every loop restores its bounded fixture and retains a
constant-size result digest.
-/

namespace Grpc.Http2.StreamFrameAppendBenchmarkHarness

open Connection

private inductive Mode where
  | reference
  | candidate

private inductive Scenario where
  | presentFirst
  | presentLast
  | absent
  deriving BEq

private def payload (seed size : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for index in [0:size] do
    bytes := bytes.push (UInt8.ofNat (seed * 17 + index * 29 + 3))
  return bytes

private def frame (streamId seed : Nat) : Frame :=
  let bytes := payload seed (seed % 5 + 3)
  {
    header := {
      length := bytes.size
      frameType := if seed % 2 == 0 then .data else .headers
      flags := UInt8.ofNat (seed % 8)
      streamId := streamId
    }
    payload := bytes
  }

private def stream (streamId seed : Nat) : StreamState := {
  streamId := streamId
  frames := #[frame streamId (seed + 11)]
  requestMetadata := some #[
    Header.of "x-stream-fixture" s!"value-{seed}",
    Header.of "x-stream-id" (toString streamId)
  ]
  requestPreflight := some {
    method := { service := s!"fixture.Service{seed}", method := s!"Call{streamId}" }
    timeout := some { value := seed + 1, unit := .millisecond }
    contentLength := some (seed * 3 + 5)
    requestUsesGzip := seed % 2 == 0
    clientAcceptsGzip := seed % 3 == 0
  }
  endHeadersReceivedAt := some (1000 + seed)
  deadline := some (100000 + seed * 13)
}

private def streamsOfDepth (depth : Nat) : Array StreamState :=
  (Array.range depth).map fun index => stream (index * 2 + 1) (index + 1)

private def rpcShapeTag : RpcShape → Nat
  | .unary => 0
  | .serverStreaming => 1
  | .serverStreamingStream => 2
  | .clientStreaming => 3
  | .clientStreamingStream => 4
  | .bidirectionalStreaming => 5
  | .bidirectionalStreamingStream => 6

private structure StreamSignature where
  streamId : Nat
  frames : Array Frame
  requestMetadata : Option Metadata
  requestPreflight : Option Headers.RequestPreflight
  authorizedEntry : Option (String × String × Nat)
  endHeadersReceivedAt : Option Nat
  deadline : Option Nat
  deriving BEq

private def signature (value : StreamState) : StreamSignature := {
  streamId := value.streamId
  frames := value.frames
  requestMetadata := value.requestMetadata
  requestPreflight := value.requestPreflight
  authorizedEntry := value.authorizedEntry?.map fun entry =>
    (entry.name.service, entry.name.method, rpcShapeTag entry.shape)
  endHeadersReceivedAt := value.endHeadersReceivedAt
  deadline := value.deadline
}

private def sameStreams (left right : Array StreamState) : Bool :=
  left.map signature == right.map signature

private structure SemanticCase where
  label : String
  streams : Array StreamState
  frame : Frame

private def semanticCases : Array SemanticCase :=
  let rich := streamsOfDepth 6
  let adjacent : Array StreamState := #[
    stream 1 10, stream 3 20, stream 3 21, stream 5 30, stream 7 40
  ]
  let separated : Array StreamState := #[
    stream 3 50, stream 1 51, stream 3 52, stream 5 53, stream 3 54
  ]
  let duplicates : Array StreamState := #[stream 3 60, stream 3 61, stream 3 62]
  #[
    { label := "empty", streams := #[], frame := frame 3 100 },
    { label := "absent", streams := rich, frame := frame 99 101 },
    { label := "single", streams := #[stream 3 70], frame := frame 3 102 },
    { label := "first", streams := rich, frame := frame 1 103 },
    { label := "middle", streams := rich, frame := frame 7 104 },
    { label := "last", streams := rich, frame := frame 11 105 },
    { label := "adjacent-duplicates", streams := adjacent, frame := frame 3 106 },
    { label := "separated-duplicates", streams := separated, frame := frame 3 107 },
    { label := "all-duplicates", streams := duplicates, frame := frame 3 108 },
    { label := "header-frame", streams := rich, frame := frame 5 109 }
  ]

private def validateSemantics : IO Nat := do
  for fixture in semanticCases do
    let reference := TestSupport.appendStreamFrameReferenceForBenchmark
      fixture.streams fixture.frame
    let candidate := TestSupport.appendStreamFrameCandidateForBenchmark
      fixture.streams fixture.frame
    unless sameStreams reference candidate do
      throw (IO.userError s!"{fixture.label}: reference and candidate differ")
    let targetId := fixture.frame.header.streamId
    let retained := fixture.streams.filter fun value => value.streamId != targetId
    unless candidate.size == retained.size + 1 do
      throw (IO.userError s!"{fixture.label}: result count is not retained count plus one")
    unless sameStreams (candidate.extract 0 retained.size) retained do
      throw (IO.userError s!"{fixture.label}: retained stream values or order changed")
    let appended := candidate[candidate.size - 1]!
    unless appended.streamId == targetId do
      throw (IO.userError s!"{fixture.label}: appended stream id changed")
    unless appended.frames.back? == some fixture.frame do
      throw (IO.userError s!"{fixture.label}: frame was not appended at the end")
    match fixture.streams.find? fun value => value.streamId == targetId with
    | some first =>
        unless appended.frames.size == first.frames.size + 1 do
          throw (IO.userError s!"{fixture.label}: first matching stream did not supply state")
        unless (candidate.filter fun value => value.streamId == targetId).size == 1 do
          throw (IO.userError s!"{fixture.label}: duplicate target states survived")
    | none =>
        unless appended.frames == #[fixture.frame]
            && appended.requestMetadata.isNone
            && appended.requestPreflight.isNone
            && appended.authorizedEntry?.isNone
            && appended.endHeadersReceivedAt.isNone
            && appended.deadline.isNone do
          throw (IO.userError s!"{fixture.label}: missing id did not create the default state")
  pure semanticCases.size

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

@[inline] private def frameDigest (digest : UInt64) (value : @& Frame) : UInt64 :=
  let digest := mix digest (UInt64.ofNat value.header.length)
  let digest := mix digest (UInt64.ofNat value.header.frameType.toUInt8.toNat)
  let digest := mix digest (UInt64.ofNat value.header.flags.toNat)
  let digest := mix digest (UInt64.ofNat value.header.streamId)
  mix digest (UInt64.ofNat value.payload.size)

@[inline] private def streamDigest (digest : UInt64) (value : @& StreamState) : UInt64 :=
  let digest := mix digest (UInt64.ofNat value.streamId)
  let digest := mix digest (UInt64.ofNat value.frames.size)
  match value.frames.back? with
  | none => mix digest 0
  | some last => frameDigest digest last

@[noinline] private def stateDigest (streams : @& Array StreamState) : UInt64 :=
  let digest := mix 1469598103934665603 (UInt64.ofNat streams.size)
  if streams.isEmpty then digest else
    let digest := streamDigest digest streams[0]!
    let digest := streamDigest digest streams[streams.size / 2]!
    streamDigest digest streams[streams.size - 1]!

private structure Fixture where
  scenario : Scenario
  streams : Array StreamState
  frames : Array Frame
  resetStates : Array StreamState
  expectedDigests : Array UInt64

private def appendWith (mode : Mode) (streams : Array StreamState) (value : Frame) :
    Array StreamState :=
  match mode with
  | .reference => TestSupport.appendStreamFrameReferenceForBenchmark streams value
  | .candidate => TestSupport.appendStreamFrameCandidateForBenchmark streams value

private def restoreAfterAppend (scenario : Scenario) (reset : StreamState)
    (streams : Array StreamState) : Array StreamState :=
  match scenario with
  | .presentFirst | .presentLast => streams.set! (streams.size - 1) reset
  | .absent => streams.pop

private def cycleOnce (mode : Mode) (scenario : Scenario)
    (frames : @& Array Frame) (resetStates : @& Array StreamState)
    (streams : Array StreamState) (index : Nat) : Array StreamState × UInt64 :=
  match scenario with
  | .absent =>
      match mode with
      | .reference =>
          -- The former HEADERS caller retained its enclosing state here.
          let original := streams
          let appended := appendWith .reference streams frames[index]!
          (original, stateDigest appended)
      | .candidate =>
          -- The whole-state helper transfers ownership before the append.
          let appended := appendWith .candidate streams frames[index]!
          let digest := stateDigest appended
          (appended.pop, digest)
  | .presentFirst | .presentLast =>
      let appended := appendWith mode streams frames[index]!
      let digest := stateDigest appended
      let restored := restoreAfterAppend scenario resetStates[index]! appended
      (restored, digest)

private def makeFixture (scenario : Scenario) (depth : Nat) : IO Fixture := do
  let streams := streamsOfDepth depth
  let (targetIds, resetStates) := match scenario with
    | .presentFirst => (streams.map fun (value : StreamState) => value.streamId, streams)
    | .presentLast =>
        if 0 < streams.size then
          (#[streams[streams.size - 1]!.streamId], #[streams[streams.size - 1]!])
        else
          (#[], #[])
    | .absent => (#[depth * 2 + 101], #[default])
  unless !targetIds.isEmpty do
    throw (IO.userError "present scenarios require a positive stream depth")
  let frames := targetIds.map fun streamId => frame streamId (streamId + depth + 200)
  let mut current := streams
  let mut expectedDigests := #[]
  for index in [0:frames.size] do
    let (next, digest) := cycleOnce .reference scenario frames resetStates current index
    current := next
    expectedDigests := expectedDigests.push digest
  unless sameStreams current streams do
    throw (IO.userError "benchmark fixture does not restore after one target cycle")
  pure { scenario, streams, frames, resetStates, expectedDigests }

@[noinline] private def ownedStreams (streams : @& Array StreamState) : Array StreamState :=
  streams.map id

@[noinline] private def runRepeated (mode : Mode) (fixture : @& Fixture)
    (iterations : Nat) : UInt64 := Id.run do
  let mut streams := ownedStreams fixture.streams
  let mut checksum : UInt64 := 0
  for iteration in [0:iterations] do
    let index := iteration % fixture.frames.size
    let (next, digest) := cycleOnce mode fixture.scenario fixture.frames
      fixture.resetStates streams index
    streams := next
    checksum := checksum + digest
  return checksum

private def expectedChecksum (fixture : @& Fixture) (iterations : Nat) : UInt64 :=
  let cycleSum := fixture.expectedDigests.foldl (init := 0) (· + ·)
  let completeCycles := iterations / fixture.expectedDigests.size
  let remainder := iterations % fixture.expectedDigests.size
  let remainderSum := (fixture.expectedDigests.extract 0 remainder).foldl (init := 0) (· + ·)
  cycleSum * UInt64.ofNat completeCycles + remainderSum

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

private def modeName : Mode → String
  | .reference => "reference"
  | .candidate => "candidate"

private def scenarioName : Scenario → String
  | .presentFirst => "present_first"
  | .presentLast => "present_last"
  | .absent => "absent"

private def parseMode : String → Option Mode
  | "reference" => some .reference
  | "candidate" => some .candidate
  | _ => none

private def parseScenario : String → Option Scenario
  | "present_first" => some .presentFirst
  | "present_last" => some .presentLast
  | "absent" => some .absent
  | _ => none

private def supportedDepth (depth : Nat) : Bool :=
  depth == 0 || depth == 1 || depth == 4 || depth == 48

def runMain (args : List String) : IO Unit := do
  let (modeText, scenarioText, depth, iterations, warmup) ← match args with
    | [mode, scenario, depth, iterations, warmup] =>
      pure (mode, scenario,
        ← parseNatural "depth" depth,
        ← parseNatural "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: stream_frame_append_benchmark (reference|candidate) " ++
          "(present_first|present_last|absent) (0|1|4|48) iterations warmup")
  let some mode := parseMode modeText
    | throw (IO.userError "mode must be reference or candidate")
  let some scenario := parseScenario scenarioText
    | throw (IO.userError "scenario must be present_first, present_last, or absent")
  unless supportedDepth depth do
    throw (IO.userError "depth must be 0, 1, 4, or 48")
  if depth == 0 && scenario != .absent then
    throw (IO.userError "depth zero is supported only for the absent scenario")

  let cases ← validateSemantics
  let fixture ← makeFixture scenario depth
  let warmupChecksum := runRepeated mode fixture warmup
  unless warmupChecksum == expectedChecksum fixture warmup do
    throw (IO.userError "warmup checksum mismatch")
  let checksum := runRepeated mode fixture iterations
  unless checksum == expectedChecksum fixture iterations do
    throw (IO.userError "measured checksum mismatch")
  IO.println <| s!"benchmark=grpc_stream_frame_append_v1 mode={modeName mode} " ++
    s!"scenario={scenarioName scenario} depth={depth} iterations={iterations} " ++
    s!"warmup={warmup} checksum={checksum}"
  IO.println <| s!"stream_frame_append_validation=pass cases={cases} " ++
    "result=exact reference=candidate theorem=total"

end Grpc.Http2.StreamFrameAppendBenchmarkHarness

def main (args : List String) : IO Unit :=
  Grpc.Http2.StreamFrameAppendBenchmarkHarness.runMain args
