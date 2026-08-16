import Grpc

open Grpc

/-!
# HTTP/2 frame-batch encoding benchmark

Measures the production `Connection.encodeFrames` bridge used when a queued
response is emitted.  Each fixture models a complete unary response batch:
initial HEADERS, one or more DATA frames, and trailing HEADERS.  Fixture
construction, the legacy byte-for-byte oracle, full decode validation, and
warmup are outside reported samples.  A constant-size wire envelope digest
remains inside every timed iteration.

This benchmark intentionally times only the production path.  Baseline and
candidate binaries are compared by the campaign harness so both sides execute
the same source-level loop and validation envelope.
-/

private structure Fixture where
  label : String
  frames : Array Http2.Frame
  expectedDigest : Nat

private def payloadOfSize (size seed : Nat) : ByteArray :=
  (List.range size).foldl (fun payload value =>
    payload.push (UInt8.ofNat ((value * 37 + seed) % 251))) ByteArray.empty

private def frame (frameType : Http2.FrameType) (flags : UInt8)
    (payload : ByteArray) : Http2.Frame := {
  header := { length := payload.size, frameType, flags, streamId := 1 }
  payload
}

private def unaryFrames (bodySizes : Array Nat) : Array Http2.Frame := Id.run do
  let mut frames := #[frame .headers Http2.FrameFlag.endHeaders (payloadOfSize 37 11)]
  for size in bodySizes do
    frames := frames.push (frame .data 0 (payloadOfSize size 29))
  frames := frames.push <| frame .headers
    (Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream])
    (payloadOfSize 19 47)
  return frames

/-- The pre-fusion production implementation, retained only as a setup oracle. -/
private def legacyEncodeFrames (frames : Array Http2.Frame) : Except Status ByteArray :=
  frames.foldlM (init := ByteArray.empty) fun out next => do
    let encoded ← Http2.Frame.encode next
    pure (out.append encoded)

@[inline] private def wireDigest (wire : @& ByteArray) : Nat :=
  let first := (wire[0]?).map UInt8.toNat |>.getD 0
  let middle := (wire[wire.size / 2]?).map UInt8.toNat |>.getD 0
  let last := (wire[wire.size - 1]?).map UInt8.toNat |>.getD 0
  wire.size * 1000003 + first * 1009 + middle * 101 + last

private def makeFixture (label : String) (frames : Array Http2.Frame) : IO Fixture := do
  let expected ← match legacyEncodeFrames frames with
    | .ok wire => pure wire
    | .error status => throw (IO.userError s!"{label}: legacy encode failed: {status.messageD}")
  let actual ← match Http2.Connection.encodeFrames frames with
    | .ok wire => pure wire
    | .error status => throw (IO.userError s!"{label}: production encode failed: {status.messageD}")
  unless actual == expected do
    throw (IO.userError s!"{label}: production bytes differ from the legacy oracle")
  match Http2.Frame.decodeAll actual with
  | .ok decoded =>
    unless decoded == frames do
      throw (IO.userError s!"{label}: encoded batch did not decode to its frames")
  | .error status =>
    throw (IO.userError s!"{label}: encoded batch failed to decode: {status.messageD}")
  pure { label, frames, expectedDigest := wireDigest expected }

@[noinline] private def encodeRepeated (fixture : @& Fixture)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match Http2.Connection.encodeFrames fixture.frames with
    | .ok wire => checksum := checksum + wireDigest wire
    | .error status => throw (IO.userError s!"{fixture.label}: {status.messageD}")
  pure checksum

private def measureFixture (fixture : @& Fixture) (iterations : Nat) : IO Nat := do
  let warmupIterations := Nat.min iterations 500
  let warmup ← encodeRepeated fixture warmupIterations
  unless warmup == fixture.expectedDigest * warmupIterations do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let started ← IO.monoNanosNow
  let checksum ← encodeRepeated fixture iterations
  let elapsed := (← IO.monoNanosNow) - started
  unless checksum == fixture.expectedDigest * iterations do
    throw (IO.userError s!"{fixture.label}: measured checksum mismatch")
  pure elapsed

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
    if value <= head then value :: head :: tail else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def report (fixture : @& Fixture) (iterations : Nat)
    (samples : Array Nat) : IO Unit := do
  let elapsed := median samples
  let perBatch := if iterations == 0 then 0 else elapsed * 100 / iterations
  let payloadBytes := fixture.frames.foldl (fun total next => total + next.payload.size) 0
  IO.println <| s!"case={fixture.label} frames_per_batch={fixture.frames.size} " ++
    s!"payload_bytes={payloadBytes} iterations={iterations}"
  IO.println s!"case={fixture.label} samples_ns={formatSamples samples}"
  IO.println s!"case={fixture.label} median_ns_per_batch={formatHundredths perBatch}"

private def parsePositive (name : String) (value? : Option String)
    (fallback : Nat) : IO Nat := do
  let value := (value? >>= String.toNat?).getD fallback
  unless value > 0 do throw (IO.userError s!"{name} must be positive")
  pure value

def main (args : List String) : IO Unit := do
  let iterations ← parsePositive "iterations" args[0]? 20000
  let rounds ← parsePositive "rounds" args[1]? 7
  unless rounds >= 3 && rounds % 2 == 1 do
    throw (IO.userError "rounds must be an odd integer of at least 3")
  unless args.length <= 2 do
    throw (IO.userError "usage: frame_batch_benchmark [iterations] [rounds]")
  let small ← makeFixture "unary_128" (unaryFrames #[128])
  let frameSized ← makeFixture "unary_16k"
    (unaryFrames #[Http2.defaultMaxFramePayloadLength])
  let split ← makeFixture "unary_split"
    (unaryFrames #[Http2.defaultMaxFramePayloadLength, 1024])
  IO.println "benchmark=http2_frame_batch_v1 path=Connection.encodeFrames validation=pass"
  for fixture in #[small, frameSized, split] do
    let mut samples := #[]
    for _ in [0:rounds] do
      samples := samples.push (← measureFixture fixture iterations)
    report fixture iterations samples
  IO.println "HTTP/2 frame-batch benchmark completed"
