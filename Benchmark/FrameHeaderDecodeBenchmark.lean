import Grpc

open Grpc

/-!
# HTTP/2 frame-header decode benchmark

Measures the exact production `Frame.decodeChunk` path for complete inbound
buffers. The fixtures isolate one HEADERS frame, a 128-byte DATA frame, a
representative three-frame unary batch, and 64 one-byte DATA frames. Fixture
construction, exact frame validation, warmup, and checksum validation remain
outside the reported samples. Wall samples are informative only; fixed-core
retired-instruction and branch counters are the deterministic acceptance gate.
-/

private structure Fixture where
  label : String
  wire : ByteArray
  expectedDigest : Nat

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

@[inline] private def frameDigest (value : Http2.Frame) : Nat :=
  value.header.length * 257 + value.header.streamId * 17 +
    value.header.frameType.toUInt8.toNat * 13 + value.header.flags.toNat * 7 +
    value.payload.size + 1

private def framesDigest (values : Array Http2.Frame) : Nat :=
  values.foldl (fun digest value => digest + frameDigest value) values.size

private def makeFixture (label : String) (frames : Array Http2.Frame) : IO Fixture := do
  let wire ← match Http2.Frame.encodeBatch frames with
    | .ok wire => pure wire
    | .error status => throw (IO.userError status.messageD)
  let decoded ← match Http2.Frame.decodeChunk {} wire with
    | .ok decoded => pure decoded
    | .error status => throw (IO.userError status.messageD)
  unless decoded.frames == frames && decoded.buffered.isEmpty do
    throw (IO.userError s!"{label}: production decode preflight changed frames or residue")
  pure { label, wire, expectedDigest := framesDigest frames }

private def tinyFrames : Array Http2.Frame := Id.run do
  let mut frames := #[]
  for index in [0:64] do
    frames := frames.push <| frame .data (index * 2 + 1)
      (ByteArray.empty.push (UInt8.ofNat (index * 29 + 5)))
      (if index == 63 then Http2.FrameFlag.endStream else 0)
  pure frames

@[noinline] private def decodeRepeated (fixture : @& Fixture)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match Http2.Frame.decodeChunk {} fixture.wire with
    | .error status => throw (IO.userError status.messageD)
    | .ok decoded => checksum := checksum + framesDigest decoded.frames + decoded.buffered.size
  pure checksum

private def expectedChecksum (fixture : @& Fixture) (iterations : Nat) : Nat :=
  fixture.expectedDigest * iterations

private def measureFixture (fixture : @& Fixture) (iterations : Nat) : IO (Nat × Nat) := do
  let warmupIterations := Nat.min iterations 1000
  let warmup ← decodeRepeated fixture warmupIterations
  unless warmup == expectedChecksum fixture warmupIterations do
    throw (IO.userError s!"{fixture.label}: warmup checksum mismatch")
  let started ← IO.monoNanosNow
  let checksum ← decodeRepeated fixture iterations
  let elapsed := (← IO.monoNanosNow) - started
  unless checksum == expectedChecksum fixture iterations do
    throw (IO.userError s!"{fixture.label}: measured checksum mismatch")
  pure (elapsed, checksum)

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

private def parsePositive (name : String) (value? : Option String)
    (fallback : Nat) : IO Nat := do
  let value := (value? >>= String.toNat?).getD fallback
  unless value > 0 do throw (IO.userError s!"{name} must be positive")
  pure value

private def report (fixture : @& Fixture) (iterations : Nat)
    (samples : Array Nat) (checksum : Nat) : IO Unit := do
  let perDecode := median samples * 100 / iterations
  IO.println <| s!"case={fixture.label} wire_bytes={fixture.wire.size} " ++
    s!"iterations={iterations} checksum={checksum}"
  IO.println s!"case={fixture.label} samples_ns={formatSamples samples}"
  IO.println s!"case={fixture.label} median_ns_per_decode={formatHundredths perDecode}"

def main (args : List String) : IO Unit := do
  let iterations ← parsePositive "iterations" args[0]? 300000
  let rounds ← parsePositive "rounds" args[1]? 7
  unless rounds >= 1 && rounds % 2 == 1 do
    throw (IO.userError "rounds must be a positive odd integer")
  let selection := args[2]?.getD "all"
  unless #["all", "headers_one", "data_128", "unary_three", "tiny_64"].contains selection do
    throw (IO.userError s!"unknown benchmark selection: {selection}")
  unless args.length <= 3 do
    throw (IO.userError <|
      "usage: frame_header_decode_benchmark [iterations] [rounds] " ++
        "[all|headers_one|data_128|unary_three|tiny_64]")

  let headers := frame .headers 1 (payloadOfSize 21 3) Http2.FrameFlag.endHeaders
  let data := frame .data 1 (payloadOfSize 128 11) Http2.FrameFlag.endStream
  let trailers := frame .headers 1 (payloadOfSize 13 19)
    (Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream])
  let fixtures := #[
    ← makeFixture "headers_one" #[headers],
    ← makeFixture "data_128" #[data],
    ← makeFixture "unary_three" #[headers, data, trailers],
    ← makeFixture "tiny_64" tinyFrames
  ]

  IO.println <| "benchmark=http2_frame_header_decode_v1 path=Frame.decodeChunk " ++
    s!"selection={selection} validation=pass"
  for fixture in fixtures do
    if selection == "all" || selection == fixture.label then
      let mut samples := #[]
      let mut checksum := 0
      for _ in [0:rounds] do
        let measured ← measureFixture fixture iterations
        samples := samples.push measured.1
        checksum := measured.2
      report fixture iterations samples checksum
  IO.println "HTTP/2 frame-header decode benchmark completed"
