import Grpc

open Grpc

private abbrev Encoded := Array Http2.Frame × Http2.Hpack.State
private abbrev Encoder :=
  Http2.Hpack.State → Nat → UnaryResponse → Nat → Bool → Except Status Encoded

private inductive Mode where
  | reference
  | candidate

private structure Fixture where
  label : String
  response : UnaryResponse
  maxFrameSize : Nat
  gzip : Bool := false

private def reusableState : Http2.Hpack.State :=
  { (Http2.Hpack.withoutDynamicTable {}) with pendingSizeUpdate := none }

private def payload (size : Nat) : ByteArray :=
  ByteArray.mk <| Array.ofFn (n := size) fun index =>
    UInt8.ofNat ((index * 17 + 29) % 251)

private def longMetadata : Metadata := #[{
  name := "x-response-benchmark"
  value := String.ofList (List.replicate 200 'a')
}]

private def fixtures : Array Fixture := #[
  { label := "empty_data", response := {},
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "exact_32", response := { data := payload 32 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "exact_128", response := { data := payload 128 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "exact_1024", response := { data := payload 1024 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "exact_16000", response := { data := payload 16000 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "exact_boundary", response := { data := payload 16379 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "one_over_boundary", response := { data := payload 16380 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength },
  { label := "gzip_128", response := { data := payload 128 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength, gzip := true },
  { label := "split_data", response := { data := payload 1024 }, maxFrameSize := 64 },
  { label := "split_headers", response := { metadata := longMetadata, data := payload 32 },
    maxFrameSize := 32 },
  { label := "split_trailers", response := { trailers := longMetadata, data := payload 32 },
    maxFrameSize := 64 },
  { label := "zero_max", response := { data := payload 32 }, maxFrameSize := 0 },
  { label := "error_status",
    response := { status := Status.internal "benchmark rejection", data := payload 32 },
    maxFrameSize := Http2.defaultMaxFramePayloadLength }
]

private def reference : Encoder :=
  fun state streamId response maxFrameSize gzip =>
    Http2.Transport.TestSupport.encodeUnaryResponseFramesReferenceForBenchmark
      state streamId response maxFrameSize gzip

private def candidate : Encoder :=
  fun state streamId response maxFrameSize gzip =>
    Http2.Transport.TestSupport.encodeUnaryResponseFramesCandidateForBenchmark
      state streamId response maxFrameSize gzip

private def sameState (left right : Http2.Hpack.State) : Bool :=
  left.dynamic == right.dynamic && left.maxSize == right.maxSize &&
    left.maxAllowedSize == right.maxAllowedSize &&
    left.pendingSizeUpdate == right.pendingSizeUpdate

private def sameResult (left right : Except Status Encoded) : Bool :=
  match left, right with
  | .ok (leftFrames, leftState), .ok (rightFrames, rightState) =>
      leftFrames == rightFrames && sameState leftState rightState
  | .error leftStatus, .error rightStatus => leftStatus == rightStatus
  | _, _ => false

private def validateParity : IO Nat := do
  for fixture in fixtures do
    let expected := reference reusableState 1 fixture.response fixture.maxFrameSize fixture.gzip
    let actual := candidate reusableState 1 fixture.response fixture.maxFrameSize fixture.gzip
    unless sameResult expected actual do
      throw (IO.userError s!"{fixture.label}: candidate differs from reference")
  pure fixtures.size

@[inline] private def byteAtD (bytes : ByteArray) (index : Nat) : UInt64 :=
  UInt64.ofNat (bytes[index]?.map UInt8.toNat |>.getD 0)

@[inline] private def frameDigest (frame : Http2.Frame) : UInt64 :=
  UInt64.ofNat frame.header.length * 1000003 +
    UInt64.ofNat frame.header.frameType.toUInt8.toNat * 10007 +
    UInt64.ofNat frame.header.flags.toNat * 101 +
    UInt64.ofNat frame.header.streamId * 17 +
    UInt64.ofNat frame.payload.size * 13 + byteAtD frame.payload 0 +
    byteAtD frame.payload (frame.payload.size - 1)

private def resultDigest : Except Status Encoded → UInt64
  | .error status =>
      UInt64.ofNat status.code.toNat * 1009 + UInt64.ofNat status.messageD.utf8ByteSize
  | .ok (frames, state) =>
      frames.foldl (fun total frame => total + frameDigest frame)
        (UInt64.ofNat frames.size * 65537 + UInt64.ofNat state.dynamic.size * 257 +
          UInt64.ofNat state.maxSize)

@[noinline] private def runIterations (encode : @& Encoder) (fixture : @& Fixture)
    (iterations : Nat) : IO UInt64 := do
  let mut checksum : UInt64 := 0
  for _ in [0:iterations] do
    checksum := checksum + resultDigest
      (encode reusableState 1 fixture.response fixture.maxFrameSize fixture.gzip)
  pure checksum

private def parseNatural (name value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{name} must be a nonnegative decimal integer")
  pure parsed

private def findFixture (label : String) : IO Fixture := do
  let some fixture := fixtures.find? (fun fixture => fixture.label == label)
    | throw (IO.userError s!"unknown fixture {label}")
  pure fixture

def main (args : List String) : IO Unit := do
  let (modeName, fixtureName, iterations, warmup) ← match args with
    | [mode, fixture, iterations, warmup] =>
      pure (mode, fixture, ← parseNatural "iterations" iterations,
        ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: unary_response_frame_assembly_benchmark " ++
          "(reference|candidate) fixture iterations warmup")
  let (mode, encode) ← match modeName with
    | "reference" => pure (Mode.reference, reference)
    | "candidate" => pure (Mode.candidate, candidate)
    | _ => throw (IO.userError "mode must be reference or candidate")
  let fixture ← findFixture fixtureName
  let semanticCases ← validateParity
  let expectedPerIteration := resultDigest
    (reference reusableState 1 fixture.response fixture.maxFrameSize fixture.gzip)
  let warmupChecksum ← runIterations encode fixture warmup
  unless warmupChecksum == expectedPerIteration * UInt64.ofNat warmup do
    throw (IO.userError "warmup checksum mismatch")
  let checksum ← runIterations encode fixture iterations
  unless checksum == expectedPerIteration * UInt64.ofNat iterations do
    throw (IO.userError "measured checksum mismatch")
  let selected := match mode with | .reference => "reference" | .candidate => "candidate"
  IO.println <| s!"benchmark=grpc_unary_response_frame_assembly_v1 mode={selected} " ++
    s!"fixture={fixture.label} iterations={iterations} warmup={warmup} checksum={checksum}"
  IO.println <| s!"semantic_parity=pass cases={semanticCases} " ++
    "scope=response_hpack,message_framing,http2_frame_assembly,result_digest"
