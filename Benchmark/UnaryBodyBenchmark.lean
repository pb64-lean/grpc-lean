import Grpc

open Grpc

/-!
# Authorized unary body benchmark

Measures the exact connection-owned body assembly performed after a unary
request reaches END_STREAM. Validation covers the ordinary one-DATA-frame
shape, fragmented and padded bodies, an empty body, and the existing frame
validation failures. The reuse label reports whether the ordinary payload is
returned without an additional copy.
-/

private def methodName : MethodName := {
  service := "acme.widgets.Benchmark"
  method := "Assemble"
}

private def registeredEntry : IO MethodEntry := do
  let registry := Registry.empty.registerUnary methodName fun request =>
    pure { data := request.data, status := Status.ok }
  match registry.findEntry? methodName with
  | some entry => pure entry
  | none => throw (IO.userError "benchmark unary entry was not registered")

private def headerFrame : Http2.Frame := {
  header := {
    length := 0
    frameType := .headers
    flags := Http2.FrameFlag.endHeaders
    streamId := 1
  }
}

private def dataFrame (payload : ByteArray) (flags : UInt8 := 0)
    (streamId : Nat := 1) : Http2.Frame := {
  header := {
    length := payload.size
    frameType := .data
    flags := flags
    streamId := streamId
  }
  payload := payload
}

private def streamState (entry : MethodEntry) (frames : Array Http2.Frame) :
    Http2.Connection.StreamState := {
  streamId := 1
  frames := frames
  requestMetadata := some Metadata.empty
  requestPreflight := some {
    method := methodName
    timeout := none
    contentLength := none
    requestUsesGzip := false
    clientAcceptsGzip := false
  }
  authorizedEntry? := some entry
}

private def assemble (state : Http2.Connection.State)
    (stream : Http2.Connection.StreamState) :
    Except Status Http2.Transport.UnaryRequestFrames :=
  Http2.Connection.TestSupport.authorizedUnaryRequestForStreamForBenchmark state stream

private def requestOrThrow (state : Http2.Connection.State)
    (stream : Http2.Connection.StreamState) : IO Http2.Transport.UnaryRequestFrames := do
  match assemble state stream with
  | .ok request => pure request
  | .error status => throw (IO.userError status.messageD)

private def expectError (state : Http2.Connection.State)
    (stream : Http2.Connection.StreamState) (message : String) : IO Unit := do
  match assemble state stream with
  | .error status =>
      unless status.messageD == message do
        throw (IO.userError s!"expected error '{message}', got '{status.messageD}'")
  | .ok _ => throw (IO.userError s!"expected error '{message}'")

private def messageWire : IO ByteArray := do
  let data := "acme.widgets unary request payload for body assembly timing".toUTF8
  match Message.encode { data := data } with
  | .ok wire => pure wire
  | .error status => throw (IO.userError status.messageD)

private def paddedPayload (body : ByteArray) : ByteArray :=
  ((ByteArray.empty.push 2).append body).push 0 |>.push 0

private def validate (state : Http2.Connection.State) (entry : MethodEntry)
    (wire : ByteArray) : IO (Http2.Connection.StreamState ×
      Http2.Connection.StreamState × Http2.Connection.StreamState) := do
  let one := streamState entry #[headerFrame,
    dataFrame wire Http2.FrameFlag.endStream]
  let split1 := wire.extract 0 2
  let split2 := wire.extract 2 11
  let split3 := wire.extract 11 wire.size
  let fragmented := streamState entry #[headerFrame, dataFrame split1,
    dataFrame split2, dataFrame split3 Http2.FrameFlag.endStream]
  let padded := streamState entry #[headerFrame,
    dataFrame (paddedPayload wire)
      (Http2.FrameFlag.padded ||| Http2.FrameFlag.endStream)]

  let oneRequest ← requestOrThrow state one
  let fragmentedRequest ← requestOrThrow state fragmented
  let paddedRequest ← requestOrThrow state padded
  let emptyRequest ← requestOrThrow state (streamState entry #[headerFrame])
  let zeroFramesRequest ← requestOrThrow state (streamState entry #[])
  let emptyThenBodyRequest ← requestOrThrow state (streamState entry #[headerFrame,
    dataFrame ByteArray.empty, dataFrame wire Http2.FrameFlag.endStream])
  unless oneRequest.body == wire && fragmentedRequest.body == wire &&
      paddedRequest.body == wire && emptyRequest.body.isEmpty &&
      zeroFramesRequest.body.isEmpty && emptyThenBodyRequest.body == wire do
    throw (IO.userError "authorized unary body assembly changed request bytes")

  expectError state (streamState entry #[headerFrame, dataFrame wire 0 3])
    "HTTP/2 request frames changed stream id"
  let wrongType : Http2.Frame := {
    header := { length := wire.size, frameType := .headers, streamId := 1 }
    payload := wire
  }
  expectError state (streamState entry #[headerFrame, wrongType])
    "expected HTTP/2 DATA frame"
  expectError state (streamState entry #[headerFrame,
    dataFrame ByteArray.empty Http2.FrameFlag.padded])
    "HTTP/2 DATA frame missing pad length"
  let excessivePadding := (ByteArray.empty.push 3).push 0
  expectError state (streamState entry #[headerFrame,
    dataFrame excessivePadding Http2.FrameFlag.padded])
    "HTTP/2 DATA padding exceeds payload size"
  let wrongStreamAndType : Http2.Frame := {
    header := {
      length := 0
      frameType := .headers
      flags := Http2.FrameFlag.padded
      streamId := 3
    }
  }
  expectError state (streamState entry #[headerFrame, wrongStreamAndType])
    "HTTP/2 request frames changed stream id"
  let wrongTypeAndPadding : Http2.Frame := {
    header := {
      length := 0
      frameType := .headers
      flags := Http2.FrameFlag.padded
      streamId := 1
    }
  }
  expectError state (streamState entry #[headerFrame, wrongTypeAndPadding])
    "expected HTTP/2 DATA frame"
  expectError state (streamState entry #[headerFrame,
    dataFrame wire Http2.FrameFlag.endStream, wrongType])
    "expected HTTP/2 DATA frame"
  pure (one, fragmented, padded)

private def assembleRepeated (state : Http2.Connection.State)
    (stream : Http2.Connection.StreamState) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match assemble state stream with
    | .ok request => checksum := checksum + request.body.size
    | .error status => throw (IO.userError status.messageD)
  pure checksum

private def measureBody (sink : IO.Ref Nat) (state : Http2.Connection.State)
    (stream : Http2.Connection.StreamState) (expectedSize iterations : Nat) : IO Nat := do
  let warmupIterations := Nat.min iterations 500
  let warmup ← assembleRepeated state stream warmupIterations
  unless warmup == expectedSize * warmupIterations do
    throw (IO.userError "unary body warmup checksum mismatch")
  let started ← IO.monoNanosNow
  sink.set (← assembleRepeated state stream iterations)
  let elapsed := (← IO.monoNanosNow) - started
  unless (← sink.get) == expectedSize * iterations do
    throw (IO.userError "unary body checksum mismatch")
  pure elapsed

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value ≤ head then value :: head :: tail
      else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def printSamples (label : String) (samples : Array Nat) (iterations : Nat) : IO Unit := do
  let elapsed := median samples
  let perOperation := if iterations == 0 then 0 else elapsed * 100 / iterations
  IO.println s!"{label}_samples_ns={formatSamples samples}"
  IO.println s!"{label}_median_ns_per_op={formatHundredths perOperation}"

private def parseNatArg (args : List String) (index fallback : Nat) : Nat :=
  match args[index]? >>= String.toNat? with
  | some value => Nat.max 1 value
  | none => fallback

unsafe def main (args : List String) : IO Unit := do
  let iterations := parseNatArg args 0 300000
  let rounds := parseNatArg args 1 9
  let state : Http2.Connection.State := {}
  let entry ← registeredEntry
  let wire ← messageWire
  let (one, fragmented, padded) ← validate state entry wire
  let oneRequest ← requestOrThrow state one
  IO.println s!"unary_body_single_payload_reused={ptrEq wire oneRequest.body}"
  IO.println "unary_body_validation=pass cases=13"

  let sink ← IO.mkRef 0
  let mut oneSamples := #[]
  let mut fragmentedSamples := #[]
  let mut paddedSamples := #[]
  for _ in [0:rounds] do
    oneSamples := oneSamples.push (← measureBody sink state one wire.size iterations)
    fragmentedSamples := fragmentedSamples.push
      (← measureBody sink state fragmented wire.size iterations)
    paddedSamples := paddedSamples.push (← measureBody sink state padded wire.size iterations)
  IO.println s!"authorized unary body: {rounds} rounds x {iterations} operations"
  printSamples "unary_body_single" oneSamples iterations
  printSamples "unary_body_fragmented" fragmentedSamples iterations
  printSamples "unary_body_padded" paddedSamples iterations
  IO.println "unary_body_checks=pass benchmark_kind=informative thresholds=none"
