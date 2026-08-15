import Grpc

open Grpc

private def method : MethodName := {
  service := "benchmark.authorization.v1.AuthorizationService"
  method := "Check"
}

private def readyState : Http2.Connection.State := {
  (Http2.Connection.initialState) with
  prefaceReceived := true
  clientSettingsReceived := true
}

private def requestMetadata (timed : Bool) : Metadata :=
  let value := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
    |>.insert "authorization" "BenchmarkScheme local-token"
  if timed then value.insert "grpc-timeout" "1H" else value

private def headersFrame (timed : Bool) : IO Http2.Frame := do
  let (payload, _) ← match Http2.Hpack.encodeHeaderBlock {} (requestMetadata timed) with
    | .ok encoded => pure encoded
    | .error status => throw (IO.userError status.messageD)
  pure {
    header := {
      length := payload.size
      frameType := .headers
      flags := Http2.FrameFlag.endHeaders
      streamId := 1
    }
    payload
  }

private def runRepeated (registry : Registry) (frame : Http2.Frame)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match ← Http2.Connection.processFrame registry readyState frame with
    | .error status => throw (IO.userError status.messageD)
    | .ok (state, emitted) =>
        checksum := checksum + state.streams.size + emitted.size
  pure checksum

private def measureRegistry (registry : Registry) (frame : Http2.Frame)
    (iterations : Nat) : IO (Nat × Nat) := do
  discard <| runRepeated registry frame (Nat.min iterations 200)
  let started ← IO.monoNanosNow
  let checksum ← runRepeated registry frame iterations
  pure ((← IO.monoNanosNow) - started, checksum)

private def measureChecked (registry : Registry) (frame : Http2.Frame)
    (iterations : Nat) : IO Nat := do
  let (elapsed, checksum) ← measureRegistry registry frame iterations
  if checksum != iterations then
    throw (IO.userError s!"authorization benchmark checksum mismatch: {checksum}")
  pure elapsed

private def measurePair (baseline candidate : Registry) (frame : Http2.Frame)
    (iterations : Nat) (reverse : Bool) : IO (Nat × Nat) := do
  if reverse then
    let candidateElapsed ← measureChecked candidate frame iterations
    let baselineElapsed ← measureChecked baseline frame iterations
    pure (baselineElapsed, candidateElapsed)
  else
    let baselineElapsed ← measureChecked baseline frame iterations
    let candidateElapsed ← measureChecked candidate frame iterations
    pure (baselineElapsed, candidateElapsed)

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value <= head then value :: head :: tail
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

private def relativePercent (candidate baseline : Nat) : String :=
  if baseline == 0 then
    "n/a"
  else if baseline <= candidate then
    s!"+{formatHundredths ((candidate - baseline) * 10000 / baseline)}"
  else
    s!"-{formatHundredths ((baseline - candidate) * 10000 / baseline)}"

private def improvementPercent (baseline candidate : Nat) : String :=
  if baseline == 0 then
    "n/a"
  else if candidate <= baseline then
    formatHundredths ((baseline - candidate) * 10000 / baseline)
  else
    s!"-{formatHundredths ((candidate - baseline) * 10000 / baseline)}"

private def printMeasurement (label : String) (elapsed iterations : Nat) : IO Unit := do
  let nsPerOpTimes100 := if iterations == 0 then 0 else elapsed * 100 / iterations
  IO.println s!"{label}: median_elapsed_ns={elapsed} median_ns_per_op={formatHundredths nsPerOpTimes100}"

private def parseIterations (args : List String) : Nat :=
  match args.head? >>= String.toNat? with
  | some n => n
  | none => 10000

private def parseRounds (args : List String) : Nat :=
  match (args.drop 1).head? >>= String.toNat? with
  | some n => Nat.max 1 n
  | none => 5

def main (args : List String) : IO Unit := do
  let iterations := parseIterations args
  let rounds := parseRounds args
  let defaultRegistry := Registry.empty.registerUnary method fun request =>
    pure { data := request.data, status := Status.ok }
  let pureRegistry := defaultRegistry.withPureRequestHeaderAuthorizer fun entry _ =>
    AuthorizationResult.acceptRegistered entry
  let effectfulRegistry := defaultRegistry.withRequestHeaderAuthorizer fun entry _ =>
    pure (AuthorizationResult.acceptRegistered entry)
  let untimed ← headersFrame false
  let timed ← headersFrame true

  IO.println s!"request-header authorization: {rounds} alternating rounds x {iterations} complete HEADERS iterations"
  let mut untimedDefaultSamples := #[]
  let mut untimedPureSamples := #[]
  let mut timedDefaultSamples := #[]
  let mut timedPureDefaultPairSamples := #[]
  let mut timedEffectfulSamples := #[]
  let mut timedPureEffectfulPairSamples := #[]
  for round in [0:rounds] do
    let reverse := round % 2 == 1
    if reverse then
      let (effectfulElapsed, pureElapsed) ←
        measurePair effectfulRegistry pureRegistry timed iterations reverse
      timedEffectfulSamples := timedEffectfulSamples.push effectfulElapsed
      timedPureEffectfulPairSamples := timedPureEffectfulPairSamples.push pureElapsed
      let (defaultElapsed, pureElapsed) ←
        measurePair defaultRegistry pureRegistry timed iterations reverse
      timedDefaultSamples := timedDefaultSamples.push defaultElapsed
      timedPureDefaultPairSamples := timedPureDefaultPairSamples.push pureElapsed
      let (defaultElapsed, pureElapsed) ←
        measurePair defaultRegistry pureRegistry untimed iterations reverse
      untimedDefaultSamples := untimedDefaultSamples.push defaultElapsed
      untimedPureSamples := untimedPureSamples.push pureElapsed
    else
      let (defaultElapsed, pureElapsed) ←
        measurePair defaultRegistry pureRegistry untimed iterations reverse
      untimedDefaultSamples := untimedDefaultSamples.push defaultElapsed
      untimedPureSamples := untimedPureSamples.push pureElapsed
      let (defaultElapsed, pureElapsed) ←
        measurePair defaultRegistry pureRegistry timed iterations reverse
      timedDefaultSamples := timedDefaultSamples.push defaultElapsed
      timedPureDefaultPairSamples := timedPureDefaultPairSamples.push pureElapsed
      let (effectfulElapsed, pureElapsed) ←
        measurePair effectfulRegistry pureRegistry timed iterations reverse
      timedEffectfulSamples := timedEffectfulSamples.push effectfulElapsed
      timedPureEffectfulPairSamples := timedPureEffectfulPairSamples.push pureElapsed

  let untimedDefault := median untimedDefaultSamples
  let untimedPure := median untimedPureSamples
  let timedDefault := median timedDefaultSamples
  let timedPureDefaultPair := median timedPureDefaultPairSamples
  let timedEffectful := median timedEffectfulSamples
  let timedPureEffectfulPair := median timedPureEffectfulPairSamples

  IO.println s!"untimed_default_samples_ns={formatSamples untimedDefaultSamples}"
  IO.println s!"untimed_pure_samples_ns={formatSamples untimedPureSamples}"
  printMeasurement "untimed_default" untimedDefault iterations
  printMeasurement "untimed_pure" untimedPure iterations
  IO.println s!"untimed_pure_overhead_pct={relativePercent untimedPure untimedDefault} target_max_pct=+5.00"
  IO.println s!"timed_default_samples_ns={formatSamples timedDefaultSamples}"
  IO.println s!"timed_pure_default_pair_samples_ns={formatSamples timedPureDefaultPairSamples}"
  printMeasurement "timed_default" timedDefault iterations
  printMeasurement "timed_pure_default_pair" timedPureDefaultPair iterations
  IO.println s!"timed_pure_overhead_pct={relativePercent timedPureDefaultPair timedDefault}"
  IO.println s!"timed_effectful_samples_ns={formatSamples timedEffectfulSamples}"
  IO.println s!"timed_pure_effectful_pair_samples_ns={formatSamples timedPureEffectfulPairSamples}"
  printMeasurement "timed_effectful" timedEffectful iterations
  printMeasurement "timed_pure_effectful_pair" timedPureEffectfulPair iterations
  IO.println s!"timed_pure_vs_effectful_improvement_pct={improvementPercent timedEffectful timedPureEffectfulPair} target_min_pct=5.00"

  unless untimedPure * 100 <= untimedDefault * 105 do
    throw (IO.userError "untimed pure authorization exceeded the +5% default-path overhead target")
  unless timedPureDefaultPair * 100 <= timedDefault * 105 do
    throw (IO.userError "timed pure authorization exceeded the +5% default-path overhead target")
  unless timedPureEffectfulPair * 100 <= timedEffectful * 95 do
    throw (IO.userError "timed pure authorization missed the 5% effectful-path improvement target")
  IO.println "authorization_benchmark_thresholds=pass"
