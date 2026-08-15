import Grpc

open Grpc

/-!
# Deadline phase benchmark

This informative benchmark separates the public deadline runner's task/promise
cost from the connection scheduler's registration cost. Timed samples use
uninstrumented runtimes and enter `Async.block` once per batch, matching a
production dispatch owner rather than charging an extra bridge to every call.
A separate bounded pass checks exact registration and unregistration counts,
verifies that no callback fired, and confirms that the no-deadline path never
consults its supplied runtime.  After the scheduler is shut down, a fixed-wave
phase measures the production dispatch-registration gate and separately checks
that no task crosses the gate before its modeled publication point.
-/

private structure RuntimeCounters where
  registrations : IO.Ref Nat
  unregisters : IO.Ref Nat
  expirations : IO.Ref Nat
  failures : IO.Ref Nat

private structure CounterSnapshot where
  registrations : Nat
  unregisters : Nat
  expirations : Nat
  failures : Nat

namespace RuntimeCounters

private def new : IO RuntimeCounters := do
  pure {
    registrations := ← IO.mkRef 0
    unregisters := ← IO.mkRef 0
    expirations := ← IO.mkRef 0
    failures := ← IO.mkRef 0
  }

private def snapshot (counters : RuntimeCounters) : IO CounterSnapshot := do
  pure {
    registrations := ← counters.registrations.get
    unregisters := ← counters.unregisters.get
    expirations := ← counters.expirations.get
    failures := ← counters.failures.get
  }

end RuntimeCounters

private def noOpRuntime : DeadlineRuntime := {
  externalTimer := true
  registerTask := fun _ _ _ _ => pure (pure ())
}

private def realSchedulerRuntime
    (scheduler : Http2.Connection.DeadlineScheduler) : DeadlineRuntime := {
  externalTimer := true
  registerTask := fun deadline cancel expire _ =>
    scheduler.register deadline expire cancel
}

private def countedNoOpRuntime (counters : RuntimeCounters) : DeadlineRuntime := {
  externalTimer := true
  registerTask := fun _ _ _ _ => do
    counters.registrations.modify (fun count => count + 1)
    pure do
      counters.unregisters.modify (fun count => count + 1)
}

private def countedSchedulerRuntime (scheduler : Http2.Connection.DeadlineScheduler)
    (counters : RuntimeCounters) : DeadlineRuntime := {
  externalTimer := true
  registerTask := fun deadline cancel expire _ => do
    counters.registrations.modify (fun count => count + 1)
    let unregister ← scheduler.register deadline
      (do
        counters.expirations.modify (fun count => count + 1)
        expire)
      (do
        counters.failures.modify (fun count => count + 1)
        cancel)
    pure do
      counters.unregisters.modify (fun count => count + 1)
      unregister
}

private def runRepeatedAsync (deadline? : Option Nat) (runtime : DeadlineRuntime)
    (iterations : Nat) : Std.Async.Async Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match ← Registry.runWithDeadlineUntilAsync deadline? (pure 1) (some runtime) with
    | .ok value => checksum := checksum + value
    | .error status => throw (IO.userError status.messageD)
  pure checksum

private def runRepeated (deadline? : Option Nat) (runtime : DeadlineRuntime)
    (iterations : Nat) : IO Nat :=
  Std.Async.Async.block (runRepeatedAsync deadline? runtime iterations)

private def measurePhase (sink : IO.Ref Nat) (deadline? : Option Nat)
    (runtime : DeadlineRuntime) (iterations : Nat) : IO Nat := do
  let started ← IO.monoNanosNow
  sink.set (← runRepeated deadline? runtime iterations)
  let ended ← IO.monoNanosNow
  let checksum ← sink.get
  unless checksum == iterations do
    throw (IO.userError s!"deadline phase benchmark checksum mismatch: {checksum}")
  pure (ended - started)

private structure Samples where
  noDeadline : Array Nat := #[]
  timedNoOp : Array Nat := #[]
  timedScheduler : Array Nat := #[]

private def runRounds (sink : IO.Ref Nat) (deadline : Nat)
    (noDeadlineRuntime timedNoOpRuntime timedSchedulerRuntime : DeadlineRuntime)
    (iterations rounds : Nat) : IO Samples := do
  let mut samples : Samples := {}
  for round in [0:rounds] do
    match round % 3 with
    | 0 =>
        let noDeadline ← measurePhase sink none noDeadlineRuntime iterations
        let timedNoOp ← measurePhase sink (some deadline) timedNoOpRuntime iterations
        let timedScheduler ←
          measurePhase sink (some deadline) timedSchedulerRuntime iterations
        samples := {
          noDeadline := samples.noDeadline.push noDeadline
          timedNoOp := samples.timedNoOp.push timedNoOp
          timedScheduler := samples.timedScheduler.push timedScheduler
        }
    | 1 =>
        let timedNoOp ← measurePhase sink (some deadline) timedNoOpRuntime iterations
        let timedScheduler ←
          measurePhase sink (some deadline) timedSchedulerRuntime iterations
        let noDeadline ← measurePhase sink none noDeadlineRuntime iterations
        samples := {
          noDeadline := samples.noDeadline.push noDeadline
          timedNoOp := samples.timedNoOp.push timedNoOp
          timedScheduler := samples.timedScheduler.push timedScheduler
        }
    | _ =>
        let timedScheduler ←
          measurePhase sink (some deadline) timedSchedulerRuntime iterations
        let noDeadline ← measurePhase sink none noDeadlineRuntime iterations
        let timedNoOp ← measurePhase sink (some deadline) timedNoOpRuntime iterations
        samples := {
          noDeadline := samples.noDeadline.push noDeadline
          timedNoOp := samples.timedNoOp.push timedNoOp
          timedScheduler := samples.timedScheduler.push timedScheduler
        }
  pure samples

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

private def nsPerOperationHundredths (elapsed iterations : Nat) : Nat :=
  if iterations == 0 then 0 else elapsed * 100 / iterations

private def printPhase (label : String) (samples : Array Nat)
    (iterations : Nat) : IO Unit := do
  let elapsed := median samples
  let perOperation := nsPerOperationHundredths elapsed iterations
  IO.println s!"{label}_samples_ns={formatSamples samples}"
  IO.println s!"{label}_median_ns_per_op={formatHundredths perOperation}"

private def printDelta (label : String) (candidate baseline iterations : Nat) : IO Unit := do
  let magnitude := if candidate ≤ baseline then baseline - candidate else candidate - baseline
  let perOperation := nsPerOperationHundredths magnitude iterations
  let sign := if candidate < baseline then "-" else "+"
  IO.println s!"{label}_ns_per_op={sign}{formatHundredths perOperation}"

private def printCounters (label : String) (snapshot : CounterSnapshot) : IO Unit :=
  IO.println <| s!"{label}_counters registrations={snapshot.registrations} " ++
    s!"unregisters={snapshot.unregisters} expirations={snapshot.expirations} " ++
    s!"failures={snapshot.failures}"

private def checkCounters (label : String) (snapshot : CounterSnapshot)
    (expectedRegistrations : Nat) : IO Unit := do
  unless snapshot.registrations == expectedRegistrations &&
      snapshot.unregisters == expectedRegistrations &&
      snapshot.expirations == 0 && snapshot.failures == 0 do
    throw (IO.userError s!"{label} deadline runtime counter mismatch")

private def dispatchRegistrationGateWaveWidth : Nat := 64

private structure DispatchGateValidation where
  publications : Nat
  resolutions : Nat
  completions : Nat
  crossedBeforePublication : Nat
  allTasksFinished : Bool
  checksum : Nat

private def runDispatchRegistrationGateAsync (iterations : Nat) : Std.Async.Async Nat := do
  let mut launched := 0
  let mut checksum := 0
  while launched < iterations do
    let waveSize := Nat.min dispatchRegistrationGateWaveWidth (iterations - launched)
    let mut tasks := #[]
    for _ in [0:waveSize] do
      let registered ← IO.Promise.new
      let task ← Std.Async.Async.toIO do
        Http2.Connection.TestSupport.waitUntilDispatchRegisteredForBenchmark registered
        pure 1
      -- Model the production spawn -> publish -> resolve ordering.  The exact
      -- spawned handle remains owned until the wave is joined below.
      registered.resolve ()
      tasks := tasks.push task
    for task in tasks do
      checksum := checksum + (← Std.Async.Async.ofAsyncTask task)
    launched := launched + waveSize
  pure checksum

private def runDispatchRegistrationGate (iterations : Nat) : IO Nat :=
  Std.Async.Async.block (runDispatchRegistrationGateAsync iterations)

private def measureDispatchRegistrationGate (sink : IO.Ref Nat)
    (iterations : Nat) : IO Nat := do
  let started ← IO.monoNanosNow
  sink.set (← runDispatchRegistrationGate iterations)
  let ended ← IO.monoNanosNow
  let checksum ← sink.get
  unless checksum == iterations do
    throw (IO.userError s!"dispatch registration gate benchmark checksum mismatch: {checksum}")
  pure (ended - started)

private def runDispatchRegistrationGateRounds (sink : IO.Ref Nat)
    (iterations rounds : Nat) : IO (Array Nat) := do
  let mut samples := #[]
  for _ in [0:rounds] do
    samples := samples.push (← measureDispatchRegistrationGate sink iterations)
  pure samples

private def validateDispatchRegistrationGateAsync
    (iterations : Nat) : Std.Async.Async DispatchGateValidation := do
  let mut launched := 0
  let mut publications := 0
  let mut resolutions := 0
  let mut completions := 0
  let mut crossedBeforePublication := 0
  let mut checksum := 0
  let mut allTasksFinished := true
  while launched < iterations do
    let waveSize := Nat.min dispatchRegistrationGateWaveWidth (iterations - launched)
    let mut tasks := #[]
    for offset in [0:waveSize] do
      let gateId := launched + offset + 1
      let published ← IO.Promise.new
      let registered ← IO.Promise.new
      let task ← Std.Async.Async.toIO do
        Http2.Connection.TestSupport.waitUntilDispatchRegisteredForBenchmark registered
        pure (1, !(← published.isResolved))
      published.resolve ()
      publications := gateId
      registered.resolve ()
      resolutions := resolutions + 1
      tasks := tasks.push task
    for task in tasks do
      let result ← Std.Async.Async.ofAsyncTask task
      checksum := checksum + result.1
      completions := completions + 1
      if result.2 then
        crossedBeforePublication := crossedBeforePublication + 1
    -- `ofAsyncTask` resumes from the async result promise.  Fence the exact
    -- native task handles as well before checking their finished state.
    for task in tasks do
      discard <| Std.Async.AsyncTask.block task
      unless ← IO.hasFinished task do
        allTasksFinished := false
    launched := launched + waveSize
  pure {
    publications := publications
    resolutions := resolutions
    completions := completions
    crossedBeforePublication := crossedBeforePublication
    allTasksFinished := allTasksFinished
    checksum := checksum
  }

private def checkDispatchGateValidation (validation : DispatchGateValidation)
    (expected : Nat) : IO Unit := do
  unless validation.publications == expected &&
      validation.resolutions == expected &&
      validation.completions == expected &&
      validation.crossedBeforePublication == 0 &&
      validation.allTasksFinished && validation.checksum == expected do
    throw (IO.userError <| s!"dispatch registration gate ordering validation failed: " ++
      s!"publications={validation.publications} resolutions={validation.resolutions} " ++
      s!"completions={validation.completions} " ++
      s!"crossed_before_publication={validation.crossedBeforePublication} " ++
      s!"all_tasks_finished={validation.allTasksFinished} checksum={validation.checksum}")

private def parseNat (value? : Option String) (fallback : Nat) : Nat :=
  Nat.max 1 ((value? >>= String.toNat?).getD fallback)

def main (args : List String) : IO Unit := do
  let iterations := parseNat args.head? 10000
  let rounds := parseNat (args.drop 1).head? 7
  let warmupIterations := Nat.min iterations 200
  let sink ← IO.mkRef 0
  let noDeadlineCounters ← RuntimeCounters.new
  let timedNoOpCounters ← RuntimeCounters.new
  let timedSchedulerCounters ← RuntimeCounters.new
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let timedSchedulerRuntime := realSchedulerRuntime scheduler
  let countedNoDeadlineRuntime := countedNoOpRuntime noDeadlineCounters
  let countedTimedNoOpRuntime := countedNoOpRuntime timedNoOpCounters
  let countedTimedSchedulerRuntime :=
    countedSchedulerRuntime scheduler timedSchedulerCounters
  let deadline := (← IO.monoNanosNow) + 24 * 60 * 60 * 1000000000
  let validationIterations := Nat.min iterations 1000

  let result : Except IO.Error Samples ←
    try
      let warmupNoDeadline ← runRepeated none noOpRuntime warmupIterations
      let warmupTimedNoOp ← runRepeated
        (some deadline) noOpRuntime warmupIterations
      let warmupTimedScheduler ← runRepeated
        (some deadline) timedSchedulerRuntime warmupIterations
      unless warmupNoDeadline == warmupIterations &&
          warmupTimedNoOp == warmupIterations &&
          warmupTimedScheduler == warmupIterations do
        throw (IO.userError "deadline phase benchmark warmup checksum mismatch")
      let samples ← runRounds sink deadline noOpRuntime noOpRuntime
        timedSchedulerRuntime iterations rounds
      let validationNoDeadline ← runRepeated none countedNoDeadlineRuntime
        validationIterations
      let validationTimedNoOp ← runRepeated (some deadline) countedTimedNoOpRuntime
        validationIterations
      let validationTimedScheduler ← runRepeated
        (some deadline) countedTimedSchedulerRuntime validationIterations
      unless validationNoDeadline == validationIterations &&
          validationTimedNoOp == validationIterations &&
          validationTimedScheduler == validationIterations do
        throw (IO.userError "deadline phase benchmark validation checksum mismatch")
      pure (Except.ok samples)
    catch error =>
      pure (Except.error error)
  discard <| Std.Async.Async.block scheduler.shutdown
  let samples ← match result with
    | Except.ok samples => pure samples
    | Except.error error => throw error

  -- Keep the deadline scheduler stopped throughout this phase so it measures
  -- only the production dispatch-registration promise/task adapter.
  let gateWarmup ← runDispatchRegistrationGate warmupIterations
  unless gateWarmup == warmupIterations do
    throw (IO.userError "dispatch registration gate warmup checksum mismatch")
  let gateValidation ← Std.Async.Async.block <|
    validateDispatchRegistrationGateAsync validationIterations
  checkDispatchGateValidation gateValidation validationIterations
  let gateSamples ← runDispatchRegistrationGateRounds sink iterations rounds

  let noDeadlineSnapshot ← noDeadlineCounters.snapshot
  let timedNoOpSnapshot ← timedNoOpCounters.snapshot
  let timedSchedulerSnapshot ← timedSchedulerCounters.snapshot
  IO.println s!"deadline_phase_validation_iterations={validationIterations}"
  printCounters "no_deadline_no_op_validation" noDeadlineSnapshot
  printCounters "timed_no_op_runtime_validation" timedNoOpSnapshot
  printCounters "timed_real_scheduler_validation" timedSchedulerSnapshot
  checkCounters "no-deadline/no-op" noDeadlineSnapshot 0
  checkCounters "timed no-op runtime" timedNoOpSnapshot validationIterations
  checkCounters "timed real scheduler" timedSchedulerSnapshot validationIterations

  IO.println s!"deadline phase benchmark: {rounds} rotating rounds x {iterations} calls"
  printPhase "no_deadline_no_op" samples.noDeadline iterations
  printPhase "timed_no_op_runtime" samples.timedNoOp iterations
  printPhase "timed_real_scheduler" samples.timedScheduler iterations
  let noDeadlineMedian := median samples.noDeadline
  let timedNoOpMedian := median samples.timedNoOp
  let timedSchedulerMedian := median samples.timedScheduler
  printDelta "timed_wrapper_incremental" timedNoOpMedian noDeadlineMedian iterations
  printDelta "real_scheduler_registration_incremental" timedSchedulerMedian timedNoOpMedian
    iterations
  printDelta "timed_real_scheduler_total_incremental" timedSchedulerMedian noDeadlineMedian
    iterations
  IO.println "deadline_phase_counter_checks=pass benchmark_kind=informative thresholds=none"
  printPhase "dispatch_registration_gate" gateSamples iterations
  IO.println s!"dispatch_registration_gate_wave_width={dispatchRegistrationGateWaveWidth}"
  IO.println <| s!"dispatch_registration_gate_validation publications={gateValidation.publications} " ++
    s!"resolutions={gateValidation.resolutions} completions={gateValidation.completions} " ++
    s!"crossed_before_publication={gateValidation.crossedBeforePublication} " ++
    s!"all_tasks_finished={gateValidation.allTasksFinished} checksum={gateValidation.checksum}"
  IO.println "dispatch_registration_gate_checks=pass benchmark_kind=informative thresholds=none"
