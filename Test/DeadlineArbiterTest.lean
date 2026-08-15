import Grpc

open Grpc

namespace Test.DeadlineArbiter

private def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do
    throw (IO.userError failure)

private def expectOk (result : Except Status α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status =>
      throw (IO.userError s!"{description}: {status.code}: {status.messageD}")

private def expectStatus (result : Except Status α) (code : Code)
    (description : String) : IO Status :=
  match result with
  | .ok _ => throw (IO.userError s!"{description}: expected {code}")
  | .error status => do
      expect (status.code == code)
        s!"{description}: expected {code}, got {status.code}: {status.messageD}"
      pure status

private def method : MethodName := {
  service := "test.deadline.v1.DeadlineService"
  method := "Check"
}

private def metadata : Metadata :=
  Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

private def preflight : Headers.RequestPreflight := {
  method := method
  timeout := none
  contentLength := none
  requestUsesGzip := false
  clientAcceptsGzip := false
}

private def requestBody : IO ByteArray :=
  expectOk (Message.encode { data := ByteArray.mk #[1, 2, 3] })
    "encode managed-unary request"

private def scriptedClock (values : Array Nat) : IO (BaseIO Nat × IO (Array Nat)) := do
  let remaining ← IO.mkRef values
  let observed ← IO.mkRef (#[] : Array Nat)
  let now : BaseIO Nat := do
    let value ← remaining.modifyGet fun values =>
      match values[0]? with
      | some value => (value, values.extract 1 values.size)
      | none => (0, #[])
    observed.modify fun seen => seen.push value
    pure value
  pure (now, observed.get)

/-- Timing is used only as a watchdog around Promise/task joins.  Every race
below is ordered by an explicit gate or a direct terminal callback. -/
private def watchdogMilliseconds : Nat := 5000

private partial def awaitTaskResultWithin (task : Task α) (remaining : Nat) :
    IO (Option α) := do
  if ← IO.hasFinished task then
    pure (some task.get)
  else if remaining == 0 then
    pure none
  else
    IO.sleep 1
    awaitTaskResultWithin task (remaining - 1)

private def awaitTaskResult (task : Task α) (description : String) : IO α := do
  match ← awaitTaskResultWithin task watchdogMilliseconds with
  | some result => pure result
  | none =>
      IO.cancel task
      throw (IO.userError s!"{description}: watchdog expired")

private def awaitPromise (promise : IO.Promise α) (description : String) : IO α := do
  let waiter ← IO.asTask do
    match ← IO.wait promise.result? with
    | some value => pure value
    | none => throw (IO.userError s!"{description}: promise was dropped")
  match ← awaitTaskResult waiter description with
  | .ok value => pure value
  | .error error => throw error

private abbrev Lifecycle (α : Type) :=
  Http2.Connection.TestSupport.ManagedDeadlineLifecycleForBenchmark α

private abbrev TerminalPhase :=
  Http2.Connection.TestSupport.ManagedDeadlineTerminalPhaseForBenchmark

private def futureDeadline : IO Nat := do
  pure ((← IO.monoNanosNow) + 60000000000)

private def registrationCount
    (scheduler : Http2.Connection.DeadlineScheduler) : IO Nat :=
  Http2.Connection.TestSupport.deadlineSchedulerRegistrationCountForBenchmark scheduler

private def snapshot (lifecycle : Lifecycle α) :=
  Http2.Connection.TestSupport.managedDeadlineLifecycleSnapshotForBenchmark lifecycle

private def awaitLifecycle (lifecycle : Lifecycle α) (description : String) :
    IO (Except IO.Error (Except Status α)) :=
  awaitTaskResult lifecycle.task description

private def shutdownScheduler
    (scheduler : Http2.Connection.DeadlineScheduler) : IO Unit := do
  let task ← Std.Async.Async.toIO scheduler.shutdown
  match ← awaitTaskResult task "join deadline scheduler" with
  | .ok () => pure ()
  | .error error => throw error

private def expectPhase (lifecycle : Lifecycle α) (phase : TerminalPhase)
    (description : String) : IO Unit := do
  let observed ← snapshot lifecycle
  expect (observed.phase == phase)
    s!"{description}: unexpected terminal phase {repr observed.phase}"

private def expectNoRegistration (scheduler : Http2.Connection.DeadlineScheduler)
    (lifecycle : Lifecycle α) (description : String) : IO Unit := do
  let observed ← snapshot lifecycle
  expect (!observed.registrationOwned)
    s!"{description}: terminal owner retained its one-shot release"
  expect ((← registrationCount scheduler) == 0)
    s!"{description}: scheduler retained a live registration"

/-- The inline handler primitive must accept a response only when both exact
clock brackets are strictly before the absolute deadline. -/
private def testInlineSuccessBeforeDeadline : IO Unit := do
  let body ← requestBody
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[99, 99]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata body preflight handler 100 now
  let response ← expectOk result "dispatch before deadline"
  expect (response.data == ByteArray.mk #[1, 2, 3])
    "before-deadline dispatch changed the handler response"
  expect ((← handlerCalls.get) == 1)
    "before-deadline dispatch did not run its handler exactly once"
  expect ((← observed) == #[99, 99])
    "before-deadline dispatch did not bracket the handler with exact clock reads"

/-- A handler that returns at the exact absolute deadline loses locally even
when no scheduler callback has run yet. -/
private def testInlinePostHandlerExactDeadlineSelfExpiry : IO Unit := do
  let body ← requestBody
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[99, 100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata body preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "post-handler exact-deadline self-expiry"
  expect ((← handlerCalls.get) == 1)
    "post-handler self-expiry did not run its handler exactly once"
  expect ((← observed) == #[99, 100])
    "post-handler self-expiry did not observe the scripted deadline crossing"

/-- Reaching the boundary before handler entry suppresses arbitrary user IO;
the terminal arbiter may therefore publish expiry without a late handler. -/
private def testInlineExactDeadlineSuppressesHandler : IO Unit := do
  let body ← requestBody
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let (now, observed) ← scriptedClock #[100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata body preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "pre-handler exact-deadline self-expiry"
  expect ((← handlerCalls.get) == 0)
    "exact pre-handler deadline entered arbitrary handler IO"
  expect ((← observed) == #[100])
    "pre-handler exact-deadline path performed an unexpected clock read"

/-- Malformed request decoding is still part of the call phase: if it
finishes at the absolute boundary, expiry wins without entering the handler. -/
private def testInlineDecodeErrorAtDeadlineSelfExpires : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let handler : UnaryHandler := fun _ => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { status := Status.ok }
  let (now, observed) ← scriptedClock #[100]
  let result ← Std.Async.Async.block <|
    Registry.empty.dispatchManagedUnaryInlineUntilAsync
      metadata ByteArray.empty preflight handler 100 now
  discard <| expectStatus result .deadlineExceeded
    "decode error at exact deadline self-expiry"
  expect ((← handlerCalls.get) == 0)
    "decode-error self-expiry entered arbitrary handler IO"
  expect ((← observed) == #[100])
    "decode-error self-expiry did not read the exact boundary once"

/-- Production decompression errors use the same local boundary rule without
adding a clock read to successful decompression. -/
private def testDecompressionErrorAtDeadlineSelfExpires : IO Unit := do
  let malformed := ByteArray.mk #[0xff, 0x00, 0x01]
  let (now, observed) ← scriptedClock #[100]
  let result ←
    Http2.Connection.TestSupport.decompressManagedUnaryBodyUntilForBenchmark
      false none malformed 100 now
  discard <| expectStatus result .deadlineExceeded
    "decompression error at exact deadline self-expiry"
  expect ((← observed) == #[100])
    "decompression-error self-expiry did not read the exact boundary once"

/-- A response wins once, releases scheduler custody, and ignores both late
expiry and late scheduler-failure callbacks. -/
private def testBeforeDeadlineSuccessAndLateExpiry : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) (pure 7)
  try
    lifecycle.publish
    match ← awaitLifecycle lifecycle "join before-deadline success" with
    | .ok (.ok value) =>
        expect (value == 7) "before-deadline lifecycle changed its response"
    | .ok (.error status) =>
        throw (IO.userError s!"before-deadline lifecycle failed: {status.messageD}")
    | .error error => throw error
    expectPhase lifecycle .publishedResponse
      "before-deadline response publication"
    expectNoRegistration scheduler lifecycle
      "before-deadline response release"
    let completed ← snapshot lifecycle
    expect completed.taskFinished
      "before-deadline response did not finish its exact retained task"

    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    Http2.Connection.TestSupport.failManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .publishedResponse
      "late terminal callbacks after response"
    expectNoRegistration scheduler lifecycle
      "late terminal callbacks after response"
  finally
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

/-- The scheduler callback claims and publishes deadline before this test ever
joins the still-retained handler task.  Repeated terminal callbacks cannot
replace that publication or retake the one-shot release. -/
private def testExpiryWhileHandlerBlocked : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let action : GrpcM Nat := do
    entered.resolve ()
    match ← IO.wait release.result? with
    | some () => pure 11
    | none => throw (Status.internal "blocked deadline handler gate was dropped")
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) action
  try
    lifecycle.publish
    awaitPromise entered "wait for blocked deadline handler"
    let active ← snapshot lifecycle
    expect (active.phase == .open && active.registrationOwned && !active.taskFinished)
      s!"blocked deadline handler was not live and registered: {repr active}"
    expect ((← registrationCount scheduler) == 1)
      "blocked deadline handler did not own exactly one scheduler registration"

    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .publishedDeadline
      "deadline publication before handler join"
    expectNoRegistration scheduler lifecycle
      "deadline publication before handler join"
    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    Http2.Connection.TestSupport.failManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .publishedDeadline
      "repeated callbacks after deadline publication"
    expectNoRegistration scheduler lifecycle
      "repeated callbacks after deadline publication"

    release.resolve ()
    discard <| awaitLifecycle lifecycle "join expired retained handler"
    let completed ← snapshot lifecycle
    expect completed.taskFinished
      "expired handler's exact retained task did not finish"
  finally
    release.resolve ()
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

/-- Once expiry has selected the terminal, a handler that returns before the
scheduler finishes publication must wait rather than retire the active owner
and suppress the winning terminal. -/
private def testClaimedExpiryRetainsLosingOuter : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let loserWaiting ← IO.Promise.new
  let action : GrpcM Nat := do
    entered.resolve ()
    match ← IO.wait release.result? with
    | some () => pure 23
    | none => throw (Status.internal "claimed-expiry handler gate was dropped")
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) action (loserWaiting.resolve ())
  try
    lifecycle.publish
    awaitPromise entered "wait for claimed-expiry handler"
    expect
      (← Http2.Connection.TestSupport.claimManagedDeadlineExpiryForBenchmark lifecycle)
      "deadline owner did not select expiry"
    release.resolve ()
    awaitPromise loserWaiting "wait for handler to lose selected expiry"

    let retained ← snapshot lifecycle
    expect (retained.phase == .claimedDeadline && retained.registrationOwned &&
        !retained.taskFinished)
      s!"losing handler retired before deadline publication: {repr retained}"
    expect ((← registrationCount scheduler) == 1)
      "selected-but-unpublished expiry lost scheduler custody"

    Http2.Connection.TestSupport.finishClaimedManagedDeadlineExpiryForBenchmark lifecycle
    discard <| awaitLifecycle lifecycle "join claimed-expiry losing handler"
    expectPhase lifecycle .publishedDeadline
      "claimed expiry publication handoff"
    expectNoRegistration scheduler lifecycle
      "claimed expiry publication handoff"
    let completed ← snapshot lifecycle
    expect completed.taskFinished
      "claimed expiry did not retire its exact handler task"
  finally
    release.resolve ()
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

/-- Reset may cancel after expiry has selected the terminal but before its
scheduler callback publishes.  Cancellation must resolve the losing outer's
completion wait as well as release the registration; cooperative task cancel
alone does not wake a task suspended on a Promise. -/
private def testCancellationReleasesClaimedExpiryHandoff : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let loserWaiting ← IO.Promise.new
  let action : GrpcM Nat := do
    entered.resolve ()
    match ← IO.wait release.result? with
    | some () => pure 29
    | none => throw (Status.internal "cancelled-claim handler gate was dropped")
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) action (loserWaiting.resolve ())
  try
    lifecycle.publish
    awaitPromise entered "wait for cancelled-claim handler"
    expect
      (← Http2.Connection.TestSupport.claimManagedDeadlineExpiryForBenchmark lifecycle)
      "deadline owner did not select cancellable expiry"
    release.resolve ()
    awaitPromise loserWaiting "wait for cancelled-claim losing handler"

    let retained ← snapshot lifecycle
    expect (retained.phase == .claimedDeadline && retained.registrationOwned &&
        !retained.taskFinished)
      s!"losing handler did not enter claimed-expiry handoff: {repr retained}"

    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitLifecycle lifecycle "join cancelled claimed-expiry handoff"
    let completed ← snapshot lifecycle
    expect (completed.phase == .cancelled && completed.cancelled && completed.taskFinished)
      s!"cancellation stranded claimed-expiry handoff: {repr completed}"
    expectNoRegistration scheduler lifecycle "cancelled claimed-expiry handoff"
  finally
    release.resolve ()
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

/-- Cancellation may win while the exact task is still held behind its
publication gate; no handler, terminal response, or scheduler registration is
allowed to escape. -/
private def testCancellationBeforePublication : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let handlerCalls ← IO.mkRef 0
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) (do
        handlerCalls.modify (fun calls => calls + 1)
        pure 13)
  try
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .cancelled "pre-publication cancellation"
    lifecycle.publish
    discard <| awaitLifecycle lifecycle "join pre-publication cancellation"
    expect ((← handlerCalls.get) == 0)
      "pre-publication cancellation entered arbitrary handler IO"
    let completed ← snapshot lifecycle
    expect (completed.phase == .cancelled && completed.cancelled && completed.taskFinished)
      s!"pre-publication cancellation did not retire exactly: {repr completed}"
    expectNoRegistration scheduler lifecycle "pre-publication cancellation"
    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    Http2.Connection.TestSupport.failManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .cancelled
      "late callbacks after pre-publication cancellation"
  finally
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

/-- Cancellation after handler entry takes the registered release, cancels the
exact retained task, and publishes no competing terminal. -/
private def testCancellationAfterRegistration : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let action : GrpcM Nat := do
    entered.resolve ()
    match ← IO.wait release.result? with
    | some () => pure 17
    | none => throw (Status.internal "registered cancellation gate was dropped")
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) action
  try
    lifecycle.publish
    awaitPromise entered "wait for registered cancellation handler"
    let active ← snapshot lifecycle
    expect (active.phase == .open && active.registrationOwned && !active.taskFinished)
      s!"registered cancellation handler was not active: {repr active}"
    expect ((← registrationCount scheduler) == 1)
      "registered cancellation handler did not own exactly one registration"

    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    release.resolve ()
    discard <| awaitLifecycle lifecycle "join registered cancellation"
    let completed ← snapshot lifecycle
    expect (completed.phase == .cancelled && completed.cancelled && completed.taskFinished)
      s!"registered cancellation did not retire exactly: {repr completed}"
    expectNoRegistration scheduler lifecycle "registered cancellation"
    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    Http2.Connection.TestSupport.failManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .cancelled
      "late callbacks after registered cancellation"
  finally
    release.resolve ()
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

/-- Scheduler shutdown drives the installed failure callback, which publishes
one failure terminal, releases registration custody, and cancels the exact
blocked task.  A later expiry remains a loser. -/
private def testSchedulerFailureWhileHandlerBlocked : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let action : GrpcM Nat := do
    entered.resolve ()
    match ← IO.wait release.result? with
    | some () => pure 19
    | none => throw (Status.internal "scheduler failure gate was dropped")
  let lifecycle ←
    Http2.Connection.TestSupport.spawnManagedDeadlineLifecycleForBenchmark
      scheduler (← futureDeadline) action
  try
    lifecycle.publish
    awaitPromise entered "wait for scheduler-failure handler"
    expect ((← registrationCount scheduler) == 1)
      "scheduler-failure handler did not register"

    shutdownScheduler scheduler
    expectPhase lifecycle .publishedSchedulerFailure
      "scheduler failure publication before handler join"
    expectNoRegistration scheduler lifecycle "scheduler failure release"
    Http2.Connection.TestSupport.failManagedDeadlineLifecycleForBenchmark lifecycle
    Http2.Connection.TestSupport.expireManagedDeadlineLifecycleForBenchmark lifecycle
    expectPhase lifecycle .publishedSchedulerFailure
      "late callbacks after scheduler failure"
    expectNoRegistration scheduler lifecycle
      "late callbacks after scheduler failure"

    release.resolve ()
    discard <| awaitLifecycle lifecycle "join scheduler-failed retained handler"
    let completed ← snapshot lifecycle
    expect completed.taskFinished
      "scheduler-failed handler's exact retained task did not finish"
  finally
    release.resolve ()
    Http2.Connection.TestSupport.cancelManagedDeadlineLifecycleForBenchmark lifecycle
    discard <| awaitTaskResultWithin lifecycle.task watchdogMilliseconds
    shutdownScheduler scheduler

def run : IO Unit := do
  testInlineSuccessBeforeDeadline
  testInlinePostHandlerExactDeadlineSelfExpiry
  testInlineExactDeadlineSuppressesHandler
  testInlineDecodeErrorAtDeadlineSelfExpires
  testDecompressionErrorAtDeadlineSelfExpires
  testBeforeDeadlineSuccessAndLateExpiry
  testExpiryWhileHandlerBlocked
  testClaimedExpiryRetainsLosingOuter
  testCancellationReleasesClaimedExpiryHandoff
  testCancellationBeforePublication
  testCancellationAfterRegistration
  testSchedulerFailureWhileHandlerBlocked
  IO.println "managed-unary deadline terminal arbiter tests pass"

end Test.DeadlineArbiter

def main : IO Unit :=
  Test.DeadlineArbiter.run
