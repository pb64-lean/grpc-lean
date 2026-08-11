import Grpc

namespace ChannelOwnerTest

open Grpc.ChannelLease
open Grpc.ChannelOwner

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def awaitSignal (promise : IO.Promise (Option Unit)) : IO Unit := do
  let some (some ()) ← IO.wait promise.result?
    | fail "test synchronization promise was dropped"

private partial def waitForPhase
    (owner : Owner Nat) (expected : Phase) (remaining : Nat := 2_000) : IO Unit := do
  if (← owner.snapshot).phase == expected then
    pure ()
  else if remaining = 0 then
    fail s!"timed out waiting for channel phase {repr expected}"
  else
    IO.sleep 1
    waitForPhase owner expected (remaining - 1)

private partial def waitForActiveCount
    (owner : Owner Nat) (expected : Nat) (remaining : Nat := 2_000) : IO Unit := do
  if (← owner.snapshot).activeCount == expected then
    pure ()
  else if remaining = 0 then
    fail s!"timed out waiting for channel active count {expected}"
  else
    IO.sleep 1
    waitForActiveCount owner expected (remaining - 1)

private def testDrainAndExactlyOnceClose : IO Unit := do
  let closeCount ← IO.mkRef 0
  let actionEntered : IO.Promise (Option Unit) ← IO.Promise.new
  let allowAction : IO.Promise (Option Unit) ← IO.Promise.new
  let owner ← Owner.create 41 {
    close := fun resource => do
      if resource != 41 then fail "owner passed the wrong resource to close"
      closeCount.modify (· + 1)
  }
  let worker ← IO.asTask <| owner.withResource fun resource => do
    if resource != 41 then fail "owner passed the wrong leased resource"
    actionEntered.resolve (some ())
    awaitSignal allowAction
    pure 17
  awaitSignal actionEntered
  let closer ← IO.asTask owner.close
  waitForPhase owner .draining
  match ← owner.withResource (fun _ => pure ()) with
  | .error (.unavailable .draining) => pure ()
  | _ => fail "draining channel admitted a new action"
  if (← closeCount.get) != 0 then
    fail "transport closed before the active lease drained"
  allowAction.resolve (some ())
  match ← IO.wait worker with
  | .ok (.ok 17) => pure ()
  | _ => fail "leased action did not complete cleanly"
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | _ => fail "channel close did not complete cleanly"
  let snapshot ← owner.snapshot
  if snapshot.phase != .closed || snapshot.activeCount != 0 then
    fail "clean close did not publish the closed invariant"
  match ← owner.close with
  | .ok () => pure ()
  | _ => fail "repeated close did not join the completed result"
  if (← closeCount.get) != 1 then
    fail "transport close did not run exactly once"

private def testActionFailureReleasesLease : IO Unit := do
  let closeCount ← IO.mkRef 0
  let owner ← Owner.create 9 {
    close := fun _ => closeCount.modify (· + 1)
  }
  match ← owner.withResource fun _ =>
      (throw (IO.userError "injected action failure") : IO Unit) with
  | .error (.action _) => pure ()
  | _ => fail "action exception was not classified"
  if (← owner.snapshot).activeCount != 0 then
    fail "action exception leaked its channel lease"
  match ← owner.close with
  | .ok () => pure ()
  | _ => fail "channel did not close after action failure"
  if (← closeCount.get) != 1 then
    fail "post-failure transport close count was wrong"

private def testRequestCloseInsideLeaseIsNonblocking : IO Unit := do
  let closeCount ← IO.mkRef 0
  let closeRan : IO.Promise (Option Unit) ← IO.Promise.new
  let owner ← Owner.create 37 {
    close := fun _ => do
      closeCount.modify (· + 1)
      closeRan.resolve (some ())
  }
  let worker ← IO.asTask <| owner.withResource fun _ => do
    match ← owner.requestClose with
    | .claimed => pure ()
    | decision =>
        fail s!"self close request did not claim cleanup: {repr decision}"
    let snapshot ← owner.snapshot
    if snapshot.phase != .draining || snapshot.activeCount != 1 then
      fail "self close request did not retain its exact active lease"
    if (← closeCount.get) != 0 then
      fail "self close request ran transport cleanup before its lease returned"
    pure 29
  match ← IO.wait worker with
  | .ok (.ok 29) => pure ()
  | _ => fail "self-requesting leased action did not return"
  awaitSignal closeRan
  match ← owner.awaitClose with
  | .ok () => pure ()
  | _ => fail "retained self-close driver did not settle"
  match ← owner.close with
  | .ok () => pure ()
  | _ => fail "close did not join the self-requested result"
  if (← closeCount.get) != 1 then
    fail "self-requested close did not run exactly once"

private def testRequestedCloseSurvivesCallerCancellation : IO Unit := do
  let closeCount ← IO.mkRef 0
  let requested : IO.Promise (Option Unit) ← IO.Promise.new
  let observeCancellation : IO.Promise (Option Unit) ← IO.Promise.new
  let owner ← Owner.create 43 {
    close := fun _ => closeCount.modify (· + 1)
  }
  let worker ← IO.asTask (owner.withResource fun _ => do
    discard <| owner.requestClose
    requested.resolve (some ())
    let some (some ()) ← IO.wait observeCancellation.result?
      | fail "cancellation fixture promise was dropped"
    if ← IO.checkCanceled then
      throw (IO.userError "requesting caller observed cancellation")
    pure ()) Task.Priority.dedicated
  awaitSignal requested
  let snapshot ← owner.snapshot
  if snapshot.phase != .draining || snapshot.activeCount != 1 then
    fail "cancelled requester did not publish its retained close driver"
  IO.cancel worker
  observeCancellation.resolve (some ())
  discard <| IO.wait worker
  waitForPhase owner .closed
  match ← owner.awaitClose with
  | .ok () => pure ()
  | _ => fail "caller cancellation abandoned the retained close driver"
  if (← closeCount.get) != 1 then
    fail "caller cancellation changed the exactly-once close count"

private def testConcurrentRequestAndCloseElection : IO Unit := do
  let closeCount ← IO.mkRef 0
  let leaseEntered : IO.Promise (Option Unit) ← IO.Promise.new
  let releaseLease : IO.Promise (Option Unit) ← IO.Promise.new
  let closeEntered : IO.Promise (Option Unit) ← IO.Promise.new
  let allowClose : IO.Promise (Option Unit) ← IO.Promise.new
  let owner ← Owner.create 47 {
    close := fun _ => do
      closeCount.modify (· + 1)
      closeEntered.resolve (some ())
      awaitSignal allowClose
  }
  let holder ← IO.asTask <| owner.withResource fun _ => do
    leaseEntered.resolve (some ())
    awaitSignal releaseLease
  awaitSignal leaseEntered

  let readyCount ← IO.mkRef 0
  let allReady : IO.Promise (Option Unit) ← IO.Promise.new
  let start : IO.Promise (Option Unit) ← IO.Promise.new
  let markReady : IO Unit := do
    let count ← readyCount.modifyGet fun current =>
      let next := current + 1
      (next, next)
    if count == 8 then allReady.resolve (some ())

  let requestCount ← IO.mkRef 0
  let requestsDone : IO.Promise (Option Unit) ← IO.Promise.new
  let claimedCount ← IO.mkRef 0
  let joinedCount ← IO.mkRef 0
  let invalidDecision ← IO.mkRef false
  let recordRequest (decision : BeginCloseDecision) : IO Unit := do
    match decision with
    | .claimed => claimedCount.modify (· + 1)
    | .joined => joinedCount.modify (· + 1)
    | .completed => invalidDecision.set true
    let count ← requestCount.modifyGet fun current =>
      let next := current + 1
      (next, next)
    if count == 4 then requestsDone.resolve (some ())

  let mut requesters :
      Array (Task (Except IO.Error (Except OwnerCloseError Unit))) := #[]
  for _ in [0:4] do
    let task ← IO.asTask (do
      markReady
      awaitSignal start
      recordRequest (← owner.requestClose)
      owner.awaitClose) Task.Priority.dedicated
    requesters := requesters.push task

  let mut closers :
      Array (Task (Except IO.Error (Except OwnerCloseError Unit))) := #[]
  for _ in [0:4] do
    let task ← IO.asTask (do
      markReady
      awaitSignal start
      owner.close) Task.Priority.dedicated
    closers := closers.push task

  awaitSignal allReady
  start.resolve (some ())
  awaitSignal requestsDone
  waitForPhase owner .draining
  let snapshot ← owner.snapshot
  if snapshot.activeCount != 1 then
    fail "concurrent close election lost the held lease"
  if ← invalidDecision.get then
    fail "a racing request observed completion before the held lease drained"
  if (← claimedCount.get) + (← joinedCount.get) != 4 then
    fail "racing request decisions were not accounted for exactly"
  if (← claimedCount.get) > 1 then
    fail "more than one racing requester claimed close ownership"
  if (← closeCount.get) != 0 then
    fail "racing close callers ran cleanup before the held lease drained"

  releaseLease.resolve (some ())
  awaitSignal closeEntered
  if (← closeCount.get) != 1 then
    fail "concurrent close election invoked more than one transport hook"
  for task in requesters do
    if ← IO.hasFinished task then
      fail "requestClose waiter returned before the elected hook settled"
  for task in closers do
    if ← IO.hasFinished task then
      fail "close waiter returned before the elected hook settled"
  allowClose.resolve (some ())

  match ← IO.wait holder with
  | .ok (.ok ()) => pure ()
  | _ => fail "held election lease did not release cleanly"
  for task in requesters do
    match ← IO.wait task with
    | .ok (.ok ()) => pure ()
    | _ => fail "racing requestClose caller did not join cleanly"
  for task in closers do
    match ← IO.wait task with
    | .ok (.ok ()) => pure ()
    | _ => fail "racing close caller did not join cleanly"
  let snapshot ← owner.snapshot
  if snapshot.phase != .closed || snapshot.activeCount != 0 then
    fail "concurrent close election did not publish a clean terminal state"
  if (← closeCount.get) != 1 then
    fail "concurrent close election did not retain exactly one hook"

private def testCleanupUncertaintyPoisonsAndCloses : IO Unit := do
  let closeCount ← IO.mkRef 0
  let owner ← Owner.create 13 {
    close := fun _ => closeCount.modify (· + 1)
  }
  match ← owner.withResourceChecked fun _ =>
      pure (.cleanupUncertain : Owner.CheckedResult Unit) with
  | .error .cleanupUncertain => pure ()
  | _ => fail "uncertain cleanup was not classified"
  let snapshot ← owner.snapshot
  if snapshot.phase != .closed || snapshot.activeCount != 0 then
    fail "uncertain cleanup did not poison and close the channel"
  match ← owner.withResourceChecked fun _ => pure (.release ()) with
  | .error (.unavailable .closed) => pure ()
  | _ => fail "poisoned channel admitted another checked action"
  match ← owner.close with
  | .ok () => pure ()
  | _ => fail "close did not join cleanup-uncertainty containment"
  if (← closeCount.get) != 1 then
    fail "cleanup-uncertainty containment did not close exactly once"

private def testCleanupUncertaintyRacesCloseAndActiveLease : IO Unit := do
  let closeCount ← IO.mkRef 0
  let owner ← Owner.create 53 {
    close := fun _ => closeCount.modify (· + 1)
  }
  let uncertainEntered : IO.Promise (Option Unit) ← IO.Promise.new
  let peerEntered : IO.Promise (Option Unit) ← IO.Promise.new
  let race : IO.Promise (Option Unit) ← IO.Promise.new
  let releasePeer : IO.Promise (Option Unit) ← IO.Promise.new

  let uncertain ← IO.asTask <| owner.withResourceChecked fun _ => do
    uncertainEntered.resolve (some ())
    awaitSignal race
    pure (.cleanupUncertain : Owner.CheckedResult Unit)
  let peer ← IO.asTask <| owner.withResource fun _ => do
    peerEntered.resolve (some ())
    awaitSignal releasePeer
    pure 71
  awaitSignal uncertainEntered
  awaitSignal peerEntered

  let closerReady : IO.Promise (Option Unit) ← IO.Promise.new
  let closer ← IO.asTask (do
    closerReady.resolve (some ())
    awaitSignal race
    owner.close) Task.Priority.dedicated
  awaitSignal closerReady
  race.resolve (some ())

  waitForPhase owner .draining
  waitForActiveCount owner 1
  if (← closeCount.get) != 0 then
    fail "cleanup uncertainty closed transport before the peer lease drained"
  if ← IO.hasFinished uncertain then
    fail "uncertain cleanup returned before the peer lease drained"
  if ← IO.hasFinished closer then
    fail "external close returned before the peer lease drained"
  match ← owner.withResource (fun _ => pure ()) with
  | .error (.unavailable .draining) => pure ()
  | _ => fail "uncertain cleanup race did not stop admission"

  releasePeer.resolve (some ())
  match ← IO.wait peer with
  | .ok (.ok 71) => pure ()
  | _ => fail "peer lease did not release cleanly"
  match ← IO.wait uncertain with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ => fail "uncertain cleanup race was not classified"
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | _ => fail "external close claimant did not join uncertain cleanup"
  let snapshot ← owner.snapshot
  if snapshot.phase != .closed || snapshot.activeCount != 0 then
    fail "uncertain cleanup race did not publish a clean terminal state"
  if (← closeCount.get) != 1 then
    fail "uncertain cleanup race did not run exactly one close hook"

private def testCloseFailureRetainsDraining : IO Unit := do
  let closeCount ← IO.mkRef 0
  let owner ← Owner.create 5 {
    close := fun _ => do
      closeCount.modify (· + 1)
      throw (IO.userError "injected close failure")
  }
  match ← owner.close with
  | .error (.transport _) => pure ()
  | _ => fail "transport close failure was not reported"
  let snapshot ← owner.snapshot
  if snapshot.phase != .draining || snapshot.activeCount != 0 then
    fail "ambiguous transport close published a clean terminal state"
  match ← owner.close with
  | .error (.transport _) => pure ()
  | _ => fail "repeated close did not join the original failure"
  if (← closeCount.get) != 1 then
    fail "ambiguous transport close was retried"

def run : IO Unit := do
  testDrainAndExactlyOnceClose
  testActionFailureReleasesLease
  testRequestCloseInsideLeaseIsNonblocking
  testRequestedCloseSurvivesCallerCancellation
  testConcurrentRequestAndCloseElection
  testCleanupUncertaintyPoisonsAndCloses
  testCleanupUncertaintyRacesCloseAndActiveLease
  testCloseFailureRetainsDraining
  IO.println "Remote channel owner tests passed"

end ChannelOwnerTest

def main : IO Unit :=
  ChannelOwnerTest.run
