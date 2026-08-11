module

public import Grpc.ChannelLease
public import Std.Sync.Mutex

public section

/-!
# Effectful owner for a shared remote channel

The mutex stores the proof-bearing `Grpc.ChannelLease.State`; the resource is
never handed out without an exact lease.  Closing has one owner, publishes
draining before waiting, waits on a one-shot drain promise, invokes the
transport close hook exactly once, and publishes `closed` only after both that
hook and the pure finish transition succeed.

The implementation is generic so concurrency and failure paths can be tested
without a network.  The managed transport channel instantiates it with the
client connection and its close operation.  That close joins its exact reader
and writer tasks; the native socket API still relies on shutdown plus handle
finalization rather than exposing a synchronous descriptor-close proof.
-/

namespace Grpc.ChannelOwner

open Grpc.ChannelLease

structure Hooks (Resource : Type) where
  close : Resource → IO Unit

inductive UseError where
  | unavailable (cause : AcquireError)
  | action (cause : IO.Error)
  /-- The exact call could not prove terminal cleanup; the channel was closed. -/
  | cleanupUncertain
  | supervisorInvariant

inductive OwnerCloseError where
  | transport (cause : IO.Error)
  | supervisorInvariant (cause : FinishCloseError)
  | completionDropped

private abbrev CloseDriver := Task (Except IO.Error Unit)

private structure RuntimeState where
  model : State
  /-- Exact custody of the elected close driver until terminal publication. -/
  driver : Option CloseDriver

structure Owner (Resource : Type) where
  private mk ::
  private resource : Resource
  private hooks : Hooks Resource
  private state : Std.Mutex RuntimeState
  private drained : IO.Promise Unit
  private completion : IO.Promise (Option (Except OwnerCloseError Unit))

namespace Owner

def create (resource : Resource) (hooks : Hooks Resource) : IO (Owner Resource) := do
  let state ← Std.Mutex.new { model := State.initial, driver := none }
  let drained ← IO.Promise.new
  let completion ← IO.Promise.new
  pure (.mk resource hooks state drained completion)

def snapshot (owner : Owner Resource) : IO State :=
  owner.state.atomically do
    pure (← get).model

private def acquireLease (owner : Owner Resource) :
    IO (Except AcquireError Lease) :=
  owner.state.atomically do
    let current ← get
    match acquire current.model with
    | .error error => pure (.error error)
    | .ok grant =>
        set { current with model := grant.state }
        pure (.ok grant.lease)

private def releaseLease (owner : Owner Resource) (lease : Lease) : IO Bool := do
  let result : Except Unit Bool ← owner.state.atomically do
    let current ← get
    match release current.model lease with
    | .error _ => pure (.error ())
    | .ok next =>
        set { current with model := next }
        pure (.ok (next.phase == .draining && next.activeCount == 0))
  match result with
  | .error () => pure false
  | .ok becameDrained =>
      if becameDrained then owner.drained.resolve ()
      pure true

/--
Run an effect while holding one exact call lease.  Both success and exception
paths release in a single `finally`-equivalent path; an impossible duplicate
or missing release is elevated to a supervisor invariant failure.
-/
def withResource
    (owner : Owner Resource) (action : Resource → IO α) :
    IO (Except UseError α) := do
  match ← owner.acquireLease with
  | .error error => pure (.error (.unavailable error))
  | .ok lease =>
      let released ← IO.mkRef false
      let result : Except IO.Error α ←
        try
          pure (Except.ok (← action owner.resource))
        catch error =>
          pure (Except.error error)
        finally
          released.set (← owner.releaseLease lease)
      if !(← released.get) then
        pure (.error .supervisorInvariant)
      else
        match result with
        | .ok value => pure (Except.ok value)
        | .error error => pure (Except.error (.action error))

private def awaitCompletion
    (owner : Owner Resource) : IO (Except OwnerCloseError Unit) := do
  let some (some result) ← IO.wait owner.completion.result?
    | pure (.error .completionDropped)
  pure result

private def publishClosed (owner : Owner Resource) :
    IO (Except OwnerCloseError Unit) :=
  owner.state.atomically do
    let current ← get
    match finishClose current.model with
    | .error error => pure (.error (.supervisorInvariant error))
    | .ok closed =>
        set { current with model := closed }
        pure (.ok ())

private def finishClaimedClose
    (owner : Owner Resource) : IO (Except OwnerCloseError Unit) := do
  let some () ← IO.wait owner.drained.result?
    | let result : Except OwnerCloseError Unit := .error .completionDropped
      owner.completion.resolve (some result)
      return result
  let transportResult : Except OwnerCloseError Unit ←
    try
      owner.hooks.close owner.resource
      pure (Except.ok ())
    catch error =>
      pure (Except.error (.transport error))
  let result ← match transportResult with
    | .error error => pure (Except.error error)
    | .ok () => owner.publishClosed
  owner.completion.resolve (some result)
  pure result

private def clearCloseDriver (owner : Owner Resource) : IO Unit :=
  owner.state.atomically do
    modify fun current => { current with driver := none }

/--
Run the elected close operation under retained task custody.  The ordinary
close path already converts transport failures to data.  This final catch also
settles the shared result if an unexpected `IO.Error` escapes the driver, so a
joined waiter cannot be left behind an owner-retained but completed task.
-/
private def driveClaimedClose (owner : Owner Resource) : IO Unit := do
  let escaped : Option IO.Error ←
    try
      discard <| owner.finishClaimedClose
      pure none
    catch error =>
      pure (some error)
  match escaped with
  | none => pure ()
  | some error =>
      owner.completion.resolve (some (.error (.transport error)))
  owner.clearCloseDriver

private structure CloseDriverCandidate (Resource : Type) where
  start : IO.Promise (Option Bool)
  task : CloseDriver

/--
Allocate a close driver behind a start gate.  The candidate cannot touch the
resource until its task handle has either been installed in `RuntimeState` or
the gate has told it that another driver already owns cleanup.

Both promise and task allocation are `BaseIO`; keeping that fact in this
helper's result type makes the checked-cleanup ordering explicit: preparing a
candidate cannot throw after the action lease has been acquired.
-/
private def prepareCloseDriver
    (owner : Owner Resource) : BaseIO (CloseDriverCandidate Resource) := do
  let start : IO.Promise (Option Bool) ← IO.Promise.new
  let task ← IO.asTask do
    let some (some elected) ← IO.wait start.result?
      | pure ()
    if elected then owner.driveClaimedClose
  pure { start, task }

private def publishCloseRequest
    (owner : Owner Resource)
    (candidate : CloseDriverCandidate Resource) :
    IO (BeginCloseDecision × Bool) :=
  owner.state.atomically do
    let current ← get
    let transition := beginClose current.model
    if transition.decision == .claimed then
      set { current with
        model := transition.state
        driver := some candidate.task }
    else
      set { current with model := transition.state }
    pure (transition.decision, transition.state.activeCount == 0)

/--
Publish draining and retain the exactly-once close driver without waiting for
active leases to drain.  This is the close operation that is safe to invoke
from inside `withResource` or `withResourceChecked`: the leased action must
return (or throw) to release its own lease before anyone calls `awaitClose`.

The driver's start gate is released only after its task handle and the
`draining` state have been published together under the owner mutex.  Dropping
or cancelling the requesting task after this function returns therefore does
not abandon cleanup.
-/
def requestClose (owner : Owner Resource) : IO BeginCloseDecision := do
  let candidate ← owner.prepareCloseDriver
  let (decision, alreadyDrained) ←
    owner.publishCloseRequest candidate
  if decision == .claimed && alreadyDrained then
    owner.drained.resolve ()
  candidate.start.resolve (some (decision == .claimed))
  pure decision

/--
Join the shared terminal close result after `requestClose` has been issued.
Calling this while the current action still owns one of this owner's leases
would wait on that same lease and is therefore invalid.
-/
def awaitClose (owner : Owner Resource) : IO (Except OwnerCloseError Unit) :=
  owner.awaitCompletion

/--
Close exactly once.  Concurrent callers join the same result.  If the
transport close fails, ownership remains visibly draining and later callers
observe the same terminal failure rather than retrying an ambiguous close.

This convenience operation requests and then joins close.  It must not be
called by an action currently running under this same owner's `withResource*`
lease: Lean exposes no current-task identity with which to distinguish that
self-lease from another task's lease.  Such an action calls `requestClose`,
returns to release its lease, and only then may an unleased caller call
`awaitClose` or `close`.  The transport `Hooks.close` callback is subject to
the same rule: it is the elected close driver itself and must not recursively
join its own `close` or `awaitClose` completion.
-/
def close (owner : Owner Resource) : IO (Except OwnerCloseError Unit) := do
  discard <| owner.requestClose
  owner.awaitClose

private def poisonAndReleaseLease
    (owner : Owner Resource) (lease : Lease) :
    IO (Except Unit BeginCloseDecision) := do
  let candidate ← owner.prepareCloseDriver
  let result : Except Unit (BeginCloseDecision × Bool) ←
    owner.state.atomically do
      let current ← get
      let transition := beginClose current.model
      match release transition.state lease with
      | .error _ => pure (.error ())
      | .ok next =>
          if transition.decision == .claimed then
            set { current with model := next, driver := some candidate.task }
          else
            set { current with model := next }
          pure (.ok (
            transition.decision,
            next.phase == .draining && next.activeCount == 0))
  match result with
  | .error () =>
      candidate.start.resolve (some false)
      pure (.error ())
  | .ok (decision, becameDrained) =>
      if becameDrained then owner.drained.resolve ()
      candidate.start.resolve (some (decision == .claimed))
      pure (.ok decision)

/--
Result of a leased action that can explicitly report uncertain transport
cleanup.  That report atomically stops admission, releases the reporting
lease, and elects (or joins) the single connection closer before returning.
-/
inductive CheckedResult (α : Type) where
  | release (value : α)
  | cleanupUncertain

/--
Run an action whose cleanup acknowledgement is part of its result.

An uncertain result poisons the whole shared transport: no later action can be
admitted, all already-admitted leases drain, and this call does not return
until the exactly-once connection close has completed or failed.
-/
def withResourceChecked
    (owner : Owner Resource)
    (action : Resource → IO (CheckedResult α)) :
    IO (Except UseError α) := do
  match ← owner.acquireLease with
  | .error error => pure (.error (.unavailable error))
  | .ok lease =>
      let result : Except IO.Error (CheckedResult α) ←
        try
          pure (Except.ok (← action owner.resource) :
            Except IO.Error (CheckedResult α))
        catch error =>
          pure (Except.error error :
            Except IO.Error (CheckedResult α))
      match result with
      | .error error =>
          if ← owner.releaseLease lease then
            pure (.error (.action error))
          else
            pure (.error .supervisorInvariant)
      | .ok (.release value) =>
          if ← owner.releaseLease lease then
            pure (.ok value)
          else
            pure (.error .supervisorInvariant)
      | .ok .cleanupUncertain =>
          match ← owner.poisonAndReleaseLease lease with
          | .error () => pure (.error .supervisorInvariant)
          | .ok _ =>
              discard <| owner.awaitCompletion
              pure (.error .cleanupUncertain)

end Owner

end Grpc.ChannelOwner
