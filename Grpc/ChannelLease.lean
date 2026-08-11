module

public import Std.Tactic

public section

/-!
# Shared outbound-channel lease kernel

A process shares one outbound channel across every remote service it calls.
This kernel models the channel owner's lock-protected state.  A runtime must
acquire a lease before starting an RPC and release it in `finally`; shutdown
first publishes `draining`, then waits for the exact lease set to become empty,
then closes the transport and publishes `closed`.

The private constructors make these safety properties structural:

* leases are unique and were allocated below `nextLease`;
* no acquisition succeeds after draining is published; and
* a closed channel owns no call leases.
-/

namespace Grpc.ChannelLease

inductive Phase where
  | accepting
  | draining
  | closed
deriving DecidableEq, Repr

instance : BEq Phase where
  beq left right := decide (left = right)

instance : LawfulBEq Phase where
  eq_of_beq := of_decide_eq_true

structure Lease where
  private mk ::
  id : Nat
deriving DecidableEq, Repr

instance : BEq Lease where
  beq left right := decide (left = right)

instance : LawfulBEq Lease where
  eq_of_beq := of_decide_eq_true

structure State where
  private mk ::
  phase : Phase
  nextLease : Nat
  private active : List Lease
  private unique : active.Nodup
  private activeBelowNext :
    ∀ lease, lease ∈ active → lease.id < nextLease
  private closedEmpty :
    phase = .closed → active = []

namespace State

def initial : State :=
  .mk .accepting 0 [] .nil (by simp) (by simp)

def activeLeases (state : State) : List Lease :=
  state.active

def activeCount (state : State) : Nat :=
  state.active.length

def owns (state : State) (lease : Lease) : Bool :=
  decide (lease ∈ state.active)

def Invariant (state : State) : Prop :=
  state.activeLeases.Nodup ∧
    (∀ lease, lease ∈ state.activeLeases → lease.id < state.nextLease) ∧
    (state.phase = .closed → state.activeLeases = [])

theorem invariant (state : State) : state.Invariant :=
  ⟨state.unique, state.activeBelowNext, state.closedEmpty⟩

theorem initial_phase : State.initial.phase = .accepting := by
  simp [State.initial]

theorem closed_has_no_leases
    (state : State) (closed : state.phase = .closed) :
    state.activeLeases = [] :=
  state.closedEmpty closed

theorem closed_active_count_zero
    (state : State) (closed : state.phase = .closed) :
    state.activeCount = 0 := by
  change state.active.length = 0
  rw [state.closedEmpty closed]
  rfl

end State

inductive AcquireError where
  | draining
  | closed
deriving BEq, DecidableEq, Repr

structure Grant where
  state : State
  lease : Lease

private def acquireAccepting
    (state : State) (_accepting : state.phase = .accepting) : Grant := by
  let lease : Lease := .mk state.nextLease
  have fresh : lease ∉ state.active := by
    intro present
    have below := state.activeBelowNext lease present
    simp [lease] at below
  refine {
    state := .mk .accepting (state.nextLease + 1) (lease :: state.active)
      (List.nodup_cons.mpr ⟨fresh, state.unique⟩) ?_ (by simp)
    lease
  }
  intro candidate present
  rcases List.mem_cons.mp present with same | previous
  · cases same
    simp [lease]
  · exact Nat.lt_succ_of_lt (state.activeBelowNext candidate previous)

def acquire (state : State) : Except AcquireError Grant :=
  match phase : state.phase with
  | .accepting => .ok (acquireAccepting state phase)
  | .draining => .error .draining
  | .closed => .error .closed

inductive ReleaseError where
  | unknownLease
deriving BEq, DecidableEq, Repr

private def releasedState
    (state : State) (lease : Lease) : State :=
  .mk state.phase state.nextLease (state.active.erase lease)
    (state.unique.erase lease)
    (by
      intro candidate present
      exact state.activeBelowNext candidate (List.mem_of_mem_erase present))
    (by
      intro closed
      rw [state.closedEmpty closed]
      simp)

def release (state : State) (lease : Lease) :
    Except ReleaseError State :=
  if _owned : lease ∈ state.active then
    .ok (releasedState state lease)
  else
    .error .unknownLease

inductive BeginCloseDecision where
  | claimed
  | joined
  | completed
deriving DecidableEq, Repr

instance : BEq BeginCloseDecision where
  beq left right := decide (left = right)

instance : LawfulBEq BeginCloseDecision where
  eq_of_beq := of_decide_eq_true

structure BeginCloseResult where
  state : State
  decision : BeginCloseDecision

private def drainingState (state : State) : State :=
  .mk .draining state.nextLease state.active state.unique
    state.activeBelowNext (by simp)

def beginClose (state : State) : BeginCloseResult :=
  match state.phase with
  | .accepting => ⟨drainingState state, .claimed⟩
  | .draining => ⟨state, .joined⟩
  | .closed => ⟨state, .completed⟩

inductive FinishCloseError where
  | notDraining
  | activeLeases (count : Nat)
deriving BEq, DecidableEq, Repr

private def closedState
    (state : State) (_draining : state.phase = .draining)
    (_empty : state.active = []) : State :=
  .mk .closed state.nextLease [] .nil (by simp) (by simp)

/--
Publish `closed` only after the transport has been closed and the exact active
lease set is empty.  The effectful owner performs the transport close between
the emptiness observation and this transition while retaining exclusive close
ownership.
-/
def finishClose (state : State) : Except FinishCloseError State :=
  match phase : state.phase with
  | .accepting | .closed => .error .notDraining
  | .draining =>
      if empty : state.active = [] then
        .ok (closedState state phase empty)
      else
        .error (.activeLeases state.active.length)

theorem acquire_success_starts_accepting
    (state : State) (grant : Grant)
    (accepted : acquire state = .ok grant) :
    state.phase = .accepting := by
  unfold acquire at accepted
  split at accepted
  · assumption
  · contradiction
  · contradiction

theorem acquire_adds_exact_lease
    (state : State) (grant : Grant)
    (accepted : acquire state = .ok grant) :
    grant.state.activeCount = state.activeCount + 1 ∧
      grant.state.owns grant.lease = true := by
  unfold acquire at accepted
  split at accepted
  · injection accepted with equality
    subst grant
    simp [acquireAccepting, State.activeCount, State.owns]
  · contradiction
  · contradiction

theorem acquire_preserves_invariant
    (state : State) (grant : Grant)
    (_accepted : acquire state = .ok grant) :
    grant.state.Invariant :=
  grant.state.invariant

theorem release_removes_exact_lease
    (state next : State) (lease : Lease)
    (released : release state lease = .ok next) :
    next.activeCount + 1 = state.activeCount ∧
      next.owns lease = false := by
  simp only [release] at released
  split at released
  · rename_i owned
    cases released
    constructor
    · simp only [releasedState, State.activeCount,
        List.length_erase_of_mem owned]
      have positive := List.length_pos_of_mem owned
      omega
    · simp [releasedState, State.owns, state.unique.not_mem_erase]
  · contradiction

theorem begin_close_stops_admission (state : State) :
    (beginClose state).state.phase ≠ .accepting ∨
      (beginClose state).decision = .completed := by
  cases phase : state.phase <;>
    simp [beginClose, drainingState, phase]

theorem draining_rejects_acquire
    (state : State) (draining : state.phase = .draining) :
    acquire state = .error .draining := by
  unfold acquire
  split <;> simp_all

theorem begin_close_claim_invalidates_admission
    (state : State)
    (claimed : (beginClose state).decision = .claimed) :
    (beginClose state).state.phase = .draining ∧
      ∀ grant, acquire (beginClose state).state ≠ .ok grant := by
  have resultPhase : (beginClose state).state.phase = .draining := by
    cases phase : state.phase with
    | accepting => simp [beginClose, drainingState, phase]
    | draining | closed => simp [beginClose, phase] at claimed
  refine ⟨resultPhase, ?_⟩
  intro grant accepted
  have accepting :=
    acquire_success_starts_accepting (beginClose state).state grant accepted
  rw [resultPhase] at accepting
  contradiction

theorem finish_close_is_clean
    (state closed : State)
    (finished : finishClose state = .ok closed) :
    closed.phase = .closed ∧ closed.activeCount = 0 := by
  unfold finishClose at finished
  split at finished
  · contradiction
  · contradiction
  · split at finished
    · injection finished with equality
      subst closed
      simp [closedState, State.activeCount]
    · contradiction

theorem finish_close_requires_drained
    (state closed : State)
    (finished : finishClose state = .ok closed) :
    state.activeCount = 0 := by
  unfold finishClose at finished
  split at finished
  · contradiction
  · contradiction
  · split at finished
    · rename_i empty
      simp [State.activeCount, empty]
    · contradiction

theorem active_channel_cannot_finish
    (state : State) (positive : 0 < state.activeCount) :
    ∀ closed, finishClose state ≠ .ok closed := by
  intro closed finished
  have drained := finish_close_requires_drained state closed finished
  omega

/-!
Phase-preservation and per-phase `beginClose` equations.  Their proofs unfold
the private transition bodies, so they live beside the kernel; the effectful
shared-channel supervisor re-proves its driver/phase coherence by rewriting
with these statements instead of unfolding this module's internals.
-/

theorem acquire_preserves_phase
    (state : State) (grant : Grant)
    (accepted : acquire state = .ok grant) :
    grant.state.phase = state.phase := by
  have oldAccepting :=
    acquire_success_starts_accepting state grant accepted
  have newAccepting : grant.state.phase = .accepting := by
    unfold acquire at accepted
    split at accepted <;> try contradiction
    injection accepted with equality
    subst grant
    rfl
  exact newAccepting.trans oldAccepting.symm

theorem release_preserves_phase
    (state next : State) (lease : Lease)
    (released : release state lease = .ok next) :
    next.phase = state.phase := by
  unfold release at released
  split at released
  · injection released with equality
    subst next
    rfl
  · contradiction

theorem beginClose_phase_nonaccepting
    (model : State) :
    (beginClose model).state.phase ≠ .accepting := by
  cases phase : model.phase with
  | accepting =>
      have resultPhase :
          (beginClose model).state.phase = .draining := by
        simp only [beginClose, phase]
        rfl
      rw [resultPhase]
      decide
  | draining =>
      simpa [beginClose, phase] using phase
  | closed =>
      simpa [beginClose, phase] using phase

theorem beginClose_closed_implies_closed
    (model : State)
    (closed : (beginClose model).state.phase = .closed) :
    model.phase = .closed := by
  cases phase : model.phase with
  | accepting =>
      have resultPhase :
          (beginClose model).state.phase = .draining := by
        simp only [beginClose, phase]
        rfl
      rw [resultPhase] at closed
      contradiction
  | draining =>
      simpa [beginClose, phase] using closed
  | closed => rfl

theorem beginClose_activeCount
    (model : State) :
    (beginClose model).state.activeCount = model.activeCount := by
  cases phase : model.phase with
  | accepting =>
      simp only [beginClose, phase]
      rfl
  | draining | closed =>
      simp [beginClose, phase]

theorem beginClose_accepting_phase
    (model : State) (accepting : model.phase = .accepting) :
    (beginClose model).state.phase = .draining := by
  simp only [beginClose, accepting]
  rfl

theorem beginClose_accepting_decision
    (model : State) (accepting : model.phase = .accepting) :
    (beginClose model).decision = .claimed := by
  simp [beginClose, accepting]

theorem beginClose_draining_state
    (model : State) (draining : model.phase = .draining) :
    (beginClose model).state = model := by
  simp [beginClose, draining]

theorem beginClose_draining_decision
    (model : State) (draining : model.phase = .draining) :
    (beginClose model).decision = .joined := by
  simp [beginClose, draining]

theorem beginClose_closed_state
    (model : State) (closed : model.phase = .closed) :
    (beginClose model).state = model := by
  simp [beginClose, closed]

theorem beginClose_closed_decision
    (model : State) (closed : model.phase = .closed) :
    (beginClose model).decision = .completed := by
  simp [beginClose, closed]

end Grpc.ChannelLease
