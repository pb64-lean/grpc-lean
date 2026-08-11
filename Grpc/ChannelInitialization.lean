module

public import Std.Tactic

public section

/-!
# Outbound-channel initialization ownership

This module is the pure ownership kernel for a future cancellable outbound
connector.  It deliberately contains no DNS, socket, TLS, task, or clock
effects.  An effectful adapter is expected to serialize observations through
this reducer and to turn a `ReleaseRequest` into a `ReleaseAck` only after the
request's exact native operation has joined and its exact socket (when any)
has been closed.

The kernel makes the following facts structural:

* at most one monotonically numbered initialization attempt is pending;
* address traversal is bounded by `maximumAddresses`;
* a pending attempt owns zero or one exact socket token;
* every post-allocation observation must present that exact socket token;
* pending, current, and retained socket partitions are pairwise disjoint;
* at most one retired socket is retained beside one pending or current owner;
* cancellation and draining make publication impossible;
* cancellation preserves any advertised failed-address release identity;
* socket ownership can be removed only by an exact release acknowledgement; and
* `closed` owns no pending attempt, current connection, or retained socket.

This is a foundation for a future capability, not a claim that the current
native connector is cancellable: as the `Grpc.ManagedChannel` header
documents, the resolver and client connector do not yet expose cancellable
DNS/TCP/TLS initialization.  The native cancellation/close implementation
must provide the release acknowledgement described above before this model
is wired into the managed channel's connector.
-/

namespace Grpc.ChannelInitialization

@[expose] def maximumAddresses : Nat := 64

/-- At most one uncertain old connection may coexist with a replacement. -/
@[expose] def maximumRetainedSockets : Nat := 1

theorem maximum_addresses_is_sixty_four : maximumAddresses = 64 := rfl

theorem maximum_retained_sockets_is_one : maximumRetainedSockets = 1 := rfl

structure AttemptId where
  private mk ::
  value : Nat
deriving DecidableEq, Repr

instance : BEq AttemptId where
  beq left right := decide (left = right)

instance : LawfulBEq AttemptId where
  eq_of_beq := of_decide_eq_true

structure SocketToken where
  private mk ::
  value : Nat
deriving DecidableEq, Repr

instance : BEq SocketToken where
  beq left right := decide (left = right)

instance : LawfulBEq SocketToken where
  eq_of_beq := of_decide_eq_true

structure Generation where
  private mk ::
  value : Nat
deriving DecidableEq, Repr

instance : BEq Generation where
  beq left right := decide (left = right)

instance : LawfulBEq Generation where
  eq_of_beq := of_decide_eq_true

inductive Phase where
  | accepting
  | draining
  | closed
deriving BEq, DecidableEq, Repr

/-!
`ready i` has resolved a bounded nonempty address vector and is ready to
allocate the socket for address `i`.  `releasing next` still owns the failed
address's socket and may proceed with `next` only after its release is
acknowledged.  `releasingCancelled next` records cancellation without changing
the already-issued failed-address release identity.  Both cancellation stages
are terminal with respect to publication.
-/
inductive Stage where
  | resolving
  | ready (addressIndex : Nat)
  | connecting (addressIndex : Nat)
  | handshaking (addressIndex : Nat)
  | validatingAlpn (addressIndex : Nat)
  | releasing (nextAddressIndex : Nat)
  | releasingCancelled (nextAddressIndex : Nat)
  | cancelling
deriving BEq, DecidableEq, Repr

namespace Stage

def Invariant
    (stage : Stage) (addressCount : Nat)
    (socket : Option SocketToken) : Prop :=
  match stage with
  | .resolving => addressCount = 0 ∧ socket = none
  | .ready index => index < addressCount ∧ socket = none
  | .connecting index
  | .handshaking index
  | .validatingAlpn index => index < addressCount ∧ socket.isSome = true
  | .releasing nextIndex
  | .releasingCancelled nextIndex =>
      0 < addressCount ∧ nextIndex ≤ addressCount ∧ socket.isSome = true
  | .cancelling => True

@[expose] def CancellationRequested : Stage → Prop
  | .releasingCancelled _ | .cancelling => True
  | _ => False

instance (stage : Stage) : Decidable stage.CancellationRequested := by
  cases stage with
  | releasingCancelled _ | cancelling => exact isTrue trivial
  | resolving | ready _ | connecting _ | handshaking _ | validatingAlpn _
  | releasing _ => exact isFalse fun impossible => impossible

end Stage

structure Pending where
  private mk ::
  attempt : AttemptId
  addressCount : Nat
  stage : Stage
  socket : Option SocketToken
  private countBound : addressCount ≤ maximumAddresses
  private stageValid : stage.Invariant addressCount socket

namespace Pending

def Invariant (pending : Pending) : Prop :=
  pending.addressCount ≤ maximumAddresses ∧
    pending.stage.Invariant pending.addressCount pending.socket

theorem invariant (pending : Pending) : pending.Invariant :=
  ⟨pending.countBound, pending.stageValid⟩

theorem address_count_bounded (pending : Pending) :
    pending.addressCount ≤ maximumAddresses :=
  pending.countBound

theorem ready_address_bounded
    (pending : Pending) (index : Nat)
    (ready : pending.stage = .ready index) :
    index < pending.addressCount := by
  have valid := pending.stageValid
  rw [ready] at valid
  exact valid.1

theorem connecting_address_bounded
    (pending : Pending) (index : Nat)
    (connecting : pending.stage = .connecting index) :
    index < pending.addressCount := by
  have valid := pending.stageValid
  rw [connecting] at valid
  exact valid.1

theorem handshaking_address_bounded
    (pending : Pending) (index : Nat)
    (handshaking : pending.stage = .handshaking index) :
    index < pending.addressCount := by
  have valid := pending.stageValid
  rw [handshaking] at valid
  exact valid.1

theorem alpn_address_bounded
    (pending : Pending) (index : Nat)
    (validating : pending.stage = .validatingAlpn index) :
    index < pending.addressCount := by
  have valid := pending.stageValid
  rw [validating] at valid
  exact valid.1

theorem active_stage_has_socket
    (pending : Pending) (index : Nat)
    (active : pending.stage = .connecting index ∨
      pending.stage = .handshaking index ∨
      pending.stage = .validatingAlpn index) :
    pending.socket.isSome = true := by
  rcases active with connecting | handshaking | validating
  · have valid := pending.stageValid
    rw [connecting] at valid
    exact valid.2
  · have valid := pending.stageValid
    rw [handshaking] at valid
    exact valid.2
  · have valid := pending.stageValid
    rw [validating] at valid
    exact valid.2

theorem resolving_has_no_socket
    (pending : Pending) (resolving : pending.stage = .resolving) :
    pending.socket = none := by
  have valid := pending.stageValid
  rw [resolving] at valid
  exact valid.2

theorem ready_has_no_socket
    (pending : Pending) (index : Nat)
    (ready : pending.stage = .ready index) :
    pending.socket = none := by
  have valid := pending.stageValid
  rw [ready] at valid
  exact valid.2

end Pending

structure Connection where
  private mk ::
  attempt : AttemptId
  generation : Generation
  socket : SocketToken
deriving DecidableEq, Repr

instance : BEq Connection where
  beq left right := decide (left = right)

instance : LawfulBEq Connection where
  eq_of_beq := of_decide_eq_true

private def pendingSockets : Option Pending → List SocketToken
  | none => []
  | some pending => pending.socket.toList

private def currentSockets : Option Connection → List SocketToken
  | none => []
  | some connection => [connection.socket]

private def ownedSocketList
    (pending : Option Pending) (current : Option Connection)
    (retained : List SocketToken) : List SocketToken :=
  pendingSockets pending ++ currentSockets current ++ retained

private def RawInvariant
    (phase : Phase)
    (nextAttempt nextSocket nextGeneration : Nat)
    (pending : Option Pending)
    (current : Option Connection)
    (retained : List SocketToken) : Prop :=
  (ownedSocketList pending current retained).Nodup ∧
  (∀ token, token ∈ ownedSocketList pending current retained →
    token.value < nextSocket) ∧
  (∀ initialization, pending = some initialization →
    initialization.attempt.value < nextAttempt) ∧
  (∀ connection, current = some connection →
    connection.attempt.value < nextAttempt ∧
      connection.generation.value < nextGeneration) ∧
  (∀ initialization, pending = some initialization → current = none) ∧
  (phase = .draining →
    ∀ initialization, pending = some initialization →
      initialization.stage.CancellationRequested) ∧
  (phase = .closed →
    pending = none ∧ current = none ∧ retained = []) ∧
  retained.length ≤ maximumRetainedSockets

structure State where
  private mk ::
  phase : Phase
  nextAttempt : Nat
  nextSocket : Nat
  nextGeneration : Nat
  pending : Option Pending
  current : Option Connection
  retained : List SocketToken
  private valid : RawInvariant phase nextAttempt nextSocket nextGeneration
    pending current retained

namespace State

def initial : State :=
  .mk .accepting 0 0 0 none none [] (by
    simp [RawInvariant, ownedSocketList, pendingSockets, currentSockets])

def ownedSockets (state : State) : List SocketToken :=
  ownedSocketList state.pending state.current state.retained

def ownerCount (state : State) : Nat :=
  (if state.pending.isSome then 1 else 0) +
    (if state.current.isSome then 1 else 0) + state.retained.length

def Invariant (state : State) : Prop :=
  RawInvariant state.phase state.nextAttempt state.nextSocket
    state.nextGeneration state.pending state.current state.retained

theorem invariant (state : State) : state.Invariant :=
  state.valid

theorem at_most_one_initialization (state : State) :
    ∀ left right,
      state.pending = some left → state.pending = some right → left = right := by
  intro left right leftPresent rightPresent
  rw [leftPresent] at rightPresent
  exact Option.some.inj rightPresent

theorem ownership_partitions_are_disjoint (state : State) :
    state.ownedSockets.Nodup :=
  state.valid.1

theorem retained_sockets_are_unique (state : State) :
    state.retained.Nodup := by
  have retainedSublist : List.Sublist state.retained state.ownedSockets := by
    simp [ownedSockets, ownedSocketList]
  exact state.ownership_partitions_are_disjoint.sublist retainedSublist

theorem owned_socket_precedes_allocator
    (state : State) (token : SocketToken)
    (owned : token ∈ state.ownedSockets) :
    token.value < state.nextSocket :=
  state.valid.2.1 token owned

theorem pending_and_current_are_exclusive
    (state : State) (pending : Pending)
    (present : state.pending = some pending) :
    state.current = none :=
  state.valid.2.2.2.2.1 pending present

theorem pending_socket_not_retained
    (state : State) (pending : Pending) (token : SocketToken)
    (pendingPresent : state.pending = some pending)
    (socketPresent : pending.socket = some token) :
    token ∉ state.retained := by
  have noCurrent := state.pending_and_current_are_exclusive pending pendingPresent
  have unique : (token :: state.retained).Nodup := by
    simpa [ownedSockets, ownedSocketList, pendingSockets, currentSockets,
      pendingPresent, socketPresent, noCurrent] using
      state.ownership_partitions_are_disjoint
  exact (List.nodup_cons.mp unique).1

theorem current_socket_not_retained
    (state : State) (connection : Connection)
    (currentPresent : state.current = some connection) :
    connection.socket ∉ state.retained := by
  have noPending : state.pending = none := by
    cases pendingPresent : state.pending with
    | none => rfl
    | some pending =>
        have impossible := state.pending_and_current_are_exclusive pending pendingPresent
        rw [currentPresent] at impossible
        contradiction
  have unique : (connection.socket :: state.retained).Nodup := by
    simpa [ownedSockets, ownedSocketList, pendingSockets, currentSockets,
      noPending, currentPresent] using state.ownership_partitions_are_disjoint
  exact (List.nodup_cons.mp unique).1

theorem draining_initialization_has_cancellation_requested
    (state : State) (draining : state.phase = .draining)
    (pending : Pending) (present : state.pending = some pending) :
    pending.stage.CancellationRequested :=
  state.valid.2.2.2.2.2.1 draining pending present

theorem retained_sockets_bounded (state : State) :
    state.retained.length ≤ maximumRetainedSockets :=
  state.valid.2.2.2.2.2.2.2

theorem closed_has_no_owners
    (state : State) (closed : state.phase = .closed) :
    state.pending = none ∧ state.current = none ∧ state.retained = [] :=
  state.valid.2.2.2.2.2.2.1 closed

theorem closed_owned_sockets_empty
    (state : State) (closed : state.phase = .closed) :
    state.ownedSockets = [] := by
  rcases state.closed_has_no_owners closed with ⟨pending, current, retained⟩
  simp [ownedSockets, ownedSocketList, pendingSockets, currentSockets,
    pending, current, retained]

theorem closed_owner_count_zero
    (state : State) (closed : state.phase = .closed) :
    state.ownerCount = 0 := by
  rcases state.closed_has_no_owners closed with ⟨pending, current, retained⟩
  simp [ownerCount, pending, current, retained]

theorem owner_count_bounded (state : State) :
    state.ownerCount ≤ maximumRetainedSockets + 1 := by
  have retainedBound := state.retained_sockets_bounded
  cases pendingPresent : state.pending with
  | none =>
      cases currentPresent : state.current <;>
        simp [ownerCount, pendingPresent, currentPresent] <;> omega
  | some pending =>
      have noCurrent := state.pending_and_current_are_exclusive pending pendingPresent
      simp [ownerCount, pendingPresent, noCurrent]
      omega

end State

inductive StartError where
  | draining
  | closed
  | initializationPending
  | connectionCurrent
deriving BEq, DecidableEq, Repr

structure StartResult where
  state : State
  attempt : AttemptId

private def startAccepting
    (state : State)
    (_accepting : state.phase = .accepting)
    (noPending : state.pending = none)
    (noCurrent : state.current = none) : StartResult := by
  let attempt : AttemptId := .mk state.nextAttempt
  let initialization : Pending :=
    .mk attempt 0 .resolving none (by simp [maximumAddresses]) (by simp [Stage.Invariant])
  refine {
    state := .mk .accepting (state.nextAttempt + 1) state.nextSocket
      state.nextGeneration (some initialization) none state.retained ?_
    attempt
  }
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have oldSockets :
      ownedSocketList state.pending state.current state.retained = state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, noPending, noCurrent]
  have retainedUnique : state.retained.Nodup := by
    simpa [oldSockets] using unique
  have retainedBelow : ∀ token, token ∈ state.retained → token.value < state.nextSocket := by
    intro token present
    apply below token
    simpa [ownedSocketList, pendingSockets, currentSockets, noPending, noCurrent]
  simp only [RawInvariant, ownedSocketList, pendingSockets, currentSockets,
    List.append_nil]
  refine ⟨retainedUnique, retainedBelow, ?_, ?_, ?_, ?_, ?_, retainedBound⟩
  · intro candidate equality
    injection equality with equality
    subst candidate
    simp [initialization, attempt]
  · intro connection equality
    contradiction
  · simp
  · simp
  · simp

def start (state : State) : Except StartError StartResult :=
  match phase : state.phase with
  | .draining => .error .draining
  | .closed => .error .closed
  | .accepting =>
      match pending : state.pending with
      | some _ => .error .initializationPending
      | none =>
          match current : state.current with
          | some _ => .error .connectionCurrent
          | none => .ok (startAccepting state phase pending current)

theorem start_allocates_monotone_attempt
    (state : State) (result : StartResult)
    (started : start state = .ok result) :
    result.attempt.value = state.nextAttempt ∧
      result.state.nextAttempt = state.nextAttempt + 1 := by
  unfold start at started
  split at started <;> try contradiction
  split at started <;> try contradiction
  split at started <;> try contradiction
  injection started with equality
  subst result
  simp [startAccepting]

inductive ProgressError where
  | notAccepting
  | noInitialization
  | staleAttempt
  | staleSocket
  | wrongStage
  | tooManyAddresses
deriving BEq, DecidableEq, Repr

inductive ResolutionDecision where
  | noAddresses
  | ready
deriving BEq, DecidableEq, Repr

structure ResolutionResult where
  state : State
  decision : ResolutionDecision

private def clearResolvedEmpty
    (state : State) (initialization : Pending)
    (present : state.pending = some initialization)
    (resolving : initialization.stage = .resolving) : State := by
  have noSocket := initialization.resolving_has_no_socket resolving
  have noCurrent := state.pending_and_current_are_exclusive initialization present
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    none none state.retained ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have sockets :
      ownedSocketList state.pending state.current state.retained = state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, present, noCurrent, noSocket]
  have retainedUnique : state.retained.Nodup := by
    simpa [sockets] using unique
  have retainedBelow : ∀ token, token ∈ state.retained → token.value < state.nextSocket := by
    intro token member
    apply below token
    simpa [ownedSocketList, pendingSockets, currentSockets, present, noCurrent, noSocket]
  simp only [RawInvariant, ownedSocketList, pendingSockets, currentSockets,
    List.nil_append, List.append_nil]
  refine ⟨retainedUnique, retainedBelow, by simp, by simp, by simp, by simp, ?_,
    retainedBound⟩
  intro isClosed
  have impossible : (some initialization : Option Pending) = none := by
    simpa [present] using (closed isClosed).1
  contradiction

private def markResolved
    (state : State) (initialization : Pending)
    (present : state.pending = some initialization)
    (resolving : initialization.stage = .resolving)
    (addressCount : Nat) (positive : 0 < addressCount)
    (bounded : addressCount ≤ maximumAddresses) : State := by
  have noSocket := initialization.resolving_has_no_socket resolving
  let nextPending : Pending := .mk initialization.attempt addressCount (.ready 0)
    none bounded (by simp [Stage.Invariant, positive])
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    (some nextPending) state.current state.retained ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have noCurrent := exclusive initialization present
  have sameSockets :
      ownedSocketList (some nextPending) state.current state.retained =
        ownedSocketList state.pending state.current state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, present, noSocket,
      nextPending]
  refine ⟨?_, ?_, ?_, currentBelow, ?_, ?_, ?_, retainedBound⟩
  · simpa [sameSockets] using unique
  · intro token member
    apply below token
    simpa [sameSockets] using member
  · intro candidate equality
    injection equality with equality
    subst candidate
    exact pendingBelow initialization present
  · intro candidate equality
    exact noCurrent
  · intro drainingPhase candidate equality
    have impossible := draining drainingPhase initialization present
    simp [resolving, Stage.CancellationRequested] at impossible
  · intro closedPhase
    have impossible : (some initialization : Option Pending) = none := by
      simpa [present] using (closed closedPhase).1
    contradiction

def resolve
    (state : State) (attempt : AttemptId) (addressCount : Nat) :
    Except ProgressError ResolutionResult :=
  if state.phase != .accepting then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else
          match resolving : initialization.stage with
          | .resolving =>
              if empty : addressCount = 0 then
                .ok ⟨clearResolvedEmpty state initialization present resolving,
                  .noAddresses⟩
              else if bounded : addressCount ≤ maximumAddresses then
                .ok ⟨markResolved state initialization present resolving addressCount
                  (Nat.pos_of_ne_zero empty) bounded, .ready⟩
              else
                .error .tooManyAddresses
          | _ => .error .wrongStage

structure SocketGrant where
  state : State
  attempt : AttemptId
  socket : SocketToken

private def allocateReadySocket
    (state : State) (initialization : Pending) (index : Nat)
    (present : state.pending = some initialization)
    (ready : initialization.stage = .ready index) : SocketGrant := by
  have noPendingSocket := initialization.ready_has_no_socket index ready
  have indexBound := initialization.ready_address_bounded index ready
  have noCurrent := state.pending_and_current_are_exclusive initialization present
  let socket : SocketToken := .mk state.nextSocket
  let nextPending : Pending :=
    .mk initialization.attempt initialization.addressCount (.connecting index)
      (some socket) initialization.countBound (by
        simp [Stage.Invariant, indexBound])
  have fresh : socket ∉ state.ownedSockets := by
    intro member
    have below := state.owned_socket_precedes_allocator socket member
    simp [socket] at below
  refine {
    state := .mk state.phase state.nextAttempt (state.nextSocket + 1)
      state.nextGeneration (some nextPending) none state.retained ?_
    attempt := initialization.attempt
    socket
  }
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have oldSockets :
      ownedSocketList state.pending state.current state.retained = state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, present,
      noPendingSocket, noCurrent]
  have oldRetainedUnique : state.retained.Nodup := by
    simpa [oldSockets] using unique
  have oldRetainedBelow :
      ∀ token, token ∈ state.retained → token.value < state.nextSocket := by
    intro token member
    apply below token
    simpa [oldSockets] using member
  have socketFreshRetained : socket ∉ state.retained := by
    intro member
    apply fresh
    simpa [State.ownedSockets, ownedSocketList, pendingSockets, currentSockets,
      present, noPendingSocket, noCurrent] using member
  simp only [RawInvariant, ownedSocketList, pendingSockets, currentSockets]
  refine ⟨List.nodup_cons.mpr ⟨socketFreshRetained, oldRetainedUnique⟩,
    ?_, ?_, by simp, by simp, ?_, ?_, retainedBound⟩
  · intro token member
    rcases List.mem_cons.mp member with equality | retainedMember
    · subst token
      simp [socket]
    · exact Nat.lt_succ_of_lt (oldRetainedBelow token retainedMember)
  · intro candidate equality
    injection equality with equality
    subst candidate
    exact pendingBelow initialization present
  · intro drainingPhase candidate equality
    have impossible := draining drainingPhase initialization present
    simp [ready, Stage.CancellationRequested] at impossible
  · intro closedPhase
    have impossible : (some initialization : Option Pending) = none := by
      simpa [present] using (closed closedPhase).1
    contradiction

def beginAddress
    (state : State) (attempt : AttemptId) :
    Except ProgressError SocketGrant :=
  if state.phase != .accepting then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else
          match ready : initialization.stage with
          | .ready index => .ok (allocateReadySocket state initialization index present ready)
          | _ => .error .wrongStage

private def replaceActiveStage
    (state : State) (initialization : Pending)
    (present : state.pending = some initialization)
    (cancellationAbsent : ¬ initialization.stage.CancellationRequested)
    (stage : Stage)
    (stageValid : stage.Invariant initialization.addressCount initialization.socket) : State := by
  let nextPending : Pending :=
    .mk initialization.attempt initialization.addressCount stage
      initialization.socket initialization.countBound stageValid
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    (some nextPending) state.current state.retained ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have sameSockets :
      ownedSocketList (some nextPending) state.current state.retained =
        ownedSocketList state.pending state.current state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, present, nextPending]
  refine ⟨?_, ?_, ?_, currentBelow, ?_, ?_, ?_, retainedBound⟩
  · simpa [sameSockets] using unique
  · intro token member
    apply below token
    simpa [sameSockets] using member
  · intro candidate equality
    injection equality with equality
    subst candidate
    exact pendingBelow initialization present
  · intro candidate equality
    exact exclusive initialization present
  · intro drainingPhase candidate equality
    have cancelled := draining drainingPhase initialization present
    exact (cancellationAbsent cancelled).elim
  · intro closedPhase
    have impossible : (some initialization : Option Pending) = none := by
      simpa [present] using (closed closedPhase).1
    contradiction

def tcpConnected
    (state : State) (attempt : AttemptId) (socket : SocketToken) :
    Except ProgressError State :=
  if state.phase != .accepting then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else if initialization.socket != some socket then
          .error .staleSocket
        else
          match connecting : initialization.stage with
          | .connecting index =>
              .ok (replaceActiveStage state initialization present
                (by simp [connecting, Stage.CancellationRequested])
                (.handshaking index) (by
                  exact ⟨initialization.connecting_address_bounded index connecting,
                    initialization.active_stage_has_socket index (Or.inl connecting)⟩))
          | _ => .error .wrongStage

def tlsEstablished
    (state : State) (attempt : AttemptId) (socket : SocketToken) :
    Except ProgressError State :=
  if state.phase != .accepting then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else if initialization.socket != some socket then
          .error .staleSocket
        else
          match handshaking : initialization.stage with
          | .handshaking index =>
              .ok (replaceActiveStage state initialization present
                (by simp [handshaking, Stage.CancellationRequested])
                (.validatingAlpn index) (by
                  exact ⟨initialization.handshaking_address_bounded index handshaking,
                    initialization.active_stage_has_socket index
                      (Or.inr (Or.inl handshaking))⟩))
          | _ => .error .wrongStage

private def markReleasing
    (state : State) (initialization : Pending) (index : Nat)
    (present : state.pending = some initialization)
    (socketPresent : initialization.socket.isSome = true)
    (indexBound : index < initialization.addressCount)
    (cancellationAbsent : ¬ initialization.stage.CancellationRequested) : State :=
  replaceActiveStage state initialization present cancellationAbsent
    (.releasing (index + 1)) (by
      exact ⟨Nat.zero_lt_of_lt indexBound, Nat.succ_le_of_lt indexBound, socketPresent⟩)

def rejectAddress
    (state : State) (attempt : AttemptId) (socket : SocketToken) :
    Except ProgressError State :=
  if state.phase != .accepting then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else if initialization.socket != some socket then
          .error .staleSocket
        else
          match active : initialization.stage with
          | .connecting index =>
              .ok (markReleasing state initialization index present
                (initialization.active_stage_has_socket index (Or.inl active))
                (initialization.connecting_address_bounded index active)
                (by simp [active, Stage.CancellationRequested]))
          | .handshaking index =>
              .ok (markReleasing state initialization index present
                (initialization.active_stage_has_socket index (Or.inr (Or.inl active)))
                (initialization.handshaking_address_bounded index active)
                (by simp [active, Stage.CancellationRequested]))
          | .validatingAlpn index =>
              .ok (markReleasing state initialization index present
                (initialization.active_stage_has_socket index (Or.inr (Or.inr active)))
                (initialization.alpn_address_bounded index active)
                (by simp [active, Stage.CancellationRequested]))
          | _ => .error .wrongStage

/-!
Cancellation never changes an already-advertised failed-address release owner.
The release acknowledgement will clear `releasingCancelled` rather than retry
the next address.  Other stages move to the ordinary attempt-level cancellation
owner.
-/
private def cancellationStage : Stage → Stage
  | .releasing nextIndex => .releasingCancelled nextIndex
  | .releasingCancelled nextIndex => .releasingCancelled nextIndex
  | _ => .cancelling

private theorem cancellationStage_valid
    (stage : Stage) (addressCount : Nat) (socket : Option SocketToken)
    (valid : stage.Invariant addressCount socket) :
    (cancellationStage stage).Invariant addressCount socket := by
  cases stage <;> simp_all [cancellationStage, Stage.Invariant]

private theorem cancellationStage_requested (stage : Stage) :
    (cancellationStage stage).CancellationRequested := by
  cases stage <;> simp [cancellationStage, Stage.CancellationRequested]

private def cancellationPending (pending : Pending) : Pending :=
  .mk pending.attempt pending.addressCount (cancellationStage pending.stage)
    pending.socket pending.countBound
      (cancellationStage_valid pending.stage pending.addressCount pending.socket
        pending.stageValid)

private theorem cancellationPending_socket (pending : Pending) :
    (cancellationPending pending).socket = pending.socket := rfl

private theorem cancellationPending_attempt (pending : Pending) :
    (cancellationPending pending).attempt = pending.attempt := rfl

private theorem cancellationPending_requested (pending : Pending) :
    (cancellationPending pending).stage.CancellationRequested :=
  cancellationStage_requested pending.stage

private def replaceWithCancelling
    (state : State) (initialization : Pending)
    (present : state.pending = some initialization) (phase : Phase)
    (phaseNotClosed : phase ≠ .closed) : State := by
  let nextPending := cancellationPending initialization
  refine .mk phase state.nextAttempt state.nextSocket state.nextGeneration
    (some nextPending) state.current state.retained ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have sameSockets :
      ownedSocketList (some nextPending) state.current state.retained =
        ownedSocketList state.pending state.current state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, present,
      nextPending, cancellationPending_socket]
  refine ⟨?_, ?_, ?_, currentBelow, ?_, ?_, ?_, retainedBound⟩
  · simpa [sameSockets] using unique
  · intro token member
    apply below token
    simpa [sameSockets] using member
  · intro candidate equality
    injection equality with equality
    subst candidate
    simpa [nextPending, cancellationPending_attempt] using
      pendingBelow initialization present
  · intro candidate equality
    exact exclusive initialization present
  · intro drainingPhase candidate equality
    injection equality with equality
    subst candidate
    exact cancellationPending_requested initialization
  · intro closedPhase
    exact (phaseNotClosed closedPhase).elim

def cancel
    (state : State) (attempt : AttemptId) : Except ProgressError State :=
  if isClosed : state.phase == .closed then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else
          .ok (replaceWithCancelling state initialization present state.phase (by
            intro closed
            rw [closed] at isClosed
            have closedSelf : (Phase.closed == Phase.closed) = true := by decide
            rw [closedSelf] at isClosed
            contradiction))

inductive ReleaseOwner where
  | cancelling (attempt : AttemptId) (socket : Option SocketToken)
  | failedAddress (attempt : AttemptId) (socket : SocketToken)
  | connection (socket : SocketToken)
deriving BEq, DecidableEq, Repr

structure ReleaseRequest where
  private mk ::
  owner : ReleaseOwner
deriving BEq, DecidableEq, Repr

structure ReleaseAck where
  private mk ::
  owner : ReleaseOwner
deriving BEq, DecidableEq, Repr

namespace ReleaseRequest

/-!
The effectful adapter must call this only after the native release operation
identified by `request.owner` has completed.  Keeping acknowledgement creation
at this explicit boundary prevents a generic success boolean from releasing a
different or newer owner.  Release queries are idempotent: an adapter may
observe the same owner more than once and must single-flight native release by
that stable owner rather than launch duplicate closes.
-/
def acknowledged (request : ReleaseRequest) : ReleaseAck :=
  .mk request.owner

@[simp] theorem acknowledged_owner (request : ReleaseRequest) :
    request.acknowledged.owner = request.owner := by
  simp [acknowledged]

end ReleaseRequest

def pendingReleaseRequest? (state : State) : Option ReleaseRequest :=
  match state.pending with
  | none => none
  | some initialization =>
      match initialization.stage, initialization.socket with
      | .cancelling, socket =>
          some (.mk (.cancelling initialization.attempt socket))
      | .releasing _, some socket
      | .releasingCancelled _, some socket =>
          some (.mk (.failedAddress initialization.attempt socket))
      | _, _ => none

def currentReleaseRequest? (state : State) : Option ReleaseRequest :=
  state.current.map fun connection => .mk (.connection connection.socket)

def retainedReleaseRequests (state : State) : List ReleaseRequest :=
  state.retained.map fun socket => .mk (.connection socket)

inductive ReleaseError where
  | staleAcknowledgement
deriving BEq, DecidableEq, Repr

private def acknowledgeCancelling
    (state : State) (initialization : Pending)
    (present : state.pending = some initialization) : State := by
  have noCurrent := state.pending_and_current_are_exclusive initialization present
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    none none state.retained ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have retainedSublist :
      List.Sublist state.retained
        (ownedSocketList state.pending state.current state.retained) := by
    simp [ownedSocketList, pendingSockets, currentSockets, present, noCurrent]
  refine ⟨unique.sublist retainedSublist, ?_, by simp, by simp, by simp,
    by simp, ?_, retainedBound⟩
  · intro token member
    exact below token (retainedSublist.subset member)
  · intro closedPhase
    have impossible : (some initialization : Option Pending) = none := by
      simpa [present] using (closed closedPhase).1
    contradiction

private def acknowledgeFailedAddress
    (state : State) (initialization : Pending) (nextIndex : Nat)
    (present : state.pending = some initialization)
    (releasing : initialization.stage = .releasing nextIndex) : State := by
  have releasingValid := initialization.stageValid
  rw [releasing] at releasingValid
  have socketPresent : initialization.socket.isSome = true := releasingValid.2.2
  have noCurrent := state.pending_and_current_are_exclusive initialization present
  have accepting : state.phase = .accepting := by
    cases phase : state.phase with
    | accepting => rfl
    | draining =>
        have cancelled :=
          state.draining_initialization_has_cancellation_requested
            phase initialization present
        simp [releasing, Stage.CancellationRequested] at cancelled
    | closed =>
        have impossible : (some initialization : Option Pending) = none := by
          simpa [present] using (state.closed_has_no_owners phase).1
        contradiction
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have retainedSublist :
      List.Sublist state.retained
        (ownedSocketList state.pending state.current state.retained) := by
    simp [ownedSocketList, pendingSockets, currentSockets, present, noCurrent]
  have retainedUnique : state.retained.Nodup := unique.sublist retainedSublist
  have retainedBelow :
      ∀ token, token ∈ state.retained → token.value < state.nextSocket := by
    intro token member
    exact below token (retainedSublist.subset member)
  by_cases retry : nextIndex < initialization.addressCount
  · let nextPending : Pending :=
      .mk initialization.attempt initialization.addressCount (.ready nextIndex)
        none initialization.countBound (by exact ⟨retry, rfl⟩)
    refine .mk .accepting state.nextAttempt state.nextSocket state.nextGeneration
      (some nextPending) none state.retained ?_
    simp only [RawInvariant, ownedSocketList, pendingSockets, currentSockets,
      nextPending]
    refine ⟨retainedUnique, retainedBelow, ?_, by simp, by simp, by simp, by simp,
      retainedBound⟩
    intro candidate equality
    injection equality with equality
    subst candidate
    exact pendingBelow initialization present
  · refine .mk .accepting state.nextAttempt state.nextSocket state.nextGeneration
      none none state.retained ?_
    simp only [RawInvariant, ownedSocketList, pendingSockets, currentSockets,
      List.nil_append]
    exact ⟨retainedUnique, retainedBelow, by simp, by simp, by simp, by simp, by simp,
      retainedBound⟩

private def removeCurrent
    (state : State) (connection : Connection)
    (present : state.current = some connection) : State := by
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    none none state.retained ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have noPending : state.pending = none := by
    cases pendingPresent : state.pending with
    | none => rfl
    | some pending =>
        have impossible := exclusive pending pendingPresent
        rw [present] at impossible
        contradiction
  have tailUnique : state.retained.Nodup := by
    have withHead : (connection.socket :: state.retained).Nodup := by
      simpa [ownedSocketList, pendingSockets, currentSockets, noPending, present]
        using unique
    exact withHead.tail
  have tailBelow : ∀ token, token ∈ state.retained → token.value < state.nextSocket := by
    intro token member
    apply below token
    simpa [ownedSocketList, pendingSockets, currentSockets, noPending, present] using
      (List.mem_cons_of_mem connection.socket member)
  simp only [RawInvariant, ownedSocketList, pendingSockets, currentSockets,
    List.nil_append]
  refine ⟨tailUnique, tailBelow, by simp, by simp, by simp, by simp, ?_,
    retainedBound⟩
  intro closedPhase
  have impossible : (some connection : Option Connection) = none := by
    simpa [present] using (closed closedPhase).2.1
  contradiction

private def removeRetained
    (state : State) (socket : SocketToken)
    (present : socket ∈ state.retained) : State := by
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    state.pending state.current (state.retained.erase socket) ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      retainedBound⟩
  have erasedSublist :
      List.Sublist (state.retained.erase socket) state.retained :=
    List.erase_sublist
  have newSublist :
      List.Sublist
        (ownedSocketList state.pending state.current (state.retained.erase socket))
        (ownedSocketList state.pending state.current state.retained) := by
    exact erasedSublist.append_left
      (pendingSockets state.pending ++ currentSockets state.current)
  refine ⟨unique.sublist newSublist, ?_, pendingBelow, currentBelow, exclusive,
    draining, ?_, ?_⟩
  · intro token member
    exact below token (newSublist.subset member)
  · intro closedPhase
    have empty := closed closedPhase
    simp_all
  · exact Nat.le_trans erasedSublist.length_le retainedBound

def acknowledgeRelease
    (state : State) (ack : ReleaseAck) : Except ReleaseError State :=
  match ack.owner with
  | .cancelling attempt socket =>
      match present : state.pending with
      | some initialization =>
          if initialization.attempt == attempt ∧
              initialization.socket == socket ∧
              initialization.stage == .cancelling then
            .ok (acknowledgeCancelling state initialization present)
          else
            .error .staleAcknowledgement
      | none => .error .staleAcknowledgement
  | .failedAddress attempt socket =>
      match present : state.pending with
      | some initialization =>
          if initialization.attempt == attempt ∧ initialization.socket == some socket then
            match releasing : initialization.stage with
            | .releasing nextIndex =>
                .ok (acknowledgeFailedAddress state initialization nextIndex present releasing)
            | .releasingCancelled _ =>
                .ok (acknowledgeCancelling state initialization present)
            | _ => .error .staleAcknowledgement
          else
            .error .staleAcknowledgement
      | none => .error .staleAcknowledgement
  | .connection socket =>
      match present : state.current with
      | some connection =>
          if connection.socket == socket then
            .ok (removeCurrent state connection present)
          else if retained : socket ∈ state.retained then
            .ok (removeRetained state socket retained)
          else
            .error .staleAcknowledgement
      | none =>
          if retained : socket ∈ state.retained then
            .ok (removeRetained state socket retained)
          else
            .error .staleAcknowledgement

structure PublishResult where
  state : State
  connection : Connection

private def publishAlpn
    (state : State) (initialization : Pending) (index : Nat)
    (present : state.pending = some initialization)
    (validating : initialization.stage = .validatingAlpn index) : PublishResult := by
  have socketPresent := initialization.active_stage_has_socket index
    (Or.inr (Or.inr validating))
  cases socketEquality : initialization.socket with
  | none =>
      simp [socketEquality] at socketPresent
  | some socket =>
      have noCurrent := state.pending_and_current_are_exclusive initialization present
      let generation : Generation := .mk state.nextGeneration
      let connection : Connection := .mk initialization.attempt generation socket
      refine {
        state := .mk .accepting state.nextAttempt state.nextSocket
          (state.nextGeneration + 1) none (some connection) state.retained ?_
        connection
      }
      rcases state.valid with
        ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
          retainedBound⟩
      have sameSockets :
          ownedSocketList none (some connection) state.retained =
            ownedSocketList state.pending state.current state.retained := by
        simp [ownedSocketList, pendingSockets, currentSockets, present, noCurrent,
          connection, socketEquality]
      refine ⟨?_, ?_, by simp, ?_, by simp, by simp, by simp, retainedBound⟩
      · simpa [sameSockets] using unique
      · intro token member
        apply below token
        simpa [sameSockets] using member
      · intro candidate equality
        injection equality with equality
        subst candidate
        constructor
        · exact pendingBelow initialization present
        · simp [connection, generation]

def publish
    (state : State) (attempt : AttemptId) (socket : SocketToken) :
    Except ProgressError PublishResult :=
  if state.phase != .accepting then
    .error .notAccepting
  else
    match present : state.pending with
    | none => .error .noInitialization
    | some initialization =>
        if initialization.attempt != attempt then
          .error .staleAttempt
        else if initialization.socket != some socket then
          .error .staleSocket
        else
          match validating : initialization.stage with
          | .validatingAlpn index =>
              .ok (publishAlpn state initialization index present validating)
          | _ => .error .wrongStage

theorem cancellation_requested_cannot_publish
    (state : State) (attempt : AttemptId) (socket : SocketToken) (pending : Pending)
    (present : state.pending = some pending)
    (cancelled : pending.stage.CancellationRequested) :
    ∀ result, publish state attempt socket ≠ .ok result := by
  intro result published
  simp only [publish] at published
  split at published
  · contradiction
  split at published
  · rename_i observed
    rw [present] at observed
    contradiction
  · rename_i initialization observed
    rw [present] at observed
    injection observed with equality
    subst initialization
    split at published
    · contradiction
    · split at published
      · contradiction
      · cases stageEq : pending.stage <;>
          simp [Stage.CancellationRequested, stageEq] at cancelled published

theorem cancelled_cannot_publish
    (state : State) (attempt : AttemptId) (socket : SocketToken) (pending : Pending)
    (present : state.pending = some pending)
    (cancelled : pending.stage = .cancelling) :
    ∀ result, publish state attempt socket ≠ .ok result := by
  apply cancellation_requested_cannot_publish state attempt socket pending present
  simp [cancelled, Stage.CancellationRequested]

inductive RetainError where
  | noCurrent
  | capacity
deriving BEq, DecidableEq, Repr

private def retainConnection
    (state : State) (connection : Connection)
    (present : state.current = some connection)
    (capacity : state.retained.length < maximumRetainedSockets) : State := by
  refine .mk state.phase state.nextAttempt state.nextSocket state.nextGeneration
    none none (connection.socket :: state.retained) ?_
  rcases state.valid with
    ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
      _retainedBound⟩
  have noPending : state.pending = none := by
    cases pendingPresent : state.pending with
    | none => rfl
    | some pending =>
        have impossible := exclusive pending pendingPresent
        rw [present] at impossible
        contradiction
  have movedSockets :
      ownedSocketList none none (connection.socket :: state.retained) =
        ownedSocketList state.pending state.current state.retained := by
    simp [ownedSocketList, pendingSockets, currentSockets, noPending, present]
  refine ⟨?_, ?_, by simp, by simp, by simp, by simp, ?_, ?_⟩
  · simpa [movedSockets] using unique
  · intro token member
    apply below token
    simpa [movedSockets] using member
  · intro closedPhase
    have impossible : (some connection : Option Connection) = none := by
      simpa [present] using (closed closedPhase).2.1
    contradiction
  · simpa using (Nat.succ_le_iff.mpr capacity)

/--
Transfer the current connection into the one-slot retained partition.  When
that slot is full, capacity failure leaves the exact current owner unchanged.
-/
def retainCurrent (state : State) : Except RetainError State :=
  match present : state.current with
  | none => .error .noCurrent
  | some connection =>
      if capacity : state.retained.length < maximumRetainedSockets then
        .ok (retainConnection state connection present capacity)
      else
        .error .capacity

theorem retain_capacity_preserves_current_owner
    (state : State) (overflow : retainCurrent state = .error .capacity) :
    state.current.isSome = true ∧
      state.retained.length = maximumRetainedSockets := by
  unfold retainCurrent at overflow
  split at overflow
  · cases overflow
  · rename_i connection present
    split at overflow
    · cases overflow
    · rename_i full
      constructor
      · simp [present]
      · exact Nat.le_antisymm state.retained_sockets_bounded
          (Nat.le_of_not_gt full)

inductive BeginCloseDecision where
  | claimed
  | joined
  | completed
deriving BEq, DecidableEq, Repr

structure BeginCloseResult where
  state : State
  decision : BeginCloseDecision

private def beginDraining (state : State) : State := by
  match present : state.pending with
  | none =>
      refine .mk .draining state.nextAttempt state.nextSocket state.nextGeneration
        none state.current state.retained ?_
      rcases state.valid with
        ⟨unique, below, pendingBelow, currentBelow, exclusive, draining, closed,
          retainedBound⟩
      have sameSockets :
          ownedSocketList none state.current state.retained =
            ownedSocketList state.pending state.current state.retained := by
        simp [ownedSocketList, pendingSockets, currentSockets, present]
      refine ⟨?_, ?_, by simp, currentBelow, by simp, by simp, by simp,
        retainedBound⟩
      · simpa [sameSockets] using unique
      · intro token member
        apply below token
        simpa [sameSockets] using member
  | some initialization =>
      exact replaceWithCancelling state initialization present .draining (by simp)

def beginClose (state : State) : BeginCloseResult :=
  match state.phase with
  | .accepting => ⟨beginDraining state, .claimed⟩
  | .draining => ⟨state, .joined⟩
  | .closed => ⟨state, .completed⟩

private theorem beginDraining_phase (state : State) :
    (beginDraining state).phase = .draining := by
  unfold beginDraining
  split <;> simp [replaceWithCancelling]

theorem begin_close_cancels_publication
    (state : State) (pending : Pending)
    (present : (beginClose state).state.pending = some pending)
    (notCompleted : (beginClose state).decision ≠ .completed) :
    pending.stage.CancellationRequested := by
  have draining : (beginClose state).state.phase = .draining := by
    cases phase : state.phase <;> simp_all [beginClose, beginDraining_phase]
  exact (beginClose state).state.draining_initialization_has_cancellation_requested
    draining pending present

inductive FinishCloseError where
  | notDraining
  | ownersRemain (count : Nat)
deriving BEq, DecidableEq, Repr

private def closedState
    (state : State) (_draining : state.phase = .draining)
    (_noPending : state.pending = none)
    (_noCurrent : state.current = none)
    (_noRetained : state.retained = []) : State :=
  .mk .closed state.nextAttempt state.nextSocket state.nextGeneration
    none none [] (by
      simp [RawInvariant, ownedSocketList, pendingSockets, currentSockets])

/-!
`finishClose` has no success path that discards ownership.  A draining owner
must first consume every release request with its exact `ReleaseAck`; only the
already-empty state can transition to `closed`.
-/
def finishClose (state : State) : Except FinishCloseError State :=
  match draining : state.phase with
  | .accepting | .closed => .error .notDraining
  | .draining =>
      match noPending : state.pending with
      | some _ => .error (.ownersRemain state.ownerCount)
      | none =>
          match noCurrent : state.current with
          | some _ => .error (.ownersRemain state.ownerCount)
          | none =>
              match noRetained : state.retained with
              | _ :: _ => .error (.ownersRemain state.ownerCount)
              | [] => .ok (closedState state draining noPending noCurrent noRetained)

theorem finish_close_requires_released
    (state closed : State) (finished : finishClose state = .ok closed) :
    state.phase = .draining ∧ state.pending = none ∧
      state.current = none ∧ state.retained = [] := by
  unfold finishClose at finished
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  simp_all

theorem unreleased_owner_blocks_close
    (state : State) (positive : 0 < state.ownerCount) :
    ∀ closed, finishClose state ≠ .ok closed := by
  intro closed finished
  rcases finish_close_requires_released state closed finished with
    ⟨draining, noPending, noCurrent, noRetained⟩
  simp [State.ownerCount, noPending, noCurrent, noRetained] at positive

theorem finish_close_is_empty
    (state closed : State) (finished : finishClose state = .ok closed) :
    closed.phase = .closed ∧ closed.pending = none ∧
      closed.current = none ∧ closed.retained = [] ∧
      closed.ownedSockets = [] := by
  unfold finishClose at finished
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  split at finished <;> try contradiction
  injection finished with equality
  subst closed
  simp [closedState, State.ownedSockets, ownedSocketList,
    pendingSockets, currentSockets]

end Grpc.ChannelInitialization
