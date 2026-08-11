import Lean.Elab.Tactic.Decide
import Grpc

namespace ChannelInitializationTest

open Grpc.ChannelInitialization

private structure PendingView where
  attempt : Nat
  addressCount : Nat
  stage : Stage
  socket : Option Nat
deriving BEq, DecidableEq, Repr

private structure ConnectionView where
  attempt : Nat
  generation : Nat
  socket : Nat
deriving BEq, DecidableEq, Repr

private structure Snapshot where
  phase : Phase
  nextAttempt : Nat
  nextSocket : Nat
  nextGeneration : Nat
  pending : Option PendingView
  current : Option ConnectionView
  retained : List Nat
deriving BEq, DecidableEq, Repr

private def pendingView (pending : Pending) : PendingView := {
  attempt := pending.attempt.value
  addressCount := pending.addressCount
  stage := pending.stage
  socket := pending.socket.map (·.value)
}

private def connectionView (connection : Connection) : ConnectionView := {
  attempt := connection.attempt.value
  generation := connection.generation.value
  socket := connection.socket.value
}

private def snapshot (state : State) : Snapshot := {
  phase := state.phase
  nextAttempt := state.nextAttempt
  nextSocket := state.nextSocket
  nextGeneration := state.nextGeneration
  pending := state.pending.map pendingView
  current := state.current.map connectionView
  retained := state.retained.map (·.value)
}

private def stageIsValid (pending : Pending) : Bool :=
  decide (pending.addressCount ≤ maximumAddresses) &&
    match pending.stage with
    | .resolving => pending.addressCount == 0 && pending.socket.isNone
    | .ready index => decide (index < pending.addressCount) && pending.socket.isNone
    | .connecting index
    | .handshaking index
    | .validatingAlpn index =>
        decide (index < pending.addressCount) && pending.socket.isSome
    | .releasing nextIndex
    | .releasingCancelled nextIndex =>
        decide (0 < pending.addressCount) &&
          decide (nextIndex ≤ pending.addressCount) && pending.socket.isSome
    | .cancelling => true

/-! Executable mirror of the propositions stored behind `State`'s constructor. -/
private def stateIsValid (state : State) : Bool :=
  decide state.ownedSockets.Nodup &&
    decide (state.retained.length ≤ maximumRetainedSockets) &&
    decide (state.ownerCount ≤ maximumRetainedSockets + 1) &&
    state.ownedSockets.all (fun token => decide (token.value < state.nextSocket)) &&
    (match state.pending with
      | none => true
      | some pending =>
          stageIsValid pending &&
            decide (pending.attempt.value < state.nextAttempt) && state.current.isNone) &&
    (match state.current with
      | none => true
      | some connection =>
          decide (connection.attempt.value < state.nextAttempt) &&
            decide (connection.generation.value < state.nextGeneration)) &&
    (match state.phase, state.pending with
      | .draining, some pending => decide pending.stage.CancellationRequested
      | _, _ => true) &&
    (match state.phase with
      | .closed =>
          state.pending.isNone && state.current.isNone && state.retained.isEmpty
      | _ => true)

private inductive Command where
  | start
  | resolveZero
  | resolveTwo
  | resolveMaximum
  | resolveOverLimit
  | beginAddress
  | tcpConnected
  | tlsEstablished
  | rejectAddress
  | publish
  | cancel
  | acknowledgePending
  | retainCurrent
  | acknowledgeCurrent
  | acknowledgeRetained
  | beginClose
  | finishClose
deriving BEq, DecidableEq, Repr

private def commands : List Command := [
  .start,
  .resolveZero,
  .resolveTwo,
  .resolveMaximum,
  .resolveOverLimit,
  .beginAddress,
  .tcpConnected,
  .tlsEstablished,
  .rejectAddress,
  .publish,
  .cancel,
  .acknowledgePending,
  .retainCurrent,
  .acknowledgeCurrent,
  .acknowledgeRetained,
  .beginClose,
  .finishClose
]

private def exceptState
    (fallback : State) (result : Except ε α) (project : α → State) : State :=
  match result with
  | .ok value => project value
  | .error _ => fallback

private def withAttempt
    (state : State) (action : AttemptId → State) : State :=
  match state.pending with
  | none => state
  | some pending => action pending.attempt

private def withActiveSocket
    (state : State) (action : AttemptId → SocketToken → State) : State :=
  match state.pending with
  | some pending =>
      match pending.socket with
      | some socket => action pending.attempt socket
      | none => state
  | none => state

private def applyCommand (state : State) : Command → State
  | .start => exceptState state (start state) (·.state)
  | .resolveZero => withAttempt state fun attempt =>
      exceptState state (resolve state attempt 0) (·.state)
  | .resolveTwo => withAttempt state fun attempt =>
      exceptState state (resolve state attempt 2) (·.state)
  | .resolveMaximum => withAttempt state fun attempt =>
      exceptState state (resolve state attempt maximumAddresses) (·.state)
  | .resolveOverLimit => withAttempt state fun attempt =>
      exceptState state (resolve state attempt (maximumAddresses + 1)) (·.state)
  | .beginAddress => withAttempt state fun attempt =>
      exceptState state (beginAddress state attempt) (·.state)
  | .tcpConnected => withActiveSocket state fun attempt socket =>
      exceptState state (tcpConnected state attempt socket) id
  | .tlsEstablished => withActiveSocket state fun attempt socket =>
      exceptState state (tlsEstablished state attempt socket) id
  | .rejectAddress => withActiveSocket state fun attempt socket =>
      exceptState state (rejectAddress state attempt socket) id
  | .publish => withActiveSocket state fun attempt socket =>
      exceptState state (publish state attempt socket) (·.state)
  | .cancel => withAttempt state fun attempt =>
      exceptState state (cancel state attempt) id
  | .acknowledgePending =>
      match pendingReleaseRequest? state with
      | none => state
      | some request =>
          exceptState state (acknowledgeRelease state request.acknowledged) id
  | .retainCurrent => exceptState state (retainCurrent state) id
  | .acknowledgeCurrent =>
      match currentReleaseRequest? state with
      | none => state
      | some request =>
          exceptState state (acknowledgeRelease state request.acknowledged) id
  | .acknowledgeRetained =>
      match retainedReleaseRequests state with
      | [] => state
      | request :: _ =>
          exceptState state (acknowledgeRelease state request.acknowledged) id
  | .beginClose => (beginClose state).state
  | .finishClose => exceptState state (finishClose state) id

private def acknowledgementCommand : Command → Bool
  | .acknowledgePending | .acknowledgeCurrent | .acknowledgeRetained => true
  | _ => false

private def transitionIsValid (state : State) (command : Command) : Bool :=
  let next := applyCommand state command
  stateIsValid next &&
    decide (state.nextAttempt ≤ next.nextAttempt) &&
    decide (next.nextAttempt ≤ state.nextAttempt + 1) &&
    decide (state.nextSocket ≤ next.nextSocket) &&
    decide (next.nextSocket ≤ state.nextSocket + 1) &&
    decide (state.nextGeneration ≤ next.nextGeneration) &&
    decide (next.nextGeneration ≤ state.nextGeneration + 1) &&
    decide (next.ownerCount ≤ maximumRetainedSockets + 1) &&
    (if next.ownedSockets.length < state.ownedSockets.length then
      acknowledgementCommand command
    else true) &&
    (match state.phase with
      | .closed => snapshot next == snapshot state
      | _ => true)

private def insertState (states : List State) (candidate : State) : List State :=
  if states.any fun state => snapshot state == snapshot candidate then
    states
  else
    candidate :: states

private def deduplicate (states : List State) : List State :=
  states.foldl insertState []

/-!
Explore every command trace up to `depth`, merging states only when every
observable ownership field and allocator counter is equal.  Depth seven covers
resolution, TCP, TLS, ALPN publication, address failure/release/retry,
cancellation, retention, and close attempts in adversarial orders.
-/
private def reachable : Nat → List State
  | 0 => [State.initial]
  | depth + 1 =>
      let previous := reachable depth
      deduplicate (previous ++ previous.flatMap fun state =>
        commands.map (applyCommand state))

private def exhaustiveTraceCheck (depth : Nat) : Bool :=
  let states := reachable depth
  states.all stateIsValid &&
    states.all fun state => commands.all (transitionIsValid state)

private def happyCloseTrace : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 1 | return false
  let .ok connecting := beginAddress resolved.state started.attempt | return false
  let .ok handshaking :=
    tcpConnected connecting.state started.attempt connecting.socket | return false
  let .ok validating :=
    tlsEstablished handshaking started.attempt connecting.socket | return false
  let .ok published :=
    publish validating started.attempt connecting.socket | return false
  let draining := (beginClose published.state).state
  match finishClose draining with
  | .ok _ => return false
  | .error (.ownersRemain 1) => pure ()
  | _ => return false
  let some request := currentReleaseRequest? draining | return false
  let .ok released := acknowledgeRelease draining request.acknowledged | return false
  let .ok closed := finishClose released | return false
  return closed.phase == .closed && closed.ownerCount == 0 &&
    closed.ownedSockets.isEmpty

private def cancelWinsPublicationRace : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 1 | return false
  let .ok connecting := beginAddress resolved.state started.attempt | return false
  let .ok handshaking :=
    tcpConnected connecting.state started.attempt connecting.socket | return false
  let .ok validating :=
    tlsEstablished handshaking started.attempt connecting.socket | return false
  let .ok cancelled := cancel validating started.attempt | return false
  match publish cancelled started.attempt connecting.socket with
  | .error .wrongStage => pure ()
  | _ => return false
  let draining := (beginClose cancelled).state
  let some request := pendingReleaseRequest? draining | return false
  let .ok released := acknowledgeRelease draining request.acknowledged | return false
  let .ok closed := finishClose released | return false
  return closed.phase == .closed && closed.ownedSockets.isEmpty

private def boundedRetryTrace : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 2 | return false
  let .ok first := beginAddress resolved.state started.attempt | return false
  let .ok releasingFirst :=
    rejectAddress first.state started.attempt first.socket | return false
  let some firstRelease := pendingReleaseRequest? releasingFirst | return false
  let .ok readySecond :=
    acknowledgeRelease releasingFirst firstRelease.acknowledged | return false
  let some pending := readySecond.pending | return false
  if pending.stage != .ready 1 || !readySecond.ownedSockets.isEmpty then return false
  let .ok second := beginAddress readySecond started.attempt | return false
  if first.socket == second.socket then return false
  let .ok releasingSecond :=
    rejectAddress second.state started.attempt second.socket | return false
  let some secondRelease := pendingReleaseRequest? releasingSecond | return false
  let .ok exhausted :=
    acknowledgeRelease releasingSecond secondRelease.acknowledged | return false
  return exhausted.pending.isNone && exhausted.ownedSockets.isEmpty &&
    exhausted.nextSocket == 2

private def retainedTransferUsesExactAck : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 1 | return false
  let .ok connecting := beginAddress resolved.state started.attempt | return false
  let .ok handshaking :=
    tcpConnected connecting.state started.attempt connecting.socket | return false
  let .ok validating :=
    tlsEstablished handshaking started.attempt connecting.socket | return false
  let .ok published :=
    publish validating started.attempt connecting.socket | return false
  let some request := currentReleaseRequest? published.state | return false
  let .ok retained := retainCurrent published.state | return false
  if retained.current.isSome || retained.retained.length != 1 then return false
  let .ok released := acknowledgeRelease retained request.acknowledged | return false
  return released.current.isNone && released.retained.isEmpty &&
    released.ownedSockets.isEmpty

/-!
One uncertain retired socket may coexist with one replacement. A second
retirement is rejected without moving the replacement out of `current`; after
the old socket's exact acknowledgement, retrying that same transfer succeeds.
-/
private def retainedCapacityPreservesCurrent : Bool := Id.run do
  let .ok firstStart := start State.initial | return false
  let .ok firstResolved := resolve firstStart.state firstStart.attempt 1 | return false
  let .ok firstSocket := beginAddress firstResolved.state firstStart.attempt | return false
  let .ok firstHandshake :=
    tcpConnected firstSocket.state firstStart.attempt firstSocket.socket | return false
  let .ok firstValidated :=
    tlsEstablished firstHandshake firstStart.attempt firstSocket.socket | return false
  let .ok firstPublished :=
    publish firstValidated firstStart.attempt firstSocket.socket | return false
  let .ok firstRetained := retainCurrent firstPublished.state | return false
  if firstRetained.retained != [firstSocket.socket] then return false

  let .ok secondStart := start firstRetained | return false
  let .ok secondResolved := resolve secondStart.state secondStart.attempt 1 | return false
  let .ok secondSocket := beginAddress secondResolved.state secondStart.attempt | return false
  let .ok secondHandshake :=
    tcpConnected secondSocket.state secondStart.attempt secondSocket.socket | return false
  let .ok secondValidated :=
    tlsEstablished secondHandshake secondStart.attempt secondSocket.socket | return false
  let .ok secondPublished :=
    publish secondValidated secondStart.attempt secondSocket.socket | return false
  let beforeOverflow := snapshot secondPublished.state
  match retainCurrent secondPublished.state with
  | .ok _ | .error .noCurrent => return false
  | .error .capacity => pure ()
  if snapshot (applyCommand secondPublished.state .retainCurrent) != beforeOverflow then
    return false
  let some current := secondPublished.state.current | return false
  if current.socket != secondSocket.socket ||
      secondPublished.state.retained != [firstSocket.socket] ||
      secondPublished.state.ownedSockets != [secondSocket.socket, firstSocket.socket] then
    return false

  let [oldRequest] := retainedReleaseRequests secondPublished.state | return false
  let .ok oldReleased :=
    acknowledgeRelease secondPublished.state oldRequest.acknowledged | return false
  let some current := oldReleased.current | return false
  if current.socket != secondSocket.socket || !oldReleased.retained.isEmpty then
    return false
  let .ok secondRetained := retainCurrent oldReleased | return false
  if secondRetained.current.isSome ||
      secondRetained.retained != [secondSocket.socket] then return false
  let draining := (beginClose secondRetained).state
  let [secondRequest] := retainedReleaseRequests draining | return false
  let .ok released := acknowledgeRelease draining secondRequest.acknowledged | return false
  let .ok closed := finishClose released | return false
  return closed.phase == .closed && closed.ownerCount == 0 &&
    closed.ownedSockets.isEmpty

private def staleAckCannotReleaseNewSocket : Bool := Id.run do
  let .ok firstStart := start State.initial | return false
  let .ok firstResolved := resolve firstStart.state firstStart.attempt 1 | return false
  let .ok firstSocket := beginAddress firstResolved.state firstStart.attempt | return false
  let .ok firstHandshake :=
    tcpConnected firstSocket.state firstStart.attempt firstSocket.socket | return false
  let .ok firstValidated :=
    tlsEstablished firstHandshake firstStart.attempt firstSocket.socket | return false
  let .ok firstPublished :=
    publish firstValidated firstStart.attempt firstSocket.socket | return false
  let some staleRequest := currentReleaseRequest? firstPublished.state | return false
  let .ok firstReleased :=
    acknowledgeRelease firstPublished.state staleRequest.acknowledged | return false
  let .ok secondStart := start firstReleased | return false
  let .ok secondResolved := resolve secondStart.state secondStart.attempt 1 | return false
  let .ok secondSocket := beginAddress secondResolved.state secondStart.attempt | return false
  match acknowledgeRelease secondSocket.state staleRequest.acknowledged with
  | .error .staleAcknowledgement =>
      return secondSocket.state.ownedSockets == [secondSocket.socket] &&
        secondSocket.socket != firstSocket.socket
  | .ok _ => return false

private def addressLimitIsEnforced : Bool := Id.run do
  let .ok started := start State.initial | return false
  match resolve started.state started.attempt (maximumAddresses + 1) with
  | .error .tooManyAddresses => pure ()
  | _ => return false
  let .ok accepted :=
    resolve started.state started.attempt maximumAddresses | return false
  let some pending := accepted.state.pending | return false
  return accepted.decision == .ready &&
    pending.addressCount == maximumAddresses && pending.stage == .ready 0

private def isStaleSocket : Except ProgressError α → Bool
  | .error .staleSocket => true
  | _ => false

/-!
Every callback below carries address zero's socket capability after address one
has started under the same attempt.  Attempt identity alone would accept these
events and mutate address one.
-/
private def staleAddressCallbacksAreRejected : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 2 | return false
  let .ok first := beginAddress resolved.state started.attempt | return false
  let .ok firstRejected :=
    rejectAddress first.state started.attempt first.socket | return false
  let some firstRelease := pendingReleaseRequest? firstRejected | return false
  let .ok readySecond :=
    acknowledgeRelease firstRejected firstRelease.acknowledged | return false
  let .ok second := beginAddress readySecond started.attempt | return false
  if first.socket == second.socket then return false
  unless isStaleSocket (tcpConnected second.state started.attempt first.socket) do
    return false
  unless isStaleSocket (rejectAddress second.state started.attempt first.socket) do
    return false
  let .ok handshaking :=
    tcpConnected second.state started.attempt second.socket | return false
  unless isStaleSocket (tlsEstablished handshaking started.attempt first.socket) do
    return false
  unless isStaleSocket (rejectAddress handshaking started.attempt first.socket) do
    return false
  let .ok validating :=
    tlsEstablished handshaking started.attempt second.socket | return false
  unless isStaleSocket (publish validating started.attempt first.socket) do
    return false
  unless isStaleSocket (rejectAddress validating started.attempt first.socket) do
    return false
  let .ok published := publish validating started.attempt second.socket | return false
  return published.connection.socket == second.socket &&
    published.state.ownedSockets == [second.socket]

/-!
Cancellation preserves an already-advertised failed-address owner.  Its exact
acknowledgement clears the attempt without retrying; duplicate and later stale
acknowledgements cannot consume a new socket.
-/
private def releaseIdentitySurvivesCancellation : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 2 | return false
  let .ok first := beginAddress resolved.state started.attempt | return false
  let .ok releasing :=
    rejectAddress first.state started.attempt first.socket | return false
  let some request := pendingReleaseRequest? releasing | return false
  let some duplicateRequest := pendingReleaseRequest? releasing | return false
  if duplicateRequest != request then return false
  let .ok cancelled := cancel releasing started.attempt | return false
  let some pending := cancelled.pending | return false
  if pending.stage != .releasingCancelled 1 then return false
  let some afterCancel := pendingReleaseRequest? cancelled | return false
  if afterCancel != request then return false
  let .ok released :=
    acknowledgeRelease cancelled request.acknowledged | return false
  if released.pending.isSome || !released.ownedSockets.isEmpty then return false
  match acknowledgeRelease released duplicateRequest.acknowledged with
  | .ok _ => return false
  | .error .staleAcknowledgement => pure ()
  let .ok nextStart := start released | return false
  let .ok nextResolved := resolve nextStart.state nextStart.attempt 1 | return false
  let .ok nextSocket := beginAddress nextResolved.state nextStart.attempt | return false
  match acknowledgeRelease nextSocket.state request.acknowledged with
  | .ok _ => return false
  | .error .staleAcknowledgement =>
      return nextSocket.state.ownedSockets == [nextSocket.socket] &&
        nextSocket.socket != first.socket

private def closePreservesFailedReleaseIdentity : Bool := Id.run do
  let .ok started := start State.initial | return false
  let .ok resolved := resolve started.state started.attempt 2 | return false
  let .ok first := beginAddress resolved.state started.attempt | return false
  let .ok releasing :=
    rejectAddress first.state started.attempt first.socket | return false
  let some request := pendingReleaseRequest? releasing | return false
  let draining := (beginClose releasing).state
  let some pending := draining.pending | return false
  if pending.stage != .releasingCancelled 1 then return false
  let some duringClose := pendingReleaseRequest? draining | return false
  if duringClose != request then return false
  let .ok released := acknowledgeRelease draining request.acknowledged | return false
  let .ok closed := finishClose released | return false
  return closed.phase == .closed && closed.ownerCount == 0

example : State.initial.Invariant := State.initial.invariant

example : exhaustiveTraceCheck 7 = true := by native_decide

example : happyCloseTrace = true := by native_decide
example : cancelWinsPublicationRace = true := by native_decide
example : boundedRetryTrace = true := by native_decide
example : retainedTransferUsesExactAck = true := by native_decide
example : retainedCapacityPreservesCurrent = true := by native_decide
example : staleAckCannotReleaseNewSocket = true := by native_decide
example : addressLimitIsEnforced = true := by native_decide
example : staleAddressCallbacksAreRejected = true := by native_decide
example : releaseIdentitySurvivesCancellation = true := by native_decide
example : closePreservesFailedReleaseIdentity = true := by native_decide

def run : IO Unit := do
  unless exhaustiveTraceCheck 7 do
    throw (IO.userError "channel-initialization exhaustive trace check failed")
  unless happyCloseTrace && cancelWinsPublicationRace && boundedRetryTrace &&
      retainedTransferUsesExactAck && retainedCapacityPreservesCurrent &&
      staleAckCannotReleaseNewSocket &&
      addressLimitIsEnforced && staleAddressCallbacksAreRejected &&
      releaseIdentitySurvivesCancellation && closePreservesFailedReleaseIdentity do
    throw (IO.userError "channel-initialization focused ownership trace failed")
  IO.println s!"Channel initialization ownership tests passed ({(reachable 7).length} states)"

end ChannelInitializationTest

def main : IO Unit :=
  ChannelInitializationTest.run
