module

public import Grpc.Client
public import Grpc.CallCredentials
public import Grpc.Cancellation
public import Grpc.Execution
public import Grpc.ManagedChannel.Config
public import Std.Async.Timer

public section

/-!
# Typed outbound unary RPCs

This is the narrow adapter between the pure channel configuration and the
in-repo `Grpc.Client` call surface.  Every invocation obtains fresh credential metadata from the
caller-supplied per-call credentials seam, starts and retains the exact
`Grpc.Client.Call`, and owns that call through its terminal `finish`.

The `grpc-timeout` header is retained for peer-side enforcement, but is not
trusted as a local deadline.  A local monotonic timer races the call owner.  If
local cancellation commits, the same call is cancelled and its owner is joined
before an ordinary local error is returned. Already-terminal peer results keep
their provenance; cleanup uncertainty is represented separately.
-/

namespace Grpc.UnaryCall

open Std.Async

/--
Construct call metadata from refined credential entries.  Keeping this
definition module-private avoids creating a publicly renderable `CallOptions`
value containing secret material.
-/
private def optionsFor
    (entries : Array CredentialEntry)
    (timeout : String) :
    Grpc.Client.CallOptions := {
  metadata := entries.map fun entry =>
    _root_.Http2.Header.of entry.name entry.exposeValue
  timeout := some timeout
}

private theorem optionsFor_timeout
    (entries : Array CredentialEntry) (timeout : String) :
    (optionsFor entries timeout).timeout = some timeout := by
  rfl

/-- Exactly the refined credential entries become call metadata headers. -/
private theorem optionsFor_metadata
    (entries : Array CredentialEntry) (timeout : String) :
    (optionsFor entries timeout).metadata =
      entries.map (fun entry =>
        _root_.Http2.Header.of entry.name entry.exposeValue) := by
  rfl

/--
A single refined entry is visible in the built call metadata under its own
name with its exact plaintext value.  This in-module certification of header
installation holds without ever rendering a `CallOptions` value.
-/
private theorem optionsFor_singleton_get?
    (entry : CredentialEntry) (timeout : String) :
    ((optionsFor #[entry] timeout).metadata.get? entry.name) =
      some entry.exposeValue := by
  simp [optionsFor, _root_.Http2.Headers.get?, _root_.Http2.Headers.getAll,
    _root_.Http2.Header.of]

/-- Obtain fresh per-call credential entries and build the call options. -/
private def callOptions
    (configuration : ManagedChannel.Config)
    (timeout : String) :
    IO Grpc.Client.CallOptions := do
  pure (optionsFor (← configuration.credentials.fresh) timeout)

inductive Error where
  | requestEncoding
  /-- The local monotonic deadline won after the exact call was joined. -/
  | localDeadlineExceeded
  /-- Cancellation prevented admission, or the admitted exact owner was joined. -/
  | ownerCancelled
  /--
  The exact terminal status and, when unambiguous, the peer's decoded
  `grpc-status-details-bin` trailer.  Synthetic adapter failures never carry
  status details.
  -/
  | rpc (status : Grpc.Status) (statusDetails : Option ByteArray := none)
  | responseDecoding
  /-- An unexpected call action failed after exact cleanup was acknowledged. -/
  | actionFailed
  /-- Neither the call nor its containing connection proved terminal cleanup. -/
  | cleanupUncertain
deriving DecidableEq

namespace Error

/-- Render only bounded classifications, never peer-controlled descriptions or details. -/
def render : Error → String
  | .requestEncoding => "transport request encoding failed"
  | .localDeadlineExceeded => "transport local deadline exceeded"
  | .ownerCancelled => "transport call was cancelled by its local owner"
  | .rpc status _ =>
      s!"transport RPC failed with status code {status.code.toNat}"
  | .responseDecoding => "transport response decoding failed"
  | .actionFailed => "transport call action failed after cleanup"
  | .cleanupUncertain =>
      "transport call cleanup was uncertain"

end Error

/-- Ordinary diagnostics redact peer-controlled status messages and binary details. -/
instance : Repr Error where
  reprPrec error _ := Std.Format.text (Error.render error)

/--
The operations required to own one already-started unary call.  This
configuration-free interface is public so lifecycle tests can be deterministic
without exposing authentication metadata or constructing a network connection.
-/
structure Primitives (Handle : Type) where
  send : Handle → ByteArray → Async (Except Grpc.Status Unit)
  closeSend : Handle → Async (Except Grpc.Status Unit)
  recv? : Handle → Async (Except Grpc.Status (Option ByteArray))
  finish :
    Handle →
      Async (Except Grpc.Status
        (Grpc.Status × _root_.Http2.Headers × _root_.Http2.Headers))
  cancel : Handle → Async Unit
  /-- Report the atomic local-cancellation commit, not whether a cancellation
  request was merely attempted. A driver without origin evidence preserves
  the owner's terminal RPC result instead of labelling it a local outcome. -/
  cancelIfActive? : Option (Handle → Async Bool) := none

/-- Invoke the driver's cancellation-origin operation when supplied. Without
one, request ordinary cancellation and preserve terminal RPC provenance. -/
def Primitives.cancelIfActive (primitives : Primitives Handle) (call : Handle) : Async Bool := do
  match primitives.cancelIfActive? with
  | some cancel => cancel call
  | none =>
      primitives.cancel call
      pure false

/--
One armed deadline and its idempotent resource cleanup.  `disarm` matters when
stream creation fails before the selector race begins.
-/
structure ArmedDeadline where
  selector : Selector Unit
  disarm : Async Unit

/--
A deadline source prepared before the call is started.  Production begins its
monotonic countdown when the exact call handle enters `Selectable.one`; tests
may supply controlled selectors.
-/
structure DeadlineDriver where
  arm : Nat → Async ArmedDeadline

private def asyncTaskSelector (task : AsyncTask α) : Selector α where
  tryFn := do
    if ← IO.hasFinished task then
      return some (← await task)
    else
      return none
  registerFn := fun waiter => do
    BaseIO.chainTask task fun result =>
      waiter.race (pure ()) fun promise =>
        promise.resolve result
  unregisterFn := pure ()

private def deadlineMilliseconds (deadline : RpcDeadline) : Nat :=
  deadline.seconds * 1000

/--
Create a real monotonic timer.  `Selectable.one` starts it and invokes its
unregister hook when the call wins, so completed calls retain neither a timer
nor a separately blocked waiter task.
-/
private def systemDeadlineDriver : DeadlineDriver where
  arm := fun milliseconds => do
    let sleeper ← Sleep.mk
      (Std.Time.Millisecond.Offset.ofNat milliseconds)
    pure {
      selector := sleeper.selector
      disarm := sleeper.stop
    }

private def grpcPrimitives : Primitives Grpc.Client.Call where
  send := Grpc.Client.Call.send
  closeSend := Grpc.Client.Call.closeSend
  recv? := Grpc.Client.Call.recv?
  finish := Grpc.Client.Call.finish
  cancel := Grpc.Client.Call.cancel
  cancelIfActive? := some Grpc.Client.Call.cancelIfActive

private def cardinalityStatus (count : String) : Grpc.Status :=
  Grpc.Status.internal s!"expected exactly one response message, got {count}"

/--
Exact status installed by the `Grpc.Client.Call.cancelIfActive` linearization
when the call was still active. This must match the status `Grpc.Client`
installs byte-for-byte. Matching text alone is never local-origin evidence:
classification also requires that cancellation's actual atomic commit.
-/
private def locallyCancelledStatus : Grpc.Status :=
  Grpc.Status.cancelled "call cancelled locally"

/--
Decode the standard rich-status trailer.  Multiple values are ambiguous and
therefore fail closed instead of making retry policy depend on header order.
Malformed binary metadata is likewise not exposed as typed status evidence.
-/
private def statusDetailsFromTrailers
    (trailers : _root_.Http2.Headers) : Option ByteArray :=
  match Grpc.Metadata.getBinaryAll trailers "grpc-status-details-bin" with
  | .ok values =>
      if values.size == 1 then values[0]? else none
  | .error _ => none

private def rpcErrorFromTerminal
    (status : Grpc.Status)
    (trailers : _root_.Http2.Headers) : Error :=
  .rpc status (statusDetailsFromTrailers trailers)

/--
Recover details after an earlier call action returned a status only when the
terminal status agrees.  This preserves the earlier status without attaching
details that may describe a different failure.
-/
private def rpcErrorAfterFinish
    (status : Grpc.Status)
    (finishResult :
      Except Grpc.Status
        (Grpc.Status × _root_.Http2.Headers × _root_.Http2.Headers)) :
    Error :=
  match finishResult with
  | .ok (terminalStatus, _, trailers) =>
      if terminalStatus == status then
        rpcErrorFromTerminal status trailers
      else
        .rpc status
  | .error _ => .rpc status

namespace Ownership

variable {Handle : Type}

/-- Primitive invocations name the exact call they operate on. -/
inductive Command (Handle : Type) where
  | send (call : Handle) (request : ByteArray)
  | closeSend (call : Handle)
  | receive (call : Handle)
  | finish (call : Handle)
  | cancel (call : Handle)

@[expose] def Command.Return : Command Handle → Type
  | .send _ _ | .closeSend _ => Except Grpc.Status Unit
  | .receive _ => Except Grpc.Status (Option ByteArray)
  | .finish _ => Except Grpc.Status
      (Grpc.Status × _root_.Http2.Headers × _root_.Http2.Headers)
  | .cancel _ => Unit

@[expose] def Outcome (command : Command Handle) : Type := Except IO.Error command.Return

abbrev Program (Handle : Type) :=
  Execution.Program (Command Handle) Outcome (Except Error ByteArray)

/-- Recovery acknowledges terminal cleanup only after cancel and finish both
return; an exception from either recovery primitive retains uncertainty. -/
def recover (call : Handle) : Program Handle :=
  .call (.cancel call) fun
    | .error _ => .done (.error .cleanupUncertain)
    | .ok () => .call (.finish call) fun
        | .error _ => .done (.error .cleanupUncertain)
        | .ok _ => .done (.error .actionFailed)

def failAfterTerminal (call : Handle) (status : Grpc.Status) : Program Handle :=
  .call (.finish call) fun
    | .error _ => recover call
    | .ok result => .done (.error (rpcErrorAfterFinish status result))

def failAfterCancel (call : Handle) (status : Grpc.Status) : Program Handle :=
  .call (.cancel call) fun
    | .error _ => recover call
    | .ok () => failAfterTerminal call status

def settleNoResponse (call : Handle) : Program Handle :=
  .call (.finish call) fun
    | .error _ => recover call
    | .ok (.error status) => .done (.error (.rpc status))
    | .ok (.ok (status, _, trailers)) =>
        if status.isOk then .done (.error (.rpc (cardinalityStatus "0")))
        else .done (.error (rpcErrorFromTerminal status trailers))

def settleOneResponse (call : Handle) (response : ByteArray) : Program Handle :=
  .call (.finish call) fun
    | .error _ => recover call
    | .ok (.error status) => .done (.error (.rpc status))
    | .ok (.ok (status, _, trailers)) =>
        if status.isOk then .done (.ok response)
        else .done (.error (rpcErrorFromTerminal status trailers))

def settleMultipleResponses (call : Handle) : Program Handle :=
  .call (.cancel call) fun
    | .error _ => recover call
    | .ok () => .call (.finish call) fun
        | .error _ => recover call
        | .ok (.error _) => .done (.error (.rpc (cardinalityStatus "at least 2")))
        | .ok (.ok (status, _, trailers)) =>
            if status.isOk then .done (.error (.rpc (cardinalityStatus "at least 2")))
            else .done (.error (rpcErrorFromTerminal status trailers))

/-- The production unary owner's complete finite control flow. Exceptions
and gRPC failures are distinct outcomes at every primitive boundary. -/
def program (call : Handle) (request : ByteArray) : Program Handle :=
  .call (.send call request) fun
    | .error _ => recover call
    | .ok (.error status) => failAfterCancel call status
    | .ok (.ok ()) => .call (.closeSend call) fun
        | .error _ => recover call
        | .ok (.error status) => failAfterTerminal call status
        | .ok (.ok ()) => .call (.receive call) fun
            | .error _ => recover call
            | .ok (.error status) => failAfterTerminal call status
            | .ok (.ok none) => settleNoResponse call
            | .ok (.ok (some response)) => .call (.receive call) fun
                | .error _ => recover call
                | .ok (.error status) => failAfterTerminal call status
                | .ok (.ok none) => settleOneResponse call response
                | .ok (.ok (some _)) => settleMultipleResponses call

private theorem recover_no_success
    (executed : Execution.Executes (recover call) trace (.ok response)) : False := by
  obtain ⟨cancelled, tail, rfl, hcancel⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases cancelled with
  | error error => cases hcancel
  | ok value =>
      cases value
      obtain ⟨finished, rest, rfl, hfinish⟩ := Execution.executes_call_iff _ _ |>.mp hcancel
      cases finished <;> cases hfinish

private theorem failAfterTerminal_no_success
    (executed : Execution.Executes (failAfterTerminal call status) trace (.ok response)) : False := by
  obtain ⟨finished, tail, rfl, next⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases finished with
  | error error => exact recover_no_success next
  | ok result => cases next

private theorem failAfterCancel_no_success
    (executed : Execution.Executes (failAfterCancel call status) trace (.ok response)) : False := by
  obtain ⟨cancelled, tail, rfl, next⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases cancelled with
  | error error => exact recover_no_success next
  | ok value => exact failAfterTerminal_no_success next

private theorem settleNoResponse_no_success
    (executed : Execution.Executes (settleNoResponse call) trace (.ok response)) : False := by
  obtain ⟨finished, tail, rfl, next⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases finished with
  | error error => exact recover_no_success next
  | ok result =>
      cases result with
      | error status => cases next
      | ok terminal =>
          rcases terminal with ⟨status, headers, trailers⟩
          simp only at next
          split at next <;> cases next

private theorem settleMultipleResponses_no_success
    (executed : Execution.Executes (settleMultipleResponses call) trace (.ok response)) : False := by
  obtain ⟨cancelled, tail, rfl, hcancel⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases cancelled with
  | error error => exact recover_no_success hcancel
  | ok value =>
      cases value
      obtain ⟨finished, rest, rfl, hfinish⟩ := Execution.executes_call_iff _ _ |>.mp hcancel
      cases finished with
      | error error => exact recover_no_success hfinish
      | ok result =>
          cases result with
          | error status => cases hfinish
          | ok terminal =>
              rcases terminal with ⟨status, headers, trailers⟩
              simp only at hfinish
              split at hfinish <;> cases hfinish

private theorem settleOneResponse_success
    (executed : Execution.Executes (settleOneResponse call response) trace (.ok returned)) :
    ∃ status headers trailers, status.isOk = true ∧ returned = response ∧
      trace = [⟨.finish call, .ok (.ok (status, headers, trailers))⟩] := by
  obtain ⟨finished, tail, rfl, next⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases finished with
  | error error => exact False.elim (recover_no_success next)
  | ok result =>
      cases result with
      | error status => cases next
      | ok terminal =>
          rcases terminal with ⟨status, headers, trailers⟩
          simp only at next
          split at next
          next successful =>
            obtain ⟨rfl, equal⟩ := Execution.executes_done_iff.mp next
            exact ⟨status, headers, trailers, successful, Except.ok.inj equal, rfl⟩
          next => cases next

/-- A successful unary owner has exactly one received message followed by
end-of-messages and a successful terminal status, all on the same call. -/
theorem success_trace
    {Handle : Type} {call : Handle} {request response : ByteArray}
    {trace : List (Execution.Event (Command Handle) Outcome)}
    (executed : Execution.Executes (program call request) trace (.ok response)) :
    ∃ status headers trailers, status.isOk = true ∧
      trace = [
        ⟨.send call request, .ok (.ok ())⟩,
        ⟨.closeSend call, .ok (.ok ())⟩,
        ⟨.receive call, .ok (.ok (some response))⟩,
        ⟨.receive call, .ok (.ok none)⟩,
        ⟨.finish call, .ok (.ok (status, headers, trailers))⟩] := by
  obtain ⟨sent, tail, rfl, hsend⟩ := Execution.executes_call_iff _ _ |>.mp executed
  cases sent with
  | error error => exact False.elim (recover_no_success hsend)
  | ok result =>
      cases result with
      | error status => exact False.elim (failAfterCancel_no_success hsend)
      | ok value =>
          cases value
          obtain ⟨closed, afterClose, rfl, hclose⟩ := Execution.executes_call_iff _ _ |>.mp hsend
          cases closed with
          | error error => exact False.elim (recover_no_success hclose)
          | ok result =>
              cases result with
              | error status => exact False.elim (failAfterTerminal_no_success hclose)
              | ok value =>
                  cases value
                  obtain ⟨received, afterFirst, rfl, hfirst⟩ := Execution.executes_call_iff _ _ |>.mp hclose
                  cases received with
                  | error error => exact False.elim (recover_no_success hfirst)
                  | ok result =>
                      cases result with
                      | error status => exact False.elim (failAfterTerminal_no_success hfirst)
                      | ok first =>
                          cases first with
                          | none => exact False.elim (settleNoResponse_no_success hfirst)
                          | some bytes =>
                              obtain ⟨secondResult, afterSecond, rfl, hsecond⟩ :=
                                Execution.executes_call_iff _ _ |>.mp hfirst
                              cases secondResult with
                              | error error => exact False.elim (recover_no_success hsecond)
                              | ok result =>
                                  cases result with
                                  | error status => exact False.elim (failAfterTerminal_no_success hsecond)
                                  | ok second =>
                                      cases second with
                                      | some bytes => exact False.elim (settleMultipleResponses_no_success hsecond)
                                      | none =>
                                          obtain ⟨status, headers, trailers, success, rfl, rfl⟩ :=
                                            settleOneResponse_success hsecond
                                          exact ⟨status, headers, trailers, success, rfl⟩

private inductive NeedsFinish (call : Handle) : Program Handle → Prop where
  | uncertain : NeedsFinish call (.done (.error .cleanupUncertain))
  | finish {next : Outcome (.finish call) → Program Handle}
      (onException : ∀ error, NeedsFinish call (next (.error error))) :
      NeedsFinish call (.call (.finish call) next)
  | step {command : Command Handle} {next : Outcome command → Program Handle}
      (following : ∀ outcome, NeedsFinish call (next outcome)) :
      NeedsFinish call (.call command next)

private theorem NeedsFinish.acknowledged {call : Handle} {p : Program Handle}
    (discipline : NeedsFinish call p)
    (executed : Execution.Executes p trace result)
    (certain : result ≠ .error .cleanupUncertain) :
    ∃ terminal, (⟨.finish call, .ok terminal⟩ : Execution.Event (Command Handle) Outcome) ∈ trace := by
  induction discipline generalizing trace result with
  | uncertain =>
      cases executed
      exact False.elim (certain rfl)
  | finish onException ih =>
      obtain ⟨outcome, tail, rfl, continuation⟩ := Execution.executes_call_iff _ _ |>.mp executed
      cases outcome with
      | error error =>
          obtain ⟨terminal, member⟩ := ih error continuation certain
          exact ⟨terminal, List.mem_cons_of_mem _ member⟩
      | ok terminal => exact ⟨terminal, List.mem_cons_self⟩
  | step following ih =>
      obtain ⟨outcome, tail, rfl, continuation⟩ := Execution.executes_call_iff _ _ |>.mp executed
      obtain ⟨terminal, member⟩ := ih outcome continuation certain
      exact ⟨terminal, List.mem_cons_of_mem _ member⟩

private theorem recover_needsFinish (call : Handle) : NeedsFinish call (recover call) := by
  apply NeedsFinish.step
  intro outcome
  cases outcome with
  | error error => exact .uncertain
  | ok value => exact .finish (fun _ => .uncertain)

private theorem failAfterTerminal_needsFinish (call : Handle) (status : Grpc.Status) :
    NeedsFinish call (failAfterTerminal call status) :=
  .finish (fun _ => recover_needsFinish call)

private theorem failAfterCancel_needsFinish (call : Handle) (status : Grpc.Status) :
    NeedsFinish call (failAfterCancel call status) := by
  apply NeedsFinish.step
  intro outcome
  cases outcome with
  | error error => exact recover_needsFinish call
  | ok value => exact failAfterTerminal_needsFinish call status

private theorem settleMultipleResponses_needsFinish (call : Handle) :
    NeedsFinish call (settleMultipleResponses call) := by
  apply NeedsFinish.step
  intro outcome
  cases outcome with
  | error error => exact recover_needsFinish call
  | ok value => exact .finish (fun _ => recover_needsFinish call)

private theorem program_needsFinish (call : Handle) (request : ByteArray) :
    NeedsFinish call (program call request) := by
  apply NeedsFinish.step
  intro sent
  cases sent with
  | error error => exact recover_needsFinish call
  | ok result =>
      cases result with
      | error status => exact failAfterCancel_needsFinish call status
      | ok value =>
          apply NeedsFinish.step
          intro closed
          cases closed with
          | error error => exact recover_needsFinish call
          | ok result =>
              cases result with
              | error status => exact failAfterTerminal_needsFinish call status
              | ok value =>
                  apply NeedsFinish.step
                  intro received
                  cases received with
                  | error error => exact recover_needsFinish call
                  | ok result =>
                      cases result with
                      | error status => exact failAfterTerminal_needsFinish call status
                      | ok first =>
                          cases first with
                          | none => exact .finish (fun _ => recover_needsFinish call)
                          | some bytes =>
                              apply NeedsFinish.step
                              intro received
                              cases received with
                              | error error => exact recover_needsFinish call
                              | ok result =>
                                  cases result with
                                  | error status => exact failAfterTerminal_needsFinish call status
                                  | ok second =>
                                      cases second with
                                      | none => exact .finish (fun _ => recover_needsFinish call)
                                      | some _ => exact settleMultipleResponses_needsFinish call

/-- Every completed owner result that acknowledges cleanup contains a returned
finish operation on its exact call. A returned gRPC error still acknowledges
finish; a thrown cleanup exception may instead yield `cleanupUncertain`. -/
theorem terminal_acknowledged {Handle : Type} {call : Handle} {request : ByteArray}
    {trace : List (Execution.Event (Command Handle) Outcome)} {result : Except Error ByteArray}
    (executed : Execution.Executes (program call request) trace result)
    (certain : result ≠ .error .cleanupUncertain) :
    ∃ terminal, (⟨.finish call, .ok terminal⟩ : Execution.Event (Command Handle) Outcome) ∈ trace :=
  (program_needsFinish call request).acknowledged executed certain

private theorem program_no_local_result (call : Handle) (request : ByteArray) :
    (program call request).ReturnsOnly (fun result =>
      result ≠ .error .ownerCancelled ∧ result ≠ .error .localDeadlineExceeded) := by
  simp only [program, recover, failAfterCancel, failAfterTerminal,
    settleNoResponse, settleOneResponse, settleMultipleResponses,
    Execution.Program.ReturnsOnly]
  repeat first
    | intro outcome; cases outcome
    | split
    | constructor
    | simp_all [rpcErrorAfterFinish, rpcErrorFromTerminal]

/-- Local cancellation provenance is selected only by the outer invocation
owner; the primitive owner cannot invent either ordinary local outcome. -/
theorem no_local_result
    (executed : Execution.Executes (program call request) trace result) :
    result ≠ .error .ownerCancelled ∧ result ≠ .error .localDeadlineExceeded :=
  Execution.returnsOnly_result
    (post := fun value => value ≠ .error .ownerCancelled ∧ value ≠ .error .localDeadlineExceeded)
    (program_no_local_result call request) executed

/-- A completion returned by interpreting the actual primitive-owner program.
The certificate is erased; the value is the owner's ordinary result. -/
@[expose] def Completion (call : Handle) (request : ByteArray) :=
  { result : Except Error ByteArray //
    ∃ trace, Execution.Executes (program call request) trace result }

private def invoke (primitives : Primitives Handle)
    (command : Command Handle) : Async (Outcome command) := do
  try
    match command with
    | .send call request => pure (.ok (← primitives.send call request))
    | .closeSend call => pure (.ok (← primitives.closeSend call))
    | .receive call => pure (.ok (← primitives.recv? call))
    | .finish call => pure (.ok (← primitives.finish call))
    | .cancel call => pure (.ok (← primitives.cancel call))
  catch error => pure (.error error)

end Ownership

/--
Own one exact call through send, half-close, receive, and terminal cleanup.
Every result except `cleanupUncertain` contains a returned exact-call finish.
-/
private def ownUnaryCall
    (primitives : Primitives Handle)
    (call : Handle)
    (request : ByteArray) : Async (Ownership.Completion call request) :=
  (Ownership.program call request).interpret (Ownership.invoke primitives)

inductive OwnerRace (α : Type) where
  | completed (value : α)
  | expired
  | cancelled

private def raceOwner
    (owner : AsyncTask α)
    (deadline : Selector Unit)
    (cancellation : Option Cancellation) : Async (OwnerRace α) := do
  let base := #[
    Selectable.case (asyncTaskSelector owner) fun value =>
      pure (.completed value),
    Selectable.case deadline fun _ =>
      pure .expired
  ]
  let choices := match cancellation with
    | none => base
    | some cancellation =>
        base.push <| Selectable.case cancellation.selector fun _ =>
          pure .cancelled
  Selectable.one choices

private def finishedOwner?
    (owner : AsyncTask α) : Async (Option α) := do
  if ← IO.hasFinished owner then
    some <$> await owner
  else
    pure none

private def decodeOwnedResult
    (decode : ByteArray → Except δ Response) :
    Except Error ByteArray → Except Error Response
  | .error error => .error error
  | .ok response =>
      match decode response with
      | .ok decoded => .ok decoded
      | .error _ => .error .responseDecoding

private theorem decodeOwnedResult_not_local {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (localError : Error)
    (isLocal : localError = .ownerCancelled ∨ localError = .localDeadlineExceeded) :
    decodeOwnedResult decode completion.val ≠ .error localError := by
  obtain ⟨trace, executed⟩ := completion.property
  have ordinary := Ownership.no_local_result executed
  cases result : completion.val with
  | error error =>
      rcases isLocal with rfl | rfl
      · simpa [decodeOwnedResult, result] using ordinary.1
      · simpa [decodeOwnedResult, result] using ordinary.2
  | ok bytes =>
      rcases isLocal with rfl | rfl <;> cases decoded : decode bytes <;>
        simp [decodeOwnedResult, result, decoded]

private theorem decodeOwnedResult_success {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) {response : Response}
    (success : decodeOwnedResult decode completion.val = .ok response) :
    ∃ bytes, completion.val = .ok bytes ∧ decode bytes = .ok response := by
  cases result : completion.val with
  | error error => simp [decodeOwnedResult, result] at success
  | ok bytes =>
      cases decoded : decode bytes with
      | error error => simp [decodeOwnedResult, result, decoded] at success
      | ok value =>
          simp only [decodeOwnedResult, result, decoded, Except.ok.injEq] at success
          exact ⟨bytes, rfl, success ▸ decoded⟩

/--
Classify the exact owner result after the adapter requested cancellation.
Local provenance requires both the actual atomic cancellation commit and its
terminal status. Peer-controlled status text alone cannot establish origin;
other terminal results retain their original provenance.
-/
private def resultAfterLocalCancellation {call : Handle} {request : ByteArray}
    (committed : Bool)
    (localResult : Error)
    (decode : ByteArray → Except δ Response) :
    Option (Ownership.Completion call request) → Except Error Response
  | none => .error .cleanupUncertain
  | some completion =>
      match completion.val with
      | .error (.rpc status statusDetails) =>
          if committed && status == locallyCancelledStatus && statusDetails.isNone then
            .error localResult
          else
            .error (.rpc status statusDetails)
      | result => decodeOwnedResult decode result

private theorem resultAfterLocalCancellation_false {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (localError : Error) :
    resultAfterLocalCancellation false localError decode (some completion) =
      decodeOwnedResult decode completion.val := by
  cases result : completion.val with
  | ok bytes => simp [resultAfterLocalCancellation, result]
  | error error => cases error <;> simp [resultAfterLocalCancellation, decodeOwnedResult, result]

private theorem local_result_requires_commit {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (requested observed : Error)
    (isLocal : observed = .ownerCancelled ∨ observed = .localDeadlineExceeded)
    (committed : Bool)
    (result : resultAfterLocalCancellation committed requested decode (some completion) =
      .error observed) : committed = true := by
  cases committed
  · rw [resultAfterLocalCancellation_false] at result
    exact False.elim (decodeOwnedResult_not_local completion decode observed isLocal result)
  · rfl

private theorem local_result_owner_certain {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (requested observed : Error)
    (isLocal : observed = .ownerCancelled ∨ observed = .localDeadlineExceeded)
    (committed : Bool)
    (result : resultAfterLocalCancellation committed requested decode (some completion) =
      .error observed) : completion.val ≠ .error .cleanupUncertain := by
  intro uncertain
  simp only [resultAfterLocalCancellation, uncertain, decodeOwnedResult, Except.error.injEq] at result
  rcases isLocal with rfl | rfl <;> contradiction

private theorem resultAfterLocalCancellation_success {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) {response : Response}
    (committed : Bool) (localError : Error)
    (success : resultAfterLocalCancellation committed localError decode (some completion) =
      .ok response) :
    ∃ bytes, completion.val = .ok bytes ∧ decode bytes = .ok response := by
  cases result : completion.val with
  | error error =>
      cases error <;>
        simp_all [resultAfterLocalCancellation, decodeOwnedResult] <;>
        split at success <;> contradiction
  | ok bytes =>
      have decoded : decodeOwnedResult decode completion.val = .ok response := by
        simpa [resultAfterLocalCancellation, result] using success
      simpa [result] using decodeOwnedResult_success completion decode decoded

private theorem resultAfterLocalCancellation_success_iff {call : Handle} {request : ByteArray}
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (response : Response)
    (committed : Bool) (localError : Error) :
    resultAfterLocalCancellation committed localError decode (some completion) = .ok response ↔
      decodeOwnedResult decode completion.val = .ok response := by
  cases result : completion.val with
  | ok bytes => simp [resultAfterLocalCancellation, result]
  | error error =>
      cases error <;> simp [resultAfterLocalCancellation, decodeOwnedResult, result]
      split <;> simp

/--
Post-admission operations for the exact call and its exact owner task. The
production interpreter and the checked finite program share this control flow.
-/
private structure OwnedRuntime (m : Type → Type) (Handle : Type) where
  disarm : ArmedDeadline → m Unit
  spawn : (call : Handle) → (request : ByteArray) → m (AsyncTask (Ownership.Completion call request))
  cancel : Handle → m Unit
  cancelIfActive : Handle → m Bool
  finish : Handle → m (Except Grpc.Status
    (Grpc.Status × _root_.Http2.Headers × _root_.Http2.Headers))
  race : {call : Handle} → {request : ByteArray} →
    AsyncTask (Ownership.Completion call request) → ArmedDeadline → Option Cancellation →
    m (OwnerRace (Ownership.Completion call request))
  completed : {call : Handle} → {request : ByteArray} →
    AsyncTask (Ownership.Completion call request) → m (Option (Ownership.Completion call request))
  join : {call : Handle} → {request : ByteArray} →
    AsyncTask (Ownership.Completion call request) → m (Ownership.Completion call request)

private def ownedInvocation [Monad m] [MonadExceptOf IO.Error m]
    (runtime : OwnedRuntime m Handle) (call : Handle) (encoded : ByteArray)
    (armedDeadline : ArmedDeadline) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) : m (Except Error Response) := do
  let scheduled : Except Error (AsyncTask (Ownership.Completion call encoded)) ←
    try
      pure (Except.ok (← runtime.spawn call encoded) :
        Except Error (AsyncTask (Ownership.Completion call encoded)))
    catch _ =>
      try
        runtime.cancel call
        discard <| runtime.finish call
        pure (Except.error .actionFailed :
          Except Error (AsyncTask (Ownership.Completion call encoded)))
      catch _ =>
        pure (Except.error .cleanupUncertain :
          Except Error (AsyncTask (Ownership.Completion call encoded)))
  let owner ← match scheduled with
    | .ok owner => pure owner
    | .error cleanup =>
        let disarmFailed ←
          try
            runtime.disarm armedDeadline
            pure false
          catch _ =>
            pure true
        if cleanup == .cleanupUncertain then
          return .error .cleanupUncertain
        else if disarmFailed then
          throw (IO.userError "RPC deadline cleanup failed")
        else
          return .error cleanup
  let raced : Except Error (OwnerRace (Ownership.Completion call encoded)) ←
    try
      pure (Except.ok
        (← runtime.race owner armedDeadline cancellation) :
        Except Error (OwnerRace (Ownership.Completion call encoded)))
    catch error =>
      let disarmFailure : Option IO.Error ←
        try
          runtime.disarm armedDeadline
          pure none
        catch disarmError =>
          pure (some disarmError)
      -- A selector/registration failure is outside the call owner. Cancel and
      -- join that exact owner before propagating it across the channel lease.
      try
        runtime.cancel call
      catch _ =>
        pure ()
      let joined : Option (Ownership.Completion call encoded) ←
        try
          some <$> runtime.join owner
        catch _ =>
          pure none
      match joined with
      | none | some ⟨.error .cleanupUncertain, _⟩ =>
          pure (Except.error .cleanupUncertain :
            Except Error (OwnerRace (Ownership.Completion call encoded)))
      | some _ =>
          match disarmFailure with
          | some disarmError => throw disarmError
          | none => throw error
  let raceResult ← match raced with
    | .ok raceResult => pure raceResult
    | .error error => return .error error
  match raceResult with
  | .completed result =>
      -- The call owner has already acknowledged terminal cleanup, so a
      -- disarm failure cannot let transport use escape its channel lease.
      runtime.disarm armedDeadline
      pure (decodeOwnedResult decode result.val)
  | .expired =>
      -- Preserve a timer cleanup failure, but never let it skip exact-call
      -- cancellation and the owner join below.
      let disarmFailure : Option IO.Error ←
        try
          runtime.disarm armedDeadline
          pure none
        catch error =>
          pure (some error)
      -- Fair selection may choose the deadline even when the exact owner has
      -- concurrently become terminal. Preserve that completed result before
      -- requesting cancellation; it is stronger evidence than selector order.
      let completed : Option (Ownership.Completion call encoded) ←
        try
          runtime.completed owner
        catch _ =>
          pure none
      let result ← match completed with
        | some completed => pure (decodeOwnedResult decode completed.val)
        | none => do
            -- Cancel the exact call and join its owner. `ownUnaryCall` cannot
            -- finish before `Call.finish`, so this await is the cleanup
            -- acknowledgement.
            let committed ← try runtime.cancelIfActive call catch _ => pure false
            let joined : Option (Ownership.Completion call encoded) ←
              try
                some <$> runtime.join owner
              catch _ =>
                pure none
            pure (resultAfterLocalCancellation
              committed .localDeadlineExceeded decode joined)
      match result with
      | .error .cleanupUncertain => pure (.error .cleanupUncertain)
      | .error .actionFailed => pure (.error .actionFailed)
      | result =>
          match disarmFailure with
          | some error => throw error
          | none => pure result
  | .cancelled =>
      let disarmFailure : Option IO.Error ←
        try
          runtime.disarm armedDeadline
          pure none
        catch error =>
          pure (some error)
      let completed : Option (Ownership.Completion call encoded) ←
        try
          runtime.completed owner
        catch _ =>
          pure none
      let result ← match completed with
        | some completed => pure (decodeOwnedResult decode completed.val)
        | none => do
            let committed ← try runtime.cancelIfActive call catch _ => pure false
            let joined : Option (Ownership.Completion call encoded) ←
              try
                some <$> runtime.join owner
              catch _ =>
                pure none
            pure (resultAfterLocalCancellation committed .ownerCancelled decode joined)
      match result with
      | .error .cleanupUncertain => pure (.error .cleanupUncertain)
      | .error .actionFailed => pure (.error .actionFailed)
      | result =>
          match disarmFailure with
          | some error => throw error
          | none => pure result

namespace Lifecycle

namespace Owned

inductive Command (Handle : Type) where
  | disarm (deadline : ArmedDeadline)
  | spawn (call : Handle) (request : ByteArray)
  | cancel (call : Handle)
  | cancelIfActive (call : Handle)
  | finish (call : Handle)
  | race (call : Handle) (request : ByteArray)
      (owner : AsyncTask (Ownership.Completion call request))
      (deadline : ArmedDeadline) (cancellation : Option Cancellation)
  | completed (call : Handle) (request : ByteArray)
      (owner : AsyncTask (Ownership.Completion call request))
  | join (call : Handle) (request : ByteArray)
      (owner : AsyncTask (Ownership.Completion call request))

@[expose] def Command.Return : Command Handle → Type
  | .disarm _ | .cancel _ => Unit
  | .cancelIfActive _ => Bool
  | .spawn call request => AsyncTask (Ownership.Completion call request)
  | .finish _ => Except Grpc.Status
      (Grpc.Status × _root_.Http2.Headers × _root_.Http2.Headers)
  | .race call request _ _ _ => OwnerRace (Ownership.Completion call request)
  | .completed call request _ => Option (Ownership.Completion call request)
  | .join call request _ => Ownership.Completion call request

@[expose] def Outcome (command : Command Handle) : Type := Except IO.Error command.Return

abbrev Program (Handle α : Type) := Execution.Program (Command Handle) Outcome α
private abbrev M (Handle α : Type) := ExceptT IO.Error (Program Handle) α

private def perform (command : Command Handle) : M Handle command.Return :=
  ExceptT.mk (.call command .done)

private def runtime : OwnedRuntime (M Handle) Handle where
  disarm deadline := perform (.disarm deadline)
  spawn call request := perform (.spawn call request)
  cancel call := perform (.cancel call)
  cancelIfActive call := perform (.cancelIfActive call)
  finish call := perform (.finish call)
  race := fun {call} {request} owner deadline cancellation =>
    perform (.race call request owner deadline cancellation)
  completed := fun {call} {request} owner => perform (.completed call request owner)
  join := fun {call} {request} owner => perform (.join call request owner)

/-- Post-start execution has no start instruction. It owns the existing call
through task startup, selection, joining, timer cleanup, and caught exceptions. -/
def program (call : Handle) (request : ByteArray) (deadline : ArmedDeadline)
    (cancellation : Option Cancellation) (decode : ByteArray → Except δ Response) :
    Program Handle (Except IO.Error (Except Error Response)) :=
  (ownedInvocation runtime call request deadline cancellation decode).run

/-- Evidence names both the spawned task and the join of that same task. The
local origin comes from a normally returned atomic cancellation commit. -/
def CancelledAndJoined (call : Handle) (request : ByteArray)
    (trace : List (Execution.Event (Command Handle) Outcome)) : Prop :=
  ∃ owner completion,
    (⟨.spawn call request, .ok owner⟩ : Execution.Event (Command Handle) Outcome) ∈ trace ∧
    (⟨.cancelIfActive call, .ok true⟩ : Execution.Event (Command Handle) Outcome) ∈ trace ∧
    (⟨.join call request owner, .ok completion⟩ : Execution.Event (Command Handle) Outcome) ∈ trace ∧
    completion.val ≠ .error .cleanupUncertain

private theorem cancelledAndJoined_of_result
    {Handle : Type} {call : Handle} {request : ByteArray}
    {trace : List (Execution.Event (Command Handle) Outcome)}
    (owner : AsyncTask (Ownership.Completion call request))
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (requested observed : Error)
    (isLocal : observed = .ownerCancelled ∨ observed = .localDeadlineExceeded)
    (committed : Bool)
    (result : resultAfterLocalCancellation committed requested decode (some completion) =
      .error observed)
    (spawned : (⟨.spawn call request, .ok owner⟩ : Execution.Event (Command Handle) Outcome) ∈ trace)
    (cancelled : committed = true →
      (⟨.cancelIfActive call, .ok true⟩ : Execution.Event (Command Handle) Outcome) ∈ trace)
    (joined : (⟨.join call request owner, .ok completion⟩ : Execution.Event (Command Handle) Outcome) ∈ trace) :
    CancelledAndJoined call request trace :=
  ⟨owner, completion, spawned,
    cancelled (local_result_requires_commit completion decode requested observed isLocal committed result),
    joined, local_result_owner_certain completion decode requested observed isLocal committed result⟩

set_option maxHeartbeats 2000000 in
private theorem program_local_checked (call : Handle) (request : ByteArray)
    (deadline : ArmedDeadline) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (localError : Error)
    (isLocal : localError = .ownerCancelled ∨ localError = .localDeadlineExceeded) :
    (program call request deadline cancellation decode).TraceChecks
      (fun trace result => result = .ok (.error localError) →
        CancelledAndJoined call request trace) [] := by
  simp only [program, ownedInvocation, runtime, perform, ExceptT.run, ExceptT.mk,
    bind, ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, ExceptT.tryCatch, throw, throwThe, MonadExceptOf.throw,
    Execution.Program.bind]
  repeat' first
    | solve | simp_all [Execution.Program.TraceChecks, ExceptT.bindCont,
        Execution.Program.bind, CancelledAndJoined, pure, bind, Functor.map, ExceptT.map]
    | solve
      | intro impossible
        exact False.elim (decodeOwnedResult_not_local _ decode localError isLocal impossible)
    | solve | rcases isLocal with rfl | rfl <;> simp_all
    | intro outcome; cases outcome
    | split
    | simp_all [Execution.Program.TraceChecks, ExceptT.bindCont, Execution.Program.bind,
        pure, bind, Functor.map, ExceptT.map]
  all_goals
    intro returned
    apply cancelledAndJoined_of_result _ _ decode _ localError isLocal _ returned
    · exact List.Mem.head _
    · intro committed; simp_all
    · simp_all

/-- Once a call is admitted, an ordinary local cancellation/deadline result
requires an actual cancellation commit and a successful join of the exact
task spawned for that same call and encoded request. A thrown join cannot
produce this result. Terminal-result precedence is defined by that commit,
not by the selector wake order or peer-controlled status text. -/
theorem local_result_cancelled_and_joined
    {Handle Response δ : Type} {call : Handle} {request : ByteArray}
    {deadline : ArmedDeadline} {cancellation : Option Cancellation}
    {decode : ByteArray → Except δ Response} {localError : Error}
    {trace : List (Execution.Event (Command Handle) Outcome)}
    (isLocal : localError = .ownerCancelled ∨ localError = .localDeadlineExceeded)
    (executed : Execution.Executes (program call request deadline cancellation decode)
      trace (.ok (.error localError))) : CancelledAndJoined call request trace := by
  have checked := Execution.traceChecks_result
    (program_local_checked call request deadline cancellation decode localError isLocal) executed
  exact checked rfl

def OwnerReturned {call : Handle} {request : ByteArray}
    (owner : AsyncTask (Ownership.Completion call request))
    (deadline : ArmedDeadline) (cancellation : Option Cancellation)
    (completion : Ownership.Completion call request)
    (trace : List (Execution.Event (Command Handle) Outcome)) : Prop :=
  (⟨.race call request owner deadline cancellation, .ok (.completed completion)⟩ :
    Execution.Event (Command Handle) Outcome) ∈ trace ∨
  (⟨.completed call request owner, .ok (some completion)⟩ :
    Execution.Event (Command Handle) Outcome) ∈ trace ∨
  (⟨.join call request owner, .ok completion⟩ :
    Execution.Event (Command Handle) Outcome) ∈ trace

def SuccessfulOwner (call : Handle) (request : ByteArray) (deadline : ArmedDeadline)
    (cancellation : Option Cancellation) (decode : ByteArray → Except δ Response)
    (response : Response) (trace : List (Execution.Event (Command Handle) Outcome)) : Prop :=
  ∃ owner completion bytes,
    (⟨.spawn call request, .ok owner⟩ : Execution.Event (Command Handle) Outcome) ∈ trace ∧
    OwnerReturned owner deadline cancellation completion trace ∧
    completion.val = .ok bytes ∧ decode bytes = .ok response

private theorem successfulOwner_of_result
    {Handle : Type} {call : Handle} {request : ByteArray}
    {deadline : ArmedDeadline} {cancellation : Option Cancellation}
    {trace : List (Execution.Event (Command Handle) Outcome)}
    (owner : AsyncTask (Ownership.Completion call request))
    (completion : Ownership.Completion call request)
    (decode : ByteArray → Except δ Response) (response : Response)
    (success : decodeOwnedResult decode completion.val = .ok response)
    (spawned : (⟨.spawn call request, .ok owner⟩ : Execution.Event (Command Handle) Outcome) ∈ trace)
    (observed : OwnerReturned owner deadline cancellation completion trace) :
    SuccessfulOwner call request deadline cancellation decode response trace := by
  obtain ⟨bytes, owned, decoded⟩ := decodeOwnedResult_success completion decode success
  exact ⟨owner, completion, bytes, spawned, observed, owned, decoded⟩

set_option maxHeartbeats 2000000 in
private theorem program_success_checked (call : Handle) (request : ByteArray)
    (deadline : ArmedDeadline) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (response : Response) :
    (program call request deadline cancellation decode).TraceChecks
      (fun trace result => result = .ok (.ok response) →
        SuccessfulOwner call request deadline cancellation decode response trace) [] := by
  simp only [program, ownedInvocation, runtime, perform, ExceptT.run, ExceptT.mk,
    bind, ExceptT.bind, ExceptT.bindCont, pure, ExceptT.pure, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, ExceptT.tryCatch, throw, throwThe, MonadExceptOf.throw,
    Execution.Program.bind]
  repeat' first
    | solve | simp_all [Execution.Program.TraceChecks, ExceptT.bindCont,
        Execution.Program.bind, pure, bind, Functor.map, ExceptT.map]
    | intro outcome; cases outcome
    | split
    | simp_all [Execution.Program.TraceChecks, ExceptT.bindCont, Execution.Program.bind,
        pure, bind, Functor.map, ExceptT.map]
  all_goals
    intro returned
    try simp only [resultAfterLocalCancellation_success_iff] at returned
    apply successfulOwner_of_result _ _ decode response returned
    · exact List.Mem.head _
    · simp [OwnerReturned]

/-- A decoded success is the exact successful output of the task spawned for
this call/request. Its primitive certificate supplies one response, successful
terminal status, and terminal finish before decoding. -/
theorem success_has_exact_owner
    {Handle Response δ : Type} {call : Handle} {request : ByteArray}
    {deadline : ArmedDeadline} {cancellation : Option Cancellation}
    {decode : ByteArray → Except δ Response} {response : Response}
    {trace : List (Execution.Event (Command Handle) Outcome)}
    (executed : Execution.Executes (program call request deadline cancellation decode)
      trace (.ok (.ok response))) :
    SuccessfulOwner call request deadline cancellation decode response trace := by
  have checked := Execution.traceChecks_result
    (program_success_checked call request deadline cancellation decode response) executed
  exact checked rfl

@[expose] def Completion (call : Handle) (request : ByteArray) (deadline : ArmedDeadline)
    (cancellation : Option Cancellation) (decode : ByteArray → Except δ Response) :=
  { result : Except Error Response // ∃ trace,
    Execution.Executes (program call request deadline cancellation decode) trace (.ok result) }

private def invoke (primitives : Primitives Handle)
    (command : Command Handle) : Async (Outcome command) := do
  try
    match command with
    | .disarm deadline => pure (.ok (← deadline.disarm))
    | .spawn call request => pure (.ok (← async (ownUnaryCall primitives call request)))
    | .cancel call => pure (.ok (← primitives.cancel call))
    | .cancelIfActive call => pure (.ok (← primitives.cancelIfActive call))
    | .finish call => pure (.ok (← primitives.finish call))
    | .race _ _ owner deadline cancellation =>
        pure (.ok (← raceOwner owner deadline.selector cancellation))
    | .completed _ _ owner => pure (.ok (← finishedOwner? owner))
    | .join _ _ owner => pure (.ok (← await owner))
  catch error => pure (.error error)

private def run (primitives : Primitives Handle) (call : Handle) (request : ByteArray)
    (deadline : ArmedDeadline) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) :
    Async (Completion call request deadline cancellation decode) := do
  let completion ← (program call request deadline cancellation decode).interpret (invoke primitives)
  match completion with
  | ⟨.ok result, proof⟩ => pure ⟨result, proof⟩
  | ⟨.error error, _⟩ => throw error

end Owned

inductive Command (Handle : Type) where
  | isCancelled (cancellation : Cancellation)
  | permit
  | arm (milliseconds : Nat)
  | disarm (deadline : ArmedDeadline)
  | start (milliseconds : Nat)
  | settle (call : Handle) (request : ByteArray) (deadline : ArmedDeadline)

@[expose] def Command.Return (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) : Command Handle → Type
  | .isCancelled _ => Bool
  | .permit => Option Nat
  | .arm _ => ArmedDeadline
  | .disarm _ => Unit
  | .start _ => Except Grpc.Status Handle
  | .settle call request deadline => Owned.Completion call request deadline cancellation decode

@[expose] def Outcome (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (command : Command Handle) : Type :=
  Except IO.Error (command.Return cancellation decode)

abbrev Program (Handle : Type) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (α : Type) :=
  Execution.Program (Command Handle) (Outcome cancellation decode) α

private abbrev ResultProgram (Handle : Type) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) :=
  Program Handle cancellation decode (Except IO.Error (Except Error Response))

private def checkCancellation (cancellation : Option Cancellation)
    (onCancelled next : ResultProgram Handle cancellation decode) :
    ResultProgram Handle cancellation decode :=
  match cancellation with
  | none => next
  | some token => .call (.isCancelled token) fun
      | .error error => .done (.error error)
      | .ok true => onCancelled
      | .ok false => next

private def startProgram (Handle : Type) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (request : ByteArray)
    (milliseconds : Nat) (deadline : ArmedDeadline) : ResultProgram Handle cancellation decode :=
  .call (.start milliseconds) fun
    | .error error => .call (.disarm deadline) fun _ => .done (.error error)
    | .ok (.error status) => .call (.disarm deadline) fun
        | .error error => .done (.error error)
        | .ok () => .done (.ok (.error (.rpc status)))
    | .ok (.ok call) => .call (.settle call request deadline) fun
        | .error error => .done (.error error)
        | .ok completion => .done (.ok completion.val)

private def armProgram (Handle : Type) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (request : ByteArray)
    (milliseconds : Nat) : ResultProgram Handle cancellation decode :=
  .call (.arm milliseconds) fun
    | .error error => .done (.error error)
    | .ok deadline => checkCancellation cancellation
        (.call (.disarm deadline) fun
          | .error error => .done (.error error)
          | .ok () => .done (.ok (.error .ownerCancelled)))
        (startProgram Handle cancellation decode request milliseconds deadline)

private def claimProgram (Handle : Type) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (request : ByteArray) :
    ResultProgram Handle cancellation decode :=
  .call .permit fun
    | .error error => .done (.error error)
    | .ok none | .ok (some 0) => .done (.ok (.error .ownerCancelled))
    | .ok (some (milliseconds + 1)) =>
        armProgram Handle cancellation decode request (milliseconds + 1)

/-- Admission performs at most one transport start and then transfers that
exact call to the certified post-start program. -/
def program (Handle : Type) (cancellation : Option Cancellation)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response) (request : Request) :
    Program Handle cancellation decode (Except IO.Error (Except Error Response)) :=
  match encode request with
  | .error _ => checkCancellation cancellation
      (.done (.ok (.error .ownerCancelled))) (.done (.ok (.error .requestEncoding)))
  | .ok encoded => checkCancellation cancellation
      (.done (.ok (.error .ownerCancelled)))
      (claimProgram Handle cancellation decode encoded)

def Command.startCost : Command Handle → Nat
  | .start _ => 1
  | _ => 0

private theorem program_startBound (cancellation : Option Cancellation)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response) (request : Request) :
    (program Handle cancellation encode decode request).CostBound Command.startCost 1 := by
  cases cancellation <;>
    simp only [program, checkCancellation, claimProgram, armProgram, startProgram]
  repeat' first
    | solve | simp_all [Execution.Program.CostBound, Command.startCost]
    | intro outcome; cases outcome
    | split
    | constructor
    | simp_all [Execution.Program.CostBound, Command.startCost]

/-- Every completed admission trace invokes the supplied transport starter at
most once. The post-start instruction set has no start operation. -/
theorem starts_at_most_once
    {Handle Request Response ε δ : Type} {cancellation : Option Cancellation}
    {encode : Request → Except ε ByteArray} {decode : ByteArray → Except δ Response}
    {request : Request}
    {trace : List (Execution.Event (Command Handle) (Outcome cancellation decode))}
    {result : Except IO.Error (Except Error Response)}
    (executed : Execution.Executes
      (program Handle cancellation encode decode request) trace result) :
    (trace.map fun event => event.command.startCost).sum ≤ 1 :=
  Execution.costBound_trace (program_startBound cancellation encode decode request) executed

/-- The same no-replay bound holds before completion, including invocations
whose primitive or owner task never returns. -/
theorem starts_at_most_once_prefix
    {Handle Request Response ε δ : Type} {cancellation : Option Cancellation}
    {encode : Request → Except ε ByteArray} {decode : ByteArray → Except δ Response}
    {request : Request}
    {before : List (Execution.Event (Command Handle) (Outcome cancellation decode))}
    {command : Command Handle}
    (invoked : Execution.Invokes
      (program Handle cancellation encode decode request) before command) :
    (before.map fun event => event.command.startCost).sum + command.startCost ≤ 1 :=
  Execution.costBound_invokes (program_startBound cancellation encode decode request) invoked

/-- An admitted ordinary return retains the post-start certificate for the
same handle returned by the actual start instruction. -/
def AdmittedReturn (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response)
    (trace : List (Execution.Event (Command Handle) (Outcome cancellation decode)))
    (result : Except Error Response) : Prop :=
  ∀ milliseconds (call : Handle),
    (⟨.start milliseconds, .ok (.ok call)⟩ :
      Execution.Event (Command Handle) (Outcome cancellation decode)) ∈ trace →
    ∃ bytes deadline, ∃ (completion : Owned.Completion call bytes deadline cancellation decode),
      (⟨.settle call bytes deadline, .ok completion⟩ :
        Execution.Event (Command Handle) (Outcome cancellation decode)) ∈ trace ∧
      result = completion.val

set_option maxHeartbeats 2000000 in
private theorem program_admittedReturn (cancellation : Option Cancellation)
    (encode : Request → Except ε ByteArray) (decode : ByteArray → Except δ Response)
    (request : Request) :
    (program Handle cancellation encode decode request).TraceChecks
      (fun trace result => ∀ value, result = .ok value → AdmittedReturn cancellation decode trace value)
      [] := by
  cases cancellation <;>
    simp only [program, checkCancellation, claimProgram, armProgram, startProgram]
  repeat' first
    | solve | simp_all [Execution.Program.TraceChecks, AdmittedReturn, heq_eq_eq]
    | apply Execution.traceChecks_call; intro outcome; cases outcome
    | split
    | simp_all [Execution.Program.TraceChecks]

  all_goals simp_all [AdmittedReturn, heq_eq_eq]
  all_goals
    intro milliseconds call sameMilliseconds returned
    have same := eq_of_heq returned
    cases same <;>
      exact ⟨_, _, _, ⟨⟨rfl, rfl, rfl⟩, .rfl⟩, rfl⟩

theorem admitted_return_has_exact_completion
    {Handle Request Response ε δ : Type} {cancellation : Option Cancellation}
    {encode : Request → Except ε ByteArray} {decode : ByteArray → Except δ Response}
    {request : Request} {result : Except Error Response}
    {trace : List (Execution.Event (Command Handle) (Outcome cancellation decode))}
    (executed : Execution.Executes (program Handle cancellation encode decode request)
      trace (.ok result)) : AdmittedReturn cancellation decode trace result := by
  have checked := Execution.traceChecks_result
    (program_admittedReturn cancellation encode decode request) executed
  exact checked result rfl

private def invoke (deadlineDriver : DeadlineDriver) (cancellation : Option Cancellation)
    (decode : ByteArray → Except δ Response) (permit : Async (Option Nat))
    (start : Nat → Async (Except Grpc.Status Handle)) (primitives : Primitives Handle)
    (command : Command Handle) : Async (Outcome cancellation decode command) := do
  try
    match command with
    | .isCancelled token => pure (.ok (← token.isCancelled))
    | .permit => pure (.ok (← permit))
    | .arm milliseconds => pure (.ok (← deadlineDriver.arm milliseconds))
    | .disarm deadline => pure (.ok (← deadline.disarm))
    | .start milliseconds => pure (.ok (← start milliseconds))
    | .settle call request deadline =>
        pure (.ok (← Owned.run primitives call request deadline cancellation decode))
  catch error => pure (.error error)

end Lifecycle

/-- Execute the certified invocation program with the production asynchronous
operations. The evidence is erased; public results and exceptions are retained. -/
def unaryWithCancellationAndPermit
    (deadlineDriver : DeadlineDriver) (cancellation : Option Cancellation)
    (permit : Async (Option Nat)) (start : Nat → Async (Except Grpc.Status Handle))
    (primitives : Primitives Handle) (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response) (request : Request) :
    Async (Except Error Response) := do
  let completion ← (Lifecycle.program Handle cancellation encode decode request).interpret
    (Lifecycle.invoke deadlineDriver cancellation decode permit start primitives)
  match completion.val with
  | .ok result => pure result
  | .error error => throw error

/--
Transport-injected unary lifecycle used by deterministic tests.  Its permit
admits the original relative deadline immediately after request encoding.
Production shared channels use `unaryCancellableWithPermit` below so lazy
setup and encoding consume the same outer absolute budget.
-/
def unaryWithCancellation
    (deadline : RpcDeadline)
    (deadlineDriver : DeadlineDriver)
    (cancellation : Option Cancellation)
    (start : Async (Except Grpc.Status Handle))
    (primitives : Primitives Handle)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    Async (Except Error Response) :=
  unaryWithCancellationAndPermit deadlineDriver cancellation
    (pure (some (deadlineMilliseconds deadline))) (fun _ => start)
    primitives encode decode request

/--
Transport-injected unary lifecycle without an external cancellation signal.
Kept as the stable deterministic-test seam.
-/
def unaryWith
    (deadline : RpcDeadline)
    (deadlineDriver : DeadlineDriver)
    (start : Async (Except Grpc.Status Handle))
    (primitives : Primitives Handle)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    Async (Except Error Response) :=
  unaryWithCancellation deadline deadlineDriver none
    start primitives encode decode request

/--
Run one generated unary method with fresh per-call credential metadata and a
locally enforced relative deadline.
-/
def unaryCancellable
    (connection : Grpc.Client.Connection)
    (configuration : ManagedChannel.Config)
    (cancellation : Option Cancellation)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    Async (Except Error Response) :=
  unaryWithCancellation configuration.deadline systemDeadlineDriver cancellation
    (do
      let options ←
        callOptions configuration configuration.deadline.grpcTimeoutValue
      Grpc.Client.start connection method.path options)
    grpcPrimitives encode decode request

private def grpcTimeoutValueForMilliseconds (milliseconds : Nat) : String :=
  if milliseconds % 1000 == 0 then
    toString (milliseconds / 1000) ++ "S"
  else if milliseconds ≤ 99_999_999 then
    toString milliseconds ++ "m"
  else
    -- The gRPC timeout grammar permits at most eight digits.  Flooring to
    -- seconds keeps peer enforcement inside, never beyond, the local budget.
    toString (milliseconds / 1000) ++ "S"

/--
Run one generated unary method after an absolute outer owner atomically admits
its transport start.  The permit's remaining milliseconds drive both the
exact-call timer and the `grpc-timeout` header, so setup never restarts a full
relative peer budget.
-/
def unaryCancellableWithPermit
    (connection : Grpc.Client.Connection)
    (configuration : ManagedChannel.Config)
    (cancellation : Cancellation)
    (permit : Async (Option Nat))
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    Async (Except Error Response) :=
  unaryWithCancellationAndPermit systemDeadlineDriver (some cancellation)
    permit
    (fun remainingMilliseconds => do
      let options ← callOptions configuration
        (grpcTimeoutValueForMilliseconds remainingMilliseconds)
      Grpc.Client.start connection method.path options)
    grpcPrimitives encode decode request

def unary
    (connection : Grpc.Client.Connection)
    (configuration : ManagedChannel.Config)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    Async (Except Error Response) :=
  unaryCancellable connection configuration none method encode decode request

end Grpc.UnaryCall
