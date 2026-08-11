module

public import Grpc.Client
public import Grpc.CallCredentials
public import Grpc.Cancellation
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
the timer wins, the same call is cancelled and its owner is joined before the
deadline error is returned.  This makes returning from `unary` a cleanup
acknowledgement suitable for releasing a shared channel-owner lease.
-/

namespace Grpc.UnaryCall

open Std.Async

/--
Construct call metadata from refined credential entries.  The produced
`CallOptions` value renders headers ordinarily, so callers hold it only at the
call boundary; the theorems below let downstream code reason about header
presence without ever rendering a value.
-/
@[expose] def optionsFor
    (entries : Array CredentialEntry)
    (timeout : String) :
    Grpc.Client.CallOptions := {
  metadata := entries.map fun entry =>
    Grpc.Header.of entry.name entry.exposeValue
  timeout := some timeout
}

theorem optionsFor_timeout
    (entries : Array CredentialEntry) (timeout : String) :
    (optionsFor entries timeout).timeout = some timeout := by
  rfl

/-- Exactly the refined credential entries become call metadata headers. -/
theorem optionsFor_metadata
    (entries : Array CredentialEntry) (timeout : String) :
    (optionsFor entries timeout).metadata =
      entries.map (fun entry =>
        Grpc.Header.of entry.name entry.exposeValue) := by
  rfl

/--
A single refined entry is visible in the built call metadata under its own
name with its exact plaintext value.  This is the exported header-presence
fact: a caller can prove its credential entry was installed without unfolding
this module's internals.
-/
theorem optionsFor_singleton_get?
    (entry : CredentialEntry) (timeout : String) :
    ((optionsFor #[entry] timeout).metadata.get? entry.name) =
      some entry.exposeValue := by
  simp [optionsFor, Grpc.Metadata.get?, Grpc.Metadata.getAll, Grpc.Header.of]

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
  /-- The supplied local owner cancellation won after the exact call was joined. -/
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
      Async (Except Grpc.Status (Grpc.Status × Grpc.Metadata × Grpc.Metadata))
  cancel : Handle → Async Unit

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

private def cardinalityStatus (count : String) : Grpc.Status :=
  Grpc.Status.internal s!"expected exactly one response message, got {count}"

/--
Exact status installed by the pinned grpc-lean `Call.cancel` linearization when
the call was still active.  A different status observed after `cancel` was
already terminal peer/transport evidence and must not be rewritten as local
deadline or owner-cancellation provenance.
-/
private def locallyCancelledStatus : Grpc.Status :=
  Grpc.Status.cancelled "call cancelled locally"

/--
Decode the standard rich-status trailer.  Multiple values are ambiguous and
therefore fail closed instead of making retry policy depend on header order.
Malformed binary metadata is likewise not exposed as typed status evidence.
-/
private def statusDetailsFromTrailers
    (trailers : Grpc.Metadata) : Option ByteArray :=
  match trailers.getBinaryAll "grpc-status-details-bin" with
  | .ok values =>
      if values.size == 1 then values[0]? else none
  | .error _ => none

private def rpcErrorFromTerminal
    (status : Grpc.Status)
    (trailers : Grpc.Metadata) : Error :=
  .rpc status (statusDetailsFromTrailers trailers)

/--
Recover details after an earlier call action returned a status only when the
terminal status agrees.  This preserves the earlier status without attaching
details that may describe a different failure.
-/
private def rpcErrorAfterFinish
    (status : Grpc.Status)
    (finishResult :
      Except Grpc.Status (Grpc.Status × Grpc.Metadata × Grpc.Metadata)) :
    Error :=
  match finishResult with
  | .ok (terminalStatus, _, trailers) =>
      if terminalStatus == status then
        rpcErrorFromTerminal status trailers
      else
        .rpc status
  | .error _ => .rpc status

private def cancelAndFinish
    (primitives : Primitives Handle)
    (call : Handle) : Async Unit := do
  primitives.cancel call
  discard <| primitives.finish call

private def failAfterCancel
    (primitives : Primitives Handle)
    (call : Handle)
    (status : Grpc.Status) : Async (Except Error ByteArray) := do
  primitives.cancel call
  let finishResult ← primitives.finish call
  pure (.error (rpcErrorAfterFinish status finishResult))

private def failAfterTerminal
    (primitives : Primitives Handle)
    (call : Handle)
    (status : Grpc.Status) : Async (Except Error ByteArray) := do
  let finishResult ← primitives.finish call
  pure (.error (rpcErrorAfterFinish status finishResult))

private def settleNoResponse
    (primitives : Primitives Handle)
    (call : Handle) : Async (Except Error ByteArray) := do
  match ← primitives.finish call with
  | .error status => pure (.error (.rpc status))
  | .ok (status, _, trailers) =>
      if status.isOk then
        pure (.error (.rpc (cardinalityStatus "0")))
      else
        pure (.error (rpcErrorFromTerminal status trailers))

private def settleOneResponse
    (primitives : Primitives Handle)
    (call : Handle)
    (response : ByteArray) : Async (Except Error ByteArray) := do
  match ← primitives.finish call with
  | .error status => pure (.error (.rpc status))
  | .ok (status, _, trailers) =>
      if status.isOk then
        pure (.ok response)
      else
        pure (.error (rpcErrorFromTerminal status trailers))

private def settleMultipleResponses
    (primitives : Primitives Handle)
    (call : Handle) : Async (Except Error ByteArray) := do
  primitives.cancel call
  match ← primitives.finish call with
  | .ok (status, _, trailers) =>
      if status.isOk then
        pure (.error (.rpc (cardinalityStatus "at least 2")))
      else
        pure (.error (rpcErrorFromTerminal status trailers))
  | .error _ =>
      -- Cancellation makes this the usual production branch.  The semantic
      -- error remains the unary response-cardinality violation.
      pure (.error (.rpc (cardinalityStatus "at least 2")))

/--
Own one exact call through send, half-close, receive, and terminal cleanup.
No branch returns while the call can still be registered with its connection.
-/
private def ownUnaryCall
    (primitives : Primitives Handle)
    (call : Handle)
    (request : ByteArray) : Async (Except Error ByteArray) := do
  try
    match ← primitives.send call request with
    | .error status => failAfterCancel primitives call status
    | .ok () =>
        match ← primitives.closeSend call with
        | .error status => failAfterTerminal primitives call status
        | .ok () =>
            match ← primitives.recv? call with
            | .error status => failAfterTerminal primitives call status
            | .ok none => settleNoResponse primitives call
            | .ok (some response) =>
                match ← primitives.recv? call with
                | .error status => failAfterTerminal primitives call status
                | .ok none => settleOneResponse primitives call response
                | .ok (some _) => settleMultipleResponses primitives call
  catch _ =>
    -- Preserve the ownership rule even if an injected primitive raises an IO
    -- error rather than returning a gRPC status.  An exception from cleanup
    -- is a distinct containment result; it must poison the shared connection.
    try
      cancelAndFinish primitives call
      pure (.error .actionFailed)
    catch _ =>
      pure (.error .cleanupUncertain)

private inductive OwnerRace (α : Type) where
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

/--
Classify the exact owner result after this adapter requested local
cancellation.  grpc-lean installs only `locallyCancelledStatus`; every other
terminal result predates (or won) that cancellation linearization and retains
its original provenance.
-/
private def resultAfterLocalCancellation
    (localResult : Error)
    (decode : ByteArray → Except δ Response) :
    Option (Except Error ByteArray) → Except Error Response
  | none => .error .cleanupUncertain
  | some (.error (.rpc status statusDetails)) =>
      if status == locallyCancelledStatus && statusDetails.isNone then
        .error localResult
      else
        .error (.rpc status statusDetails)
  | some result => decodeOwnedResult decode result

/--
Transport-injected unary lifecycle with a call-start permit.

Encoding happens before the permit is claimed.  The permit is therefore the
linearization point at which an absolute outer invocation owner authorizes a
transport call, and it returns the exact remaining local budget.  Returning
`none` proves that cancellation or expiry won before transport admission.
The injected start action deliberately captures no public call options.
-/
def unaryWithCancellationAndPermit
    (deadlineDriver : DeadlineDriver)
    (cancellation : Option Cancellation)
    (permit : Async (Option Nat))
    (start : Nat → Async (Except Grpc.Status Handle))
    (primitives : Primitives Handle)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    Async (Except Error Response) := do
  let encoded ← match encode request with
    | .ok encoded => pure encoded
    | .error _ =>
        match cancellation with
        | some cancellation =>
            if ← cancellation.isCancelled then
              return .error .ownerCancelled
        | none => pure ()
        return .error .requestEncoding

  -- Avoid claiming transport admission for a signal already known terminal.
  -- The permit performs the authoritative atomic check immediately below.
  match cancellation with
  | some cancellation =>
      if ← cancellation.isCancelled then
        return .error .ownerCancelled
  | none => pure ()
  let some remainingMilliseconds ← permit
    | return .error .ownerCancelled
  if remainingMilliseconds == 0 then
    return .error .ownerCancelled

  -- The absolute outer owner has already charged encoding and setup.  This
  -- exact-call timer owns only the remaining interval returned by the permit.
  let armedDeadline ← deadlineDriver.arm remainingMilliseconds
  -- For the standalone relative-deadline adapter, this final active-state
  -- read is the cooperative start-admission linearization: cancellation that
  -- follows it is concurrent and will cancel/join the admitted call. Shared
  -- channels additionally linearize their owner token with the absolute gate
  -- before this inner signal is checked.
  match cancellation with
  | some cancellation =>
      if ← cancellation.isCancelled then
        armedDeadline.disarm
        return .error .ownerCancelled
  | none => pure ()
  let startResult ←
    try
      start remainingMilliseconds
    catch error =>
      try
        armedDeadline.disarm
      catch _ =>
        pure ()
      throw error
  let call ← match startResult with
    | .ok call => pure call
    | .error status =>
        armedDeadline.disarm
        return .error (.rpc status)

  let scheduled : Except Error (AsyncTask (Except Error ByteArray)) ←
    try
      pure (Except.ok (← async (ownUnaryCall primitives call encoded)) :
        Except Error (AsyncTask (Except Error ByteArray)))
    catch _ =>
      try
        cancelAndFinish primitives call
        pure (Except.error .actionFailed :
          Except Error (AsyncTask (Except Error ByteArray)))
      catch _ =>
        pure (Except.error .cleanupUncertain :
          Except Error (AsyncTask (Except Error ByteArray)))
  let owner ← match scheduled with
    | .ok owner => pure owner
    | .error cleanup =>
        let disarmFailed ←
          try
            armedDeadline.disarm
            pure false
          catch _ =>
            pure true
        if cleanup == .cleanupUncertain then
          return .error .cleanupUncertain
        else if disarmFailed then
          throw (IO.userError "RPC deadline cleanup failed")
        else
          return .error cleanup
  let raced : Except Error (OwnerRace (Except Error ByteArray)) ←
    try
      pure (Except.ok
        (← raceOwner owner armedDeadline.selector cancellation) :
        Except Error (OwnerRace (Except Error ByteArray)))
    catch error =>
      let disarmFailure : Option IO.Error ←
        try
          armedDeadline.disarm
          pure none
        catch disarmError =>
          pure (some disarmError)
      -- A selector/registration failure is outside the call owner. Cancel and
      -- join that exact owner before propagating it across the channel lease.
      try
        primitives.cancel call
      catch _ =>
        pure ()
      let joined : Option (Except Error ByteArray) ←
        try
          some <$> await owner
        catch _ =>
          pure none
      match joined with
      | none | some (.error .cleanupUncertain) =>
          pure (Except.error .cleanupUncertain :
            Except Error (OwnerRace (Except Error ByteArray)))
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
      armedDeadline.disarm
      pure (decodeOwnedResult decode result)
  | .expired =>
      -- Preserve a timer cleanup failure, but never let it skip exact-call
      -- cancellation and the owner join below.
      let disarmFailure : Option IO.Error ←
        try
          armedDeadline.disarm
          pure none
        catch error =>
          pure (some error)
      -- Fair selection may choose the deadline even when the exact owner has
      -- concurrently become terminal. Preserve that completed result before
      -- requesting cancellation; it is stronger evidence than selector order.
      let completed : Option (Except Error ByteArray) ←
        try
          finishedOwner? owner
        catch _ =>
          pure none
      let result ← match completed with
        | some completed => pure (decodeOwnedResult decode completed)
        | none => do
            -- Cancel the exact call and join its owner. `ownUnaryCall` cannot
            -- finish before `Call.finish`, so this await is the cleanup
            -- acknowledgement.
            try
              primitives.cancel call
            catch _ =>
              pure ()
            let joined : Option (Except Error ByteArray) ←
              try
                some <$> await owner
              catch _ =>
                pure none
            pure (resultAfterLocalCancellation
              .localDeadlineExceeded decode joined)
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
          armedDeadline.disarm
          pure none
        catch error =>
          pure (some error)
      let completed : Option (Except Error ByteArray) ←
        try
          finishedOwner? owner
        catch _ =>
          pure none
      let result ← match completed with
        | some completed => pure (decodeOwnedResult decode completed)
        | none => do
            try
              primitives.cancel call
            catch _ =>
              pure ()
            let joined : Option (Except Error ByteArray) ←
              try
                some <$> await owner
              catch _ =>
                pure none
            pure (resultAfterLocalCancellation .ownerCancelled decode joined)
      match result with
      | .error .cleanupUncertain => pure (.error .cleanupUncertain)
      | .error .actionFailed => pure (.error .actionFailed)
      | result =>
          match disarmFailure with
          | some error => throw error
          | none => pure result

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
