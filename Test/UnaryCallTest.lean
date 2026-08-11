import Grpc

namespace UnaryCallTest

open Std.Async
open Grpc
open Grpc.UnaryCall

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do fail message

private def record
    (events : IO.Ref (Array String)) (event : String) : IO Unit :=
  events.modify (·.push event)

private def credentialEntry : IO CredentialEntry := do
  let some entry :=
      CredentialEntry.of? "authorization" "Bearer production-api-key"
    | fail "test credential entry was rejected"
  pure entry

private def configuration :
    IO Grpc.ManagedChannel.Config := do
  let endpoint ← match Endpoint.parse "https://api.example.test" with
    | .ok endpoint => pure endpoint
    | .error error => fail s!"test endpoint was rejected: {repr error}"
  pure {
    endpoint
    credentials := .ofEntries #[← credentialEntry]
    deadline := .default
  }

private def neverSelector : Selector Unit where
  tryFn := pure none
  registerFn := fun _ => pure ()
  unregisterFn := pure ()

private def neverDeadline : DeadlineDriver where
  arm := fun _ => pure {
    selector := neverSelector
    disarm := pure ()
  }

private def promiseSelector (signal : IO.Promise Unit) : Selector Unit where
  tryFn := do
    if ← signal.isResolved then
      discard <| await signal
      pure (some ())
    else
      pure none
  registerFn := fun waiter => do
    BaseIO.chainTask signal.result? fun
      | none => pure ()
      | some () =>
          waiter.race (pure ()) fun promise =>
            promise.resolve (.ok ())
  unregisterFn := pure ()

private def encodeString (value : String) : Except Unit ByteArray :=
  .ok value.toUTF8

private def decodeString (bytes : ByteArray) : Except Unit String :=
  match String.fromUTF8? bytes with
  | some value => .ok value
  | none => .error ()

private structure ScriptedCall where
  events : IO.Ref (Array String)
  sent : IO.Ref (Option ByteArray)
  responses : IO.Ref (List ByteArray)
  finishResult :
    Except Grpc.Status (Grpc.Status × Grpc.Metadata × Grpc.Metadata)

private def scriptedPrimitives : Primitives ScriptedCall where
  send := fun call message => do
    record call.events "send"
    call.sent.set (some message)
    pure (.ok ())
  closeSend := fun call => do
    record call.events "closeSend"
    pure (.ok ())
  recv? := fun call => do
    record call.events "recv"
    match ← call.responses.get with
    | [] => pure (.ok none)
    | response :: rest =>
        call.responses.set rest
        pure (.ok (some response))
  finish := fun call => do
    record call.events "finish"
    pure call.finishResult
  cancel := fun call =>
    record call.events "cancel"

private def scriptedCall
    (events : IO.Ref (Array String))
    (responses : List ByteArray)
    (finishResult : Except Grpc.Status Grpc.Status := .ok Grpc.Status.ok)
    (trailers : Grpc.Metadata := Grpc.Metadata.empty) :
    IO ScriptedCall := do
  let finishResult := match finishResult with
    | .ok status => .ok (status, Grpc.Metadata.empty, trailers)
    | .error status => .error status
  pure {
    events
    sent := ← IO.mkRef none
    responses := ← IO.mkRef responses
    finishResult
  }

private def runScripted
    (call : ScriptedCall)
    (deadlineDriver : DeadlineDriver := neverDeadline)
    (encode : String → Except Unit ByteArray := encodeString)
    (decode : ByteArray → Except Unit String := decodeString) :
    IO (Except Error String) :=
  Async.block <| unaryWith RpcDeadline.default deadlineDriver
    (pure (.ok call)) scriptedPrimitives encode decode "request"

private def testCompletedBeforeTimeout : IO Unit := do
  let events ← IO.mkRef #[]
  let disarmed ← IO.mkRef false
  let deadlineDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := neverSelector
      disarm := disarmed.set true
    }
  }
  let call ← scriptedCall events ["response".toUTF8]
  match ← runScripted call deadlineDriver with
  | .ok "response" => pure ()
  | result => fail s!"completed unary call returned {repr result}"
  record events "returned"
  expect (← disarmed.get)
    "completed call retained its armed deadline"
  expect ((← call.sent.get) == some "request".toUTF8)
    "unary call did not send exactly the encoded request"
  expect ((← events.get) ==
    #["send", "closeSend", "recv", "recv", "finish", "returned"])
    "completed call did not finish before returning"

private def testEncodingAndDecodingErrors : IO Unit := do
  let encodingEvents ← IO.mkRef #[]
  let encodingCall ← scriptedCall encodingEvents ["unused".toUTF8]
  match ← runScripted encodingCall (encode := fun _ => .error ()) with
  | .error .requestEncoding => pure ()
  | result => fail s!"request codec failure returned {repr result}"
  expect (← encodingEvents.get).isEmpty
    "request codec failure started a transport call"

  let decodingEvents ← IO.mkRef #[]
  let decodingCall ← scriptedCall decodingEvents [ByteArray.empty.push 0xff]
  match ← runScripted decodingCall with
  | .error .responseDecoding => pure ()
  | result => fail s!"response codec failure returned {repr result}"
  expect ((← decodingEvents.get).back? == some "finish")
    "response was decoded before terminal cleanup"

private def testStatusAndCardinality : IO Unit := do
  let denied := Grpc.Status.error .unauthenticated "denied"
  let statusEvents ← IO.mkRef #[]
  let statusCall ← scriptedCall statusEvents ["ignored".toUTF8] (.ok denied)
  match ← runScripted statusCall with
  | .error (.rpc status _) =>
      expect (status == denied) "server status was not preserved"
  | result => fail s!"non-OK server status returned {repr result}"

  for peerStatus in #[
      Grpc.Status.error .cancelled "peer cancelled",
      Grpc.Status.error .deadlineExceeded "peer deadline exceeded"] do
    let peerEvents ← IO.mkRef #[]
    let peerCall ← scriptedCall peerEvents ["ignored".toUTF8] (.ok peerStatus)
    match ← runScripted peerCall with
    | .error (.rpc status _) =>
        expect (status == peerStatus)
          "peer cancellation/deadline provenance was changed"
    | result =>
        fail s!"peer cancellation/deadline returned {repr result}"

  let emptyEvents ← IO.mkRef #[]
  let emptyCall ← scriptedCall emptyEvents []
  match ← runScripted emptyCall with
  | .error (.rpc status _) =>
      expect (status.code == .internal)
        "zero-response unary call was not rejected as INTERNAL"
  | result => fail s!"zero-response unary call returned {repr result}"

  let multipleEvents ← IO.mkRef #[]
  let multipleCall ← scriptedCall multipleEvents ["one".toUTF8, "two".toUTF8]
  match ← runScripted multipleCall with
  | .error (.rpc status _) =>
      expect (status.code == .internal)
        "multi-response unary call was not rejected as INTERNAL"
  | result => fail s!"multi-response unary call returned {repr result}"
  expect ((← multipleEvents.get).back? == some "finish")
    "multi-response rejection did not finish the call"
  expect ((← multipleEvents.get).contains "cancel")
    "multi-response rejection did not cancel the open stream"

private def testStatusDetailsTrailers : IO Unit := do
  let denied := Grpc.Status.error .invalidArgument "invalid request"

  -- `insertBinary` exercises grpc-lean's normal unpadded `-bin` encoding.
  let unpaddedDetails := "unpadded-rich-status".toUTF8
  let unpaddedTrailers := Grpc.Metadata.empty.insertBinary
    "grpc-status-details-bin" unpaddedDetails
  let unpaddedEvents ← IO.mkRef #[]
  let unpaddedCall ← scriptedCall unpaddedEvents ["ignored".toUTF8]
    (.ok denied) unpaddedTrailers
  match ← runScripted unpaddedCall with
  | .error (.rpc status (some details)) =>
      expect (status == denied && details == unpaddedDetails)
        "unpadded grpc-status-details-bin was not decoded exactly"
  | result => fail s!"unpadded status details returned {repr result}"

  let noResponseEvents ← IO.mkRef #[]
  let noResponseCall ← scriptedCall noResponseEvents []
    (.ok denied) unpaddedTrailers
  match ← runScripted noResponseCall with
  | .error (.rpc status (some details)) =>
      expect (status == denied && details == unpaddedDetails)
        "status details were lost on the no-response terminal path"
  | result => fail s!"no-response status details returned {repr result}"

  let multipleEvents ← IO.mkRef #[]
  let multipleCall ← scriptedCall multipleEvents
    ["one".toUTF8, "two".toUTF8] (.ok denied) unpaddedTrailers
  match ← runScripted multipleCall with
  | .error (.rpc status (some details)) =>
      expect (status == denied && details == unpaddedDetails)
        "status details were lost after multi-response cancellation"
  | result => fail s!"multi-response status details returned {repr result}"

  let syntheticEvents ← IO.mkRef #[]
  let syntheticCall ← scriptedCall syntheticEvents []
    (.ok Grpc.Status.ok) unpaddedTrailers
  match ← runScripted syntheticCall with
  | .error (.rpc status none) =>
      expect (status.code == .internal)
        "synthetic cardinality failure changed classification"
  | result =>
      fail s!"synthetic cardinality failure retained peer details: {repr result}"

  -- Peers may send the standard padded base64 spelling as well.
  let paddedDetails := ByteArray.empty.push 1 |>.push 2
  let paddedTrailers := Grpc.Metadata.empty.insert
    "grpc-status-details-bin" "AQI="
  let paddedEvents ← IO.mkRef #[]
  let paddedCall ← scriptedCall paddedEvents ["ignored".toUTF8]
    (.ok denied) paddedTrailers
  match ← runScripted paddedCall with
  | .error (.rpc status (some details)) =>
      expect (status == denied && details == paddedDetails)
        "padded grpc-status-details-bin was not decoded exactly"
  | result => fail s!"padded status details returned {repr result}"

  let duplicateTrailers := Grpc.Metadata.empty
    |>.insertBinary "grpc-status-details-bin" "first-details".toUTF8
    |>.insertBinary "grpc-status-details-bin" "second-details".toUTF8
  let duplicateEvents ← IO.mkRef #[]
  let duplicateCall ← scriptedCall duplicateEvents ["ignored".toUTF8]
    (.ok denied) duplicateTrailers
  match ← runScripted duplicateCall with
  | .error (.rpc status none) =>
      expect (status == denied)
        "duplicate status-details rejection changed the terminal status"
  | result =>
      fail s!"duplicate grpc-status-details-bin did not fail closed: {repr result}"

  let malformedTrailers := Grpc.Metadata.empty.insert
    "grpc-status-details-bin" "not%%%base64"
  let malformedEvents ← IO.mkRef #[]
  let malformedCall ← scriptedCall malformedEvents ["ignored".toUTF8]
    (.ok denied) malformedTrailers
  match ← runScripted malformedCall with
  | .error (.rpc status none) =>
      expect (status == denied)
        "malformed status-details rejection changed the terminal status"
  | result =>
      fail s!"malformed grpc-status-details-bin did not fail closed: {repr result}"

private def testFastActionErrorsRecoverStatusDetails : IO Unit := do
  let actionStatus := Grpc.Status.error .failedPrecondition "rejected early"
  let details := "fast-action-status-details".toUTF8
  let trailers := Grpc.Metadata.empty.insertBinary
    "grpc-status-details-bin" details

  let sendEvents ← IO.mkRef #[]
  let sendCall ← scriptedCall sendEvents [] (.ok actionStatus) trailers
  let sendPrimitives : Primitives ScriptedCall := {
    scriptedPrimitives with
    send := fun call _ => do
      record call.events "send"
      pure (.error actionStatus)
  }
  let sendResult ← Async.block <| unaryWith RpcDeadline.default neverDeadline
    (pure (.ok sendCall)) sendPrimitives encodeString decodeString "request"
  match sendResult with
  | .error (.rpc status (some observed)) =>
      expect (status == actionStatus && observed == details)
        "fast send error did not recover matching terminal status details"
  | result => fail s!"fast send error returned {repr result}"
  expect ((← sendEvents.get) == #["send", "cancel", "finish"])
    "fast send error did not cancel and finish exactly once"

  let closeEvents ← IO.mkRef #[]
  let closeCall ← scriptedCall closeEvents [] (.ok actionStatus) trailers
  let closePrimitives : Primitives ScriptedCall := {
    scriptedPrimitives with
    closeSend := fun call => do
      record call.events "closeSend"
      pure (.error actionStatus)
  }
  let closeResult ← Async.block <| unaryWith RpcDeadline.default neverDeadline
    (pure (.ok closeCall)) closePrimitives encodeString decodeString "request"
  match closeResult with
  | .error (.rpc status (some observed)) =>
      expect (status == actionStatus && observed == details)
        "fast close-send error did not recover matching terminal status details"
  | result => fail s!"fast close-send error returned {repr result}"
  expect ((← closeEvents.get) == #["send", "closeSend", "finish"])
    "fast close-send error did not finish exactly once"

  let mismatchedStatus := Grpc.Status.error .unavailable "different terminal"
  let mismatchEvents ← IO.mkRef #[]
  let mismatchCall ← scriptedCall mismatchEvents []
    (.ok mismatchedStatus) trailers
  let mismatchPrimitives : Primitives ScriptedCall := {
    scriptedPrimitives with
    closeSend := fun call => do
      record call.events "closeSend"
      pure (.error actionStatus)
  }
  let mismatchResult ← Async.block <| unaryWith RpcDeadline.default neverDeadline
    (pure (.ok mismatchCall)) mismatchPrimitives encodeString decodeString "request"
  match mismatchResult with
  | .error (.rpc status none) =>
      expect (status == actionStatus)
        "terminal mismatch replaced the original call-action status"
  | result =>
      fail s!"mismatched terminal status attached unrelated details: {repr result}"

private def testErrorRenderingRedactsPeerEvidence : IO Unit := do
  let error : Error := .rpc
    (Grpc.Status.error .permissionDenied "peer-message-sentinel")
    (some "binary-details-sentinel".toUTF8)
  let rendered := reprStr error
  expect (!(rendered.contains "peer-message-sentinel") &&
      !(rendered.contains "binary-details-sentinel") &&
      !(rendered.contains "112, 101, 101, 114") &&
      !(rendered.contains "98, 105, 110, 97, 114, 121"))
    "Call.Error Repr exposed peer status text or status-details bytes"
  expect (rendered.contains
      s!"status code {Grpc.Code.permissionDenied.toNat}")
    "Call.Error Repr omitted the bounded status classification"

private structure TimeoutCall where
  events : IO.Ref (Array String)
  recvEntered : IO.Promise Unit
  cancelled : IO.Promise Unit

private def locallyCancelledStatus : Grpc.Status :=
  Grpc.Status.cancelled "call cancelled locally"

private def timeoutPrimitives : Primitives TimeoutCall where
  send := fun call _ => do
    record call.events "send"
    pure (.ok ())
  closeSend := fun call => do
    record call.events "closeSend"
    pure (.ok ())
  recv? := fun call => do
    record call.events "recv"
    call.recvEntered.resolve ()
    discard <| await call.cancelled
    record call.events "recvReleased"
    pure (.error locallyCancelledStatus)
  finish := fun call => do
    record call.events "finish"
    pure (.error locallyCancelledStatus)
  cancel := fun call => do
    record call.events "cancel"
    call.cancelled.resolve ()

private def testTimeoutCancelsAndJoinsCleanup : IO Unit := do
  let events ← IO.mkRef #[]
  let recvEntered : IO.Promise Unit ← IO.Promise.new
  let cancelled : IO.Promise Unit ← IO.Promise.new
  let call : TimeoutCall := { events, recvEntered, cancelled }
  let deadlineDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := promiseSelector recvEntered
      disarm := pure ()
    }
  }
  let result ← Async.block <| unaryWith RpcDeadline.default deadlineDriver
    (pure (.ok call)) timeoutPrimitives encodeString decodeString "request"
  record events "returned"
  match result with
  | .error .localDeadlineExceeded => pure ()
  | other => fail s!"timed-out unary call returned {repr other}"
  expect ((← events.get) ==
    #["send", "closeSend", "recv", "cancel", "recvReleased", "finish", "returned"])
    "timeout did not cancel, finish, and join the exact call before returning"

private def testExternalCancellationCancelsAndJoinsCleanup : IO Unit := do
  let events ← IO.mkRef #[]
  let recvEntered : IO.Promise Unit ← IO.Promise.new
  let cancelled : IO.Promise Unit ← IO.Promise.new
  let call : TimeoutCall := { events, recvEntered, cancelled }
  let cancellation ← Cancellation.create
  let owner ← IO.asTask
    (Async.block <| unaryWithCancellation RpcDeadline.default neverDeadline
      (some cancellation) (pure (.ok call)) timeoutPrimitives
      encodeString decodeString "request")
    Task.Priority.dedicated
  let some () ← IO.wait recvEntered.result?
    | fail "externally cancellable call never entered receive"
  cancellation.cancel
  let result ← IO.ofExcept (← IO.wait owner)
  record events "returned"
  match result with
  | .error .ownerCancelled => pure ()
  | other => fail s!"externally cancelled unary call returned {repr other}"
  expect ((← events.get) ==
    #["send", "closeSend", "recv", "cancel", "recvReleased", "finish", "returned"])
    "external cancellation did not cancel, finish, and join the exact call"

private structure CompletionRaceCall where
  events : IO.Ref (Array String)
  recvEntered : IO.Promise Unit
  release : IO.Promise Unit
  finished : IO.Promise Unit
  receives : IO.Ref Nat
  response : ByteArray
  terminalStatus : Option Grpc.Status := none

private def completionRacePrimitives : Primitives CompletionRaceCall where
  send := fun call _ => do
    record call.events "send"
    pure (.ok ())
  closeSend := fun call => do
    record call.events "closeSend"
    pure (.ok ())
  recv? := fun call => do
    record call.events "recv"
    let receive ← call.receives.get
    call.receives.set (receive + 1)
    if receive == 0 then
      call.recvEntered.resolve ()
      discard <| await call.release
      match call.terminalStatus with
      | some status => pure (.error status)
      | none => pure (.ok (some call.response))
    else
      pure (.ok none)
  finish := fun call => do
    record call.events "finish"
    call.finished.resolve ()
    match call.terminalStatus with
    | some status => pure (.error status)
    | none => pure (.ok
        (Grpc.Status.ok, Grpc.Metadata.empty, Grpc.Metadata.empty))
  cancel := fun call =>
    record call.events "cancel"

private def completionRaceDeadline
    (call : CompletionRaceCall) : DeadlineDriver := {
  arm := fun _ => pure {
    selector := {
      -- Force the deadline selector to win only after the owner has crossed
      -- its exact `finish`. This deterministically exercises the post-race
      -- nonblocking owner check despite `Selectable.one` fairness shuffling.
      tryFn := do
        discard <| await call.recvEntered
        call.release.resolve ()
        discard <| await call.finished
        -- `finish` is the final primitive action, but its promise can wake this
        -- selector just before the owner task publishes its return value. Give
        -- that already-terminal owner one scheduler turn before selecting the
        -- injected deadline. This wait exists only in the deterministic seam.
        IO.sleep 1
        pure (some ())
      registerFn := fun _ => pure ()
      unregisterFn := pure ()
    }
    disarm := pure ()
  }
}

private def completionRaceCall
    (terminalStatus : Option Grpc.Status := none) : IO CompletionRaceCall := do
  pure {
    events := ← IO.mkRef #[]
    recvEntered := ← IO.Promise.new
    release := ← IO.Promise.new
    finished := ← IO.Promise.new
    receives := ← IO.mkRef 0
    response := "raced-response".toUTF8
    terminalStatus
  }

private def testDeadlineWinnerPreservesCompletedOwner : IO Unit := do
  let responseCall ← completionRaceCall
  let responseResult ← Async.block <| unaryWith RpcDeadline.default
    (completionRaceDeadline responseCall) (pure (.ok responseCall))
    completionRacePrimitives encodeString decodeString "request"
  match responseResult with
  | .ok "raced-response" => pure ()
  | other =>
      fail s!"deadline winner discarded a completed response: {repr other}"
  let responseEvents ← responseCall.events.get
  expect (!(responseEvents.contains "cancel"))
    "deadline winner cancelled an owner already proven terminal"
  expect (responseEvents.back? == some "finish")
    "completed response was returned before exact finish"

  -- A completed peer cancellation remains exact RPC evidence. The byte-equal
  -- grpc-lean local-cancel sentinel is intentionally covered only where this
  -- adapter really issued cancel: without a lower-level cancel disposition,
  -- those two sources cannot be distinguished after the fact.
  let peerStatus := Grpc.Status.cancelled "peer completed cancellation"
  let statusCall ← completionRaceCall (some peerStatus)
  let statusResult ← Async.block <| unaryWith RpcDeadline.default
    (completionRaceDeadline statusCall) (pure (.ok statusCall))
    completionRacePrimitives encodeString decodeString "request"
  match statusResult with
  | .error (.rpc status _) =>
      expect (status == peerStatus)
        "completed peer status was rewritten as local deadline provenance"
  | other =>
      fail s!"deadline winner discarded a completed status: {repr other}"
  expect (!((← statusCall.events.get).contains "cancel"))
    "completed peer status triggered a redundant local cancel"

private inductive PostCancelOutcome where
  | response (value : ByteArray)
  | status (value : Grpc.Status)
  | actionFailed
  | cleanupUncertain

private structure PostCancelCall where
  events : IO.Ref (Array String)
  recvEntered : IO.Promise Unit
  cancelled : IO.Promise Unit
  receives : IO.Ref Nat
  cancels : IO.Ref Nat
  outcome : PostCancelOutcome
  finishResult :
    Except Grpc.Status (Grpc.Status × Grpc.Metadata × Grpc.Metadata)

private def postCancelPrimitives : Primitives PostCancelCall where
  send := fun call _ => do
    record call.events "send"
    pure (.ok ())
  closeSend := fun call => do
    record call.events "closeSend"
    pure (.ok ())
  recv? := fun call => do
    record call.events "recv"
    let receive ← call.receives.get
    call.receives.set (receive + 1)
    if receive == 0 then call.recvEntered.resolve ()
    discard <| await call.cancelled
    match call.outcome with
    | .response value =>
        if receive == 0 then pure (.ok (some value)) else pure (.ok none)
    | .status status => pure (.error status)
    | .actionFailed | .cleanupUncertain =>
        throw (IO.userError "injected post-cancel receive failure")
  finish := fun call => do
    record call.events "finish"
    pure call.finishResult
  cancel := fun call => do
    record call.events "cancel"
    let count ← call.cancels.get
    call.cancels.set (count + 1)
    if count == 0 then
      call.cancelled.resolve ()
    else
      match call.outcome with
      | .cleanupUncertain =>
          throw (IO.userError "injected post-cancel cleanup failure")
      | _ => pure ()

private def runPostCancel
    (outcome : PostCancelOutcome)
    (disarmFails : Bool := false) :
    IO (Except Error String × Array String) := do
  let events ← IO.mkRef #[]
  let recvEntered ← IO.Promise.new
  let call : PostCancelCall := {
    events
    recvEntered
    cancelled := ← IO.Promise.new
    receives := ← IO.mkRef 0
    cancels := ← IO.mkRef 0
    outcome
    finishResult := .ok
      (Grpc.Status.ok, Grpc.Metadata.empty, Grpc.Metadata.empty)
  }
  let deadlineDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := promiseSelector recvEntered
      disarm :=
        if disarmFails then
          throw (IO.userError "injected deadline disarm failure")
        else
          pure ()
    }
  }
  let result ← Async.block <| unaryWith RpcDeadline.default deadlineDriver
    (pure (.ok call)) postCancelPrimitives encodeString decodeString "request"
  pure (result, ← events.get)

private def testPostCancelOwnerEvidenceDominatesLocalDeadline : IO Unit := do
  for status in #[
      Grpc.Status.cancelled "peer cancelled concurrently",
      Grpc.Status.deadlineExceeded "peer deadline won concurrently",
      Grpc.Status.error .unavailable "connection failed concurrently"] do
    let (result, events) ← runPostCancel (.status status)
    match result with
    | .error (.rpc observed _) =>
        expect (observed == status)
          "post-cancel terminal RPC status lost its exact provenance"
    | other =>
        fail s!"post-cancel terminal status returned {repr other}"
    expect (events.contains "cancel")
      "post-cancel status fixture never requested local cancellation"
    expect (events.back? == some "finish")
      "post-cancel status returned before exact finish"

  let (completed, completedEvents) ←
    runPostCancel (.response "completed-after-cancel".toUTF8)
  match completed with
  | .ok "completed-after-cancel" => pure ()
  | other =>
      fail s!"post-cancel completed response was discarded: {repr other}"
  expect (completedEvents.contains "cancel")
    "post-cancel response fixture did not cross local cancellation"

  let (failed, failedEvents) ← runPostCancel .actionFailed
  match failed with
  | .error .actionFailed => pure ()
  | other =>
      fail s!"post-cancel action failure was rewritten: {repr other}"
  expect (failedEvents.back? == some "finish")
    "post-cancel action failure returned before cleanup acknowledgement"

  let (failedWithDisarm, _) ← runPostCancel .actionFailed true
  match failedWithDisarm with
  | .error .actionFailed => pure ()
  | other =>
      fail s!"deadline disarm failure rewrote owner action failure: {repr other}"

  let (uncertain, uncertainEvents) ← runPostCancel .cleanupUncertain
  match uncertain with
  | .error .cleanupUncertain => pure ()
  | other =>
      fail s!"post-cancel cleanup uncertainty was rewritten: {repr other}"
  expect ((uncertainEvents.filter (· == "cancel")).size == 2)
    "post-cancel cleanup uncertainty did not retain both cleanup attempts"

  let (uncertainWithDisarm, _) ← runPostCancel .cleanupUncertain true
  match uncertainWithDisarm with
  | .error .cleanupUncertain => pure ()
  | other =>
      fail s!"deadline disarm failure rewrote cleanup uncertainty: {repr other}"

private def testPostCancelPreservesPeerStatusDetails : IO Unit := do
  let events ← IO.mkRef #[]
  let recvEntered ← IO.Promise.new
  let details := "peer-cancel-status-details".toUTF8
  let trailers := Grpc.Metadata.empty.insertBinary
    "grpc-status-details-bin" details
  -- Deliberately use grpc-lean's byte-equal local-cancel sentinel.  The rich
  -- trailer is terminal peer evidence and must prevent local reclassification.
  let call : PostCancelCall := {
    events
    recvEntered
    cancelled := ← IO.Promise.new
    receives := ← IO.mkRef 0
    cancels := ← IO.mkRef 0
    outcome := .status locallyCancelledStatus
    finishResult := .ok
      (locallyCancelledStatus, Grpc.Metadata.empty, trailers)
  }
  let deadlineDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := promiseSelector recvEntered
      disarm := pure ()
    }
  }
  let result ← Async.block <| unaryWith RpcDeadline.default deadlineDriver
    (pure (.ok call)) postCancelPrimitives encodeString decodeString "request"
  match result with
  | .error (.rpc status (some observed)) =>
      expect (status == locallyCancelledStatus && observed == details)
        "post-cancel peer details were rewritten as a local deadline"
  | other =>
      fail s!"post-cancel peer status details returned {repr other}"
  let observedEvents ← events.get
  expect (observedEvents.contains "cancel" &&
      (observedEvents.filter (· == "finish")).size == 1)
    "post-cancel peer-details path did not finish exactly once"

private def testTimeoutDisarmFailureStillJoinsCleanup : IO Unit := do
  let events ← IO.mkRef #[]
  let recvEntered : IO.Promise Unit ← IO.Promise.new
  let cancelled : IO.Promise Unit ← IO.Promise.new
  let call : TimeoutCall := { events, recvEntered, cancelled }
  let deadlineDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := promiseSelector recvEntered
      disarm := do
        record events "disarm"
        throw (IO.userError "injected deadline disarm failure")
    }
  }
  let threw ←
    try
      discard <| Async.block <| unaryWith RpcDeadline.default deadlineDriver
        (pure (.ok call)) timeoutPrimitives encodeString decodeString "request"
      pure false
    catch _ =>
      record events "returned"
      pure true
  expect threw "deadline disarm failure was swallowed"
  expect ((← events.get) ==
    #["send", "closeSend", "recv", "disarm", "cancel",
      "recvReleased", "finish", "returned"])
    "deadline disarm failure released the caller before exact-call cleanup"

private def testSelectorFailureCancelsAndJoinsCleanup : IO Unit := do
  let events ← IO.mkRef #[]
  let recvEntered : IO.Promise Unit ← IO.Promise.new
  let cancelled : IO.Promise Unit ← IO.Promise.new
  let call : TimeoutCall := { events, recvEntered, cancelled }
  let throwingSelector : Selector Unit := {
    tryFn := do
      discard <| await recvEntered
      throw (IO.userError "injected selector failure")
    registerFn := fun _ => pure ()
    unregisterFn := pure ()
  }
  let deadlineDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := throwingSelector
      disarm := record events "disarm"
    }
  }
  let threw ←
    try
      discard <| Async.block <| unaryWith RpcDeadline.default deadlineDriver
        (pure (.ok call)) timeoutPrimitives encodeString decodeString "request"
      pure false
    catch _ =>
      record events "returned"
      pure true
  expect threw "selector failure was swallowed"
  expect ((← events.get) ==
    #["send", "closeSend", "recv", "disarm", "cancel",
      "recvReleased", "finish", "returned"])
    "selector failure released the caller before exact-call cleanup"

private def testStartStatusAndDeadlineDisarm : IO Unit := do
  let disarmed ← IO.mkRef false
  let driver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := neverSelector
      disarm := disarmed.set true
    }
  }
  let unavailable := Grpc.Status.error .unavailable "not connected"
  let result ← Async.block <| unaryWith RpcDeadline.default driver
    (pure (.error unavailable : Except Grpc.Status ScriptedCall))
    scriptedPrimitives encodeString decodeString "request"
  match result with
  | .error (.rpc status none) =>
      expect (status == unavailable) "start failure status was not preserved"
  | other => fail s!"start failure returned {repr other}"
  expect (← disarmed.get) "start failure leaked its armed deadline"

  let exceptionDisarmed ← IO.mkRef false
  let exceptionDriver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := neverSelector
      disarm := exceptionDisarmed.set true
    }
  }
  let threw ←
    try
      discard <| Async.block <| unaryWith RpcDeadline.default exceptionDriver
        (throw (IO.userError "injected start exception") :
          Async (Except Grpc.Status ScriptedCall))
        scriptedPrimitives encodeString decodeString "request"
      pure false
    catch _ =>
      pure true
  expect threw "injected start exception was swallowed"
  expect (← exceptionDisarmed.get)
    "thrown start failure leaked its armed deadline"

private def testPrimitiveExceptionCleansCallAndDeadline : IO Unit := do
  let events ← IO.mkRef #[]
  let disarmed ← IO.mkRef false
  let driver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := neverSelector
      disarm := disarmed.set true
    }
  }
  let call ← scriptedCall events ["unused".toUTF8]
  let throwingPrimitives : Primitives ScriptedCall := {
    scriptedPrimitives with
    send := fun call _ => do
      record call.events "send"
      throw (IO.userError "injected primitive exception")
  }
  let result ← Async.block <| unaryWith RpcDeadline.default driver
    (pure (.ok call)) throwingPrimitives
    encodeString decodeString "request"
  match result with
  | .error .actionFailed => pure ()
  | other => fail s!"injected call primitive exception returned {repr other}"
  expect ((← events.get) == #["send", "cancel", "finish"])
    "primitive exception did not cancel and finish its exact call"
  expect (← disarmed.get)
    "primitive exception leaked its armed deadline"

private def testPrimitiveCleanupUncertaintyIsExplicit : IO Unit := do
  let events ← IO.mkRef #[]
  let driver : DeadlineDriver := {
    arm := fun _ => pure {
      selector := neverSelector
      disarm := record events "disarm"
    }
  }
  let call ← scriptedCall events ["unused".toUTF8]
  let throwingPrimitives : Primitives ScriptedCall := {
    scriptedPrimitives with
    send := fun call _ => do
      record call.events "send"
      throw (IO.userError "injected primitive exception")
    cancel := fun call => do
      record call.events "cancel"
      throw (IO.userError "injected cancellation failure")
  }
  let result ← Async.block <| unaryWith RpcDeadline.default driver
    (pure (.ok call)) throwingPrimitives
    encodeString decodeString "request"
  match result with
  | .error .cleanupUncertain => pure ()
  | other => fail s!"uncertain primitive cleanup returned {repr other}"
  expect ((← events.get) == #["send", "cancel", "disarm"])
    "uncertain primitive cleanup changed its bounded containment sequence"

private def testStartPermitControlsRemainingBudget : IO Unit := do
  let deniedArms ← IO.mkRef 0
  let deniedStarts ← IO.mkRef 0
  let deniedDriver : DeadlineDriver := {
    arm := fun _ => do
      deniedArms.modify (· + 1)
      pure { selector := neverSelector, disarm := pure () }
  }
  let deniedEvents ← IO.mkRef #[]
  let deniedCall ← scriptedCall deniedEvents ["unused".toUTF8]
  let denied ← Async.block <|
    unaryWithCancellationAndPermit deniedDriver none (pure none)
      (fun _ => do
        deniedStarts.modify (· + 1)
        pure (.ok deniedCall)) scriptedPrimitives
      encodeString decodeString "request"
  match denied with
  | .error .ownerCancelled => pure ()
  | other => fail s!"denied call-start permit returned {repr other}"
  expect ((← deniedArms.get) == 0 && (← deniedStarts.get) == 0 &&
      (← deniedEvents.get).isEmpty)
    "denied call-start permit armed or started transport work"

  let armedWith ← IO.mkRef (none : Option Nat)
  let startedWith ← IO.mkRef (none : Option Nat)
  let admittedDriver : DeadlineDriver := {
    arm := fun remaining => do
      armedWith.set (some remaining)
      pure { selector := neverSelector, disarm := pure () }
  }
  let admittedEvents ← IO.mkRef #[]
  let admittedCall ← scriptedCall admittedEvents ["response".toUTF8]
  let admitted ← Async.block <|
    unaryWithCancellationAndPermit admittedDriver none (pure (some 1_234))
      (fun remaining => do
        startedWith.set (some remaining)
        pure (.ok admittedCall)) scriptedPrimitives
      encodeString decodeString "request"
  match admitted with
  | .ok "response" => pure ()
  | other => fail s!"admitted call-start permit returned {repr other}"
  expect ((← armedWith.get) == some 1_234 &&
      (← startedWith.get) == some 1_234)
    "remaining absolute budget diverged between local timer and transport start"

  let cancelled ← Cancellation.create
  cancelled.cancel
  let permitCalls ← IO.mkRef 0
  let preCancelled ← Async.block <|
    unaryWithCancellationAndPermit deniedDriver (some cancelled)
      (do permitCalls.modify (· + 1); pure (some 1_000))
      (fun _ => do
        deniedStarts.modify (· + 1)
        pure (.ok deniedCall)) scriptedPrimitives
      (fun (_ : String) => .error ()) decodeString "request"
  match preCancelled with
  | .error .ownerCancelled => pure ()
  | other => fail s!"pre-cancelled encoding returned {repr other}"
  expect ((← permitCalls.get) == 0)
    "pre-cancelled encoding claimed transport admission"

private def testNoOrdinarySecretRendering : IO Unit := do
  let configuration ← configuration
  expect (reprStr configuration.credentials == "[REDACTED]")
    "credentials Repr exposed secret material"
  expect (toString configuration.credentials == "[REDACTED]")
    "credentials ToString exposed secret material"
  let entry ← credentialEntry
  expect (!(reprStr entry).contains "production-api-key" &&
      !(toString entry).contains "production-api-key")
    "credential entry rendering exposed secret material"
  expect (!(reprStr configuration).contains "production-api-key")
    "configuration rendering exposed secret material"
  let fetched ← configuration.credentials.fresh
  expect (fetched.map (fun entry => (entry.name, entry.exposeValue)) ==
      #[("authorization", "Bearer production-api-key")])
    "per-call credentials changed their fresh entries"

private partial def waitForRegisteredWaiters
    (cancellation : Cancellation)
    (expected : Nat)
    (remaining : Nat := 2_000) : IO Unit := do
  if (← Cancellation.TestSupport.registeredWaiters cancellation) == expected then
    pure ()
  else if remaining == 0 then
    fail s!"timed out waiting for {expected} cancellation waiters"
  else
    IO.sleep 1
    waitForRegisteredWaiters cancellation expected (remaining - 1)

private def testReusableCancellationSelectorPrunesWaiters : IO Unit := do
  let shared ← Cancellation.create
  for _ in [0:256] do
    let winner ← Cancellation.create
    let task : Task (Except IO.Error Unit) ← IO.asTask <|
      (Selectable.one #[
        Selectable.case shared.selector fun _ => pure (),
        Selectable.case winner.selector fun _ => pure ()
      ]).block
    waitForRegisteredWaiters shared 1
    winner.cancel
    match ← IO.wait task with
    | .ok () => pure ()
    | .error error =>
        fail s!"cancellation selector race failed: {error}"
    waitForRegisteredWaiters shared 0
  expect ((← Cancellation.TestSupport.registeredWaiters shared) == 0)
    "reused cancellation retained completed selector registrations"

private def testCancellationLinearizationLockOrdersTransitions : IO Unit := do
  let cancellation ← Cancellation.create
  let entered ← IO.Promise.new
  let allowTransition ← IO.Promise.new
  let transition : Task (Except IO.Error (Option Nat)) ← IO.asTask <|
    cancellation.linearizeIfActive do
      entered.resolve ()
      let some () ← IO.wait allowTransition.result?
        | throw (IO.userError "linearization test signal dropped")
      pure 17
  let some () ← IO.wait entered.result?
    | fail "active transition never acquired the cancellation lock"
  let cancelTask : Task (Except IO.Error Unit) ←
    IO.asTask cancellation.cancel
  IO.sleep 50
  expect (!(← IO.hasFinished cancelTask))
    "cancellation bypassed an active ownership transition"
  allowTransition.resolve ()
  match ← IO.wait transition with
  | .ok (some 17) => pure ()
  | _ => fail "active transition lost its pre-cancellation linearization"
  match ← IO.wait cancelTask with
  | .ok () => pure ()
  | .error error => fail s!"ordered cancellation failed: {error}"

  let alreadyCancelled ← Cancellation.create
  alreadyCancelled.cancel
  let actionRan ← IO.mkRef false
  match ← alreadyCancelled.linearizeIfActive do
      actionRan.set true
      pure 23 with
  | none => pure ()
  | some _ => fail "post-cancellation transition was admitted"
  expect (!(← actionRan.get))
    "post-cancellation transition executed its action"

private def testTokenCancelCommitsOnceAndWakesSelectors : IO Unit := do
  -- The winning selector's synchronous unregister hook re-enters the token
  -- mutex; callback-safe cancellation must resolve consumers only after that
  -- mutex has been released, and must commit the sticky transition once.
  let token ← Std.CancellationToken.new
  let bystander ← Std.CancellationToken.new
  let race : Task (Except IO.Error Unit) ← IO.asTask <|
    (Selectable.one #[
      Selectable.case token.selector fun _ => pure (),
      Selectable.case bystander.selector fun _ => pure ()
    ]).block
  expect (← Grpc.CancellationToken.cancel token)
    "first callback-safe cancellation did not perform the transition"
  match ← IO.wait race with
  | .ok () => pure ()
  | .error error => fail s!"callback-safe cancellation race failed: {error}"
  expect (← token.isCancelled)
    "callback-safe cancellation did not publish the sticky transition"
  expect (!(← Grpc.CancellationToken.cancel token))
    "repeated callback-safe cancellation claimed the one transition again"

def run : IO Unit := do
  testCompletedBeforeTimeout
  testEncodingAndDecodingErrors
  testStatusAndCardinality
  testStatusDetailsTrailers
  testFastActionErrorsRecoverStatusDetails
  testErrorRenderingRedactsPeerEvidence
  testTimeoutCancelsAndJoinsCleanup
  testExternalCancellationCancelsAndJoinsCleanup
  testDeadlineWinnerPreservesCompletedOwner
  testPostCancelOwnerEvidenceDominatesLocalDeadline
  testPostCancelPreservesPeerStatusDetails
  testTimeoutDisarmFailureStillJoinsCleanup
  testSelectorFailureCancelsAndJoinsCleanup
  testStartStatusAndDeadlineDisarm
  testPrimitiveExceptionCleansCallAndDeadline
  testPrimitiveCleanupUncertaintyIsExplicit
  testStartPermitControlsRemainingBudget
  testNoOrdinarySecretRendering
  testReusableCancellationSelectorPrunesWaiters
  testCancellationLinearizationLockOrdersTransitions
  testTokenCancelCommitsOnceAndWakesSelectors
  IO.println "transport call lifecycle tests passed"

end UnaryCallTest

def main : IO Unit :=
  UnaryCallTest.run
