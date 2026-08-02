import Grpc

open Grpc
open Grpc.Services

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectStatusOk (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def expectProtoOk (result : Except Protobuf.Encoding.ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

def runGrpcM (action : GrpcM α) : IO α := do
  match (← action.run) with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def expectGrpcMError (action : GrpcM α) : IO Status := do
  match (← action.run) with
  | .ok _ => throw (IO.userError "expected gRPC status error")
  | .error status => pure status

def requestHeadersForPath (path : String) : Metadata :=
  Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

def healthBody (request : Health.CheckRequest) : IO ByteArray := do
  let data ← expectProtoOk (Health.CheckRequest.encode request)
  expectStatusOk (Message.encode { data := data })

def dispatchCheck (registry : Registry) (service : String) : IO (Except Status Health.CheckResponse) := do
  let body ← healthBody { service := service }
  let result ← (registry.dispatchUnary
    (requestHeadersForPath Health.checkMethodName.path) body).run
  match result with
  | .error status => pure (.error status)
  | .ok response => do
      let decoded ← expectProtoOk (Health.CheckResponse.decode response.data)
      pure (.ok decoded)

def expectCheck (registry : Registry) (service : String) (expected : Health.ServingStatus)
    (msg : String) : IO Unit := do
  match ← dispatchCheck registry service with
  | .ok response => expectEq response.status expected msg
  | .error status => throw (IO.userError s!"{msg}: unexpected error {status.messageD}")

def testWireRoundTrip : IO Unit := do
  let request : Health.CheckRequest := { service := "a.b.C" }
  let encoded ← expectProtoOk (Health.CheckRequest.encode request)
  let decoded ← expectProtoOk (Health.CheckRequest.decode encoded)
  expectEq decoded request "HealthCheckRequest should round-trip"
  let emptyRequest ← expectProtoOk (Health.CheckRequest.encode {})
  expectEq emptyRequest.size 0 "empty service name should be omitted on the wire"
  let decodedEmpty ← expectProtoOk (Health.CheckRequest.decode ByteArray.empty)
  expectEq decodedEmpty.service "" "empty request should decode to empty service name"
  for status in [Health.ServingStatus.unknown, .serving, .notServing, .serviceUnknown] do
    let response : Health.CheckResponse := { status := status }
    let encoded ← expectProtoOk (Health.CheckResponse.encode response)
    let decoded ← expectProtoOk (Health.CheckResponse.decode encoded)
    expectEq decoded response "HealthCheckResponse should round-trip"
  let unknownWire ← expectProtoOk (Health.CheckResponse.encode { status := .unknown })
  expectEq unknownWire.size 0 "UNKNOWN (0) status should be omitted on the wire"

def testCheck : IO Unit := do
  let (health, registry) ← Health.register Registry.empty
  expectCheck registry "" .serving "overall server status should default to SERVING"

  health.setStatus "lean.example.proto.NoteService" .serving
  expectCheck registry "lean.example.proto.NoteService" .serving
    "registered service should report SERVING"

  health.setNotServing "lean.example.proto.NoteService"
  expectCheck registry "lean.example.proto.NoteService" .notServing
    "setNotServing should be reflected by Check"

  match ← dispatchCheck registry "never.Registered" with
  | .ok _ => throw (IO.userError "unknown service Check should fail")
  | .error status =>
      expectEq status.code Code.notFound "unknown service Check should return NOT_FOUND"

  health.shutdown
  expectCheck registry "" .notServing "shutdown should mark the overall status NOT_SERVING"
  expectCheck registry "lean.example.proto.NoteService" .notServing
    "shutdown should mark every registered service NOT_SERVING"
  health.setServing "lean.example.proto.NoteService"
  expectCheck registry "lean.example.proto.NoteService" .notServing
    "terminal health state should ignore attempts to restore SERVING"
  health.setServing "registered.after.shutdown"
  match ← dispatchCheck registry "registered.after.shutdown" with
  | .ok _ => throw (IO.userError "terminal health state admitted a new service")
  | .error status =>
      expectEq status.code Code.notFound
        "terminal health state should ignore newly registered services"

def recvResponse (stream : MessageStream ByteArray) : IO Health.CheckResponse := do
  match ← runGrpcM stream.recv? with
  | none => throw (IO.userError "health watch stream ended unexpectedly")
  | some data => expectProtoOk (Health.CheckResponse.decode data)

def dispatchWatch (registry : Registry) (service : String) : IO (MessageStream ByteArray) := do
  let body ← healthBody { service := service }
  let response ← runGrpcM (registry.dispatchServerStreamingStream
    (requestHeadersForPath Health.watchMethodName.path) body)
  expectEq response.status.code Code.ok "health watch status should be OK"
  pure response.messages

def expectWatcherCount (health : Health.Service) (expected : Nat) (msg : String) : IO Unit := do
  expectEq (← health.activeWatcherCount) expected msg

def testWatch : IO Unit := do
  let (health, registry) ← Health.register Registry.empty

  -- Registered service: initial status, then updates on every change.
  health.setStatus "svc" .serving
  let stream ← dispatchWatch registry "svc"
  expectWatcherCount health 1 "watch should retain exactly one live owner"
  let initial ← recvResponse stream
  expectEq initial.status .serving "watch should immediately send the current status"
  health.setStatus "svc" .notServing
  let update ← recvResponse stream
  expectEq update.status .notServing "watch should send a message when the status changes"
  -- No-op update (same status) should not produce a message before the next real change.
  health.setStatus "svc" .notServing
  health.setStatus "svc" .serving
  let next ← recvResponse stream
  expectEq next.status .serving "watch should skip no-op updates and deliver the next change"
  runGrpcM stream.cancel
  expectWatcherCount health 0
    "watch cancellation should remove its owner before returning"
  -- Exact cancellation is idempotent and must not affect future identities.
  runGrpcM stream.cancel
  expectWatcherCount health 0
    "duplicate watch cancellation should not resurrect or remove another owner"

  -- Unregistered service: SERVICE_UNKNOWN is not an error for Watch, and later
  -- registration is delivered as an update.
  let unknownStream ← dispatchWatch registry "later.Registered"
  expectWatcherCount health 1 "unknown-service watch should own one stream"
  let unknownInitial ← recvResponse unknownStream
  expectEq unknownInitial.status .serviceUnknown
    "watch on an unregistered service should send SERVICE_UNKNOWN"
  health.setStatus "later.Registered" .serving
  let registeredUpdate ← recvResponse unknownStream
  expectEq registeredUpdate.status .serving
    "watch should deliver the status once the service is registered"
  runGrpcM unknownStream.cancel
  expectWatcherCount health 0
    "unknown-service cancellation should remove its owner immediately"

  -- Cancellation removes the exact watcher identity, even when a peer watches
  -- the same service and the stale cancellation is repeated.
  let cancelledStream ← dispatchWatch registry "svc"
  let liveStream ← dispatchWatch registry "svc"
  expectWatcherCount health 2 "parallel watchers should retain two distinct owners"
  let cancelledInitial ← recvResponse cancelledStream
  expectEq cancelledInitial.status .serving "first parallel watcher should see the current status"
  let liveInitial ← recvResponse liveStream
  expectEq liveInitial.status .serving "second parallel watcher should see the current status"
  runGrpcM cancelledStream.cancel
  expectWatcherCount health 1 "cancellation should remove only its exact watcher owner"
  runGrpcM cancelledStream.cancel
  expectWatcherCount health 1 "stale duplicate cancellation should preserve the peer watcher"
  health.setStatus "svc" .notServing
  let liveUpdate ← recvResponse liveStream
  expectEq liveUpdate.status .notServing
    "peer watcher should keep receiving updates after exact cancellation"
  runGrpcM liveStream.cancel
  expectWatcherCount health 0 "final watcher cancellation should leave no owners"

def testImmediateCancellationChurn : IO Unit := do
  let health ← Health.Service.new
  health.setServing "svc"
  for _ in Array.range 2000 do
    let stream ← runGrpcM (health.watch { service := "svc" })
    let initial ← runGrpcM stream.recv?
    match initial with
    | some response =>
        expectEq response.status .serving
          "churn watcher should receive its initial status first"
    | none => throw (IO.userError "churn watcher ended before its initial status")
    runGrpcM stream.cancel
    expectWatcherCount health 0
      "cancelled churn watcher remained retained without a status transition"

def awaitTask (task : Task (Except IO.Error Unit)) : IO Unit := do
  match ← IO.wait task with
  | .ok () => pure ()
  | .error error => throw error

def testConcurrentShutdownIsTerminal : IO Unit := do
  let (health, registry) ← Health.register Registry.empty
  health.setServing "svc"
  let setters ← (Array.range 8).mapM fun worker => IO.asTask do
    for i in Array.range 500 do
      health.setStatus "svc"
        (if (worker + i) % 2 == 0 then .serving else .notServing)
  let shutdown ← IO.asTask health.shutdown Task.Priority.dedicated
  for setter in setters do
    awaitTask setter
  awaitTask shutdown
  expectCheck registry "svc" .notServing
    "concurrent status writers must not resurrect a terminal service"
  health.setServing "svc"
  expectCheck registry "svc" .notServing
    "terminal state must remain stable after concurrent writers join"

  let stream ← dispatchWatch registry "svc"
  let initial ← recvResponse stream
  expectEq initial.status .notServing
    "a Watch registered after shutdown should initially see NOT_SERVING"
  runGrpcM stream.cancel
  expectWatcherCount health 0
    "post-shutdown Watch cancellation should release its owner"

def testConcurrentWatchUpdateCancel : IO Unit := do
  let health ← Health.Service.new
  health.setServing "svc"
  let worker : IO Unit := do
    for _ in Array.range 250 do
      let stream ← runGrpcM (health.watch { service := "svc" })
      let initial ← runGrpcM stream.recv?
      match initial with
      | some _ => pure ()
      | none => throw (IO.userError "concurrent watcher missed its initial status")
      runGrpcM stream.cancel
  let workers ← (Array.range 16).mapM fun _ => IO.asTask worker
  let updater ← IO.asTask do
    for i in Array.range 4000 do
      health.setStatus "svc" (if i % 2 == 0 then .serving else .notServing)
  for task in workers do
    awaitTask task
  awaitTask updater
  expectWatcherCount health 0
    "concurrent Watch/update/cancel churn leaked watcher ownership"
  -- The status registry shares the same mutex, so it remains usable after the
  -- race rather than losing a concurrent state write.
  health.setServing "svc"
  expectEq (← health.checkStatus? "svc") (some .serving)
    "health registry was corrupted by concurrent watcher cancellation"

def main : IO Unit := do
  testWireRoundTrip
  testCheck
  testWatch
  testImmediateCancellationChurn
  testConcurrentShutdownIsTerminal
  testConcurrentWatchUpdateCancel
