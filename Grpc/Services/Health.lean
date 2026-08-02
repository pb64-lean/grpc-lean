module

public import Grpc.Server
public import Protobuf.Encoding
public import Std.Sync.Mutex

public section

namespace Grpc
namespace Services
namespace Health

namespace Wire

abbrev ProtoMessage := Protobuf.Encoding.Message
abbrev ProtoError := Protobuf.Encoding.ProtoError

private def decodeProtoMessage (bytes : ByteArray) : Except ProtoError ProtoMessage := do
  Protobuf.Encoding.protoDecodeParseResultExcept
    (Binary.Get.run (Binary.getThe ProtoMessage) bytes).toExcept

private def encodeProtoMessage (message : ProtoMessage) : Except ProtoError ByteArray := do
  message.validate
  pure (Binary.Put.run (Binary.put message))

private def setStringIfNotEmpty (message : ProtoMessage) (fieldNum : Nat) (value : String) :
    Except ProtoError ProtoMessage := do
  if value.isEmpty then
    pure message
  else
    let value ← Protobuf.Encoding.ProtoVal.ofString value
    pure (message.set fieldNum value)

private def setInt32IfNonZero (message : ProtoMessage) (fieldNum : Nat) (value : Int32) :
    Except ProtoError ProtoMessage := do
  if value == 0 then
    pure message
  else
    let value ← Protobuf.Encoding.ProtoVal.ofVarint_int32 value
    pure (message.set fieldNum value)

end Wire

open Wire

def serviceName : String :=
  "grpc.health.v1.Health"

def checkMethodName : MethodName :=
  { service := serviceName, method := "Check" }

def watchMethodName : MethodName :=
  { service := serviceName, method := "Watch" }

/-- `grpc.health.v1.HealthCheckResponse.ServingStatus`. -/
inductive ServingStatus where
  | unknown
  | serving
  | notServing
  | serviceUnknown
  deriving Inhabited, Repr, DecidableEq

namespace ServingStatus

def toInt32 : ServingStatus -> Int32
  | .unknown => 0
  | .serving => 1
  | .notServing => 2
  | .serviceUnknown => 3

def ofInt32 : Int32 -> ServingStatus
  | 1 => .serving
  | 2 => .notServing
  | 3 => .serviceUnknown
  | _ => .unknown

end ServingStatus

/-- `grpc.health.v1.HealthCheckRequest`. -/
structure CheckRequest where
  service : String := ""
  deriving Inhabited, Repr, DecidableEq

namespace CheckRequest

def fromMessage (message : ProtoMessage) : Except ProtoError CheckRequest := do
  pure { service := (← message.getString? 1).getD "" }

def toMessage (request : CheckRequest) : Except ProtoError ProtoMessage := do
  setStringIfNotEmpty Protobuf.Encoding.Message.empty 1 request.service

def decode (bytes : ByteArray) : Except ProtoError CheckRequest := do
  fromMessage (← decodeProtoMessage bytes)

def encode (request : CheckRequest) : Except ProtoError ByteArray := do
  encodeProtoMessage (← toMessage request)

end CheckRequest

/-- `grpc.health.v1.HealthCheckResponse`. -/
structure CheckResponse where
  status : ServingStatus := .unknown
  deriving Inhabited, Repr, DecidableEq

namespace CheckResponse

def fromMessage (message : ProtoMessage) : Except ProtoError CheckResponse := do
  pure { status := ServingStatus.ofInt32 ((← message.getVarint_int32? 1).getD 0) }

def toMessage (response : CheckResponse) : Except ProtoError ProtoMessage := do
  setInt32IfNonZero Protobuf.Encoding.Message.empty 1 response.status.toInt32

def decode (bytes : ByteArray) : Except ProtoError CheckResponse := do
  fromMessage (← decodeProtoMessage bytes)

def encode (response : CheckResponse) : Except ProtoError ByteArray := do
  encodeProtoMessage (← toMessage response)

end CheckResponse

private structure WatcherId where
  value : Nat
  deriving BEq, DecidableEq

private structure Watcher where
  id : WatcherId
  service : String
  producer : MessageStream.Producer CheckResponse

private structure State where
  statuses : Array (String × ServingStatus) := #[("", .serving)]
  watchers : Array Watcher := #[]
  nextWatcherId : Nat := 0
  terminal : Bool := false

/--
A mutable registry backing the standard `grpc.health.v1.Health` service.

The overall server status (the empty service name) starts as SERVING. Watchers
receive the current status immediately and a new message on every subsequent
status change for the watched service. Updates are pushed through unbounded
in-process channels, so `setStatus` never blocks on slow watchers; watchers
are assigned monotonically increasing identities and are removed from this
registry before their stream cancellation returns. The mutex serializes the
initial value, status changes, and exact watcher removal, so neither a
concurrent update nor a cancelled stream can resurrect or overwrite another
watcher's ownership.
-/
structure Service where
  private mk ::
  private state : Std.Mutex State

namespace Service

def new : IO Service := do
  pure { state := ← Std.Mutex.new {} }

private def lookupStatus? (state : State) (service : String) : Option ServingStatus :=
  state.statuses.findSome? fun entry =>
    if entry.1 == service then some entry.2 else none

private def setStatusEntry (statuses : Array (String × ServingStatus)) (service : String)
    (status : ServingStatus) : Array (String × ServingStatus) :=
  if statuses.any (fun entry => entry.1 == service) then
    statuses.map fun entry => if entry.1 == service then (service, status) else entry
  else
    statuses.push (service, status)

/-- Send a status update to a watcher, reporting whether the watcher is still alive. -/
private def notifyWatcher (watcher : Watcher) (status : ServingStatus) : IO Bool := do
  match ← (watcher.producer.send { status := status }).run with
  | .ok () => pure true
  | .error _ => pure false

private def notifyWatchers (state : State) (service : String) (status : ServingStatus) :
    IO (Array Watcher) := do
  let mut alive := #[]
  for watcher in state.watchers do
    if watcher.service == service then
      if ← notifyWatcher watcher status then
        alive := alive.push watcher
    else
      alive := alive.push watcher
  pure alive

/-- Set the serving status of `service`; notifies watchers if the status changed. -/
def setStatus (health : Service) (service : String) (status : ServingStatus) : IO Unit := do
  health.state.atomically do
    let state ← get
    if state.terminal then
      pure ()
    else
      let previous := lookupStatus? state service
      if previous == some status then
        pure ()
      else
        -- Sending to these unbounded channels completes without waiting for a
        -- consumer. Keeping it inside the state mutex gives every watcher one
        -- total order: initial value, status updates, then cancellation.
        let watchers ← notifyWatchers state service status
        set {
          state with
          statuses := setStatusEntry state.statuses service status
          watchers := watchers
        }

def setServing (health : Service) (service : String) : IO Unit :=
  health.setStatus service .serving

def setNotServing (health : Service) (service : String) : IO Unit :=
  health.setStatus service .notServing

/--
Atomically enter the terminal state: mark every registered service (including
the overall server status) NOT_SERVING and ignore all later status mutations.
-/
def shutdown (health : Service) : IO Unit := do
  health.state.atomically do
    let state ← get
    if state.terminal then
      pure ()
    else
      let mut watchers := state.watchers
      for entry in state.statuses do
        if entry.2 != .notServing then
          watchers ← notifyWatchers { state with watchers := watchers }
            entry.1 .notServing
      set {
        state with
        statuses := state.statuses.map fun (entry : String × ServingStatus) =>
          (entry.1, .notServing)
        watchers := watchers
        terminal := true
      }

def checkStatus? (health : Service) (service : String) : IO (Option ServingStatus) := do
  health.state.atomically do
    pure (lookupStatus? (← get) service)

/-- Number of currently retained Watch streams, for bounded-owner diagnostics. -/
def activeWatcherCount (health : Service) : IO Nat := do
  health.state.atomically do
    pure (← get).watchers.size

def check (health : Service) (request : CheckRequest) : GrpcM CheckResponse := do
  match ← health.checkStatus? request.service with
  | some status => pure { status := status }
  | none => throw (Status.error .notFound s!"unknown service: {request.service}")

private def removeWatcher (health : Service) (id : WatcherId) : IO Unit := do
  health.state.atomically do
    modify fun state => {
      state with watchers := state.watchers.filter fun watcher => watcher.id != id
    }

def watch (health : Service) (request : CheckRequest) : GrpcM (MessageStream CheckResponse) := do
  let producer ← MessageStream.pipe (α := CheckResponse) (capacity := none)
  let registered ← health.state.atomically do
    let state ← get
    let id : WatcherId := { value := state.nextWatcherId }
    let watcher : Watcher := {
      id := id
      service := request.service
      producer := producer
    }
    -- Publish the initial status before the watcher becomes visible. A
    -- concurrent setStatus therefore cannot enqueue a newer value first.
    match ← (producer.send {
        status := (lookupStatus? state request.service).getD .serviceUnknown
      }).run with
    | .error status => pure (.error status)
    | .ok () =>
        set {
          state with
          watchers := state.watchers.push watcher
          nextWatcherId := state.nextWatcherId + 1
        }
        pure (.ok id)
  let id ← GrpcM.ofExcept registered
  let stream := producer.stream
  pure {
    recv? := stream.recv?
    cancel := do
      -- Removal precedes channel close and is idempotent. Once this returns,
      -- no retained producer can be reached by a later status update.
      health.removeWatcher id
      producer.cancel
  }

def registerWith (health : Service) (registry : Registry) : Registry :=
  registry
    |>.registerUnaryCodec checkMethodName CheckRequest.decode CheckResponse.encode health.check
    |>.registerServerStreamingStreamCodec watchMethodName CheckRequest.decode CheckResponse.encode
      health.watch

end Service

/-- Create a health service and register its handlers, returning the service handle. -/
def register (registry : Registry) : IO (Service × Registry) := do
  let health ← Service.new
  pure (health, health.registerWith registry)

end Health
end Services
end Grpc
