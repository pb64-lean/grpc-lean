module

public import Std.Sync.Mutex
public import Http2.Connection
public import Grpc.Http2.Grpc
import Std.Async.Timer
import Std.Data.HashMap
import Std.Sync.Channel

public section

namespace Grpc
namespace Http2
namespace Connection

private def ofHttp2 {α} (result : Except _root_.Http2.Error α) : Except Status α :=
  match result with
  | .ok value => .ok value
  | .error error => .error (Status.ofHttp2Error error)

/-- A failure crossing the gRPC/HTTP/2 connection-owner boundary.  Protocol
errors retain their exact RFC error code and scope; application failures remain
gRPC statuses and become INTERNAL_ERROR only when they terminate a connection. -/
inductive ProcessError where
  | http2 (error : _root_.Http2.Error)
  | application (status : Status)
  deriving Inhabited, Repr

namespace ProcessError

def errorCode : ProcessError → _root_.Http2.ErrorCode
  | .http2 error => error.code
  | .application _ => .internalError

def message : ProcessError → String
  | .http2 error => error.message
  | .application status => status.messageD

end ProcessError

private structure ScheduledDeadline where
  deadline : Nat
  expire : IO Unit
  fail : IO Unit

private structure DeadlineSchedulerState where
  nextId : Nat := 0
  /-- The timer target currently owned by the scheduler.  It may be earlier
  than every live registration after a fast call unregisters; that is harmless
  and avoids rearming the shared timer on every RPC. -/
  scheduled : Option Nat := none
  registrations : Std.HashMap Nat ScheduledDeadline := {}
  /-- Header-authorized calls that are still waiting for END_STREAM.  These
  are keyed by HTTP/2 stream id so frame transitions can update them in place
  instead of allocating one timer task (or accumulating stale registrations)
  per request. -/
  pendingBodies : Std.HashMap Nat ScheduledDeadline := {}
  failed : Bool := false
  deriving Inhabited

/-- One independent deadline owner per HTTP/2 connection.  Registrations are
cheap hash-map operations; a single native timer services all active calls.
The task is independent of frame processing and the connection-state mutex, so
deadline delivery does not depend on the socket loop returning from user IO. -/
structure DeadlineScheduler where
  private state : Std.Mutex DeadlineSchedulerState
  private wake : Std.Channel Unit
  private stopped : IO.Ref Bool
  private task : IO.Ref (Option (Task (Except IO.Error Unit)))

namespace DeadlineScheduler

private inductive Event where
  | wake
  | deadline

private def millisecondsUntil (deadline : Nat) : IO Nat := do
  let now ← IO.monoNanosNow
  if deadline <= now then
    pure 0
  else
    pure ((deadline - now + 999999) / 1000000)

private def nextEvent (scheduler : DeadlineScheduler) (deadline? : Option Nat) :
    Std.Async.Async Event := do
  match deadline? with
  | none =>
      discard <| Std.Async.Async.ofTask (← scheduler.wake.recv)
      pure .wake
  | some deadline =>
      let remaining ← millisecondsUntil deadline
      if remaining == 0 then
        pure .deadline
      else
        let timer ← Std.Async.Selector.sleep
          (Std.Time.Millisecond.Offset.ofNat remaining)
        Std.Async.Selectable.one #[
          Std.Async.Selectable.case scheduler.wake.recvSelector fun _ => pure Event.wake,
          Std.Async.Selectable.case timer fun _ => pure Event.deadline
        ]

private def expireDue (scheduler : DeadlineScheduler) : IO Unit := do
  let now ← IO.monoNanosNow
  let expirations ← scheduler.state.atomically do
    let state ← get
    let due := state.registrations.valuesArray.filter fun item => item.deadline <= now
    let future := state.registrations.filter fun _ item => item.deadline > now
    let pendingDue := state.pendingBodies.valuesArray.filter fun item => item.deadline <= now
    let pendingFuture := state.pendingBodies.filter fun _ item => item.deadline > now
    let scheduled := future.fold (init := none) fun nearest _ item =>
      match nearest with
      | none => some item.deadline
      | some deadline => some (Nat.min deadline item.deadline)
    let scheduled := pendingFuture.fold (init := scheduled) fun nearest _ item =>
      match nearest with
      | none => some item.deadline
      | some deadline => some (Nat.min deadline item.deadline)
    set {
      state with
      scheduled := scheduled,
      registrations := future,
      pendingBodies := pendingFuture
    }
    pure ((due.append pendingDue).map (·.expire))
  for expiration in expirations do
    try
      expiration
    catch _ =>
      pure ()

private def failAll (scheduler : DeadlineScheduler) : IO Unit := do
  let failures ← scheduler.state.atomically do
    let state ← get
    set {
      state with
      scheduled := none,
      registrations := {},
      pendingBodies := {},
      failed := true
    }
    pure ((state.registrations.valuesArray.append state.pendingBodies.valuesArray).map (·.fail))
  scheduler.stopped.set true
  for fail in failures do
    try
      fail
    catch _ =>
      pure ()

private partial def loop (scheduler : DeadlineScheduler) : Std.Async.Async Unit := do
  if ← scheduler.stopped.get then
    pure ()
  else
    let scheduled ← scheduler.state.atomically do
      pure (← get).scheduled
    match ← nextEvent scheduler scheduled with
    | .wake => loop scheduler
    | .deadline =>
        expireDue scheduler
        loop scheduler

/-- Start an independent per-connection deadline scheduler. -/
def new : IO DeadlineScheduler := do
  let state ← Std.Mutex.new (default : DeadlineSchedulerState)
  let wake ← Std.Channel.new
  let stopped ← IO.mkRef false
  let taskRef ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
  let scheduler : DeadlineScheduler := {
    state := state,
    wake := wake,
    stopped := stopped,
    task := taskRef
  }
  let task ← Std.Async.Async.toIO do
    try
      loop scheduler
    catch _ =>
      -- A failed shared timer must never leave live calls waiting forever.
      -- Fail their normal cancellation race and make future registration
      -- fail closed; the connection owner still retains and joins each child.
      failAll scheduler
  taskRef.set (some task)
  pure scheduler

/-- Register a one-shot absolute deadline and return its idempotent release. -/
def register (scheduler : DeadlineScheduler) (deadline : Nat)
    (expire fail : IO Unit) :
    IO (IO Unit) := do
  let (id?, shouldWake) ← scheduler.state.atomically do
    let state ← get
    if state.failed then
      pure (none, false)
    else
      let id := state.nextId
      let shouldWake := match state.scheduled with
        | none => true
        | some scheduled => deadline < scheduled
      set {
        state with
        nextId := id + 1,
        scheduled := if shouldWake then some deadline else state.scheduled,
        registrations := state.registrations.insert id {
          deadline := deadline,
          expire := expire,
          fail := fail
        }
      }
      pure (some id, shouldWake)
  match id? with
  | none =>
      fail
      pure (pure ())
  | some id =>
      if shouldWake then
        discard <| scheduler.wake.trySend ()
      pure do
        scheduler.state.atomically do
          modify fun state => {
            state with registrations := state.registrations.erase id
          }

/-- Reconcile the one timer registration owned by an incomplete request body.
Unchanged DATA frames are a no-op; completion/reset erases by stream id, and a
newly authorized body installs exactly one callback on the connection timer. -/
private def reconcilePendingBody (scheduler : DeadlineScheduler) (streamId : Nat)
    (deadline? : Option Nat) (expire fail : Nat → IO Unit) : IO Unit := do
  let (failedDeadline?, shouldWake) ← scheduler.state.atomically do
    let state ← get
    match deadline? with
    | none =>
        set { state with pendingBodies := state.pendingBodies.erase streamId }
        pure (none, false)
    | some deadline =>
        if state.failed then
          pure (some deadline, false)
        else
          match state.pendingBodies.get? streamId with
          | some existing =>
              if existing.deadline == deadline then
                pure (none, false)
              else
                let shouldWake := state.scheduled.all fun scheduled => deadline < scheduled
                set {
                  state with
                  scheduled := if shouldWake then some deadline else state.scheduled,
                  pendingBodies := state.pendingBodies.insert streamId {
                    deadline := deadline,
                    expire := expire deadline,
                    fail := fail deadline
                  }
                }
                pure (none, shouldWake)
          | none =>
              let shouldWake := state.scheduled.all fun scheduled => deadline < scheduled
              set {
                state with
                scheduled := if shouldWake then some deadline else state.scheduled,
                pendingBodies := state.pendingBodies.insert streamId {
                  deadline := deadline,
                  expire := expire deadline,
                  fail := fail deadline
                }
              }
              pure (none, shouldWake)
  match failedDeadline? with
  | some deadline =>
      try fail deadline catch _ => pure ()
  | none =>
      if shouldWake then
        discard <| scheduler.wake.trySend ()

/-- Stop and join the exact scheduler task. -/
def shutdown (scheduler : DeadlineScheduler) : Std.Async.Async Unit := do
  -- Close registration before waking/joining.  Otherwise a call racing
  -- shutdown could register successfully after the scheduler task had exited
  -- and wait forever for a deadline that no task can deliver.
  failAll scheduler
  discard <| scheduler.wake.trySend ()
  match ← scheduler.task.modifyGet fun task? => (task?, none) with
  | none => pure ()
  | some task =>
      try
        discard <| Std.Async.Async.ofAsyncTask task
      catch _ =>
        pure ()

end DeadlineScheduler

structure StreamState where
  streamId : Nat
  /-- Aggregate request body bytes retained for handlers that do not consume a
  live `MessageStream`. -/
  body : ByteArray := ByteArray.empty
  /-- Incremental framing validator for the retained aggregate body. Completed
  messages stay in `body`; only the residual prefix/payload is retained here. -/
  decodeState : Message.DecodeState := {}
  /-- Size of the normalized identity-framed body represented by complete
  messages already retained in `body`. This bounds gzip expansion before an
  aggregate handler is allowed to run. -/
  retainedDecodedBytes : Nat := 0
  peerEnded : Bool := false
  requestMetadata : Option _root_.Http2.Headers := none
  /-- Validated header facts parsed once when END_HEADERS completed. -/
  requestPreflight : Option Headers.RequestPreflight := none
  /-- The registry entry accepted by request-header authorization at
  END_HEADERS.  `none` means the header block has not been authorized, so the
  stream must not dispatch. -/
  authorizedEntry? : Option MethodEntry := none
  /-- Monotonic arrival time of the frame that completed the header block. -/
  endHeadersReceivedAt : Option Nat := none
  /-- Absolute request deadline captured when END_HEADERS was received. -/
  deadline : Option Nat := none
  deriving Inhabited

structure ActiveRequestStream where
  streamId : Nat
  producer : MessageStream.Producer ByteArray
  decodeState : Message.DecodeState := {}
  usesGzip : Bool := false
  /-- Wire size of each decoded-but-unconsumed message; the matching stream
  WINDOW_UPDATE is granted only when the handler consumes the message. -/
  pendingRequestCredits : Array Nat := #[]
  /-- Normalized identity-framed bytes retained by the producer queue. Kept
  parallel to `pendingRequestCredits` so consumption releases both budgets. -/
  pendingRequestDecodedBytes : Array Nat := #[]
  retainedDecodedBytes : Nat := 0

private structure DeadlineChild where
  cancel? : Option (IO Unit)
  expire? : Option (IO Unit)
  join : Std.Async.Async Unit

structure ActiveDispatch where
  streamId : Nat
  task : Task (Except IO.Error Unit)
  cancelled : IO.Ref Bool
  requestStreamCancel : IO.Ref (Option (IO Unit))
  responseStreamCancel : IO.Ref (Option (IO Unit))
  /-- Exact handler/stream-receive child currently owned by a timed dispatch. -/
  private deadlineChild : Option (IO.Ref (Option DeadlineChild)) := none

/-- A custom request-header authorizer currently owned by the connection.
The callback itself runs without the connection-state mutex.  Keeping its
cancellation flag and exact child handle here lets shutdown signal it without
waiting for arbitrary user IO to release that mutex. -/
structure ActiveAuthorization where
  streamId : Nat
  cancelled : IO.Ref Bool
  private deadlineChild : IO.Ref (Option DeadlineChild)

/-- Advertised per-stream receive window (`SETTINGS_INITIAL_WINDOW_SIZE`): the
default 4 MiB gRPC message limit, its 5-byte frame prefix, and a 64 KiB margin.
A whole maximum-size message must fit inside one stream window, because
credit-on-consume flow control only replenishes the stream window once the
handler has consumed a *complete* message; see
`defaultStreamWindow_admits_max_message` for the deadlock-freedom argument. -/
@[expose] def defaultStreamWindow : Nat := 4194304 + 5 + 65536

/-- Upper bound on buffered application DATA awaiting peer flow-control credit.
It admits one maximum-size default message together with its gRPC wire prefix. -/
def maxPendingOutboundBytes : Nat :=
  Message.prefixLength + Message.defaultMaxDecompressedSize

/-- One application output transition waiting to be committed by the HTTP/2
state machine.  Header compression, frame splitting, stream phases, and flow
control remain exclusively in `Http2.Connection.State`. -/
inductive OutboundCommand where
  | headers (streamId : Nat) (fields : _root_.Http2.Headers) (endStream : Bool)
  | data (streamId : Nat) (bytes : ByteArray) (endStream : Bool)
  deriving Inhabited

namespace OutboundCommand

def streamId : OutboundCommand → Nat
  | .headers streamId _ _ | .data streamId _ _ => streamId

def bufferedBytes : OutboundCommand → Nat
  | .headers _ _ _ => 0
  | .data _ bytes _ => bytes.size

end OutboundCommand

/-- Per-stream semantic output.  Commands remain ordered within a stream;
the outer array is a round-robin scheduler cursor across streams. -/
structure PendingResponseQueue where
  streamId : Nat
  commands : Array OutboundCommand := #[]
  deriving Inhabited

structure State where
  /-- The complete RFC 9113 connection state.  The surrounding fields own
  only gRPC request/handler lifecycle and application buffering. -/
  protocol : _root_.Http2.Connection.State := Id.run do
    let protocol := _root_.Http2.Connection.initial .server {
      initialWindowSize := defaultStreamWindow
    }
    pure {
      protocol with
      hpackEncode := _root_.Http2.Hpack.withoutDynamicTable protocol.hpackEncode
    }
  /-- Sticky once forced connection teardown has selected cancellation.  Work
  prepared before that selection must not publish a new handler afterward. -/
  closing : Bool := false
  /-- A terminal non-NO_ERROR GOAWAY has been elected for this connection.
  Graceful GOAWAY does not set this bit, so one later fatal GOAWAY may tighten
  the reason while retaining a non-increasing last-stream identifier. -/
  terminalGoAwaySent : Bool := false
  /-- Per-stream ordered gRPC response operations not yet admitted by peer
  flow-control. These are semantic operations rather than pre-encoded frames. -/
  pendingResponses : Array PendingResponseQueue := #[]
  /-- Connection-wide retained DATA budget, normally one configured maximum
  response message plus its gRPC prefix. -/
  maxPendingResponseBytes : Nat := maxPendingOutboundBytes
  streams : Array StreamState := #[]
  activeRequestStreams : Array ActiveRequestStream := #[]
  activeDispatches : Array ActiveDispatch := #[]
  activeAuthorizations : Array ActiveAuthorization := #[]
  /-- Requests detached from inbound buffering whose gated handler task has not
  yet been published in `activeDispatches`.  This is an ownership token, not
  merely a diagnostic: graceful drain must count it, and a concurrent stream
  reset removes it so the later publication attempt cannot start a handler for
  a stream the peer already closed. -/
  pendingDispatchPublications : Array Nat := #[]
  pendingKeepalivePing : Option ByteArray := none
  /-- Independent owner for active handler deadlines.  Direct state-machine
  users may leave this absent and retain the per-call timer fallback. -/
  deadlineScheduler : Option DeadlineScheduler := none
  deriving Inhabited

def initialState (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : State :=
  let protocol := _root_.Http2.Connection.initial .server {
      maxConcurrentStreams := maxConcurrentStreams,
      initialWindowSize := initialWindowSize,
      maxHeaderListSize := maxHeaderListSize
    }
  {
    (default : State) with
    protocol := {
      protocol with
      hpackEncode := _root_.Http2.Hpack.withoutDynamicTable protocol.hpackEncode
    }
  }

def isDrainedAfterOutboundGoAway (state : State) : Bool :=
  match state.protocol.localGoAwayLastStream? with
  | none => false
  | some _ =>
      state.protocol.streams.all (fun stream => stream.phase == .closed)
        && state.streams.isEmpty
        && state.activeRequestStreams.isEmpty
        && state.activeDispatches.isEmpty
        && state.activeAuthorizations.isEmpty
        && state.pendingDispatchPublications.isEmpty
        && state.pendingResponses.isEmpty

private def findStream? (streams : Array StreamState) (streamId : Nat) : Option StreamState :=
  streams.find? (fun stream => stream.streamId == streamId)

/-- Allocation-building stream-removal specification.  The executable path
below is compared against this definition over empty, absent, duplicate, and
ordered targets. -/
private def removeStreamReference (streams : Array StreamState) (streamId : Nat) : Array StreamState :=
  streams.filter (fun stream => stream.streamId != streamId)

/-- Consuming order-preserving filter specialized to stream ids.  `eraseIdx`
back-shifts and pops in place when the array is uniquely owned.  Continuing at
the same index after an erase removes adjacent and non-adjacent duplicates, so
this retains the reference filter's behavior without relying on `WellFormed`'s
stream-id uniqueness.  Each step either retains or erases one original entry,
which makes the original array size sufficient structural recursion fuel. -/
private def removeStreamErasingFrom :
    Nat → Array StreamState → Nat → Nat → Array StreamState
  | 0, streams, _, _ => streams
  | fuel + 1, streams, streamId, index =>
      if h : index < streams.size then
        if streams[index].streamId == streamId then
          removeStreamErasingFrom fuel (streams.eraseIdx index h) streamId index
        else
          removeStreamErasingFrom fuel streams streamId (index + 1)
      else
        streams

def removeStreamErasing (streams : Array StreamState) (streamId : Nat) : Array StreamState :=
  removeStreamErasingFrom streams.size streams streamId 0

/-- Remove every state for `streamId` without reordering retained streams.
The logical definition remains `Array.filter`; generated code uses the
consuming erase implementation. -/
@[implemented_by removeStreamErasing]
def removeStream (streams : Array StreamState) (streamId : Nat) : Array StreamState :=
  removeStreamReference streams streamId

private def replaceStream (streams : Array StreamState) (stream : StreamState) : Array StreamState :=
  (removeStream streams stream.streamId).push stream

private def activeDispatchesForStream (dispatches : Array ActiveDispatch) (streamId : Nat) :
    Array ActiveDispatch :=
  dispatches.filter (fun dispatch => dispatch.streamId == streamId)

private def removeActiveDispatchesForStream (dispatches : Array ActiveDispatch) (streamId : Nat) :
    Array ActiveDispatch :=
  dispatches.filter (fun dispatch => dispatch.streamId != streamId)

private def removeActiveAuthorizationsForStream
    (authorizations : Array ActiveAuthorization) (streamId : Nat) :
    Array ActiveAuthorization :=
  authorizations.filter (fun authorization => authorization.streamId != streamId)

private def activeAuthorizationsForStream
    (authorizations : Array ActiveAuthorization) (streamId : Nat) :
    Array ActiveAuthorization :=
  authorizations.filter (fun authorization => authorization.streamId == streamId)

def containsStreamId (streamIds : Array Nat) (streamId : Nat) : Bool :=
  streamIds.any (· == streamId)

private def removeStreamId (streamIds : Array Nat) (streamId : Nat) : Array Nat :=
  streamIds.filter (· != streamId)

private def pushUniqueStreamId (streamIds : Array Nat) (streamId : Nat) : Array Nat :=
  if containsStreamId streamIds streamId then
    streamIds
  else
    streamIds.push streamId

private def findActiveRequestStream? (streams : Array ActiveRequestStream) (streamId : Nat) :
    Option ActiveRequestStream :=
  streams.find? (fun stream => stream.streamId == streamId)

private def removeActiveRequestStream (streams : Array ActiveRequestStream) (streamId : Nat) :
    Array ActiveRequestStream :=
  streams.filter (fun stream => stream.streamId != streamId)

private def replaceActiveRequestStream (streams : Array ActiveRequestStream)
    (stream : ActiveRequestStream) : Array ActiveRequestStream :=
  (removeActiveRequestStream streams stream.streamId).push stream

private def pendingResponseBytes (queues : Array PendingResponseQueue) : Nat :=
  queues.foldl (fun total queue =>
    total + queue.commands.foldl (fun subtotal command =>
      subtotal + command.bufferedBytes) 0) 0

private def removePendingResponsesForStream (queues : Array PendingResponseQueue)
    (streamId : Nat) : Array PendingResponseQueue :=
  queues.filter (fun queue => queue.streamId != streamId)

private def enqueueResponse (queues : Array PendingResponseQueue)
    (command : OutboundCommand) : Array PendingResponseQueue :=
  if queues.any (·.streamId == command.streamId) then
    queues.map fun queue =>
      if queue.streamId == command.streamId then
        { queue with commands := queue.commands.push command }
      else
        queue
  else
    queues.push { streamId := command.streamId, commands := #[command] }

private def enqueueResponses (queues : Array PendingResponseQueue)
    (commands : Array OutboundCommand) : Array PendingResponseQueue :=
  commands.foldl enqueueResponse queues

private def replaceQueueHead (queue : PendingResponseQueue)
    (command? : Option OutboundCommand) : PendingResponseQueue :=
  let rest := queue.commands.extract 1 queue.commands.size
  { queue with commands := command?.map (#[·] ++ rest) |>.getD rest }

private def rotateResponseQueue (queues : Array PendingResponseQueue)
    (queue : PendingResponseQueue) : Array PendingResponseQueue :=
  let rest := queues.extract 1 queues.size
  if queue.commands.isEmpty then rest else rest.push queue

/-- Commit queued output in round-robin order. A DATA command without credit
rotates behind other streams, so it cannot block their headers or writable
DATA. Commands within each stream retain their original order. -/
private partial def flushResponses (state : State)
    (emitted : Array _root_.Http2.Frame := #[]) (blocked : Nat := 0) :
    Except Status (State × Array _root_.Http2.Frame) := do
  match (state.pendingResponses[0]? : Option PendingResponseQueue) with
  | none => pure (state, emitted)
  | some queue =>
    match (queue.commands[0]? : Option OutboundCommand) with
    | none =>
        flushResponses { state with pendingResponses :=
          state.pendingResponses.extract 1 state.pendingResponses.size } emitted 0
    | some (OutboundCommand.headers streamId fields endStream) =>
        let (protocol, frames) ← ofHttp2 <|
          _root_.Http2.Connection.sendHeaders state.protocol streamId fields endStream
        let queue := replaceQueueHead queue none
        flushResponses {
          state with
          protocol := protocol
          pendingResponses := rotateResponseQueue state.pendingResponses queue
        } (emitted.append frames) 0
    | some (OutboundCommand.data streamId bytes endStream) =>
        let credit := (_root_.Http2.Connection.outboundCredit? state.protocol streamId).getD 0
        if !bytes.isEmpty && credit == 0 then
          let pendingResponses := rotateResponseQueue state.pendingResponses queue
          if blocked + 1 >= state.pendingResponses.size then
            pure ({ state with pendingResponses := pendingResponses }, emitted)
          else
            flushResponses { state with pendingResponses := pendingResponses }
              emitted (blocked + 1)
        else
          let sendSize := Nat.min bytes.size credit
          let chunk := if sendSize == bytes.size then bytes else bytes.extract 0 sendSize
          let final := sendSize == bytes.size
          let (protocol, frames) ← ofHttp2 <|
            _root_.Http2.Connection.sendData state.protocol streamId chunk (endStream && final)
          let command? := if final then none else
            some (.data streamId (bytes.extract sendSize bytes.size) endStream)
          let queue := replaceQueueHead queue command?
          flushResponses {
            state with
            protocol := protocol
            pendingResponses := rotateResponseQueue state.pendingResponses queue
          } (emitted.append frames) 0

private def queueResponses (state : State) (commands : Array OutboundCommand) :
    Except Status (State × Array _root_.Http2.Frame) := do
  let commandBytes := commands.foldl (fun total command => total + command.bufferedBytes) 0
  if pendingResponseBytes state.pendingResponses + commandBytes >
      state.maxPendingResponseBytes then
    throw (Status.resourceExhausted
      "HTTP/2 outbound buffer limit exceeded: peer is not consuming flow-controlled data")
  flushResponses { state with pendingResponses := enqueueResponses state.pendingResponses commands }

private def emitFrameBatch (emit : Array _root_.Http2.Frame -> IO Unit) (frames : Array _root_.Http2.Frame) :
    IO (Except Status Unit) := do
  if frames.isEmpty then
    pure (.ok ())
  else
    try
      emit frames
      pure (.ok ())
    catch err =>
      pure (.error (Status.ofIOError err))

structure DetachedDispatch where
  request : Transport.ManagedRequest
  entry : MethodEntry
  preflight : Headers.RequestPreflight
  private deadlineScheduler : Option DeadlineScheduler := none

/-- The dispatch family for a request whose body is fed to the handler
incrementally, carrying the authorized handler at its exact shape. -/
inductive RequestStreamingKind where
  | clientStreaming (handler : ClientStreamingStreamHandler)
  | bidirectionalStreaming (handler : BidirectionalStreamingStreamHandler)

structure RequestStreamingDispatch where
  streamId : Nat
  metadata : _root_.Http2.Headers
  kind : RequestStreamingKind
  preflight : Headers.RequestPreflight
  requestError : Option Status := none
  closeImmediately : Bool := false
  /-- Absolute request deadline captured at END_HEADERS. -/
  deadline : Option Nat := none
  private deadlineScheduler : Option DeadlineScheduler := none

structure RequestStreamFeed where
  producer : MessageStream.Producer ByteArray
  messages : Array ByteArray := #[]
  error : Option Status := none
  close : Bool := false

/-- A validated custom header-authorization phase that must run after the
connection-state transition has been published.  In particular, no user IO
runs while the connection-state mutex is held. -/
private structure PendingAuthorization where
  streamId : Nat
  entry : MethodEntry
  metadata : _root_.Http2.Headers
  preflight : Headers.RequestPreflight
  deadline : Option Nat
  endStream : Bool
  scheduler : Option DeadlineScheduler
  active : ActiveAuthorization

structure SharedFrameResult where
  emitted : Array _root_.Http2.Frame := #[]
  detached : Option DetachedDispatch := none
  requestStreaming : Option RequestStreamingDispatch := none
  requestFeeds : Array RequestStreamFeed := #[]
  cancelDispatches : Array ActiveDispatch := #[]
  cancelAuthorizations : Array ActiveAuthorization := #[]
  private pendingAuthorization : Option PendingAuthorization := none

/-- Incremental request-body dispatch applies exactly to entries whose shape
consumes a `MessageStream`; aggregate shapes buffer the body instead. -/
private def requestStreamingKind? (entry : MethodEntry) : Option RequestStreamingKind :=
  match entry with
  | { shape := .clientStreamingStream, handler, .. } => some (.clientStreaming handler)
  | { shape := .bidirectionalStreamingStream, handler, .. } =>
      some (.bidirectionalStreaming handler)
  | _ => none

private def retainedDecodedRequestLimit (registry : Registry) : Nat :=
  Message.prefixLength +
    registry.maxReceiveMessageSize.getD Message.defaultMaxDecompressedSize

private def protocolDispatchForStream (state : State) (streamId : Nat) :
    Except Status (State × Option DetachedDispatch × Option RequestStreamingDispatch) := do
  let stream ← match findStream? state.streams streamId with
    | some stream => pure stream
    | none => throw (Status.internal s!"unknown HTTP/2 stream {streamId}")
  let entry ← match stream.authorizedEntry? with
    | some entry => pure entry
    | none => throw (Status.internal "request dispatch attempted before header authorization")
  let metadata ← match stream.requestMetadata with
    | some metadata => pure metadata
    | none => throw (Status.internal "authorized request metadata was not retained")
  let preflight ← match stream.requestPreflight with
    | some preflight => pure preflight
    | none => throw (Status.internal "authorized request preflight was not retained")
  match requestStreamingKind? entry with
  | some kind =>
      let state := {
        state with
        streams := removeStream state.streams streamId,
        pendingDispatchPublications :=
          pushUniqueStreamId state.pendingDispatchPublications streamId
      }
      pure (state, none, some {
        streamId := streamId,
        metadata := metadata,
        kind := kind,
        preflight := preflight,
        closeImmediately := stream.peerEnded,
        deadline := stream.deadline,
        deadlineScheduler := state.deadlineScheduler
      })
  | none =>
      if stream.peerEnded then
        let request : Transport.ManagedRequest := {
          streamId := stream.streamId,
          metadata := metadata,
          deadline := stream.deadline,
          body := stream.body
        }
        let state := {
          state with
          streams := removeStream state.streams streamId,
          pendingDispatchPublications :=
            pushUniqueStreamId state.pendingDispatchPublications streamId
        }
        pure (state, some {
          request := request,
          entry := entry,
          preflight := preflight,
          deadlineScheduler := state.deadlineScheduler
        }, none)
      else
        pure (state, none, none)

/-- Pure state transition for a request rejected at completed request
headers: the buffered stream is dropped and the stream id is either forgotten
entirely (the request already carried END_STREAM) or put in drain-only mode
so later DATA is consumed without dispatch.  See the authorization-before-body
properties section at the end of this file for the theorems about
this transition. -/
private def decodeActiveRequestBytes (registry : Registry) (active : ActiveRequestStream)
    (bytes : ByteArray) (endStream : Bool) :
    Except Status (ActiveRequestStream × Array ByteArray × Bool) := do
  let decoded ← Message.decodeChunkWithLimit registry.maxReceiveMessageSize
    active.decodeState bytes
  let retainedLimit := retainedDecodedRequestLimit registry
  let maxMessageSize :=
    registry.maxReceiveMessageSize.getD Message.defaultMaxDecompressedSize
  let mut messages : Array ByteArray := #[]
  let mut decodedSizes : Array Nat := #[]
  let mut retainedDecodedBytes := active.retainedDecodedBytes
  -- Decompress and admit one message at a time. Building the whole decoded
  -- batch before checking its total would let a tiny compressed DATA frame
  -- transiently allocate many maximum-sized messages.
  for message in decoded.messages do
    let decompressed ← Message.decompress active.usesGzip maxMessageSize message
    let decodedSize := Message.prefixLength + decompressed.data.size
    if retainedDecodedBytes + decodedSize > retainedLimit then
      throw (Status.resourceExhausted
        s!"gRPC streaming request exceeds retained decoded-byte limit {retainedLimit}")
    retainedDecodedBytes := retainedDecodedBytes + decodedSize
    messages := messages.push decompressed.data
    decodedSizes := decodedSizes.push decodedSize
  if endStream && !decoded.buffered.isEmpty then
    throw (Status.internal "incomplete gRPC message")
  let active := {
    active with
    decodeState := { buffered := decoded.buffered },
    pendingRequestCredits := active.pendingRequestCredits.append
      (decoded.messages.map fun message => Message.prefixLength + message.data.size),
    pendingRequestDecodedBytes := active.pendingRequestDecodedBytes.append decodedSizes,
    retainedDecodedBytes := retainedDecodedBytes
  }
  pure (active, messages, endStream)

private def responseHeaders (gzip : Bool) (metadata : _root_.Http2.Headers) :
    _root_.Http2.Headers :=
  let base := if gzip then
      Headers.responseHeaders.insert "grpc-encoding" Headers.gzipEncoding
    else
      Headers.responseHeaders
  _root_.Http2.Headers.append base metadata

private def terminalHeaders (status : Status) (metadata trailers : _root_.Http2.Headers) :
    _root_.Http2.Headers :=
  _root_.Http2.Headers.append
    (_root_.Http2.Headers.append Headers.responseHeaders metadata)
    (Headers.trailers status trailers)

private def unaryResponseCommands (streamId : Nat) (response : UnaryResponse)
    (gzip : Bool := false) : Except Status (Array OutboundCommand) := do
  if !response.status.isOk then
    pure #[.headers streamId (terminalHeaders response.status response.metadata response.trailers) true]
  else
    let message ← Message.encode
      (if gzip then Message.gzipped response.data else { data := response.data })
    pure #[
      .headers streamId (responseHeaders gzip response.metadata) false,
      .data streamId message false,
      .headers streamId (Headers.trailers response.status response.trailers) true
    ]

private def httpStatusCommands (streamId : Nat) (statusCode : String) : Array OutboundCommand :=
  #[.headers streamId (_root_.Http2.Headers.empty.insert ":status" statusCode) true]

private def queueResponsesShared (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (commands : Array OutboundCommand) :
    IO (Except Status Unit) := do
  let emitted? ← stateMutex.atomically do
    let state ← get
    if state.closing then
      pure (Except.error (Status.cancelled "HTTP/2 connection is closing"))
    else
      match queueResponses state commands with
      | .error status => pure (.error status)
      | .ok (state, emitted) =>
          set state
          pure (.ok emitted)
  match emitted? with
  | .error status => pure (.error status)
  | .ok emitted => emitFrameBatch emit emitted

private def emitUnaryResponseShared (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (streamId : Nat)
    (response : UnaryResponse) (gzip : Bool := false) : IO (Except Status Unit) := do
  match unaryResponseCommands streamId response gzip with
  | .error status => pure (.error status)
  | .ok commands => queueResponsesShared stateMutex emit commands

private partial def emitStreamingMessagesShared (registry : Registry)
    (stateMutex : Std.Mutex State) (emit : Array _root_.Http2.Frame -> IO Unit)
    (streamId : Nat) (stream : MessageStream ByteArray) (gzip : Bool)
    (deadline : Option Nat) (runtime? : Option DeadlineRuntime) :
    Std.Async.Async (Except Status (Option Status)) := do
  match ← Registry.recvWithDeadlineUntilAsync deadline stream runtime? with
  | .error status => pure (.ok (some status))
  | .ok none => pure (.ok none)
  | .ok (some data) =>
      match Message.encode (if gzip then Message.gzipped data else { data := data }) with
      | .error status => pure (.ok (some status))
      | .ok bytes =>
          match ← queueResponsesShared stateMutex emit #[.data streamId bytes false] with
          | .error status => pure (.error status)
          | .ok () =>
              emitStreamingMessagesShared registry stateMutex emit streamId stream gzip
                deadline runtime?

private def finishStreamingResponseShared (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (streamId : Nat)
    (stream : MessageStream ByteArray) (status : Status)
    (trailers : _root_.Http2.Headers) (streamStatus? : Option Status) :
    Std.Async.Async (Except Status Unit) := do
  let result ← queueResponsesShared stateMutex emit
    #[.headers streamId (Headers.trailers status trailers) true]
  if streamStatus?.isSome then
    try discard <| stream.cancel.run catch _ => pure ()
  pure result

private def emitStreamingResponseShared (registry : Registry)
    (stateMutex : Std.Mutex State) (emit : Array _root_.Http2.Frame -> IO Unit)
    (streamId : Nat) (response : ServerStreamingStreamResponse) (gzip : Bool)
    (deadline : Option Nat) (runtime? : Option DeadlineRuntime) :
    Std.Async.Async (Except Status Unit) := do
  if !response.status.isOk then
    -- A non-OK final status does not erase messages already produced by a
    -- server stream.  Peek once so an actually empty error response can still
    -- use trailers-only form, while a nonempty response sends its messages
    -- before the final non-OK trailers.
    match ← Registry.recvWithDeadlineUntilAsync deadline response.messages runtime? with
    | .error status =>
        let result ← queueResponsesShared stateMutex emit
          #[.headers streamId (terminalHeaders status response.metadata response.trailers) true]
        try discard <| response.messages.cancel.run catch _ => pure ()
        pure result
    | .ok none =>
        queueResponsesShared stateMutex emit
          #[.headers streamId
            (terminalHeaders response.status response.metadata response.trailers) true]
    | .ok (some firstMessage) =>
        match ← queueResponsesShared stateMutex emit
            #[.headers streamId (responseHeaders gzip response.metadata) false] with
        | .error status => pure (.error status)
        | .ok () =>
            match Message.encode
                (if gzip then Message.gzipped firstMessage else { data := firstMessage }) with
            | .error status => pure (.error status)
            | .ok bytes =>
                match ← queueResponsesShared stateMutex emit #[.data streamId bytes false] with
                | .error status => pure (.error status)
                | .ok () =>
                    match ← emitStreamingMessagesShared registry stateMutex emit streamId
                        response.messages gzip deadline runtime? with
                    | .error status => pure (.error status)
                    | .ok streamStatus? =>
                        finishStreamingResponseShared stateMutex emit streamId response.messages
                          (streamStatus?.getD response.status) response.trailers streamStatus?
  else
    match ← queueResponsesShared stateMutex emit
        #[.headers streamId (responseHeaders gzip response.metadata) false] with
    | .error status => pure (.error status)
    | .ok () =>
        match ← emitStreamingMessagesShared registry stateMutex emit streamId response.messages
            gzip deadline runtime? with
        | .error status => pure (.error status)
        | .ok streamStatus? =>
            let status := streamStatus?.getD response.status
            finishStreamingResponseShared stateMutex emit streamId response.messages status
              response.trailers streamStatus?

private def pendingDeadlineStream (state : State) (stream : StreamState) : Bool :=
  stream.deadline.isSome
    && stream.authorizedEntry?.isSome
    && !containsStreamId state.pendingDispatchPublications stream.streamId
    && !state.activeDispatches.any (fun dispatch => dispatch.streamId == stream.streamId)

private def pendingDeadlineForStream? (state : State) (streamId : Nat) : Option Nat :=
  match findStream? state.streams streamId with
  | some stream =>
      if pendingDeadlineStream state stream then stream.deadline else none
  | none => none

private def takeDeadlineChildExpiry
    (childRef : IO.Ref (Option DeadlineChild)) : IO (Option (IO Unit)) :=
  childRef.modifyGet fun child? =>
    match child? with
    | none => (none, none)
    | some child =>
        (child.expire?, some { child with cancel? := none, expire? := none })

private def cancelDeadlineChildRef
    (childRef : IO.Ref (Option DeadlineChild)) : IO Unit := do
  let cancel? ← childRef.modifyGet fun child? =>
    match child? with
    | none => (none, none)
    | some child =>
        (child.cancel?, some { child with cancel? := none, expire? := none })
  match cancel? with
  | none => pure ()
  | some cancel =>
      try
        cancel
      catch _ =>
        pure ()

private def registerDeadlineChild (childRef : IO.Ref (Option DeadlineChild))
    (scheduler? : Option DeadlineScheduler) (deadline : Nat)
    (cancel expire : IO Unit) (join : Std.Async.Async Unit) : IO (IO Unit) := do
  childRef.set (some { cancel? := some cancel, expire? := some expire, join := join })
  let unregisterDeadline ← match scheduler? with
    | none => pure (pure ())
    | some scheduler =>
        let expireFromScheduler : IO Unit := do
          match ← takeDeadlineChildExpiry childRef with
          | none => pure ()
          | some expire => expire
        let failFromScheduler : IO Unit := cancelDeadlineChildRef childRef
        scheduler.register deadline expireFromScheduler failFromScheduler
  -- Peer/shutdown cancellation may race the scheduler registration.  Install
  -- timer release into the same one-shot cancellation callback; if that
  -- callback was already taken, release the just-published registration now.
  let cancellationOwned ← childRef.modifyGet fun child? =>
    match child? with
    | some child =>
        match child.cancel? with
        | some cancel =>
            (true, some { child with cancel? := some do unregisterDeadline; cancel })
        | none => (false, some child)
    | none => (false, none)
  unless cancellationOwned do
    unregisterDeadline
  pure do
    unregisterDeadline
    childRef.set none

private def nearerDeadline (current candidate : Option Nat) : Option Nat :=
  match current, candidate with
  | none, deadline => deadline
  | some current, some deadline => some (Nat.min current deadline)
  | some current, none => some current

/-- Earliest deadline among complete headers still waiting for the request
body. The independent scheduler normally owns these too; this value keeps the
connection event-loop timer available as a scheduler fail-safe. -/
def nextPendingDeadline? (state : State) : Option Nat :=
  state.streams.foldl (init := none) fun nearest stream =>
    if pendingDeadlineStream state stream then
      nearerDeadline nearest stream.deadline
    else
      nearest

/-- Deadline for a connection event loop that does not have an independent
scheduler. Managed connections install that scheduler before processing input,
so racing the same absolute instant with another `Selector.sleep` only
allocates a redundant timer. -/
def nextPendingDeadlineFallback? (state : State) : Option Nat :=
  if state.deadlineScheduler.isSome then
    none
  else
    nextPendingDeadline? state

private def terminatePendingDeadlineStream (state : State) (stream : StreamState)
    (status : Status) : Except Status (State × Array _root_.Http2.Frame) := do
  let commands ← unaryResponseCommands stream.streamId
    { status := status, data := ByteArray.empty }
  queueResponses { state with streams := removeStream state.streams stream.streamId } commands

/-- Terminate one exact pending-body generation from the independent scheduler.
The state/deadline checks make timer delivery harmless after END_STREAM, reset,
or another owner has already won. -/
private def terminatePendingDeadlineSharedWith (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame → IO Unit) (streamId expectedDeadline : Nat)
    (status : Status) (requireDue : Bool) : IO (Except Status Unit) := do
  let now ← IO.monoNanosNow
  let prepared : Except Status (Array _root_.Http2.Frame) ← stateMutex.atomically do
    let state ← get
    if state.closing then
      pure (Except.ok #[])
    else
      match findStream? state.streams streamId with
      | none => pure (Except.ok #[])
      | some stream =>
          if !pendingDeadlineStream state stream
              || stream.deadline != some expectedDeadline
              || (requireDue && expectedDeadline > now) then
            pure (Except.ok #[])
          else
            match terminatePendingDeadlineStream state stream status with
            | .error status => pure (.error status)
            | .ok (state, frames) =>
                set state
                pure (.ok frames)
  match prepared with
  | .error status => pure (.error status)
  | .ok frames => emitFrameBatch emit frames

private def reconcilePendingBodyDeadline (scheduler : DeadlineScheduler)
    (stateMutex : Std.Mutex State) (emit : Array _root_.Http2.Frame → IO Unit)
    (streamId : Nat) (deadline? : Option Nat) : IO Unit := do
  scheduler.reconcilePendingBody streamId deadline?
    (fun deadline => do
      discard <| terminatePendingDeadlineSharedWith stateMutex emit streamId deadline
        Deadline.exceededStatus true)
    (fun deadline => do
      -- A broken connection scheduler cannot leave the call live forever.  It
      -- is an internal transport failure rather than an early deadline.
      discard <| terminatePendingDeadlineSharedWith stateMutex emit streamId deadline
        (Status.internal "deadline scheduler failed") false)

private def reconcileCurrentPendingBodyDeadline (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame → IO Unit) (streamId : Nat) : IO Unit := do
  let target ← stateMutex.atomically do
    let state ← get
    pure (state.deadlineScheduler.bind fun scheduler =>
      (pendingDeadlineForStream? state streamId).map fun deadline =>
        (scheduler, deadline))
  match target with
  | none => pure ()
  | some (scheduler, deadline) =>
      reconcilePendingBodyDeadline scheduler stateMutex emit streamId (some deadline)

/-- Expire every header-authorized request whose peer has not completed its
body.  A trailers-only DEADLINE_EXCEEDED response closes the local half while
the remote half remains in drain mode until END_STREAM, preserving HTTP/2
flow-control and concurrent-stream accounting. -/
def expirePendingDeadlinesSharedWith (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) : IO (Except Status Unit) := do
  let now ← IO.monoNanosNow
  let prepared ← stateMutex.atomically do
    let state ← get
    if state.closing then
      pure (Except.ok #[])
    else
      let expired := state.streams.filter fun stream =>
        pendingDeadlineStream state stream
          && stream.deadline.any (fun deadline => deadline <= now)
      let result : Except Status (State × Array _root_.Http2.Frame) :=
        expired.foldlM (init := (state, #[])) fun (state, frames) stream => do
          let (state, terminal) ←
            terminatePendingDeadlineStream state stream Deadline.exceededStatus
          pure (state, frames.append terminal)
      match result with
      | .error status => pure (Except.error status)
      | .ok (state, frames) =>
          set state
          pure (Except.ok frames)
  match prepared with
  | .error status => pure (.error status)
  | .ok frames => emitFrameBatch emit frames

private def cancelStreamRef (streamCancel : IO.Ref (Option (IO Unit))) : IO Unit := do
  -- Taking the callback before invoking arbitrary user IO gives cancellation
  -- exactly-once semantics even when a late response-stream registration races
  -- connection or RST_STREAM teardown.
  match ← streamCancel.modifyGet fun cancel? => (cancel?, none) with
  | none => pure ()
  | some cancel =>
      try
        cancel
      catch _ =>
        pure ()

private def cancelResponseStreamRef (responseStreamCancel : IO.Ref (Option (IO Unit))) : IO Unit :=
  cancelStreamRef responseStreamCancel

private def cancelRequestStreamRef (requestStreamCancel : IO.Ref (Option (IO Unit))) : IO Unit := do
  cancelStreamRef requestStreamCancel

private def joinDeadlineChildRef
    (childRef : IO.Ref (Option DeadlineChild)) : Std.Async.Async Unit := do
  match ← childRef.modifyGet fun child? => (child?, none) with
  | none => pure ()
  | some child => child.join

private def joinDeadlineChildRef?
    (childRef? : Option (IO.Ref (Option DeadlineChild))) : Std.Async.Async Unit := do
  match childRef? with
  | none => pure ()
  | some childRef => joinDeadlineChildRef childRef

private def runPendingAuthorization (registry : Registry)
    (authorization : PendingAuthorization) :
    Std.Async.Async (Except Status MethodEntry) := do
  if ← authorization.active.cancelled.get then
    pure (.error (Status.cancelled "request authorization cancelled"))
  else
    let result ← match authorization.deadline with
      | some _ =>
          let runtime : DeadlineRuntime := {
            externalTimer := true,
            registerTask := fun deadline cancel expire join => do
              let unregister ← registerDeadlineChild
                authorization.active.deadlineChild authorization.scheduler
                deadline cancel expire join
              if ← authorization.active.cancelled.get then
                cancelDeadlineChildRef authorization.active.deadlineChild
              pure unregister
          }
          Registry.runWithDeadlineUntilAsync authorization.deadline
            (registry.authorizeRequestHeaders authorization.entry authorization.metadata)
            (some runtime)
      | none => do
          let task ← IO.asTask do
            try
              registry.authorizeRequestHeaders authorization.entry authorization.metadata |>.run
            catch error =>
              pure (.error (Status.ofIOError error))
          let join : Std.Async.Async Unit := do
            try
              discard <| Std.Async.Async.ofAsyncTask task
            catch _ =>
              pure ()
          authorization.active.deadlineChild.set (some {
            cancel? := some (IO.cancel task),
            expire? := none,
            join := join
          })
          if ← authorization.active.cancelled.get then
            cancelDeadlineChildRef authorization.active.deadlineChild
          let result ← try
              Std.Async.Async.ofAsyncTask task
            catch error =>
              pure (.error (Status.ofIOError error))
          authorization.active.deadlineChild.set none
          pure result
    match result with
    | .error status => pure (.error status)
    | .ok (.reject status) => pure (.error status)
    | .ok (.accept handler) =>
        pure (.ok {
          authorization.entry with
          handler := handler
          requestHeaderHandlerResolver := .registered
        })

/-- Commit an authorization result against current connection state.  The
outbound HPACK encoder is intentionally read only now—not when the callback
started—because other streams may have completed while user IO was running. -/
private def retirePendingAuthorization (stateMutex : Std.Mutex State)
    (authorization : PendingAuthorization) : IO Unit := do
  stateMutex.atomically do
    modify fun state => {
      state with
      activeAuthorizations := removeActiveAuthorizationsForStream
        state.activeAuthorizations authorization.streamId
    }

private def prepareProtocolAuthorization (registry : Registry) (state : State)
    (streamId : Nat) (metadata : _root_.Http2.Headers) (endStream : Bool)
    (receivedAt : Nat) : IO (Except Status (State × SharedFrameResult)) := do
  match Transport.preflightRequest registry metadata with
  | .rejectHttp statusCode =>
      match queueResponses state (httpStatusCommands streamId statusCode) with
      | .error status => pure (.error status)
      | .ok (state, emitted) => pure (.ok (state, { emitted := emitted }))
  | .rejectGrpc status =>
      match unaryResponseCommands streamId { status := status, data := ByteArray.empty } with
      | .error status => pure (.error status)
      | .ok commands =>
          match queueResponses state commands with
          | .error status => pure (.error status)
          | .ok (state, emitted) => pure (.ok (state, { emitted := emitted }))
  | .accept entry preflight =>
      let deadline ← Deadline.fromTimeoutAt? preflight.timeout (some receivedAt)
      let cancelled ← IO.mkRef false
      let deadlineChild ← IO.mkRef (none : Option DeadlineChild)
      let active : ActiveAuthorization := {
        streamId := streamId,
        cancelled := cancelled,
        deadlineChild := deadlineChild
      }
      let stream : StreamState := {
        streamId := streamId,
        peerEnded := endStream,
        requestMetadata := some metadata,
        requestPreflight := some preflight,
        endHeadersReceivedAt := some receivedAt,
        deadline := deadline
      }
      let authorization : PendingAuthorization := {
        streamId := streamId,
        entry := entry,
        metadata := metadata,
        preflight := preflight,
        deadline := deadline,
        endStream := endStream,
        scheduler := state.deadlineScheduler,
        active := active
      }
      pure (.ok ({
        state with
        streams := replaceStream state.streams stream,
        activeAuthorizations := state.activeAuthorizations.push active
      }, { pendingAuthorization := some authorization }))

private def commitProtocolAuthorization (stateMutex : Std.Mutex State)
    (authorization : PendingAuthorization) (decision : Except Status MethodEntry) :
    IO (Except Status SharedFrameResult) := do
  stateMutex.atomically do
    let state ← get
    let owned := state.activeAuthorizations.any fun active =>
      active.streamId == authorization.streamId
    if state.closing || !owned || (← authorization.active.cancelled.get) then
      pure (.ok {})
    else
      let state := {
        state with
        activeAuthorizations := removeActiveAuthorizationsForStream
          state.activeAuthorizations authorization.streamId
      }
      match findStream? state.streams authorization.streamId with
      | none =>
          set state
          pure (.ok {})
      | some stream =>
          match decision with
          | .error status =>
              match unaryResponseCommands authorization.streamId
                  { status := status, data := ByteArray.empty } with
              | .error status => pure (.error status)
              | .ok commands =>
                  match queueResponses
                      { state with streams := removeStream state.streams authorization.streamId }
                      commands with
                  | .error status => pure (.error status)
                  | .ok (state, emitted) =>
                      set state
                      pure (.ok { emitted := emitted })
          | .ok entry =>
              let stream := { stream with authorizedEntry? := some entry }
              let state := { state with streams := replaceStream state.streams stream }
              match protocolDispatchForStream state authorization.streamId with
              | .error status => pure (.error status)
              | .ok (state, detached, requestStreaming) =>
                  set state
                  pure (.ok { detached := detached, requestStreaming := requestStreaming })

private def cancelResponseStream (dispatch : ActiveDispatch) : IO Unit :=
  cancelResponseStreamRef dispatch.responseStreamCancel

private def cancelRequestStream (dispatch : ActiveDispatch) : IO Unit :=
  cancelRequestStreamRef dispatch.requestStreamCancel

private def signalDispatches (dispatches : Array ActiveDispatch) : IO Unit := do
  -- A timed dispatch suspends on a child-task completion promise, so cancelling
  -- only its outer task cannot wake it.  Signal the exact child first; its
  -- completion resolves the race and lets the retained outer owner retire.
  for dispatch in dispatches do
    match dispatch.deadlineChild with
    | none => pure ()
    | some childRef => cancelDeadlineChildRef childRef
  for dispatch in dispatches do
    IO.cancel dispatch.task

/-- Finish cancellation of an already-signalled detached set while retaining
exact ownership in the calling connection task. An uncooperative handler or
callback parks its registered connection owner instead of becoming detached
work. -/
private def finishDispatchCancellationOwned (dispatches : Array ActiveDispatch) :
    Std.Async.Async Unit := do
  for dispatch in dispatches do
    cancelRequestStream dispatch
    cancelResponseStream dispatch
  for dispatch in dispatches do
    try
      Std.Async.Async.ofAsyncTask dispatch.task
    catch _ =>
      pure ()
  -- Cancellation can make the outer dispatch finish before its suspended
  -- deadline race resumes.  Join the separately retained child as well, so a
  -- handler can never outlive the connection/stream owner that cancelled it.
  for dispatch in dispatches do
    match dispatch.deadlineChild with
    | none => pure ()
    | some childRef => joinDeadlineChildRef childRef

private def signalAuthorizations (authorizations : Array ActiveAuthorization) : IO Unit := do
  for authorization in authorizations do
    cancelDeadlineChildRef authorization.deadlineChild

private def finishAuthorizationCancellationOwned
    (authorizations : Array ActiveAuthorization) : Std.Async.Async Unit := do
  for authorization in authorizations do
    try
      joinDeadlineChildRef authorization.deadlineChild
    catch _ =>
      pure ()

/-- Unbounded so that feeding inbound messages from the connection loop never
blocks on a slow handler (one stalled stream must not stall the connection).
Memory stays bounded by HTTP/2 stream flow control: the peer can have at most
one stream window of unconsumed payload in flight per stream, because the
stream window is only credited back as the handler consumes messages. -/
private def runGrpcPipe : IO (Except Status (MessageStream.Producer ByteArray)) :=
  (MessageStream.pipe (α := ByteArray) (capacity := none)).run

private def feedRequestStream (feed : RequestStreamFeed) : IO (Except Status Unit) := do
  for message in feed.messages do
    match ← (feed.producer.send message).run with
    | .ok () => pure ()
    | .error status => return .error status
  match feed.error with
  | some status =>
      -- Reset and stream-error handling first cancels and joins the dispatch
      -- that owns this producer.  Its cancellation may therefore close the
      -- pipe before this best-effort terminal notification runs.  That is an
      -- idempotent stream-local outcome, not a connection-level application
      -- failure.
      match ← feed.producer.fail status with
      | .ok () | .error _ => pure (.ok ())
  | none =>
      if feed.close then
        feed.producer.close.run
      else
        pure (.ok ())

/-- Wait for the dispatch to be registered in connection state before running the
handler. Resolved immediately after the spawn site's registration, so the wait is
momentary; a promise (instead of a poll loop) avoids adding latency to every RPC. -/
private def waitUntilDispatchRegistered
    (registered : IO.Promise Unit) : Std.Async.Async Unit :=
  Std.Async.Async.ofAsyncTask <|
    registered.result?.map (sync := true) fun
      | some () => .ok ()
      | none => .error (IO.userError "dispatch registration gate was dropped")

private def abortStreamShared (stateMutex : Std.Mutex State) (emit : Array _root_.Http2.Frame -> IO Unit)
    (streamId : Nat) (code : _root_.Http2.ErrorCode) : IO Unit := do
  let reset? ← stateMutex.atomically do
    let state ← get
    match _root_.Http2.Connection.resetStream state.protocol streamId code with
    | .error _ => pure none
    | .ok (protocol, reset?) =>
        set {
          state with
          protocol := protocol,
          streams := removeStream state.streams streamId,
          activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId,
          pendingResponses := removePendingResponsesForStream state.pendingResponses streamId
        }
        pure reset?
  match reset? with
  | none => pure ()
  | some rst =>
      try
        emit #[rst]
      catch _ =>
        pure ()

/-- A deliberate connection/stream teardown has already selected the wire-level
error (or received one from the peer). In that case task cancellation performs
bookkeeping only; an unrelated INTERNAL_ERROR reset would contradict it. -/
private def abortStreamSharedUnlessCancelled (cancelled : IO.Ref Bool)
    (stateMutex : Std.Mutex State) (emit : Array _root_.Http2.Frame -> IO Unit)
    (streamId : Nat) (code : _root_.Http2.ErrorCode) : IO Unit := do
  unless ← cancelled.get do
    abortStreamShared stateMutex emit streamId code

/-- Close a managed unary stream while leaving its exact outer task discoverable
in `activeDispatches`.  Scheduler callbacks run outside that task, so only the
task's own retirement (or connection teardown, which retains its handle) may
remove this ownership record. -/
private def spawnDetachedDispatch (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (detached : DetachedDispatch) : Std.Async.Async Unit := do
  let cancelled ← IO.mkRef false
  let registered ← IO.Promise.new
  let deadlineChild? ←
    if detached.request.deadline.isSome then
      some <$> IO.mkRef (none : Option DeadlineChild)
    else
      pure none
  let requestStreamCancel ← IO.mkRef (none : Option (IO Unit))
  let responseStreamCancel ← IO.mkRef (none : Option (IO Unit))
  let deadlineRuntime? ← match deadlineChild? with
    | none => pure none
    | some deadlineChild =>
        let deadlineScheduler? := detached.deadlineScheduler
        pure (some {
          externalTimer := deadlineScheduler?.isSome,
          registerTask := fun deadline cancel expire join => do
            let unregister ← registerDeadlineChild deadlineChild deadlineScheduler?
              deadline cancel expire join
            if ← cancelled.get then
              cancelDeadlineChildRef deadlineChild
            pure unregister
        })
  let registerResponseStream (stream : MessageStream ByteArray) :
      IO (MessageStream ByteArray) := do
    let cancel : IO Unit := do
      discard <| stream.cancel.run
    responseStreamCancel.set (some cancel)
    if ← cancelled.get then
      cancelResponseStreamRef responseStreamCancel
    pure {
      stream with
      cancel := ExceptT.mk do
        cancelResponseStreamRef responseStreamCancel
        pure (.ok ())
    }
  let emitUnary (response : UnaryResponse) : IO (Except Status Unit) := do
    if ← IO.checkCanceled then
      pure (.error (Status.cancelled Status.dispatchCancelledMessage))
    else if ← cancelled.get then
      pure (.error (Status.cancelled Status.dispatchCancelledMessage))
    else
      let gzip := registry.enableResponseCompression && detached.preflight.clientAcceptsGzip
      emitUnaryResponseShared stateMutex emit detached.request.streamId response gzip
  let emitStreaming (response : ServerStreamingStreamResponse) (deadline : Option Nat) :
      Std.Async.Async (Except Status Unit) := do
    let stream ← try
      registerResponseStream response.messages
    catch err =>
      return .error (Status.ofIOError err)
    let gzip := registry.enableResponseCompression && detached.preflight.clientAcceptsGzip
    emitStreamingResponseShared registry stateMutex emit detached.request.streamId
      { response with messages := stream } gzip deadline deadlineRuntime?
  let task ← Std.Async.Async.toIO do
    waitUntilDispatchRegistered registered
    if ← cancelled.get then
      pure ()
    else try
      let result ← Transport.dispatchManagedRequestWithAsync registry detached.request
        detached.entry detached.preflight deadlineRuntime?
      let result ← match result with
        | .error status => emitUnary { status := status, data := ByteArray.empty }
        | .ok (.unary response) => emitUnary response
        | .ok (.streaming response deadline) => emitStreaming response deadline
      joinDeadlineChildRef? deadlineChild?
      match result with
      | .ok () =>
          stateMutex.atomically do
            let state ← get
            let activeDispatches := removeActiveDispatchesForStream
              state.activeDispatches detached.request.streamId
            set {
              state with
              activeDispatches := activeDispatches
            }
      | .error _status =>
          cancelResponseStreamRef responseStreamCancel
          stateMutex.atomically do
            let state ← get
            set {
              state with
              activeDispatches := removeActiveDispatchesForStream
                state.activeDispatches detached.request.streamId
            }
          abortStreamSharedUnlessCancelled cancelled stateMutex emit
            detached.request.streamId _root_.Http2.ErrorCode.internalError
    catch _ =>
      joinDeadlineChildRef? deadlineChild?
      cancelResponseStreamRef responseStreamCancel
      stateMutex.atomically do
        let state ← get
        set {
          state with
          activeDispatches := removeActiveDispatchesForStream
            state.activeDispatches detached.request.streamId
        }
      abortStreamSharedUnlessCancelled cancelled stateMutex emit
        detached.request.streamId _root_.Http2.ErrorCode.internalError
  let published ← stateMutex.atomically do
    let state ← get
    let ownsPublication :=
      containsStreamId state.pendingDispatchPublications detached.request.streamId
    let state := {
      state with
      pendingDispatchPublications := removeStreamId
        state.pendingDispatchPublications detached.request.streamId
    }
    if state.closing || !ownsPublication then
      set state
      pure false
    else
      set {
        state with
        activeDispatches := state.activeDispatches.push {
          streamId := detached.request.streamId,
          task := task,
          cancelled := cancelled,
          requestStreamCancel := requestStreamCancel,
          responseStreamCancel := responseStreamCancel,
          deadlineChild := deadlineChild?
        }
      }
      pure true
  unless published do
    -- Cancellation won the publication race.  The task is still behind its
    -- gate, so retire the exact handle before arbitrary handler IO can start.
    cancelled.set true
    IO.cancel task
  registered.resolve ()
  unless published do
    try
      discard <| Std.Async.Async.ofAsyncTask task
    catch _ =>
      pure ()
    joinDeadlineChildRef? deadlineChild?
    return
  if ← IO.hasFinished task then
    stateMutex.atomically do
      let state ← get
      set {
        state with
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches detached.request.streamId
      }

/-- Pure half of credit-on-consume: pop the next deferred per-message credit
and put exactly that many bytes back into the stream's receive window.  The
returned amount is what the peer's WINDOW_UPDATE must carry. -/
private def grantProtocolRequestStreamCredit (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (streamId : Nat) : IO (Except Status Unit) := do
  let prepared : Except Status (Array _root_.Http2.Frame) ← stateMutex.atomically do
    let state ← get
    match findActiveRequestStream? state.activeRequestStreams streamId with
    | none => pure (Except.ok #[])
    | some active =>
        match active.pendingRequestCredits[0]? with
        | none => pure (Except.ok #[])
        | some credit =>
            let decodedCredit := active.pendingRequestDecodedBytes[0]?.getD 0
            match ofHttp2 <| _root_.Http2.Connection.acknowledgeData
                state.protocol streamId credit with
            | .error status => pure (Except.error status)
            | .ok (protocol, frames) =>
                let active := {
                  active with
                  pendingRequestCredits :=
                    active.pendingRequestCredits.extract 1 active.pendingRequestCredits.size,
                  pendingRequestDecodedBytes := active.pendingRequestDecodedBytes.extract 1
                    active.pendingRequestDecodedBytes.size,
                  retainedDecodedBytes := active.retainedDecodedBytes - decodedCredit
                }
                set {
                  state with
                  protocol := protocol,
                  activeRequestStreams := replaceActiveRequestStream
                    state.activeRequestStreams active
                }
                pure (Except.ok frames)
  match prepared with
  | .error status => pure (.error status)
  | .ok frames => emitFrameBatch emit frames

/-- Wrap a streaming request body so each consumed message grants its deferred
stream flow-control credit back to the peer. -/
private def protocolCreditingRequestStream (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (streamId : Nat)
    (inner : MessageStream ByteArray) : MessageStream ByteArray :=
  {
    recv? := ExceptT.mk do
      match ← inner.recv?.run with
      | .error status => pure (.error status)
      | .ok none => pure (.ok none)
      | .ok (some item) =>
          match ← grantProtocolRequestStreamCredit stateMutex emit streamId with
          | .ok () => pure (.ok (some item))
          | .error status => pure (.error status)
    cancel := inner.cancel
  }

private def spawnRequestStreamingDispatch (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (dispatch : RequestStreamingDispatch) :
    Std.Async.Async (Except Status Unit) := do
  let producer ← match ← runGrpcPipe with
    | .ok producer => pure producer
    | .error status => return .error status
  let rawRequestStream := protocolCreditingRequestStream stateMutex emit dispatch.streamId producer.stream
  let acceptsGzip := dispatch.preflight.clientAcceptsGzip
  let cancelled ← IO.mkRef false
  let registered ← IO.Promise.new
  let deadlineChild? ←
    if dispatch.deadline.isSome then
      some <$> IO.mkRef (none : Option DeadlineChild)
    else
      pure none
  let requestStreamCancel ← IO.mkRef (some (discard <| producer.cancel.run) : Option (IO Unit))
  let responseStreamCancel ← IO.mkRef (none : Option (IO Unit))
  let requestStream : MessageStream ByteArray := {
    rawRequestStream with
    cancel := ExceptT.mk do
      cancelRequestStreamRef requestStreamCancel
      pure (.ok ())
  }
  let deadlineRuntime? ← match deadlineChild? with
    | none => pure none
    | some deadlineChild =>
        let deadlineScheduler? := dispatch.deadlineScheduler
        pure (some {
          externalTimer := deadlineScheduler?.isSome,
          registerTask := fun deadline cancel expire join => do
            let unregister ← registerDeadlineChild deadlineChild deadlineScheduler?
              deadline cancel expire join
            if ← cancelled.get then
              cancelDeadlineChildRef deadlineChild
            pure unregister
        })
  let registerResponseStream (stream : MessageStream ByteArray) :
      IO (MessageStream ByteArray) := do
    let cancel : IO Unit := do
      discard <| stream.cancel.run
    responseStreamCancel.set (some cancel)
    if ← cancelled.get then
      cancelResponseStreamRef responseStreamCancel
    pure {
      stream with
      cancel := ExceptT.mk do
        cancelResponseStreamRef responseStreamCancel
        pure (.ok ())
    }
  let finish (outputCommitted : Bool) : Std.Async.Async Unit := do
    joinDeadlineChildRef? deadlineChild?
    cancelRequestStreamRef requestStreamCancel
    stateMutex.atomically do
      let state ← get
      let state := {
        state with
        activeRequestStreams := removeActiveRequestStream state.activeRequestStreams dispatch.streamId,
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches dispatch.streamId
      }
      let state :=
        if outputCommitted then
          state
        else
          { state with pendingResponses :=
              removePendingResponsesForStream state.pendingResponses dispatch.streamId }
      let state := { state with streams := removeStream state.streams dispatch.streamId }
      set state
  let encodeUnary (response : UnaryResponse) : IO (Except Status Unit) :=
    emitUnaryResponseShared stateMutex emit dispatch.streamId response
      (registry.enableResponseCompression && acceptsGzip)
  let encodeStreaming (response : ServerStreamingStreamResponse) (deadline : Option Nat) :
      Std.Async.Async (Except Status Unit) := do
    let messages ← try
      registerResponseStream response.messages
    catch err =>
      return .error (Status.ofIOError err)
    emitStreamingResponseShared registry stateMutex emit dispatch.streamId
      { response with messages := messages }
      (registry.enableResponseCompression && acceptsGzip) deadline deadlineRuntime?
  let emptyStreamingResponse (status : Status) : ServerStreamingStreamResponse := {
    messages := { recv? := pure none },
    status := status
  }
  let task ← Std.Async.Async.toIO do
    waitUntilDispatchRegistered registered
    if ← cancelled.get then
      pure ()
    else try
      match dispatch.requestError with
      | some status =>
          let encoded ← match dispatch.kind with
            | .clientStreaming _ =>
                encodeUnary { status := status, data := ByteArray.empty }
            | .bidirectionalStreaming _ =>
                encodeStreaming (emptyStreamingResponse status) none
          match encoded with
          | .ok () => finish true
          | .error _status =>
              cancelResponseStreamRef responseStreamCancel
              finish false
              abortStreamSharedUnlessCancelled cancelled stateMutex emit
                dispatch.streamId _root_.Http2.ErrorCode.internalError
      | none =>
          match dispatch.kind with
          | .clientStreaming handler =>
              let result ← registry.dispatchManagedClientStreamingMessageStreamAsync
                dispatch.metadata requestStream dispatch.preflight handler dispatch.deadline
                deadlineRuntime?
              let encoded ← match result with
                | .ok response => encodeUnary response
                | .error status => encodeUnary { status := status, data := ByteArray.empty }
              match encoded with
              | .ok () => finish true
              | .error _status =>
                  cancelResponseStreamRef responseStreamCancel
                  finish false
                  abortStreamSharedUnlessCancelled cancelled stateMutex emit
                    dispatch.streamId _root_.Http2.ErrorCode.internalError
          | .bidirectionalStreaming handler =>
              let result ← registry.dispatchManagedBidirectionalStreamingMessageStreamAsync
                dispatch.metadata requestStream dispatch.preflight handler dispatch.deadline
                deadlineRuntime?
              let encoded ← match result with
                | .ok (response, deadline) => encodeStreaming response deadline
                | .error status =>
                    -- Preserve the expired handler child in `deadlineChild`
                    -- until `finish` queues trailers and joins that exact
                    -- generation.  The synthetic terminal stream itself has
                    -- no work that needs another deadline race.
                    encodeStreaming (emptyStreamingResponse status) none
              match encoded with
              | .ok () => finish true
              | .error _status =>
                  cancelResponseStreamRef responseStreamCancel
                  finish false
                  abortStreamSharedUnlessCancelled cancelled stateMutex emit
                    dispatch.streamId _root_.Http2.ErrorCode.internalError
    catch _ =>
      cancelResponseStreamRef responseStreamCancel
      finish false
      abortStreamSharedUnlessCancelled cancelled stateMutex emit
        dispatch.streamId _root_.Http2.ErrorCode.internalError
  let published ← stateMutex.atomically do
    let state ← get
    let ownsPublication :=
      containsStreamId state.pendingDispatchPublications dispatch.streamId
    let state := {
      state with
      pendingDispatchPublications := removeStreamId
        state.pendingDispatchPublications dispatch.streamId
    }
    if state.closing || !ownsPublication then
      set state
      pure false
    else
      let activeDispatch : ActiveDispatch := {
        streamId := dispatch.streamId,
        task := task,
        cancelled := cancelled,
        requestStreamCancel := requestStreamCancel,
        responseStreamCancel := responseStreamCancel,
        deadlineChild := deadlineChild?
      }
      let activeRequestStreams :=
        if dispatch.closeImmediately then
          state.activeRequestStreams
        else
          state.activeRequestStreams.push {
            streamId := dispatch.streamId,
            producer := producer,
            usesGzip := dispatch.preflight.requestUsesGzip
          }
      set {
        state with
        activeDispatches := state.activeDispatches.push activeDispatch,
        activeRequestStreams := activeRequestStreams
      }
      pure true
  unless published do
    cancelled.set true
    IO.cancel task
  registered.resolve ()
  unless published do
    try
      discard <| Std.Async.Async.ofAsyncTask task
    catch _ =>
      pure ()
    joinDeadlineChildRef? deadlineChild?
    cancelRequestStreamRef requestStreamCancel
    cancelResponseStreamRef responseStreamCancel
    return .ok ()
  if dispatch.closeImmediately then
    match ← producer.close.run with
    | .ok () => pure ()
    | .error status => return .error status
  if ← IO.hasFinished task then
    stateMutex.atomically do
      let state ← get
      set {
        state with
        streams := removeStream state.streams dispatch.streamId,
        activeRequestStreams := removeActiveRequestStream
          state.activeRequestStreams dispatch.streamId,
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches dispatch.streamId
      }
  pure (.ok ())

def signalCancelActiveShared (stateMutex : Std.Mutex State) : IO Unit := do
  let (dispatches, authorizations) ← stateMutex.atomically do
    let state ← get
    for dispatch in state.activeDispatches do
      dispatch.cancelled.set true
    for authorization in state.activeAuthorizations do
      authorization.cancelled.set true
    set { state with closing := true }
    pure (state.activeDispatches, state.activeAuthorizations)
  -- This entry point is safe for shutdown/error callbacks: it never enters
  -- arbitrary MessageStream.cancel IO and never waits for a handler.
  signalAuthorizations authorizations
  signalDispatches dispatches

def cancelActiveSharedOwned (stateMutex : Std.Mutex State) : Std.Async.Async State := do
  let (state, dispatches, authorizations, requestStreams, scheduler?) ← stateMutex.atomically do
    let state ← get
    let dispatches := state.activeDispatches
    let authorizations := state.activeAuthorizations
    let requestStreams := state.activeRequestStreams
    let scheduler? := state.deadlineScheduler
    for dispatch in dispatches do
      dispatch.cancelled.set true
    for authorization in authorizations do
      authorization.cancelled.set true
    let state := {
      state with
      closing := true,
      streams := #[],
      activeRequestStreams := #[],
      activeDispatches := #[],
      activeAuthorizations := #[],
      pendingDispatchPublications := #[],
      pendingResponses := #[],
      deadlineScheduler := none
    }
    set state
    pure (state, dispatches, authorizations, requestStreams, scheduler?)
  -- Wake every deadline/authorization race before joining any arbitrary user
  -- callback.  A callback may be uncooperative, but no other owned phase is
  -- left waiting merely because it was signalled later in the loop.
  signalAuthorizations authorizations
  signalDispatches dispatches
  -- The scheduler is infrastructure, not arbitrary user IO. Retire it after
  -- every child has been signalled but before joining callbacks that may be
  -- uncooperative, so teardown never leaks the shared timer task.
  match scheduler? with
  | none => pure ()
  | some scheduler => scheduler.shutdown
  finishDispatchCancellationOwned dispatches
  finishAuthorizationCancellationOwned authorizations
  -- Streaming dispatches own their producer cancellation through
  -- requestStreamCancel. Retain ownership for any defensive orphan as well.
  for requestStream in requestStreams do
    unless dispatches.any (fun dispatch => dispatch.streamId == requestStream.streamId) do
      discard <| requestStream.producer.cancel.run
  pure state

private def finishSharedFrameResult (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (result : SharedFrameResult) :
    Std.Async.Async (Except Status Unit) := do
  -- Select and signal a stream error first, then publish its wire frame.  User
  -- cleanup cannot suppress the peer-visible RST_STREAM; cleanup is still
  -- joined even when emission reports a transport error.
  for dispatch in result.cancelDispatches do
    dispatch.cancelled.set true
  for authorization in result.cancelAuthorizations do
    authorization.cancelled.set true
  signalAuthorizations result.cancelAuthorizations
  signalDispatches result.cancelDispatches
  let emitResult ← emitFrameBatch emit result.emitted
  finishDispatchCancellationOwned result.cancelDispatches
  -- Authorization retains a single original owner from prepare through
  -- retire. A concurrent reset only signals that owner: stealing its join
  -- handle here could let the original owner retire the active marker while
  -- this task was still waiting on an uncooperative child.
  match emitResult with
  | .error status => pure (.error status)
  | .ok () =>
      for feed in result.requestFeeds do
        match ← feedRequestStream feed with
        | .ok () => pure ()
        | .error status => return .error status
      match result.requestStreaming with
      | some dispatch =>
          match ← spawnRequestStreamingDispatch registry stateMutex emit dispatch with
          | .error status => return .error status
          | .ok () => pure ()
      | none => pure ()
      match result.detached with
      | none => pure (.ok ())
      | some detached =>
          spawnDetachedDispatch registry stateMutex emit detached
          pure (.ok ())

private def aggregateRequestWireLimit (registry : Registry) : Nat :=
  retainedDecodedRequestLimit registry

private def retainedDecodedMessageBytes (registry : Registry) (usesGzip : Bool)
    (messages : Array Message) : Except Status Nat :=
  messages.foldlM (init := 0) fun total message => do
    let message ← Message.decompress usesGzip
      (registry.maxReceiveMessageSize.getD Message.defaultMaxDecompressedSize) message
    pure (total + Message.prefixLength + message.data.size)

private def rejectAggregateRequest (state : State) (streamId : Nat) (status : Status) :
    Except Status (State × SharedFrameResult) := do
  let commands ← unaryResponseCommands streamId {
    status := status
    data := ByteArray.empty
  }
  let (state, responseFrames) ← queueResponses
    { state with streams := removeStream state.streams streamId } commands
  let (protocol, reset?) ← ofHttp2 <|
    _root_.Http2.Connection.resetStream state.protocol streamId .enhanceYourCalm
  pure ({ state with protocol := protocol }, {
    emitted := match reset? with
      | none => responseFrames
      | some reset => responseFrames.push reset
  })

private def rejectActiveRequest (state : State) (streamId : Nat) (status : Status) :
    Except Status (State × SharedFrameResult) := do
  let commands ← unaryResponseCommands streamId {
    status := status
    data := ByteArray.empty
  }
  let dispatches := activeDispatchesForStream state.activeDispatches streamId
  let base := {
    state with
    streams := removeStream state.streams streamId,
    activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId,
    activeDispatches := removeActiveDispatchesForStream state.activeDispatches streamId,
    pendingDispatchPublications := removeStreamId state.pendingDispatchPublications streamId,
    pendingResponses := removePendingResponsesForStream state.pendingResponses streamId
  }
  let (state, responseFrames) ← queueResponses base commands
  let (protocol, reset?) ← ofHttp2 <|
    _root_.Http2.Connection.resetStream state.protocol streamId .enhanceYourCalm
  pure ({ state with protocol := protocol }, {
    emitted := match reset? with
      | none => responseFrames
      | some reset => responseFrames.push reset
    cancelDispatches := dispatches
  })

private def completeProtocolRequest (state : State) (streamId : Nat) :
    Except Status (State × SharedFrameResult) := do
  match findActiveRequestStream? state.activeRequestStreams streamId with
  | some active =>
      let state := {
        state with
        activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId
      }
      pure (state, { requestFeeds := #[{ producer := active.producer, close := true }] })
  | none =>
      match findStream? state.streams streamId with
      | none => pure (state, {})
      | some stream =>
          let stream := { stream with peerEnded := true }
          let state := { state with streams := replaceStream state.streams stream }
          let (state, detached, requestStreaming) ← protocolDispatchForStream state streamId
          pure (state, { detached := detached, requestStreaming := requestStreaming })

private def processProtocolDataEvent (registry : Registry) (state : State)
    (streamId : Nat) (bytes : ByteArray) (endStream : Bool) :
    Except Status (State × SharedFrameResult) := do
  match findActiveRequestStream? state.activeRequestStreams streamId with
  | some active =>
      match decodeActiveRequestBytes registry active bytes endStream with
      | .error status =>
          if status.code == .resourceExhausted then
            rejectActiveRequest state streamId status
          else
            let state := {
              state with
              activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId
            }
            pure (state, {
              requestFeeds := #[{ producer := active.producer, error := some status }]
            })
      | .ok (active, messages, close) =>
          let state := {
            state with
            activeRequestStreams := if close then
                removeActiveRequestStream state.activeRequestStreams streamId
              else
                replaceActiveRequestStream state.activeRequestStreams active
          }
          pure (state, { requestFeeds := #[{
            producer := active.producer,
            messages := messages,
            close := close
          }] })
  | none =>
      match findStream? state.streams streamId with
      | none => pure (state, {})
      | some stream =>
          let limit := aggregateRequestWireLimit registry
          if stream.body.size + bytes.size > limit then
            rejectAggregateRequest state streamId <| Status.resourceExhausted
              s!"gRPC aggregate request exceeds configured wire buffer limit {limit}"
          else
            match Message.decodeChunkWithLimit registry.maxReceiveMessageSize
                stream.decodeState bytes with
            | .error status => rejectAggregateRequest state streamId status
            | .ok decoded =>
                let preflight ← match stream.requestPreflight with
                  | some preflight => pure preflight
                  | none => throw (Status.internal
                      "request DATA arrived before gRPC header preflight completed")
                match retainedDecodedMessageBytes registry preflight.requestUsesGzip
                    decoded.messages with
                | .error status => rejectAggregateRequest state streamId status
                | .ok addedDecodedBytes =>
                    let retainedDecodedBytes :=
                      stream.retainedDecodedBytes + addedDecodedBytes
                    let decodedLimit := retainedDecodedRequestLimit registry
                    if retainedDecodedBytes > decodedLimit then
                      rejectAggregateRequest state streamId <| Status.resourceExhausted
                        s!"gRPC aggregate request exceeds retained decoded-byte limit {decodedLimit}"
                    else
                      let stream := {
                        stream with
                        body := stream.body.append bytes,
                        decodeState := { buffered := decoded.buffered },
                        retainedDecodedBytes := retainedDecodedBytes,
                        peerEnded := stream.peerEnded || endStream
                      }
                      let state := { state with streams := replaceStream state.streams stream }
                      if endStream then
                        let (state, detached, requestStreaming) ←
                          protocolDispatchForStream state streamId
                        pure (state, {
                          detached := detached,
                          requestStreaming := requestStreaming
                        })
                      else
                        pure (state, {})

private def cancelProtocolStream (state : State) (streamId : Nat) (message : String) :
    State × SharedFrameResult :=
  let dispatches := activeDispatchesForStream state.activeDispatches streamId
  let authorizations := activeAuthorizationsForStream state.activeAuthorizations streamId
  let feed := (findActiveRequestStream? state.activeRequestStreams streamId).map fun active =>
    ({ producer := active.producer,
       error := some (Status.cancelled message) } : RequestStreamFeed)
  ({
    state with
    streams := removeStream state.streams streamId,
    activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId,
    activeDispatches := removeActiveDispatchesForStream state.activeDispatches streamId,
    activeAuthorizations := removeActiveAuthorizationsForStream state.activeAuthorizations streamId,
    pendingDispatchPublications := removeStreamId state.pendingDispatchPublications streamId,
    pendingResponses := removePendingResponsesForStream state.pendingResponses streamId
  }, {
    requestFeeds := feed.map (#[·]) |>.getD #[],
    cancelDispatches := dispatches,
    cancelAuthorizations := authorizations
  })

/-- `Http2.Connection.processBytes` commits every complete frame in a chunk
before returning its ordered events.  If a later frame in that same chunk
closed a stream, no earlier application event for that stream may start or
resume gRPC work against the already-closed protocol state. -/
private def protocolStreamClosed (state : State) (streamId : Nat) : Bool :=
  match _root_.Http2.Connection.stream? state.protocol streamId with
  | some stream => stream.phase == .closed
  | none => true

private def processProtocolHeaderEvent (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (streamId : Nat)
    (metadata : _root_.Http2.Headers) (endStream trailers : Bool) (receivedAt : Nat) :
    Std.Async.Async (Except Status Unit) := do
  let prepared : Except Status SharedFrameResult ← stateMutex.atomically do
    let state ← get
    if state.closing || protocolStreamClosed state streamId then
      pure (Except.ok ({} : SharedFrameResult))
    else if trailers then
      match completeProtocolRequest state streamId with
      | .error status => pure (Except.error status)
      | .ok (state, result) =>
          set state
          pure (Except.ok result)
    else
      match ← prepareProtocolAuthorization registry state streamId metadata endStream receivedAt with
      | .error status => pure (Except.error status)
      | .ok (state, result) =>
          set state
          pure (Except.ok result)
  match prepared with
  | .error status => pure (.error status)
  | .ok result =>
      match result.pendingAuthorization with
      | none => finishSharedFrameResult registry stateMutex emit result
      | some authorization =>
          let outcome ← try
            let decision ← runPendingAuthorization registry authorization
            match ← commitProtocolAuthorization stateMutex authorization decision with
            | .error status => pure (.error status)
            | .ok resolved =>
                reconcileCurrentPendingBodyDeadline stateMutex emit authorization.streamId
                finishSharedFrameResult registry stateMutex emit resolved
          catch error =>
            cancelDeadlineChildRef authorization.active.deadlineChild
            pure (.error (Status.ofIOError error))
          try joinDeadlineChildRef authorization.active.deadlineChild catch _ => pure ()
          retirePendingAuthorization stateMutex authorization
          pure outcome

private def processProtocolEventShared (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) (receivedAt : Nat) :
    _root_.Http2.Connection.Event → Std.Async.Async (Except Status Unit)
  | .headers streamId metadata endStream trailers =>
      processProtocolHeaderEvent registry stateMutex emit streamId metadata endStream trailers receivedAt
  | .data streamId bytes endStream => do
      let result : Except Status SharedFrameResult ← stateMutex.atomically do
        let state ← get
        if state.closing || protocolStreamClosed state streamId then
          pure (Except.ok ({} : SharedFrameResult))
        else
          match processProtocolDataEvent registry state streamId bytes endStream with
          | .error status => pure (Except.error status)
          | .ok (state, result) =>
              set state
              pure (Except.ok result)
      match result with
      | .error status => pure (.error status)
      | .ok result => do
          let outcome ← finishSharedFrameResult registry stateMutex emit result
          reconcileCurrentPendingBodyDeadline stateMutex emit streamId
          pure outcome
  | .reset streamId _ => do
      let result ← stateMutex.atomically do
        let state ← get
        let (state, result) := cancelProtocolStream state streamId "request stream reset by peer"
        for dispatch in result.cancelDispatches do dispatch.cancelled.set true
        for authorization in result.cancelAuthorizations do authorization.cancelled.set true
        set state
        pure result
      finishSharedFrameResult registry stateMutex emit result
  | .streamError streamId _ message => do
      let result ← stateMutex.atomically do
        let state ← get
        let (state, result) := cancelProtocolStream state streamId message
        for dispatch in result.cancelDispatches do dispatch.cancelled.set true
        for authorization in result.cancelAuthorizations do authorization.cancelled.set true
        set state
        pure result
      finishSharedFrameResult registry stateMutex emit result
  | .pingAcknowledged payload => do
      stateMutex.atomically do
        modify fun state =>
          if state.pendingKeepalivePing == some payload then
            { state with pendingKeepalivePing := none }
          else
            state
      pure (.ok ())
  | .settingsChanged settings => do
      stateMutex.atomically do
        modify fun state => {
          state with
          protocol := {
            state.protocol with
            hpackEncode := _root_.Http2.Hpack.setMaxAllowedSizeWithoutDynamicTable
              state.protocol.hpackEncode settings.headerTableSize
          }
        }
      pure (.ok ())
  | .settingsAcknowledged | .goAway _ _ _ | .priority _ =>
      pure (.ok ())

private def flushProtocolResponsesShared (stateMutex : Std.Mutex State)
    (emit : Array _root_.Http2.Frame -> IO Unit) : IO (Except Status Unit) := do
  let result : Except Status (Array _root_.Http2.Frame) ← stateMutex.atomically do
    let state ← get
    match flushResponses state with
    | .error status => pure (Except.error status)
    | .ok (state, frames) =>
        set state
        pure (Except.ok frames)
  match result with
  | .error status => pure (.error status)
  | .ok frames => emitFrameBatch emit frames

def processBytesSharedWithOwned (registry : Registry) (stateMutex : Std.Mutex State)
    (chunk : ByteArray)
    (emit : Array _root_.Http2.Frame -> IO Unit) : Std.Async.Async (Except ProcessError Unit) := do
  let receivedAt ← IO.monoNanosNow
  let processed : Except ProcessError
      (Array _root_.Http2.Frame × Array _root_.Http2.Connection.Event ×
        Option _root_.Http2.Error) ←
    stateMutex.atomically do
    let state ← get
    if state.closing then
      pure (Except.ok (#[], #[], none))
    else
      match _root_.Http2.Connection.processBytes state.protocol chunk with
      | .error error => pure (Except.error (.http2 error))
      | .ok result =>
          -- Publish peer SETTINGS and the zero-table concurrency policy in
          -- the same critical section. A response task must never observe the
          -- foundation's intermediate nonzero encoder state between parsing
          -- SETTINGS and delivering its semantic event.
          let protocol := {
            result.state with
            hpackEncode := _root_.Http2.Hpack.setMaxAllowedSizeWithoutDynamicTable
              result.state.hpackEncode result.state.peerSettings.headerTableSize
          }
          set { state with protocol := protocol }
          pure (Except.ok (result.outbound, result.events, result.error?))
  match processed with
  | .error error => pure (.error error)
  | .ok (automatic, events, terminalError?) =>
      let mut applicationError? := match ← emitFrameBatch emit automatic with
        | .error status => some status
        | .ok () => none
      -- A later frame in this chunk may already have selected a connection
      -- error. Process preceding valid semantic events only until their first
      -- application failure, then preserve the terminal RFC error below.
      if applicationError?.isNone then
        for event in events do
          if applicationError?.isNone then
            match ← processProtocolEventShared registry stateMutex emit receivedAt event with
            | .error status => applicationError? := some status
            | .ok () => pure ()
      if applicationError?.isNone then
        match ← flushProtocolResponsesShared stateMutex emit with
        | .error status => applicationError? := some status
        | .ok () => pure ()
      match terminalError?, applicationError? with
      | some error, _ => pure (.error (.http2 error))
      | none, some status => pure (.error (.application status))
      | none, none => pure (.ok ())

def expirePendingDeadlinesEncodedSharedWith (stateMutex : Std.Mutex State)
    (emit : ByteArray -> IO Unit) : IO (Except Status Unit) :=
  expirePendingDeadlinesSharedWith stateMutex fun frames => do
    match ofHttp2 <| _root_.Http2.Frame.encodeBatch frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

def processBytesEncodedSharedWithOwned (registry : Registry) (stateMutex : Std.Mutex State)
    (chunk : ByteArray) (emit : ByteArray -> IO Unit) :
    Std.Async.Async (Except ProcessError Unit) := do
  processBytesSharedWithOwned registry stateMutex chunk fun frames => do
    match ofHttp2 <| _root_.Http2.Frame.encodeBatch frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

theorem defaultStreamWindow_admits_max_message :
    Message.prefixLength + Message.defaultMaxDecompressedSize ≤ defaultStreamWindow := by
  decide
end Connection
end Http2
end Grpc
