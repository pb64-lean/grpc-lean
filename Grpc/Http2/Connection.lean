module

public import Std.Sync.Mutex
public import Grpc.Http2.Frame
public import Grpc.Http2.Grpc
import Std.Async.Timer
import Std.Data.HashMap
import Std.Sync.Channel

public section

namespace Grpc
namespace Http2
namespace Connection

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
  frames : Array Frame := #[]
  requestMetadata : Option Metadata := none
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

structure OutboundStreamWindow where
  streamId : Nat
  window : Int
  deriving Inhabited

structure InboundStreamWindow where
  streamId : Nat
  window : Nat
  deriving Inhabited

structure ActiveRequestStream where
  streamId : Nat
  producer : MessageStream.Producer ByteArray
  decodeState : Message.DecodeState := {}
  contentLength : Option Nat := none
  receivedBodyBytes : Nat := 0
  usesGzip : Bool := false
  /-- Wire size of each decoded-but-unconsumed message; the matching stream
  WINDOW_UPDATE is granted only when the handler consumes the message. -/
  pendingRequestCredits : Array Nat := #[]

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
  /-- Exact handler/stream-receive child currently owned by a timed dispatch.
  Optional with a default to preserve construction compatibility for callers
  that use this public diagnostic structure. -/
  private deadlineChild : Option (IO.Ref (Option DeadlineChild)) := none

/-- A custom request-header authorizer currently owned by the connection.
The callback itself runs without the connection-state mutex.  Keeping its
cancellation flag and exact child handle here lets shutdown signal it without
waiting for arbitrary user IO to release that mutex. -/
structure ActiveAuthorization where
  streamId : Nat
  cancelled : IO.Ref Bool
  private deadlineChild : IO.Ref (Option DeadlineChild)

def initialFlowControlWindow : Nat := 65535

/-- Advertised per-stream receive window (`SETTINGS_INITIAL_WINDOW_SIZE`): the
default 4 MiB gRPC message limit, its 5-byte frame prefix, and a 64 KiB margin.
A whole maximum-size message must fit inside one stream window, because
credit-on-consume flow control only replenishes the stream window once the
handler has consumed a *complete* message; see
`defaultStreamWindow_admits_max_message` and `inboundWindow_pos_of_incomplete`
for the deadlock-freedom argument. -/
@[expose] def defaultStreamWindow : Nat := 4194304 + 5 + 65536

/-- Upper bound on a reassembled HEADERS + CONTINUATION header block. -/
def maxHeaderBlockSize : Nat := 1048576

/-- Upper bound on buffered outbound frame payload bytes awaiting flow-control window. -/
def maxPendingOutboundBytes : Nat := 4194304

structure State where
  /-- Sticky once forced connection teardown has selected cancellation.  Work
  prepared before that selection must not publish a new handler afterward. -/
  closing : Bool := false
  prefaceReceived : Bool := false
  clientSettingsReceived : Bool := false
  prefaceBuffer : ByteArray := ByteArray.empty
  decoder : Frame.DecodeState := {}
  hpack : Hpack.State := {}
  /-- Response encoding uses a zero-sized dynamic table.  Concurrent HTTP/2
  streams may finish out of order; independent header blocks avoid stale
  encoder snapshots without putting arbitrary handler work behind one lock. -/
  outboundHpack : Hpack.State := Hpack.withoutDynamicTable {}
  lastClientStreamId : Nat := 0
  outboundGoAwayLastStreamId : Option Nat := none
  outboundConnectionWindow : Nat := initialFlowControlWindow
  outboundInitialStreamWindow : Nat := initialFlowControlWindow
  outboundMaxFramePayloadLength : Nat := defaultMaxFramePayloadLength
  inboundMaxFramePayloadLength : Nat := defaultMaxFramePayloadLength
  inboundConnectionWindow : Nat := initialFlowControlWindow
  inboundInitialStreamWindow : Nat := initialFlowControlWindow
  inboundMaxConcurrentStreams : Option Nat := none
  inboundMaxHeaderListSize : Option Nat := none
  inboundStreamWindows : Array InboundStreamWindow := #[]
  outboundStreamWindows : Array OutboundStreamWindow := #[]
  pendingOutbound : Array Frame := #[]
  streams : Array StreamState := #[]
  /-- Request bodies rejected without resetting the HTTP/2 stream. These remain
  active for concurrency and graceful-drain accounting until peer END_STREAM. -/
  ignoredInboundStreams : Array Nat := #[]
  /-- Locally reset streams whose late, in-flight DATA still needs connection
  flow-control accounting. Unlike `ignoredInboundStreams`, these streams are
  already closed and therefore consume neither concurrency slots nor drain time. -/
  resetInboundStreams : Array Nat := #[]
  /-- One incomplete field block received after a local reset. It is kept out
  of `streams` because the reset stream is closed, but must reach HPACK before
  any later frame can be processed. -/
  resetHeaderBlock : Option Frame := none
  /-- Streams accepted only so their field block is decoded, to be reset with
  RST_STREAM the moment the block has been read.  See
  `inboundStreamCapacityRefusal?`. -/
  refusedInboundStreams : Array Nat := #[]
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

def serverSettingsFrame (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : Except Status Frame :=
  let settings := #[]
  let settings := match maxConcurrentStreams with
    | none => settings
    | some value => settings.push { id := SettingId.maxConcurrentStreams, value := value }
  let settings := match maxHeaderListSize with
    | none => settings
    | some value => settings.push { id := SettingId.maxHeaderListSize, value := value }
  let settings :=
    if initialWindowSize == initialFlowControlWindow then
      settings
    else
      settings.push { id := SettingId.initialWindowSize, value := initialWindowSize }
  Settings.frame settings

def initialState (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : State :=
  {
    (default : State) with
    inboundMaxConcurrentStreams := maxConcurrentStreams,
    inboundMaxHeaderListSize := maxHeaderListSize,
    inboundInitialStreamWindow := initialWindowSize
  }

def isDrainedAfterOutboundGoAway (state : State) : Bool :=
  match state.outboundGoAwayLastStreamId with
  | none => false
  | some _ =>
      state.streams.isEmpty
        && state.ignoredInboundStreams.isEmpty
        && state.resetHeaderBlock.isNone
        && state.activeRequestStreams.isEmpty
        && state.activeDispatches.isEmpty
        && state.activeAuthorizations.isEmpty
        && state.pendingDispatchPublications.isEmpty
        && state.pendingOutbound.isEmpty

def serverPrefaceBytes (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : Except Status ByteArray := do
  let frame ← serverSettingsFrame maxConcurrentStreams maxHeaderListSize initialWindowSize
  Frame.encode frame

private def findStream? (streams : Array StreamState) (streamId : Nat) : Option StreamState :=
  streams.find? (fun stream => stream.streamId == streamId)

def removeStream (streams : Array StreamState) (streamId : Nat) : Array StreamState :=
  streams.filter (fun stream => stream.streamId != streamId)

private def appendStreamFrame (streams : Array StreamState) (frame : Frame) : Array StreamState :=
  (removeStream streams frame.header.streamId).push <|
    match findStream? streams frame.header.streamId with
    | some stream => { stream with frames := stream.frames.push frame }
    | none => { streamId := frame.header.streamId, frames := #[frame] }

private def replaceStream (streams : Array StreamState) (stream : StreamState) : Array StreamState :=
  (removeStream streams stream.streamId).push stream

private def recordEndHeadersReceivedAt (state : State) (streamId : Nat)
    (receivedAt : Option Nat) : State :=
  match receivedAt, findStream? state.streams streamId with
  | some receivedAt, some stream =>
      let stream := { stream with endHeadersReceivedAt := some receivedAt }
      { state with streams := replaceStream state.streams stream }
  | _, _ => state

private def findOutboundStreamWindow? (windows : Array OutboundStreamWindow) (streamId : Nat) :
    Option OutboundStreamWindow :=
  windows.find? (fun window => window.streamId == streamId)

private def removeOutboundStreamWindow (windows : Array OutboundStreamWindow) (streamId : Nat) :
    Array OutboundStreamWindow :=
  windows.filter (fun window => window.streamId != streamId)

def findInboundStreamWindow? (windows : Array InboundStreamWindow) (streamId : Nat) :
    Option InboundStreamWindow :=
  windows.find? (fun window => window.streamId == streamId)

private def removeInboundStreamWindow (windows : Array InboundStreamWindow) (streamId : Nat) :
    Array InboundStreamWindow :=
  windows.filter (fun window => window.streamId != streamId)

private def outboundStreamWindow (state : State) (streamId : Nat) : Int :=
  match findOutboundStreamWindow? state.outboundStreamWindows streamId with
  | some window => window.window
  | none => Int.ofNat state.outboundInitialStreamWindow

/-- The receive window currently advertised for `streamId`: the per-stream
entry when one exists, otherwise the connection's advertised initial window. -/
def inboundStreamWindow (state : State) (streamId : Nat) : Nat :=
  match findInboundStreamWindow? state.inboundStreamWindows streamId with
  | some window => window.window
  | none => state.inboundInitialStreamWindow

private def setOutboundStreamWindow (state : State) (streamId : Nat) (window : Int) : State :=
  {
    state with
    outboundStreamWindows := (removeOutboundStreamWindow state.outboundStreamWindows streamId).push {
      streamId := streamId,
      window := window
    }
  }

private def setInboundStreamWindow (state : State) (streamId window : Nat) : State :=
  {
    state with
    inboundStreamWindows := (removeInboundStreamWindow state.inboundStreamWindows streamId).push {
      streamId := streamId,
      window := window
    }
  }

private def replaceFirstFrame (frames : Array Frame) (frame : Frame) : Array Frame :=
  #[frame].append (frames.extract 1 frames.size)

private def popFirstFrame (frames : Array Frame) : Array Frame :=
  frames.extract 1 frames.size

private def removePendingOutboundForStream (frames : Array Frame) (streamId : Nat) : Array Frame :=
  frames.filter (fun frame => frame.header.streamId != streamId)

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

private def activeInboundStreamIds (state : State) : Array Nat :=
  let streamIds := state.streams.foldl
    (init := #[])
    (fun ids stream => pushUniqueStreamId ids stream.streamId)
  let streamIds := state.ignoredInboundStreams.foldl
    (init := streamIds)
    (fun ids streamId => pushUniqueStreamId ids streamId)
  let streamIds := state.pendingDispatchPublications.foldl
    (init := streamIds)
    (fun ids streamId => pushUniqueStreamId ids streamId)
  state.activeDispatches.foldl
    (init := streamIds)
    (fun ids dispatch => pushUniqueStreamId ids dispatch.streamId)

def activeInboundStreamCount (state : State) : Nat :=
  activeInboundStreamIds state |>.size

private def findActiveRequestStream? (streams : Array ActiveRequestStream) (streamId : Nat) :
    Option ActiveRequestStream :=
  streams.find? (fun stream => stream.streamId == streamId)

private def removeActiveRequestStream (streams : Array ActiveRequestStream) (streamId : Nat) :
    Array ActiveRequestStream :=
  streams.filter (fun stream => stream.streamId != streamId)

private def replaceActiveRequestStream (streams : Array ActiveRequestStream)
    (stream : ActiveRequestStream) : Array ActiveRequestStream :=
  (removeActiveRequestStream streams stream.streamId).push stream

private def removeOutboundStreamState (state : State) (streamId : Nat) : State :=
  {
    state with
    outboundStreamWindows := removeOutboundStreamWindow state.outboundStreamWindows streamId,
    pendingOutbound := removePendingOutboundForStream state.pendingOutbound streamId,
    activeDispatches := removeActiveDispatchesForStream state.activeDispatches streamId,
    pendingDispatchPublications := removeStreamId state.pendingDispatchPublications streamId
  }

private def removeInboundStreamState (state : State) (streamId : Nat) : State :=
  {
    state with
    inboundStreamWindows := removeInboundStreamWindow state.inboundStreamWindows streamId,
    ignoredInboundStreams := removeStreamId state.ignoredInboundStreams streamId,
    resetInboundStreams := removeStreamId state.resetInboundStreams streamId,
    resetHeaderBlock := state.resetHeaderBlock.bind fun frame =>
      if frame.header.streamId == streamId then none else some frame,
    refusedInboundStreams := removeStreamId state.refusedInboundStreams streamId,
    activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId
  }

private def ignoreInboundStreamBody (state : State) (streamId : Nat) : State :=
  {
    state with
    streams := removeStream state.streams streamId,
    ignoredInboundStreams := pushUniqueStreamId state.ignoredInboundStreams streamId
  }

private def drainResetInboundStreamBody (state : State) (streamId : Nat) : State :=
  {
    state with
    streams := removeStream state.streams streamId,
    ignoredInboundStreams := removeStreamId state.ignoredInboundStreams streamId,
    resetInboundStreams := pushUniqueStreamId state.resetInboundStreams streamId
  }

private def drainsInboundStreamBody (state : State) (streamId : Nat) : Bool :=
  containsStreamId state.ignoredInboundStreams streamId
    || containsStreamId state.resetInboundStreams streamId

/-- Client-initiated stream ids are the odd ones (RFC 9113 §5.1.1). -/
def isClientStreamId (streamId : Nat) : Bool :=
  streamId % 2 == 1

/-- Connection error.  RFC 9113 §5.1.1: "An endpoint that receives an
unexpected stream identifier MUST respond with a connection error
(Section 5.4.1) of type PROTOCOL_ERROR", and §6.1 says the same of a DATA frame
whose stream identifier is 0x00.  A frame that names no valid stream cannot be
scoped to one, so there is nothing to reset. -/
private def requireClientStreamId (streamId : Nat) (frameName : String) : Except Status Unit := do
  if streamId == 0 then
    throw (Status.internal s!"HTTP/2 {frameName} frame must use a stream id")
  if !isClientStreamId streamId then
    throw (Status.internal s!"HTTP/2 {frameName} frame uses a server-initiated stream id")

/-- Connection error.  RFC 9113 §5.1.1: "The identifier of a newly established
stream MUST be numerically greater than all streams that the initiating
endpoint has opened or reserved. ... An endpoint that receives an unexpected
stream identifier MUST respond with a connection error (Section 5.4.1) of type
PROTOCOL_ERROR."  Reusing an id means the two peers disagree about which stream
is which, which no per-stream reset can repair. -/
private def requireNewClientStreamId (state : State) (streamId : Nat) : Except Status Unit := do
  requireClientStreamId streamId "HEADERS"
  if streamId <= state.lastClientStreamId then
    throw (Status.internal "HTTP/2 client stream id must increase monotonically")

private def refusedStreamFrame (streamId : Nat) : Except Status Frame :=
  RstStream.frame streamId ErrorCode.refusedStream

private def rejectNewStreamAfterOutboundGoAway? (state : State) (streamId : Nat) :
    Except Status (Option Frame) := do
  match state.outboundGoAwayLastStreamId with
  | none => pure none
  | some lastStreamId =>
      if streamId > lastStreamId then
        some <$> refusedStreamFrame streamId
      else
        pure none

/-- `some REFUSED_STREAM` when opening one more stream would exceed the
advertised SETTINGS_MAX_CONCURRENT_STREAMS.

RFC 9113 §5.1.2: "An endpoint that receives a HEADERS frame that causes its
advertised concurrent stream limit to be exceeded MUST treat this as a stream
error (Section 5.4.2) of type PROTOCOL_ERROR or REFUSED_STREAM."  REFUSED_STREAM
is the better of the two here because §8.7 lets a client safely retry a stream
the server never processed, and because a client that is merely ahead of the
limit should back off rather than lose the connection.

The refusal is *recorded*, not raised: the stream is opened so its field block
still reaches the HPACK decoder, which RFC 9113 §4.3 requires of every field
block ("A receiver MUST terminate the connection with a connection error of
type COMPRESSION_ERROR if it does not decompress a field block"), and
`authorizeRequestHeadersForStream` resets it the moment the block is read. -/
private def inboundStreamCapacityRefusal? (state : State) : Option ErrorCode :=
  match state.inboundMaxConcurrentStreams with
  | none => none
  | some limit =>
      if activeInboundStreamCount state >= limit then
        some ErrorCode.refusedStream
      else
        none

private def headerComplete (frame : Frame) : Bool :=
  frame.header.frameType == FrameType.headers
    && FrameFlag.has frame.header.flags FrameFlag.endHeaders

private def streamHeaderComplete (stream : StreamState) : Bool :=
  match stream.frames[0]? with
  | some frame => headerComplete frame
  | none => false

/-- The stream's header block is still open: its first frame is a HEADERS frame
without END_HEADERS, so only CONTINUATION frames for this stream may follow. -/
def streamHeaderPending (stream : StreamState) : Bool :=
  match stream.frames[0]? with
  | some frame => frame.header.frameType == FrameType.headers && !headerComplete frame
  | none => false

def pendingHeaderStream? (streams : Array StreamState) : Option Nat :=
  streams.findSome? fun stream =>
    if streamHeaderPending stream then some stream.streamId else none

/-- Connection errors throughout.  RFC 9113 §6.10: "A CONTINUATION frame MUST
be preceded by a HEADERS, PUSH_PROMISE or CONTINUATION frame without the
END_HEADERS flag set.  A recipient that observes violation of this rule MUST
respond with a connection error (Section 5.4.1) of type PROTOCOL_ERROR."  The
oversized-block case is a connection error for the reason in §4.3 — a field
block that is not decompressed desynchronises the connection-wide HPACK
decoder, so it cannot be answered with RST_STREAM. -/
def appendContinuationFrame (streams : Array StreamState) (frame : Frame) :
    Except Status (Array StreamState) := do
  requireClientStreamId frame.header.streamId "CONTINUATION"
  let stream ← match findStream? streams frame.header.streamId with
    | some stream => pure stream
    | none => throw (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS")
  let headersFrame ← match stream.frames[0]? with
    | some headersFrame => pure headersFrame
    | none => throw (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS")
  if headersFrame.header.frameType != FrameType.headers then
    throw (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS")
  if headerComplete headersFrame then
    throw (Status.internal "unexpected HTTP/2 CONTINUATION after END_HEADERS")
  let payload := headersFrame.payload.append frame.payload
  if payload.size > maxHeaderBlockSize then
    throw (Status.internal "HTTP/2 header block exceeds the maximum supported size")
  let flags :=
    if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
      UInt8.ofNat (headersFrame.header.flags.toNat + FrameFlag.endHeaders.toNat)
    else
      headersFrame.header.flags
  let headersFrame := {
    headersFrame with
    header := { headersFrame.header with length := payload.size, flags := flags },
    payload := payload
  }
  pure <| replaceStream streams {
    stream with frames := replaceFirstFrame stream.frames headersFrame
  }

private def clearFlag (flags flag : UInt8) : UInt8 :=
  if FrameFlag.has flags flag then
    UInt8.ofNat (flags.toNat - flag.toNat)
  else
    flags

/-- Connection error.  RFC 9113 §6.1: "If the length of the padding is the
length of the frame payload or greater, the recipient MUST treat this as a
connection error (Section 5.4.1) of type PROTOCOL_ERROR."  The frame boundary
itself is in doubt, so the byte stream cannot be resynchronised per stream. -/
private def stripPadding (frame : Frame) (frameName : String) : Except Status Frame := do
  if !FrameFlag.has frame.header.flags FrameFlag.padded then
    pure frame
  else if frame.payload.size < 1 then
    throw (Status.internal s!"HTTP/2 padded {frameName} frame is missing the pad length octet")
  else
    let padLength := frame.payload[0]!.toNat
    let body := frame.payload.extract 1 frame.payload.size
    if padLength > body.size then
      throw (Status.internal s!"HTTP/2 {frameName} frame padding exceeds the payload length")
    else
      let payload := body.extract 0 (body.size - padLength)
      pure {
        frame with
        header := {
          frame.header with
          length := payload.size,
          flags := clearFlag frame.header.flags FrameFlag.padded
        },
        payload := payload
      }

/-- A truncated priority section is connection-fatal because it makes the
field-block boundary unknowable. Well-formed dependency fields are stripped and
otherwise ignored: RFC 9113 removed the RFC 7540 priority tree. -/
private def stripHeadersPriority (frame : Frame) : Except Status Frame := do
  if !FrameFlag.has frame.header.flags FrameFlag.priority then
    pure frame
  else if frame.payload.size < 5 then
    throw (Status.internal "HTTP/2 HEADERS frame priority section is truncated")
  else
    let payload := frame.payload.extract 5 frame.payload.size
    pure {
      frame with
      header := {
        frame.header with
        length := payload.size,
        flags := clearFlag frame.header.flags FrameFlag.priority
      },
      payload := payload
    }

/-- Strip the optional padding and priority sections from an inbound HEADERS frame so
downstream header-block handling sees only the header block fragment. Flow control does
not apply to HEADERS, so this can run before any window accounting. -/
private def normalizeHeadersFrame (frame : Frame) : Except Status Frame := do
  stripHeadersPriority (← stripPadding frame "HEADERS")

private def dataWindowUpdates (frame : Frame) : Except Status (Array Frame) := do
  if frame.payload.isEmpty then
    pure #[]
  else
    let connectionUpdate ← WindowUpdate.frame 0 frame.payload.size
    let streamUpdate ← WindowUpdate.frame frame.header.streamId frame.payload.size
    pure #[connectionUpdate, streamUpdate]

private def dataFrameWithPayload (frame : Frame) (payload : ByteArray) : Frame :=
  { frame with header := { frame.header with length := payload.size }, payload := payload }

/-- A partial DATA prefix is not the logical end of its stream.  Preserve every
other standard or extension flag while clearing only the low END_STREAM bit;
the queued suffix retains the original flags and therefore closes the stream
when it is eventually emitted. -/
private def withoutEndStream (frame : Frame) : Frame :=
  { frame with header := { frame.header with
      flags := clearFlag frame.header.flags FrameFlag.endStream } }

/-- Low-level receive-window debit. A connection-window overrun is necessarily
connection-fatal because the peer has lost track of shared credit. The public
frame transitions intercept an otherwise valid open stream's *stream-only*
overrun before calling this helper and emit RST_STREAM(FLOW_CONTROL_ERROR),
while direct/internal callers still receive an error for either insufficient
window. -/
def consumeInboundDataWindow (state : State) (frame : Frame) : Except Status State := do
  let size := frame.payload.size
  if size == 0 then
    pure state
  else if size > state.inboundConnectionWindow then
    throw (Status.internal "HTTP/2 DATA frame exceeds connection flow-control window")
  else
    let streamWindow := inboundStreamWindow state frame.header.streamId
    if size > streamWindow then
      throw (Status.internal "HTTP/2 DATA frame exceeds stream flow-control window")
    else
      let state := {
        state with inboundConnectionWindow := state.inboundConnectionWindow - size
      }
      pure (setInboundStreamWindow state frame.header.streamId (streamWindow - size))

private def replenishInboundConnectionWindow (state : State) (size : Nat) : State :=
  if size == 0 then
    state
  else
    { state with inboundConnectionWindow := state.inboundConnectionWindow + size }

private def replenishInboundStreamWindowBy (state : State) (streamId size : Nat) : State :=
  if size == 0 then
    state
  else
    setInboundStreamWindow state streamId (inboundStreamWindow state streamId + size)

/-- Window updates for DATA on a streaming request: the connection window is
credited for the whole frame immediately (so one stalled stream cannot starve
the connection), while the stream window is only credited for padding — the
payload's stream credit is granted when the handler consumes each message. -/
private def activeDataWindowUpdates (streamId originalSize paddingBytes : Nat) :
    Except Status (Array Frame) := do
  let updates := #[]
  let updates ←
    if originalSize == 0 then
      pure updates
    else do
      let connectionUpdate ← WindowUpdate.frame 0 originalSize
      pure (updates.push connectionUpdate)
  if paddingBytes == 0 then
    pure updates
  else do
    let streamUpdate ← WindowUpdate.frame streamId paddingBytes
    pure (updates.push streamUpdate)

private def replenishInboundDataWindow (state : State) (frame : Frame) : State :=
  let size := frame.payload.size
  if size == 0 then
    state
  else
    let streamWindow := inboundStreamWindow state frame.header.streamId
    let state := { state with inboundConnectionWindow := state.inboundConnectionWindow + size }
    setInboundStreamWindow state frame.header.streamId (streamWindow + size)

private def cleanupOutboundIfEndStream (state : State) (frame : Frame) : State :=
  if FrameFlag.has frame.header.flags FrameFlag.endStream then
    { state with outboundStreamWindows := removeOutboundStreamWindow state.outboundStreamWindows frame.header.streamId }
  else
    state

private theorem cleanupOutboundIfEndStream_pendingOutbound (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).pendingOutbound = state.pendingOutbound := by
  unfold cleanupOutboundIfEndStream
  split <;> rfl

private theorem popFirstFrame_size_lt {frames : Array Frame} {frame : Frame}
    (h : frames[0]? = some frame) : (popFirstFrame frames).size < frames.size := by
  have hpos : 0 < frames.size := (Array.getElem?_eq_some_iff.mp h).1
  simp only [popFirstFrame, Array.size_extract]
  omega

def flushOutbound (state : State) (emitted : Array Frame := #[]) :
    State × Array Frame :=
  match h : state.pendingOutbound[0]? with
  | none => (state, emitted)
  | some frame =>
      if frame.header.frameType != FrameType.data then
        let state := { state with pendingOutbound := popFirstFrame state.pendingOutbound }
        let state := cleanupOutboundIfEndStream state frame
        flushOutbound state (emitted.push frame)
      else
        let streamWindow := outboundStreamWindow state frame.header.streamId
        let streamWindowAvailable := streamWindow.toNat
        let available := Nat.min state.outboundConnectionWindow streamWindowAvailable
        if available == 0 then
          (state, emitted)
        else
          let sendSize := Nat.min available frame.payload.size
          let state := {
            state with
            outboundConnectionWindow := state.outboundConnectionWindow - sendSize
          }
          let state := setOutboundStreamWindow state frame.header.streamId
            (streamWindow - Int.ofNat sendSize)
          if sendSize == frame.payload.size then
            -- Reuse an exact-fit payload.  `dataFrameWithPayload` still
            -- normalizes the frame header for defensive direct callers, but
            -- no longer copies every fully admitted DATA payload.
            let sentFrame := dataFrameWithPayload frame frame.payload
            let state := { state with pendingOutbound := popFirstFrame state.pendingOutbound }
            let state := cleanupOutboundIfEndStream state sentFrame
            flushOutbound state (emitted.push sentFrame)
          else
            let sendPayload := frame.payload.extract 0 sendSize
            let sentFrame := dataFrameWithPayload (withoutEndStream frame) sendPayload
            let remaining := frame.payload.extract sendSize frame.payload.size
            let remainingFrame := dataFrameWithPayload frame remaining
            let state := {
              state with pendingOutbound := replaceFirstFrame state.pendingOutbound remainingFrame
            }
            (state, emitted.push sentFrame)
  termination_by state.pendingOutbound.size
  decreasing_by
    all_goals
      simp only [cleanupOutboundIfEndStream_pendingOutbound, setOutboundStreamWindow]
      exact popFirstFrame_size_lt h

/-- Queue an ordered outbound frame batch and emit the prefix admitted by peer
flow-control credit.  New frames are appended after any existing pending work,
then the single established flush path performs ordering and window debit. -/
def queueOutbound (state : State) (frames : Array Frame) : State × Array Frame :=
  flushOutbound { state with pendingOutbound := state.pendingOutbound.append frames }

private def addOutboundConnectionWindow (kind : String) (current increment : Nat) :
    Except Status Nat := do
  let updated := current + increment
  if updated > maxStreamId then
    throw (Status.internal s!"HTTP/2 {kind} flow-control window exceeds 31-bit length")
  else
    pure updated

private def addOutboundStreamWindow (kind : String) (current : Int) (increment : Nat) :
    Except Status Int := do
  let updated := current + Int.ofNat increment
  if updated > Int.ofNat maxStreamId then
    throw (Status.internal s!"HTTP/2 {kind} flow-control window exceeds 31-bit length")
  else
    pure updated

private def applyWindowUpdate (state : State) (frame : Frame) : Except Status State := do
  let increment ← WindowUpdate.decode frame
  if frame.header.streamId == 0 then
    let window ← addOutboundConnectionWindow "connection" state.outboundConnectionWindow increment
    pure { state with outboundConnectionWindow := window }
  else
    let window := outboundStreamWindow state frame.header.streamId
    let window ← addOutboundStreamWindow "stream" window increment
    pure (setOutboundStreamWindow state frame.header.streamId window)

private def processWindowUpdate (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  if frame.header.streamId != 0 then
    requireClientStreamId frame.header.streamId "WINDOW_UPDATE"
  let state ← applyWindowUpdate state frame
  pure (flushOutbound state)

private def adjustWindow (oldInitial newInitial : Nat) (current : Int) : Int :=
  current + Int.ofNat newInitial - Int.ofNat oldInitial

/-- Re-base every outbound stream window on a new SETTINGS_INITIAL_WINDOW_SIZE,
rejecting any window that would leave the 31-bit range.  Written as an explicit
`foldlM` (rather than `mapM`) so the bound on the result is provable by list
induction. -/
private def adjustOutboundWindowStep (oldInitial newInitial : Nat)
    (accumulated : Array OutboundStreamWindow) (window : OutboundStreamWindow) :
    Except Status (Array OutboundStreamWindow) :=
  if adjustWindow oldInitial newInitial window.window > Int.ofNat maxStreamId then
    throw (Status.internal "HTTP/2 stream flow-control window exceeds 31-bit length")
  else
    pure (accumulated.push
      { window with window := adjustWindow oldInitial newInitial window.window })

private def adjustOutboundWindows (oldInitial newInitial : Nat)
    (windows : Array OutboundStreamWindow) : Except Status (Array OutboundStreamWindow) :=
  windows.foldlM (init := #[]) (adjustOutboundWindowStep oldInitial newInitial)

/-- Connection error.  RFC 9113 §6.5.2: "Values above the maximum flow-control
window size of 2^31-1 MUST be treated as a connection error (Section 5.4.1) of
type FLOW_CONTROL_ERROR."  A SETTINGS frame is connection-scoped, so there is no
stream to reset. -/
private def applyInitialWindowSize (state : State) (value : Nat) : Except Status State := do
  if value > maxStreamId then
    throw (Status.internal "HTTP/2 SETTINGS_INITIAL_WINDOW_SIZE exceeds 31-bit length")
  let windows ← adjustOutboundWindows state.outboundInitialStreamWindow value
    state.outboundStreamWindows
  pure {
    state with
    outboundInitialStreamWindow := value,
    outboundStreamWindows := windows
  }

/-- Connection error.  RFC 9113 §6.5.2: SETTINGS_MAX_FRAME_SIZE "The initial
value is 2^14 octets ... Values outside this range MUST be treated as a
connection error (Section 5.4.1) of type PROTOCOL_ERROR." -/
private def applyMaxFrameSize (state : State) (value : Nat) : Except Status State := do
  if value < defaultMaxFramePayloadLength || value > maxFramePayloadLength then
    throw (Status.internal "HTTP/2 SETTINGS_MAX_FRAME_SIZE is outside the allowed range")
  pure { state with outboundMaxFramePayloadLength := value }

private def applyPeerSetting (state : State) (setting : Setting) : Except Status State := do
  match setting.id with
  | .headerTableSize =>
      pure { state with outboundHpack :=
        Hpack.setMaxAllowedSizeWithoutDynamicTable state.outboundHpack setting.value }
  | .enablePush =>
      if setting.value == 0 || setting.value == 1 then
        pure state
      else
        -- Connection error.  RFC 9113 §6.5.2: SETTINGS_ENABLE_PUSH "Any value
        -- other than 0 or 1 MUST be treated as a connection error
        -- (Section 5.4.1) of type PROTOCOL_ERROR."
        throw (Status.internal "HTTP/2 SETTINGS_ENABLE_PUSH must be 0 or 1")
  | .initialWindowSize =>
      applyInitialWindowSize state setting.value
  | .maxFrameSize =>
      applyMaxFrameSize state setting.value
  | .maxConcurrentStreams =>
      pure state
  | .maxHeaderListSize =>
      pure state
  | .unknown _ =>
      pure state

private def applyPeerSettings (state : State) (settings : Array Setting) : Except Status State :=
  settings.foldlM (init := state) applyPeerSetting

/-- Connection error.  RFC 9113 §3.4: "Clients and servers MUST treat an
invalid connection preface as a connection error (Section 5.4.1) of type
PROTOCOL_ERROR."  No stream exists yet to scope an error to. -/
private def consumePreface (state : State) (chunk : ByteArray) : Except Status (State × ByteArray) := do
  if state.prefaceReceived then
    pure (state, chunk)
  else
    let buffered := state.prefaceBuffer.append chunk
    if buffered.size < connectionPreface.size then
      pure ({ state with prefaceBuffer := buffered }, ByteArray.empty)
    else
      let seenPreface := buffered.extract 0 connectionPreface.size
      if seenPreface != connectionPreface then
        throw (Status.internal "invalid HTTP/2 client connection preface")
      else
        pure (
          { state with prefaceReceived := true, prefaceBuffer := ByteArray.empty },
          buffered.extract connectionPreface.size buffered.size
        )

private def emitFrameBatch (emit : Array Frame -> IO Unit) (frames : Array Frame) :
    IO (Except Status Unit) := do
  if frames.isEmpty then
    pure (.ok ())
  else
    try
      emit frames
      pure (.ok ())
    catch err =>
      pure (.error (Status.ofIOError err))

private def emitResultFrames (emit : Array Frame -> IO Unit)
    (result : Except Status (State × Array Frame)) : IO (Except Status State) := do
  match result with
  | .error status => pure (.error status)
  | .ok (state, frames) =>
      match ← emitFrameBatch emit frames with
      | .error status => pure (.error status)
      | .ok () => pure (.ok state)

structure DetachedDispatch where
  request : Transport.UnaryRequestFrames
  outboundHpack : Hpack.State
  maxDataFrameSize : Nat
  private deadlineScheduler : Option DeadlineScheduler := none

/-- The dispatch family for a request whose body is fed to the handler
incrementally, carrying the authorized handler at its exact shape. -/
inductive RequestStreamingKind where
  | clientStreaming (handler : ClientStreamingStreamHandler)
  | bidirectionalStreaming (handler : BidirectionalStreamingStreamHandler)

structure RequestStreamingDispatch where
  streamId : Nat
  metadata : Metadata
  outboundHpack : Hpack.State
  maxDataFrameSize : Nat
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
  metadata : Metadata
  preflight : Headers.RequestPreflight
  deadline : Option Nat
  endStream : Bool
  scheduler : DeadlineScheduler
  active : ActiveAuthorization

private inductive RequestHeaderAuthorization where
  | accepted
  | rejected (frames : Array Frame)
  | pending (authorization : PendingAuthorization)

structure SharedFrameResult where
  emitted : Array Frame := #[]
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

private def requestStreamingDispatchForStream? (state : State)
    (streamId : Nat) : Except Status (State × Option RequestStreamingDispatch) := do
  let stream ← match findStream? state.streams streamId with
    | some stream => pure stream
    | none => throw (Status.internal s!"unknown HTTP/2 stream {streamId}")
  let headersFrame ← match stream.frames[0]? with
    | some frame => pure frame
    | none => throw (Status.internal "missing HTTP/2 HEADERS frame")
  if !headerComplete headersFrame then
    pure (state, none)
  else
    let entry ← match stream.authorizedEntry? with
      | some entry => pure entry
      | none =>
          throw (Status.internal "request body dispatch attempted before header authorization")
    let metadata ← match stream.requestMetadata with
      | some metadata => pure metadata
      | none => throw (Status.internal "authorized request metadata was not retained")
    let preflight ← match stream.requestPreflight with
      | some preflight => pure preflight
      | none => throw (Status.internal "authorized request preflight was not retained")
    match requestStreamingKind? entry with
    | none => pure (state, none)
    | some kind =>
        let closeImmediately := FrameFlag.has headersFrame.header.flags FrameFlag.endStream
        let requestError :=
          if closeImmediately then
            match Headers.validateContentLengthValue preflight.contentLength 0 with
            | .ok () => none
            | .error status => some status
          else
            none
        let state := {
          state with
          streams :=
            if closeImmediately then
              removeStream state.streams streamId
            else
              state.streams
        }
        let state :=
          if closeImmediately then
            removeInboundStreamState state streamId
          else
            state
        -- Removing the buffered stream and publishing its handler are two
        -- separate mutex transitions.  Retain an explicit ownership token in
        -- between so graceful drain cannot mistake that interval for an idle
        -- connection.
        let state := {
          state with
          pendingDispatchPublications :=
            pushUniqueStreamId state.pendingDispatchPublications streamId
        }
        pure (state, some {
          streamId := streamId,
          metadata := metadata,
          deadline := stream.deadline,
          deadlineScheduler := state.deadlineScheduler,
          outboundHpack := state.outboundHpack,
          maxDataFrameSize := state.outboundMaxFramePayloadLength,
          kind := kind,
          preflight := preflight,
          requestError := requestError,
          closeImmediately := closeImmediately
        })

/-- Pure state transition for a request rejected at completed request
headers: the buffered stream is dropped and the stream id is either forgotten
entirely (the request already carried END_STREAM) or put in drain-only mode
so later DATA is consumed without dispatch.  See the authorization-before-body
properties section at the end of this file for the theorems about
this transition. -/
def rejectStreamAtHeaders (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) (endStream : Bool) : State :=
  let state := {
    state with
    hpack := inboundHpack,
    outboundHpack := outboundHpack,
    streams := removeStream state.streams streamId
  }
  if endStream then
    removeInboundStreamState state streamId
  else
    ignoreInboundStreamBody state streamId

/-- Rejecting one stream commits the already-decoded connection-wide HPACK
state (and the encoder state used for its rejection response) regardless of
whether the peer ended the request at HEADERS.  This is the key reason a
stream-scoped header error cannot desynchronise later streams. -/
theorem rejectStreamAtHeaders_tables (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) (endStream : Bool) :
    let rejected := rejectStreamAtHeaders state streamId inboundHpack outboundHpack endStream
    rejected.hpack = inboundHpack ∧ rejected.outboundHpack = outboundHpack := by
  unfold rejectStreamAtHeaders
  split <;> exact ⟨rfl, rfl⟩

private def authorizeRequestHeadersForStream (registry : Registry) (state : State)
    (streamId : Nat) : IO (Except Status (State × RequestHeaderAuthorization)) := do
  let decoded : Except Status (StreamState × Frame × Transport.RequestHeadersFrames) := do
    let stream ← match findStream? state.streams streamId with
      | some stream => pure stream
      | none => throw (Status.internal s!"unknown HTTP/2 stream {streamId}")
    let headersFrame ← match stream.frames[0]? with
      | some frame => pure frame
      | none => throw (Status.internal "missing HTTP/2 HEADERS frame")
    if !headerComplete headersFrame then
      throw (Status.internal "request header authorization ran before END_HEADERS")
    let headers ← Transport.decodeRequestHeadersFrame
      state.hpack headersFrame state.inboundMaxHeaderListSize
    pure (stream, headersFrame, headers)
  match decoded with
  | .error status => pure (.error status)
  | .ok (stream, _headersFrame, headers) =>
    if containsStreamId state.refusedInboundStreams streamId then
      -- The field block is decoded (`headers.hpack` carries the advanced
      -- decoder), so the connection stays in step; the stream itself is reset.
      -- RFC 9113 §5.1.2 / §5.4.2.
      match RstStream.frame streamId ErrorCode.refusedStream with
      | .error status => pure (.error status)
      | .ok rst =>
          let state := {
            state with
            refusedInboundStreams := removeStreamId state.refusedInboundStreams streamId
          }
          let state := rejectStreamAtHeaders state streamId headers.hpack
            state.outboundHpack headers.endStream
          let state :=
            if headers.endStream then state else drainResetInboundStreamBody state streamId
          pure (.ok (state, .rejected #[rst]))
    else
      match Transport.preflightEarlyRequest registry state.outboundHpack streamId
          headers.metadata state.outboundMaxFramePayloadLength with
      | .error status => pure (.error status)
      | .ok (.reject frames outboundHpack) =>
          pure (.ok (rejectStreamAtHeaders state streamId headers.hpack outboundHpack
            headers.endStream, .rejected frames))
      | .ok (.accept entry preflight) =>
          -- Derive the absolute deadline exactly once, anchored to the frame
          -- arrival that completed END_HEADERS, before any authorizer IO.
          let deadline ←
            Deadline.fromTimeoutAt? preflight.timeout stream.endHeadersReceivedAt
          let authorizeNow : IO (Except Status (State × RequestHeaderAuthorization)) := do
            match ← Transport.authorizePreflightedEarlyRequest registry state.outboundHpack
                streamId headers.metadata entry state.outboundMaxFramePayloadLength deadline with
            | .error status => pure (.error status)
            | .ok (.accept authorizedEntry) =>
                let stream := {
                  stream with
                  requestMetadata := some headers.metadata,
                  requestPreflight := some preflight,
                  deadline := deadline,
                  authorizedEntry? := some authorizedEntry
                }
                pure (.ok ({
                  state with
                  hpack := headers.hpack,
                  streams := replaceStream state.streams stream
                }, .accepted))
            | .ok (.reject frames outboundHpack) =>
                pure (.ok (rejectStreamAtHeaders state streamId headers.hpack outboundHpack
                  headers.endStream, .rejected frames))
          match state.deadlineScheduler with
          | some scheduler =>
              if registry.usesCustomRequestHeaderAuthorizer then
                let cancelled ← IO.mkRef false
                let deadlineChild ← IO.mkRef (none : Option DeadlineChild)
                let active : ActiveAuthorization := {
                  streamId := streamId,
                  cancelled := cancelled,
                  deadlineChild := deadlineChild
                }
                let stream := {
                  stream with
                  requestMetadata := some headers.metadata,
                  requestPreflight := some preflight,
                  deadline := deadline,
                  authorizedEntry? := none
                }
                let state := {
                  state with
                  hpack := headers.hpack,
                  streams := replaceStream state.streams stream,
                  activeAuthorizations := state.activeAuthorizations.push active
                }
                pure (.ok (state, .pending {
                  streamId := streamId,
                  entry := entry,
                  metadata := headers.metadata,
                  preflight := preflight,
                  deadline := deadline,
                  endStream := headers.endStream,
                  scheduler := scheduler,
                  active := active
                }))
              else
                authorizeNow
          | none => authorizeNow

private def earlyRequestRejectionForStream? (registry : Registry) (state : State) (streamId : Nat) :
    IO (Except Status (State × Option SharedFrameResult)) := do
  match ← authorizeRequestHeadersForStream registry state streamId with
  | .error status => pure (.error status)
  | .ok (state, .accepted) => pure (.ok (state, none))
  | .ok (state, .rejected frames) => pure (.ok (state, some { emitted := frames }))
  | .ok (state, .pending authorization) =>
      pure (.ok (state, some { pendingAuthorization := some authorization }))

private def processIgnoredInboundData (state : State) (frame : Frame) :
    Except Status (State × Array Frame) := do
  let state ← consumeInboundDataWindow state frame
  let updates ← dataWindowUpdates frame
  let state := replenishInboundDataWindow state frame
  let frame ← stripPadding frame "DATA"
  discard <| Transport.normalizeDataFrame frame
  let state :=
    if FrameFlag.has frame.header.flags FrameFlag.endStream then
      removeInboundStreamState state frame.header.streamId
    else
      state
  pure (state, updates)

/-- DATA received after a local RST_STREAM is still charged to connection flow
control, but the closed stream no longer has a receive window to replenish. -/
private def processResetInboundData (state : State) (frame : Frame) :
    Except Status (State × Array Frame) := do
  let size := frame.payload.size
  if size > state.inboundConnectionWindow then
    throw (Status.internal "HTTP/2 DATA frame exceeds connection flow-control window")
  let updates ←
    if size == 0 then
      pure #[]
    else
      let update ← WindowUpdate.frame 0 size
      pure #[update]
  let frame ← stripPadding frame "DATA"
  discard <| Transport.normalizeDataFrame frame
  let state :=
    if FrameFlag.has frame.header.flags FrameFlag.endStream then
      removeInboundStreamState state frame.header.streamId
    else
      state
  pure (state, updates)

private def processDrainingInboundData (state : State) (frame : Frame) :
    Except Status (State × Array Frame) :=
  if containsStreamId state.resetInboundStreams frame.header.streamId then
    processResetInboundData state frame
  else
    processIgnoredInboundData state frame

/-- Content-length policing for a streaming request body.  `exact` is set at
END_STREAM, where the received size must match rather than merely not exceed
the declared one. -/
private def checkContentLength? (contentLength : Option Nat) (received : Nat) (exact : Bool) :
    Option Status :=
  match contentLength with
  | none => none
  | some expected =>
      if exact then
        match Headers.validateContentLengthValue contentLength received with
        | .ok () => none
        | .error status => some status
      else
        if received > expected then
          some (Status.invalidArgument
            s!"content-length {expected} is smaller than received request body size {received}")
        else
          none

/-- Record the decoder's residue and queue one deferred stream credit per
message it completed.  Each credit is that message's wire size, so the credits
plus the residue account for every byte the peer's DATA frames delivered. -/
private def queueRequestCredits (active : ActiveRequestStream) (decoded : Message.DecodeState)
    (receivedBodyBytes : Nat) : ActiveRequestStream :=
  {
    active with
    decodeState := { buffered := decoded.buffered },
    receivedBodyBytes := receivedBodyBytes,
    pendingRequestCredits := active.pendingRequestCredits.append
      (decoded.messages.map (fun message => Message.prefixLength + message.data.size))
  }

def decodeActiveRequestData (registry : Registry) (active : ActiveRequestStream)
    (frame : Frame) : Except Status (ActiveRequestStream × Array ByteArray × Bool) :=
  match checkContentLength? active.contentLength
      (active.receivedBodyBytes + frame.payload.size) false with
  | some status => .error status
  | none =>
    match Message.decodeChunkWithLimit registry.maxReceiveMessageSize
        active.decodeState frame.payload with
    | .error status => .error status
    | .ok decoded =>
      match decoded.messages.mapM (fun message =>
          (match Message.decompress active.usesGzip
              (registry.maxReceiveMessageSize.getD Message.defaultMaxDecompressedSize) message with
            | .error status => Except.error status
            | .ok decompressed => Except.ok decompressed.data : Except Status ByteArray)) with
      | .error status => .error status
      | .ok messages =>
        if FrameFlag.has frame.header.flags FrameFlag.endStream && !decoded.buffered.isEmpty then
          .error (Status.internal "incomplete gRPC message")
        else
          match checkContentLength? active.contentLength
              (active.receivedBodyBytes + frame.payload.size)
              (FrameFlag.has frame.header.flags FrameFlag.endStream) with
          | some status => .error status
          | none =>
              .ok (queueRequestCredits active decoded
                    (active.receivedBodyBytes + frame.payload.size),
                messages, FrameFlag.has frame.header.flags FrameFlag.endStream)

private def authorizedUnaryRequestForStream (state : State) (stream : StreamState) :
    Except Status Transport.UnaryRequestFrames := do
  let entry ← match stream.authorizedEntry? with
    | some entry => pure entry
    | none =>
        throw (Status.internal "request body dispatch attempted before header authorization")
  let metadata ← match stream.requestMetadata with
    | some metadata => pure metadata
    | none => throw (Status.internal "authorized request metadata was not retained")
  let preflight ← match stream.requestPreflight with
    | some preflight => pure preflight
    | none => throw (Status.internal "authorized request preflight was not retained")
  let body ← (stream.frames.extract 1 stream.frames.size).foldlM
    (init := ByteArray.empty) fun body frame => do
      if frame.header.streamId != stream.streamId then
        throw (Status.internal "HTTP/2 request frames changed stream id")
      if frame.header.frameType != FrameType.data then
        throw (Status.internal "expected HTTP/2 DATA frame")
      let frame ← Transport.normalizeDataFrame frame
      pure (body.append frame.payload)
  pure {
    streamId := stream.streamId,
    metadata := metadata,
    deadline := stream.deadline,
    body := body,
    hpack := state.hpack,
    authorizedEntry? := some entry,
    preflight? := some preflight
  }

private def detachStreamForDispatch (state : State) (streamId : Nat) :
    Except Status (State × DetachedDispatch) :=
  match findStream? state.streams streamId with
  | none => .error (Status.internal s!"unknown HTTP/2 stream {streamId}")
  | some stream =>
    match authorizedUnaryRequestForStream state stream with
    | .error status => .error status
    | .ok request =>
        let detachedState := removeInboundStreamState
          { state with streams := removeStream state.streams streamId } streamId
        let detachedState := {
          detachedState with
          pendingDispatchPublications :=
            pushUniqueStreamId detachedState.pendingDispatchPublications streamId
        }
        .ok (detachedState, {
          request := request,
          outboundHpack := detachedState.outboundHpack,
          maxDataFrameSize := detachedState.outboundMaxFramePayloadLength,
          deadlineScheduler := detachedState.deadlineScheduler
        })

private def framePayloadBytes (frames : Array Frame) : Nat :=
  frames.foldl (fun total frame => total + frame.payload.size) 0

private def queueOutboundShared (stateMutex : Std.Mutex State) (emit : Array Frame -> IO Unit)
    (frames : Array Frame) : IO (Except Status Unit) := do
  let emitted? ← stateMutex.atomically do
    let state ← get
    if state.closing then
      pure (Except.error (Status.cancelled "HTTP/2 connection is closing"))
    else if framePayloadBytes state.pendingOutbound + framePayloadBytes frames
        > maxPendingOutboundBytes then
      pure (Except.error
        (Status.resourceExhausted "HTTP/2 outbound buffer limit exceeded: peer is not consuming flow-controlled data"))
    else
      let (state, emitted) := queueOutbound state frames
      set state
      pure (Except.ok emitted)
  match emitted? with
  | .error status => pure (.error status)
  | .ok emitted => emitFrameBatch emit emitted

/-- A header-authorized request that has not reached dispatch yet.  Incremental
request handlers already have their own deadline race, so excluding active
dispatch ids prevents two owners from expiring the same stream. -/
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
connection event-loop timer as a fail-safe and compatibility path. -/
def nextPendingDeadline? (state : State) : Option Nat :=
  state.streams.foldl (init := none) fun nearest stream =>
    if pendingDeadlineStream state stream then
      nearerDeadline nearest stream.deadline
    else
      nearest

/-- Deadline for a connection event loop that does not have an independent
scheduler. Managed connections install that scheduler before processing input,
so racing the same absolute instant with another `Selector.sleep` only
allocates a redundant timer. Direct state-machine owners that leave the
scheduler absent retain the compatibility fallback. -/
def nextPendingDeadlineFallback? (state : State) : Option Nat :=
  if state.deadlineScheduler.isSome then
    none
  else
    nextPendingDeadline? state

private def terminatePendingDeadlineStream (state : State) (stream : StreamState)
    (status : Status) : Except Status (State × Array Frame) := do
  let encoded ← Transport.encodeUnaryResponseFrames state.outboundHpack stream.streamId
    { status := status, data := ByteArray.empty }
    state.outboundMaxFramePayloadLength
  let state := removeOutboundStreamState
    { state with outboundHpack := encoded.2 } stream.streamId
  let peerEnded := stream.frames.any fun frame =>
    FrameFlag.has frame.header.flags FrameFlag.endStream
  let state :=
    if peerEnded then
      removeInboundStreamState
        { state with streams := removeStream state.streams stream.streamId }
        stream.streamId
    else
      ignoreInboundStreamBody state stream.streamId
  pure (state, encoded.1)

/-- Terminate one exact pending-body generation from the independent scheduler.
The state/deadline checks make timer delivery harmless after END_STREAM, reset,
or another owner has already won. -/
private def terminatePendingDeadlineSharedWith (stateMutex : Std.Mutex State)
    (emit : Array Frame → IO Unit) (streamId expectedDeadline : Nat)
    (status : Status) (requireDue : Bool) : IO (Except Status Unit) := do
  let now ← IO.monoNanosNow
  let prepared ← stateMutex.atomically do
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
    (stateMutex : Std.Mutex State) (emit : Array Frame → IO Unit)
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
    (emit : Array Frame → IO Unit) (streamId : Nat) : IO Unit := do
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
    (emit : Array Frame -> IO Unit) : IO (Except Status Unit) := do
  let now ← IO.monoNanosNow
  let prepared ← stateMutex.atomically do
    let state ← get
    if state.closing then
      pure (Except.ok #[])
    else
      let expired := state.streams.filter fun stream =>
        pendingDeadlineStream state stream
          && stream.deadline.any (fun deadline => deadline <= now)
      let result : Except Status (State × Array Frame) :=
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

/-- Run a prepared custom authorizer with exact child ownership.  Timed calls
share the connection scheduler; untimed custom callbacks still get a retained
cancellable task so shutdown never loses the computation merely because no
deadline was supplied. -/
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
                authorization.active.deadlineChild (some authorization.scheduler)
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
        pure (.ok { authorization.entry with handler := handler })

/-- Commit an authorization result against current connection state.  The
outbound HPACK encoder is intentionally read only now—not when the callback
started—because other streams may have completed while user IO was running. -/
private def commitPendingAuthorization (stateMutex : Std.Mutex State)
    (authorization : PendingAuthorization) (decision : Except Status MethodEntry) :
    IO (Except Status SharedFrameResult) := do
  stateMutex.atomically do
    let state ← get
    let isOwned := state.activeAuthorizations.any fun active =>
      active.streamId == authorization.streamId
    if state.closing || !isOwned || (← authorization.active.cancelled.get) then
      pure (.ok {})
    else
      match findStream? state.streams authorization.streamId with
      | none => pure (.ok {})
      | some stream =>
          match decision with
          | .error status =>
              match Transport.encodeUnaryResponseFrames state.outboundHpack
                  authorization.streamId
                  { status := status, data := ByteArray.empty }
                  state.outboundMaxFramePayloadLength with
              | .error encodeStatus => pure (.error encodeStatus)
              | .ok encoded =>
                  let state := rejectStreamAtHeaders state authorization.streamId
                    state.hpack encoded.2 authorization.endStream
                  set state
                  pure (.ok { emitted := encoded.1 })
          | .ok entry =>
              let stream := {
                stream with
                requestPreflight := some authorization.preflight,
                authorizedEntry? := some entry
              }
              let state := { state with streams := replaceStream state.streams stream }
              match requestStreamingDispatchForStream? state authorization.streamId with
              | .error status => pure (.error status)
              | .ok (state, some requestStreaming) =>
                  set state
                  pure (.ok { requestStreaming := some requestStreaming })
              | .ok (state, none) =>
                  if authorization.endStream then
                    match detachStreamForDispatch state authorization.streamId with
                    | .error status => pure (.error status)
                    | .ok (state, detached) =>
                        set state
                        pure (.ok { detached := some detached })
                  else
                    set state
                    pure (.ok {})

private def retirePendingAuthorization (stateMutex : Std.Mutex State)
    (authorization : PendingAuthorization) : IO Unit := do
  stateMutex.atomically do
    modify fun state => {
      state with
      activeAuthorizations := removeActiveAuthorizationsForStream
        state.activeAuthorizations authorization.streamId
    }

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
  | some status => feed.producer.fail status
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

namespace TestSupport

/-- Benchmark seam for the exact dispatch-registration gate used by production
dispatch tasks.  Keeping the adapter here avoids duplicating its task/promise
behavior in measurement code. -/
def waitUntilDispatchRegisteredForBenchmark
    (registered : IO.Promise Unit) : Std.Async.Async Unit :=
  waitUntilDispatchRegistered registered

/-- Benchmark seam for the exact unary-body assembly performed when an
authorized stream detaches for dispatch. -/
def authorizedUnaryRequestForStreamForBenchmark (state : State) (stream : StreamState) :
    Except Status Transport.UnaryRequestFrames :=
  authorizedUnaryRequestForStream state stream

end TestSupport

/-- Drop all connection-level state for a stream and send RST_STREAM so the peer learns
the stream is dead instead of waiting on a response that will never arrive. -/
private def abortStreamShared (stateMutex : Std.Mutex State) (emit : Array Frame -> IO Unit)
    (streamId : Nat) (code : ErrorCode) : IO Unit := do
  stateMutex.atomically do
    let state ← get
    let peerEnded := (findActiveRequestStream? state.activeRequestStreams streamId).isNone
    let state := { state with streams := removeStream state.streams streamId }
    let state := removeInboundStreamState state streamId
    let state := removeOutboundStreamState state streamId
    set (if peerEnded then state else drainResetInboundStreamBody state streamId)
  match RstStream.frame streamId code with
  | .error _ => pure ()
  | .ok rst =>
      try
        emit #[rst]
      catch _ =>
        pure ()

/-- A deliberate connection/stream teardown has already selected the wire-level
error (or received one from the peer). In that case task cancellation performs
bookkeeping only; an unrelated INTERNAL_ERROR reset would contradict it. -/
private def abortStreamSharedUnlessCancelled (cancelled : IO.Ref Bool)
    (stateMutex : Std.Mutex State) (emit : Array Frame -> IO Unit)
    (streamId : Nat) (code : ErrorCode) : IO Unit := do
  unless ← cancelled.get do
    abortStreamShared stateMutex emit streamId code

private def spawnDetachedDispatch (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (detached : DetachedDispatch) : Std.Async.Async Unit := do
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
  let emitOutbound (frames : Array Frame) : IO Unit := do
    if ← IO.checkCanceled then
      throw (IO.userError Status.dispatchCancelledMessage)
    else if ← cancelled.get then
      throw (IO.userError Status.dispatchCancelledMessage)
    else
      match ← queueOutboundShared stateMutex emit frames with
      | .ok () => pure ()
      | .error status => throw (IO.userError status.messageD)
  let task ← Std.Async.Async.toIO do
    waitUntilDispatchRegistered registered
    if ← cancelled.get then
      pure ()
    else try
      let result ← Transport.dispatchDecodedUnaryFramesWithAsync
          registry detached.outboundHpack detached.request emitOutbound detached.maxDataFrameSize
          registerResponseStream true deadlineRuntime?
      joinDeadlineChildRef? deadlineChild?
      match result with
      | .ok result =>
          stateMutex.atomically do
            let state ← get
            let activeDispatches := removeActiveDispatchesForStream
              state.activeDispatches detached.request.streamId
            set {
              state with
              outboundHpack := result.outboundHpack,
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
            detached.request.streamId ErrorCode.internalError
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
        detached.request.streamId ErrorCode.internalError
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
def takeRequestStreamCredit (state : State) (streamId : Nat) : State × Nat :=
  match findActiveRequestStream? state.activeRequestStreams streamId with
  | none => (state, 0)
  | some active =>
      match active.pendingRequestCredits[0]? with
      | none => (state, 0)
      | some credit =>
          let credited := replenishInboundStreamWindowBy state streamId credit
          ({ credited with
              activeRequestStreams := replaceActiveRequestStream credited.activeRequestStreams
                { active with
                  pendingRequestCredits :=
                    active.pendingRequestCredits.extract 1 active.pendingRequestCredits.size } },
            credit)

/-- Pop the wire size of the next consumed message and send the deferred
stream WINDOW_UPDATE for it, keeping our inbound window accounting in sync. -/
private def grantRequestStreamCredit (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (streamId : Nat) : IO (Except Status Unit) := do
  let credit ← stateMutex.atomically do
    let state ← get
    let (state, credit) := takeRequestStreamCredit state streamId
    set state
    pure credit
  if credit == 0 then
    pure (.ok ())
  else
    match WindowUpdate.frame streamId credit with
    | .error status => pure (.error status)
    | .ok frame => queueOutboundShared stateMutex emit #[frame]

/-- Wrap a streaming request body so each consumed message grants its deferred
stream flow-control credit back to the peer. -/
private def creditingRequestStream (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (streamId : Nat)
    (inner : MessageStream ByteArray) : MessageStream ByteArray :=
  {
    recv? := ExceptT.mk do
      match ← inner.recv?.run with
      | .error status => pure (.error status)
      | .ok none => pure (.ok none)
      | .ok (some item) =>
          match ← grantRequestStreamCredit stateMutex emit streamId with
          | .ok () => pure (.ok (some item))
          | .error status => pure (.error status)
    cancel := inner.cancel
  }

private def spawnRequestStreamingDispatch (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (dispatch : RequestStreamingDispatch) :
    Std.Async.Async (Except Status Unit) := do
  let producer ← match ← runGrpcPipe with
    | .ok producer => pure producer
    | .error status => return .error status
  let rawRequestStream := creditingRequestStream stateMutex emit dispatch.streamId producer.stream
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
  let emitOutbound (frames : Array Frame) : IO Unit := do
    if ← IO.checkCanceled then
      throw (IO.userError Status.dispatchCancelledMessage)
    else if ← cancelled.get then
      throw (IO.userError Status.dispatchCancelledMessage)
    else
      match ← queueOutboundShared stateMutex emit frames with
      | .ok () => pure ()
      | .error status => throw (IO.userError status.messageD)
  let finish (outboundHpack : Option Hpack.State) : Std.Async.Async Unit := do
    joinDeadlineChildRef? deadlineChild?
    cancelRequestStreamRef requestStreamCancel
    stateMutex.atomically do
      let state ← get
      let peerEnded := (findActiveRequestStream? state.activeRequestStreams dispatch.streamId).isNone
      let state := {
        state with
        activeRequestStreams := removeActiveRequestStream state.activeRequestStreams dispatch.streamId,
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches dispatch.streamId
      }
      -- A successful encoder may have queued DATA followed by terminal
      -- trailers behind a closed peer flow-control window.  Those frames and
      -- the stream window remain live until `flushOutbound` actually emits
      -- END_STREAM; its normal cleanup then retires the window.  Only a failed
      -- encoder/reset may discard pending outbound work here.
      let state :=
        if outboundHpack.isSome then
          state
        else
          removeOutboundStreamState state dispatch.streamId
      -- A handler may finish (most importantly, at its deadline) before the
      -- peer closes its request half.  The local trailers close only our half
      -- of the HTTP/2 stream; keep accepting and flow-controlling legal late
      -- DATA until END_STREAM, but discard it without re-entering the handler.
      let state :=
        if peerEnded then
          removeInboundStreamState
            { state with streams := removeStream state.streams dispatch.streamId }
            dispatch.streamId
        else
          ignoreInboundStreamBody state dispatch.streamId
      let state := match outboundHpack with
        | none => state
        | some outboundHpack => { state with outboundHpack := outboundHpack }
      set state
  let encodeUnary (response : UnaryResponse) : IO (Except Status Hpack.State) := do
    match Transport.encodeUnaryResponseFrames
        dispatch.outboundHpack dispatch.streamId response dispatch.maxDataFrameSize acceptsGzip with
    | .error status => pure (.error status)
    | .ok encoded =>
        match ← queueOutboundShared stateMutex emit encoded.1 with
        | .error status => pure (.error status)
        | .ok () => pure (.ok encoded.2)
  let encodeStreaming (response : ServerStreamingStreamResponse) (deadline : Option Nat) :
      Std.Async.Async (Except Status Hpack.State) := do
    let messages ← try
      registerResponseStream response.messages
    catch err =>
      return .error (Status.ofIOError err)
    let response := { response with messages := messages }
    Transport.encodeServerStreamingStreamResponseFramesWithAsync
      dispatch.outboundHpack dispatch.streamId response emitOutbound dispatch.maxDataFrameSize
      acceptsGzip deadline deadlineRuntime?
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
          | .ok outboundHpack => finish (some outboundHpack)
          | .error _status =>
              cancelResponseStreamRef responseStreamCancel
              finish none
              abortStreamSharedUnlessCancelled cancelled stateMutex emit
                dispatch.streamId ErrorCode.internalError
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
              | .ok outboundHpack => finish (some outboundHpack)
              | .error _status =>
                  cancelResponseStreamRef responseStreamCancel
                  finish none
                  abortStreamSharedUnlessCancelled cancelled stateMutex emit
                    dispatch.streamId ErrorCode.internalError
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
              | .ok outboundHpack => finish (some outboundHpack)
              | .error _status =>
                  cancelResponseStreamRef responseStreamCancel
                  finish none
                  abortStreamSharedUnlessCancelled cancelled stateMutex emit
                    dispatch.streamId ErrorCode.internalError
    catch _ =>
      cancelResponseStreamRef responseStreamCancel
      finish none
      abortStreamSharedUnlessCancelled cancelled stateMutex emit
        dispatch.streamId ErrorCode.internalError
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
            contentLength := dispatch.preflight.contentLength,
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
      ignoredInboundStreams := #[],
      resetInboundStreams := #[],
      resetHeaderBlock := none,
      activeRequestStreams := #[],
      activeDispatches := #[],
      activeAuthorizations := #[],
      pendingDispatchPublications := #[],
      pendingOutbound := #[],
      inboundStreamWindows := #[],
      outboundStreamWindows := #[],
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

/-- Synchronous compatibility wrapper. Managed servers use
`cancelActiveSharedOwned`, so arbitrary nested cancellation cannot park the
thread executing `Server.wait`. -/
def cancelActiveShared (stateMutex : Std.Mutex State) : IO State :=
  Std.Async.Async.block (cancelActiveSharedOwned stateMutex)

private def finalizeStreamWith (registry : Registry) (state : State) (streamId : Nat)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match findStream? state.streams streamId with
  | none => pure (.error (Status.internal s!"unknown HTTP/2 stream {streamId}"))
  | some stream =>
      let request ← match authorizedUnaryRequestForStream state stream with
        | .ok request => pure request
        | .error status => return .error status
      let streams := removeStream state.streams streamId
      let stateRef ← IO.mkRef { state with streams := streams }
      let emitOutbound (frames : Array Frame) : IO Unit := do
        let state ← stateRef.get
        let (state, emitted) := queueOutbound state frames
        stateRef.set state
        emit emitted
      match (← Transport.dispatchDecodedUnaryFramesWith
          registry state.outboundHpack request emitOutbound
          state.outboundMaxFramePayloadLength) with
      | .ok result =>
          let state ← stateRef.get
          let state := {
            state with
            hpack := result.inboundHpack,
            outboundHpack := result.outboundHpack
          }
          pure (.ok (removeInboundStreamState state streamId))
      | .error status => pure (.error status)

private def finalizeStream (registry : Registry) (state : State) (streamId : Nat) :
    IO (Except Status (State × Array Frame)) := do
  let emittedRef ← IO.mkRef #[]
  match ← finalizeStreamWith registry state streamId
      (fun frames => emittedRef.modify fun emitted => emitted.append frames) with
  | .ok state => pure (.ok (state, ← emittedRef.get))
  | .error status => pure (.error status)

private def processSettings (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  let settings ← Settings.decode frame
  if Settings.isAck frame then
    if state.prefaceReceived && !state.clientSettingsReceived then
      throw (Status.internal "HTTP/2 client preface must be followed by a non-ACK SETTINGS frame")
    else
      pure (state, #[])
  else
    let state ← applyPeerSettings state settings
    let state := { state with clientSettingsReceived := true }
    let ack ← Settings.frame #[] (ack := true)
    let (state, flushed) := flushOutbound state
    pure (state, #[ack].append flushed)

private def processPing (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  let payload ← Ping.decode frame
  if Ping.isAck frame then
    let state :=
      match state.pendingKeepalivePing with
      | some pending =>
          if pending == payload then
            { state with pendingKeepalivePing := none }
          else
            state
      | none => state
    pure (state, #[])
  else
    let ack ← Ping.frame payload (ack := true)
    pure (state, #[ack])

private def processGoAway (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  discard <| GoAway.decode frame
  pure (state, #[])

private def hasOpenInboundStream (state : State) (streamId : Nat) : Bool :=
  (findStream? state.streams streamId).isSome
    || (findActiveRequestStream? state.activeRequestStreams streamId).isSome
    || !(activeDispatchesForStream state.activeDispatches streamId).isEmpty

/-- Drop only `streamId`'s state after a locally generated RST_STREAM.  When
the peer may still have DATA in flight, retain the id in drain-only mode so
those connection-flow-controlled bytes cannot affect dispatch. -/
private def resetLocalStream (state : State) (streamId : Nat) (peerEnded : Bool := false) : State :=
  let wasOpen := hasOpenInboundStream state streamId
  -- The original authorization owner retains its active marker until it has
  -- observed cancellation and joined any child published concurrently with
  -- this reset.  Removing the marker here could make drain accounting report
  -- completion during the child-publication gap.
  let state := { state with streams := removeStream state.streams streamId }
  let state := removeInboundStreamState (removeOutboundStreamState state streamId) streamId
  if wasOpen && !peerEnded then drainResetInboundStreamBody state streamId else state

private def processPriority (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  discard <| Priority.decode frame
  -- RFC 9113 §6.3 permits deprecated PRIORITY frames in any stream state and
  -- says they do not create or alter a stream, so a structurally valid
  -- PRIORITY changes nothing here.  §6.3's two error cases never reach this
  -- function through the transition APIs: `containStreamError?` runs first
  -- and turns a malformed length into that stream's
  -- RST_STREAM(FRAME_SIZE_ERROR) and stream id 0 into a connection error.
  -- The `Priority.decode` above re-checks the same structure, so a caller
  -- that skips that classification still cannot ignore a malformed frame —
  -- it merely escalates it.
  pure (state, #[])

private def streamWindowOverrun (state : State) (frame : Frame) : Bool :=
  frame.payload.size <= state.inboundConnectionWindow
    && frame.payload.size > inboundStreamWindow state frame.header.streamId

/-- Contain an otherwise well-framed DATA overrun to its stream.  The bytes
still consume connection credit, immediately returned by the connection-level
WINDOW_UPDATE; no stream credit is returned after the FLOW_CONTROL_ERROR. -/
def resetStreamFlowControl (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  let connectionUpdate ← WindowUpdate.frame 0 frame.payload.size
  let rst ← RstStream.frame frame.header.streamId ErrorCode.flowControlError
  let cancelDispatches := activeDispatchesForStream state.activeDispatches frame.header.streamId
  let cancelAuthorizations :=
    activeAuthorizationsForStream state.activeAuthorizations frame.header.streamId
  let state := resetLocalStream state frame.header.streamId
    (peerEnded := FrameFlag.has frame.header.flags FrameFlag.endStream)
  pure (state, {
    emitted := #[connectionUpdate, rst],
    cancelDispatches := cancelDispatches,
    cancelAuthorizations := cancelAuthorizations
  })

/-- A stream receive-window violation consumes no lasting connection credit,
produces no dispatch work, cancels only work attributable to the offending
stream, and emits exactly a connection-credit refund followed by that stream's
FLOW_CONTROL_ERROR reset.  In particular, connection identity and HPACK state
are untouched. -/
theorem resetStreamFlowControl_scoped {state state' : State} {frame : Frame}
    {result : SharedFrameResult}
    (h : resetStreamFlowControl state frame = .ok (state', result)) :
    result.requestFeeds = #[] ∧ result.detached = none ∧ result.requestStreaming = none
      ∧ state'.inboundConnectionWindow = state.inboundConnectionWindow
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ state'.hpack = state.hpack
      ∧ state'.outboundHpack = state.outboundHpack
      ∧ (∀ dispatch ∈ result.cancelDispatches,
          dispatch.streamId = frame.header.streamId)
      ∧ (∃ connectionUpdate rst,
          WindowUpdate.frame 0 frame.payload.size = .ok connectionUpdate
            ∧ RstStream.frame frame.header.streamId ErrorCode.flowControlError = .ok rst
            ∧ result.emitted = #[connectionUpdate, rst]) := by
  unfold resetStreamFlowControl at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next connectionUpdate hconnectionUpdate =>
    split at h
    next => cases h
    next rst hrst =>
      cases h
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [resetLocalStream, removeInboundStreamState, removeOutboundStreamState,
          drainResetInboundStreamBody]
        split <;> rfl
      · simp only [resetLocalStream, removeInboundStreamState, removeOutboundStreamState,
          drainResetInboundStreamBody]
        split <;> rfl
      · simp only [resetLocalStream, removeInboundStreamState, removeOutboundStreamState,
          drainResetInboundStreamBody]
        split <;> rfl
      · simp only [resetLocalStream, removeInboundStreamState, removeOutboundStreamState,
          drainResetInboundStreamBody]
        split <;> rfl
      · intro dispatch hd
        have hstream := (Array.mem_filter.mp hd).2
        simpa using hstream
      · exact ⟨connectionUpdate, rst, hconnectionUpdate, hrst, rfl⟩

/-- Stream error for a malformed PRIORITY on a stream that is no longer idle.
RFC 9113 §6.3 prescribes FRAME_SIZE_ERROR.  PRIORITY is not flow controlled, so
unlike `resetStreamFlowControl` there is no connection credit to refund; the
stream's local state is torn down exactly as for any other locally generated
RST_STREAM, and work attributable to it is cancelled. -/
private def resetPriorityFrameSize (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  let rst ← RstStream.frame frame.header.streamId ErrorCode.frameSizeError
  let cancelDispatches := activeDispatchesForStream state.activeDispatches frame.header.streamId
  let cancelAuthorizations :=
    activeAuthorizationsForStream state.activeAuthorizations frame.header.streamId
  let state := resetLocalStream state frame.header.streamId
  pure (state, {
    emitted := #[rst],
    cancelDispatches := cancelDispatches,
    cancelAuthorizations := cancelAuthorizations
  })

/-- Classify the frame-local failures whose per-frame-type processors would
otherwise escalate them, after the caller has completed all connection-scoped
validation: a DATA overrun of an otherwise valid open stream's receive window,
and a PRIORITY frame whose length is not 5 (RFC 9113 §6.3).  Every transition
API consults this same helper before dispatching on the frame type, so for
exactly these cases choosing the aggregate, emitting, or shared runtime API
cannot change the required RFC 9113 stream error into a connection error.
The remaining stream errors are contained inside their own frame processors
(`resetClosedStreamData`, `rejectStreamAtHeaders`). -/
private def containStreamError? (state : State) (frame : Frame) :
    Except Status (Option (State × SharedFrameResult)) := do
  match frame.header.frameType with
  | .data =>
      requireClientStreamId frame.header.streamId "DATA"
      -- Invalid padding is a connection error (§6.1) and therefore takes
      -- precedence over the stream-window classification below. Keep using
      -- the raw payload size for flow control: padding bytes consume credit.
      discard <| stripPadding frame "DATA"
      let validOpenStream :=
        (findActiveRequestStream? state.activeRequestStreams frame.header.streamId).isSome
          || ((findStream? state.streams frame.header.streamId).map streamHeaderComplete).getD false
      if validOpenStream && streamWindowOverrun state frame then
        some <$> resetStreamFlowControl state frame
      else
        pure none
  | .priority =>
      -- Connection error.  RFC 9113 §6.3: "If a PRIORITY frame is received
      -- with a stream identifier of 0x00, the recipient MUST respond with a
      -- connection error (Section 5.4.1) of type PROTOCOL_ERROR."
      if frame.header.streamId == 0 then
        throw (Status.internal "HTTP/2 PRIORITY frame must use a stream id")
      if frame.payload.size != 5 then
        -- PRIORITY itself never opens a stream (§6.3), while §6.4 forbids
        -- sending RST_STREAM for an idle stream.  This server never creates
        -- even-numbered pushed streams, and an odd client stream above the
        -- monotonic frontier has never been opened.  Escalate those cases as
        -- §5.4.1 permits; only an open/half-closed/closed stream can receive
        -- the §6.3 stream error.
        if frame.header.streamId % 2 == 0
            || frame.header.streamId > state.lastClientStreamId then
          throw (Status.internal
            "HTTP/2 malformed PRIORITY identifies an idle stream")
        some <$> resetPriorityFrameSize state frame
      else
        pure none
  | _ => pure none

private def processRstStream (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  discard <| RstStream.decode frame
  requireClientStreamId frame.header.streamId "RST_STREAM"
  let state := { state with streams := removeStream state.streams frame.header.streamId }
  let state := removeInboundStreamState state frame.header.streamId
  pure (removeOutboundStreamState state frame.header.streamId, #[])

private def processRstStreamShared (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  discard <| RstStream.decode frame
  requireClientStreamId frame.header.streamId "RST_STREAM"
  let cancelDispatches := activeDispatchesForStream state.activeDispatches frame.header.streamId
  let cancelAuthorizations :=
    activeAuthorizationsForStream state.activeAuthorizations frame.header.streamId
  let state := {
    state with
    streams := removeStream state.streams frame.header.streamId
  }
  let state := removeInboundStreamState state frame.header.streamId
  pure (removeOutboundStreamState state frame.header.streamId, {
    cancelDispatches := cancelDispatches,
    cancelAuthorizations := cancelAuthorizations
  })

/-- HPACK is connection-wide, so even a field block that crossed a local reset
must be decompressed before it is discarded. Request semantics are intentionally
not revalidated: this closed stream can no longer reach a handler. -/
private def discardResetHeaderBlock (state : State) (headersFrame : Frame) : Except Status State := do
  if !headerComplete headersFrame then
    throw (Status.internal "reset HTTP/2 header block ended before END_HEADERS")
  let decoded ← Hpack.decodeHeaderBlock state.hpack headersFrame.payload
  Metadata.validateHeaderListSize state.inboundMaxHeaderListSize decoded.headers
  let state := {
    state with
    hpack := decoded.state,
    resetHeaderBlock := none
  }
  pure <| if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
    removeInboundStreamState state headersFrame.header.streamId
  else
    state

private def appendResetContinuationFrame (headersFrame frame : Frame) : Except Status Frame := do
  requireClientStreamId frame.header.streamId "CONTINUATION"
  if frame.header.streamId != headersFrame.header.streamId then
    throw (Status.internal "HTTP/2 CONTINUATION frame changed reset stream id")
  if headerComplete headersFrame then
    throw (Status.internal "unexpected HTTP/2 CONTINUATION after reset END_HEADERS")
  let payload := headersFrame.payload.append frame.payload
  if payload.size > maxHeaderBlockSize then
    throw (Status.internal "HTTP/2 reset header block exceeds the maximum supported size")
  let flags :=
    if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
      UInt8.ofNat (headersFrame.header.flags.toNat + FrameFlag.endHeaders.toNat)
    else
      headersFrame.header.flags
  pure {
    headersFrame with
    header := { headersFrame.header with length := payload.size, flags := flags },
    payload := payload
  }

private def processResetHeaders (state : State) (frame : Frame) :
    Except Status (State × Array Frame) := do
  requireClientStreamId frame.header.streamId "HEADERS"
  let state ←
    if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
      discardResetHeaderBlock state frame
    else
      pure { state with resetHeaderBlock := some frame }
  pure (state, #[])

private def processResetContinuation (state : State) (frame : Frame) :
    Except Status (State × Array Frame) := do
  let headersFrame ← match state.resetHeaderBlock with
    | some headersFrame => pure headersFrame
    | none => throw (Status.internal "HTTP/2 CONTINUATION frame arrived before reset HEADERS")
  let headersFrame ← appendResetContinuationFrame headersFrame frame
  let state ←
    if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
      discardResetHeaderBlock state headersFrame
    else
      pure { state with resetHeaderBlock := some headersFrame }
  pure (state, #[])

private def processHeaders (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match requireClientStreamId frame.header.streamId "HEADERS" with
  | .error status => pure (.error status)
  | .ok () =>
    if (findStream? state.streams frame.header.streamId).isSome then
      pure (.error (Status.internal "HTTP/2 duplicate HEADERS for active unary stream"))
    else
      match requireNewClientStreamId state frame.header.streamId with
      | .error status => pure (.error status)
      | .ok () =>
        match rejectNewStreamAfterOutboundGoAway? state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (some rst) => pure (.ok (state, #[rst]))
        | .ok none =>
            let state := {
              state with
              lastClientStreamId := frame.header.streamId,
              streams := appendStreamFrame state.streams frame,
              refusedInboundStreams :=
                if (inboundStreamCapacityRefusal? state).isSome then
                  pushUniqueStreamId state.refusedInboundStreams frame.header.streamId
                else
                  state.refusedInboundStreams
            }
            if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
              match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
              | .error status => pure (.error status)
              | .ok (state, .rejected frames) => pure (.ok (state, frames))
              | .ok (_, .pending _) =>
                  pure (.error (Status.internal
                    "managed header authorization reached synchronous frame processing"))
              | .ok (state, .accepted) =>
                  if FrameFlag.has frame.header.flags FrameFlag.endStream then
                    finalizeStream registry state frame.header.streamId
                  else
                    pure (.ok (state, #[]))
            else
              pure (.ok (state, #[]))

private def processHeadersWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match requireClientStreamId frame.header.streamId "HEADERS" with
  | .error status => pure (.error status)
  | .ok () =>
    if (findStream? state.streams frame.header.streamId).isSome then
      pure (.error (Status.internal "HTTP/2 duplicate HEADERS for active unary stream"))
    else
      match requireNewClientStreamId state frame.header.streamId with
      | .error status => pure (.error status)
      | .ok () =>
        match rejectNewStreamAfterOutboundGoAway? state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (some rst) =>
            match ← emitFrameBatch emit #[rst] with
            | .error status => pure (.error status)
            | .ok () => pure (.ok state)
        | .ok none =>
            let state := {
              state with
              lastClientStreamId := frame.header.streamId,
              streams := appendStreamFrame state.streams frame,
              refusedInboundStreams :=
                if (inboundStreamCapacityRefusal? state).isSome then
                  pushUniqueStreamId state.refusedInboundStreams frame.header.streamId
                else
                  state.refusedInboundStreams
            }
            if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
              match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
              | .error status => pure (.error status)
              | .ok (state, .rejected frames) =>
                  match ← emitFrameBatch emit frames with
                  | .error status => pure (.error status)
                  | .ok () => pure (.ok state)
              | .ok (_, .pending _) =>
                  pure (.error (Status.internal
                    "managed header authorization reached synchronous frame processing"))
              | .ok (state, .accepted) =>
                  if FrameFlag.has frame.header.flags FrameFlag.endStream then
                    finalizeStreamWith registry state frame.header.streamId emit
                  else
                    pure (.ok state)
            else
              pure (.ok state)

private def processContinuation (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match appendContinuationFrame state.streams frame with
  | .error status => pure (.error status)
  | .ok streams =>
      let state := { state with streams := streams }
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        match findStream? streams frame.header.streamId with
        | some stream =>
            match stream.frames[0]? with
            | some headersFrame =>
                match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
                | .error status => pure (.error status)
                | .ok (state, .rejected frames) => pure (.ok (state, frames))
                | .ok (_, .pending _) =>
                    pure (.error (Status.internal
                      "managed header authorization reached synchronous frame processing"))
                | .ok (state, .accepted) =>
                    if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
                      finalizeStream registry state frame.header.streamId
                    else
                      pure (.ok (state, #[]))
            | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
        | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
      else
        pure (.ok (state, #[]))

private def processContinuationWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match appendContinuationFrame state.streams frame with
  | .error status => pure (.error status)
  | .ok streams =>
      let state := { state with streams := streams }
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        match findStream? streams frame.header.streamId with
        | some stream =>
            match stream.frames[0]? with
            | some headersFrame =>
                match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
                | .error status => pure (.error status)
                | .ok (state, .rejected frames) =>
                    match ← emitFrameBatch emit frames with
                    | .error status => pure (.error status)
                    | .ok () => pure (.ok state)
                | .ok (_, .pending _) =>
                    pure (.error (Status.internal
                      "managed header authorization reached synchronous frame processing"))
                | .ok (state, .accepted) =>
                    if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
                      finalizeStreamWith registry state frame.header.streamId emit
                    else
                      pure (.ok state)
            | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
        | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
      else
        pure (.ok state)

private def processData (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match requireClientStreamId frame.header.streamId "DATA" with
  | .error status => pure (.error status)
  | .ok () =>
    if drainsInboundStreamBody state frame.header.streamId then
      match processDrainingInboundData state frame with
      | .error status => pure (.error status)
      | .ok result => pure (.ok result)
    else match findStream? state.streams frame.header.streamId with
    | none =>
        pure (.error (Status.internal "HTTP/2 DATA frame arrived before request HEADERS"))
    | some stream =>
        if !streamHeaderComplete stream then
          pure (.error (Status.internal "HTTP/2 DATA frame arrived before END_HEADERS"))
        else
          match consumeInboundDataWindow state frame with
          | .error status => pure (.error status)
          | .ok state =>
            match dataWindowUpdates frame with
            | .error status => pure (.error status)
            | .ok updates =>
              let state := replenishInboundDataWindow state frame
              match stripPadding frame "DATA" with
              | .error status => pure (.error status)
              | .ok frame =>
                let state := { state with streams := appendStreamFrame state.streams frame }
                if FrameFlag.has frame.header.flags FrameFlag.endStream then
                  match (← finalizeStream registry state frame.header.streamId) with
                  | .ok (state, frames) => pure (.ok (state, updates.append frames))
                  | .error status => pure (.error status)
                else
                  pure (.ok (state, updates))

private def processDataWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match requireClientStreamId frame.header.streamId "DATA" with
  | .error status => pure (.error status)
  | .ok () =>
    if drainsInboundStreamBody state frame.header.streamId then
      match processDrainingInboundData state frame with
      | .error status => pure (.error status)
      | .ok (state, updates) =>
          match ← emitFrameBatch emit updates with
          | .error status => pure (.error status)
          | .ok () => pure (.ok state)
    else match findStream? state.streams frame.header.streamId with
    | none =>
        pure (.error (Status.internal "HTTP/2 DATA frame arrived before request HEADERS"))
    | some stream =>
        if !streamHeaderComplete stream then
          pure (.error (Status.internal "HTTP/2 DATA frame arrived before END_HEADERS"))
        else
          match consumeInboundDataWindow state frame with
          | .error status => pure (.error status)
          | .ok state =>
            match dataWindowUpdates frame with
            | .error status => pure (.error status)
            | .ok updates =>
              let state := replenishInboundDataWindow state frame
              match stripPadding frame "DATA" with
              | .error status => pure (.error status)
              | .ok frame =>
                let state := { state with streams := appendStreamFrame state.streams frame }
                match ← emitFrameBatch emit updates with
                | .error status => pure (.error status)
                | .ok () =>
                    if FrameFlag.has frame.header.flags FrameFlag.endStream then
                      finalizeStreamWith registry state frame.header.streamId emit
                    else
                      pure (.ok state)

/-- Connection error.  RFC 9113 §6.2: "A HEADERS frame without the END_HEADERS
flag set MUST be followed by a CONTINUATION frame for the same stream.  A
receiver MUST treat the receipt of any other type of frame or a frame on a
different stream as a connection error (Section 5.4.1) of type
PROTOCOL_ERROR." -/
private def requireHeaderBlockContinuation (state : State) (frame : Frame) : Except Status Unit := do
  let pending := match state.resetHeaderBlock with
    | some headersFrame => some headersFrame.header.streamId
    | none => pendingHeaderStream? state.streams
  match pending with
  | none => pure ()
  | some streamId =>
      if frame.header.frameType == FrameType.continuation && frame.header.streamId == streamId then
        pure ()
      else
        throw (Status.internal "HTTP/2 header block must be followed by CONTINUATION frames")

/-- Connection errors.  A header/payload length mismatch means the decoder and
the peer disagree about where frames begin, which is unrecoverable per stream.
The advertised-size check is RFC 9113 §4.2 ("An endpoint MUST send an error code
of FRAME_SIZE_ERROR if a frame exceeds the size defined in
SETTINGS_MAX_FRAME_SIZE"); §4.2 permits a stream error for frames that cannot
alter connection state, but this check runs before frame-type dispatch and an
oversized frame has already consumed an unknown amount of the stream, so it is
kept connection-scoped. -/
private def requireInboundFrameSize (state : State) (frame : Frame) : Except Status Unit := do
  if frame.header.length != frame.payload.size then
    throw (Status.internal "HTTP/2 frame header length does not match payload size")
  if frame.payload.size > state.inboundMaxFramePayloadLength then
    throw (Status.internal "HTTP/2 inbound frame exceeds advertised max frame size")

private def withNormalizedHeaders (frame : Frame)
    (k : Frame -> IO (Except Status α)) : IO (Except Status α) := do
  match normalizeHeadersFrame frame with
  | .error status => pure (.error status)
  | .ok frame => k frame

/-- Connection error.  RFC 9113 §3.4: "The server connection preface consists
of a potentially empty SETTINGS frame ... that MUST be the first frame the
server sends", and the client preface "MUST be followed by a SETTINGS frame";
§6.5 makes anything else at that point a connection error of type
PROTOCOL_ERROR. -/
private def requireClientSettingsFrame (state : State) (frame : Frame) : Except Status Unit := do
  if state.prefaceReceived
      && !state.clientSettingsReceived
      && frame.header.frameType != FrameType.settings then
    throw (Status.internal "HTTP/2 client preface must be followed by a non-ACK SETTINGS frame")

def processFrame (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match requireInboundFrameSize state frame with
  | .error status => pure (.error status)
  | .ok () =>
      match requireClientSettingsFrame state frame with
      | .error status => pure (.error status)
      | .ok () =>
          match requireHeaderBlockContinuation state frame with
          | .error status => pure (.error status)
          | .ok () =>
              match containStreamError? state frame with
              | .error status => pure (.error status)
              | .ok (some (state, result)) => pure (.ok (state, result.emitted))
              | .ok none =>
                match frame.header.frameType with
                | .settings => pure (processSettings state frame)
                | .headers => withNormalizedHeaders frame (fun frame =>
                    if containsStreamId state.resetInboundStreams frame.header.streamId then
                      pure (processResetHeaders state frame)
                    else
                      processHeaders registry state frame)
                | .data => processData registry state frame
                | .rstStream => pure (processRstStream state frame)
                | .windowUpdate => pure (processWindowUpdate state frame)
                | .ping => pure (processPing state frame)
                | .continuation =>
                    if containsStreamId state.resetInboundStreams frame.header.streamId then
                      pure (processResetContinuation state frame)
                    else
                      processContinuation registry state frame
                | .priority => pure (processPriority state frame)
                | .goAway => pure (processGoAway state frame)
                | .pushPromise => pure (.error (Status.unimplemented "HTTP/2 PUSH_PROMISE frames are not supported"))
                | .unknown _ => pure (.ok (state, #[]))

def processFrameWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match requireInboundFrameSize state frame with
  | .error status => pure (.error status)
  | .ok () =>
      match requireClientSettingsFrame state frame with
      | .error status => pure (.error status)
      | .ok () =>
          match requireHeaderBlockContinuation state frame with
          | .error status => pure (.error status)
          | .ok () =>
              match containStreamError? state frame with
              | .error status => pure (.error status)
              | .ok (some (state, result)) =>
                  emitResultFrames emit (.ok (state, result.emitted))
              | .ok none =>
                match frame.header.frameType with
                | .settings => emitResultFrames emit (processSettings state frame)
                | .headers => withNormalizedHeaders frame (fun frame =>
                    if containsStreamId state.resetInboundStreams frame.header.streamId then
                      emitResultFrames emit (processResetHeaders state frame)
                    else
                      processHeadersWith registry state frame emit)
                | .data => processDataWith registry state frame emit
                | .rstStream => emitResultFrames emit (processRstStream state frame)
                | .windowUpdate => emitResultFrames emit (processWindowUpdate state frame)
                | .ping => emitResultFrames emit (processPing state frame)
                | .continuation =>
                    if containsStreamId state.resetInboundStreams frame.header.streamId then
                      emitResultFrames emit (processResetContinuation state frame)
                    else
                      processContinuationWith registry state frame emit
                | .priority => emitResultFrames emit (processPriority state frame)
                | .goAway => emitResultFrames emit (processGoAway state frame)
                | .pushPromise => pure (.error (Status.unimplemented "HTTP/2 PUSH_PROMISE frames are not supported"))
                | .unknown _ => pure (.ok state)

/-- The pure bookkeeping `processHeadersShared` performs before the `IO`
authorizer call: stream-id validation, buffering the header frame, and
claiming the stream id.  Factored out so the authorization-before-body
properties (end of file) can cover HEADERS steps without touching
`IO`. -/
def prepareHeadersShared (state : State) (frame : Frame) :
    Except Status (State × Option Frame) := do
  requireClientStreamId frame.header.streamId "HEADERS"
  if (findStream? state.streams frame.header.streamId).isSome then
    throw (Status.internal "HTTP/2 duplicate HEADERS for active unary stream")
  requireNewClientStreamId state frame.header.streamId
  match ← rejectNewStreamAfterOutboundGoAway? state frame.header.streamId with
  | some rst => pure (state, some rst)
  | none =>
      -- Over the concurrency limit the stream is still opened, so its field
      -- block reaches the HPACK decoder (RFC 9113 §4.3); it is marked for
      -- RST_STREAM(REFUSED_STREAM) the moment the block has been read.
      pure ({
        state with
        lastClientStreamId := frame.header.streamId,
        streams := appendStreamFrame state.streams frame,
        refusedInboundStreams :=
          if (inboundStreamCapacityRefusal? state).isSome then
            pushUniqueStreamId state.refusedInboundStreams frame.header.streamId
          else
            state.refusedInboundStreams
      }, none)

private def processHeadersShared (registry : Registry) (state : State) (frame : Frame)
    (receivedAt : Option Nat := none) :
    IO (Except Status (State × SharedFrameResult)) := do
  match prepareHeadersShared state frame with
  | .error status => pure (.error status)
  | .ok (state, some rst) => pure (.ok (state, { emitted := #[rst] }))
  | .ok (state, none) =>
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        let state := recordEndHeadersReceivedAt state frame.header.streamId receivedAt
        match ← earlyRequestRejectionForStream? registry state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (state, some result) => pure (.ok (state, result))
        | .ok (state, none) =>
            match requestStreamingDispatchForStream? state frame.header.streamId with
            | .error status => pure (.error status)
            | .ok (state, some requestStreaming) =>
                pure (.ok (state, { requestStreaming := some requestStreaming }))
            | .ok (state, none) =>
                if FrameFlag.has frame.header.flags FrameFlag.endStream then
                  match detachStreamForDispatch state frame.header.streamId with
                  | .error status => pure (.error status)
                  | .ok (state, detached) => pure (.ok (state, { detached := some detached }))
                else
                  pure (.ok (state, {}))
      else
        pure (.ok (state, {}))

private def processContinuationShared (registry : Registry) (state : State) (frame : Frame)
    (receivedAt : Option Nat := none) :
    IO (Except Status (State × SharedFrameResult)) := do
  match appendContinuationFrame state.streams frame with
  | .error status => pure (.error status)
  | .ok streams =>
    let state := { state with streams := streams }
    if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
      let state := recordEndHeadersReceivedAt state frame.header.streamId receivedAt
      let headersFrame? := (findStream? streams frame.header.streamId).bind fun stream =>
        stream.frames[0]?
      match headersFrame? with
      | none => pure (.error
          (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
      | some headersFrame =>
        match ← earlyRequestRejectionForStream? registry state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (state, some result) => pure (.ok (state, result))
        | .ok (state, none) =>
          match requestStreamingDispatchForStream? state frame.header.streamId with
          | .error status => pure (.error status)
          | .ok (state, some requestStreaming) =>
              pure (.ok (state, { requestStreaming := some requestStreaming }))
          | .ok (state, none) =>
            if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
              match detachStreamForDispatch state frame.header.streamId with
              | .error status => pure (.error status)
              | .ok (state, detached) => pure (.ok (state, { detached := some detached }))
            else
              pure (.ok (state, {}))
    else
      pure (.ok (state, {}))

/-- DATA for a streaming request body.  The connection window is credited for
the whole frame immediately (so one stalled stream cannot starve the
connection); the stream window is credited only for padding, because the
payload's stream credit is deferred until the handler consumes each message. -/
def processActiveRequestData (registry : Registry) (state : State) (frame : Frame)
    (active : ActiveRequestStream) : Except Status (State × SharedFrameResult) :=
  match consumeInboundDataWindow state frame with
  | .error status => .error status
  | .ok consumed =>
    match stripPadding frame "DATA" with
    | .error status => .error status
    | .ok stripped =>
      match activeDataWindowUpdates stripped.header.streamId frame.payload.size
          (frame.payload.size - stripped.payload.size) with
      | .error status => .error status
      | .ok updates =>
        match Transport.normalizeDataFrame stripped with
        | .error status => .error status
        | .ok normalized =>
          let credited := replenishInboundStreamWindowBy
            (replenishInboundConnectionWindow consumed frame.payload.size)
            stripped.header.streamId (frame.payload.size - stripped.payload.size)
          match decodeActiveRequestData registry active normalized with
          | .ok (active, messages, close) =>
              let closedState := removeInboundStreamState {
                credited with
                streams := removeStream credited.streams normalized.header.streamId,
                activeRequestStreams := removeActiveRequestStream
                  credited.activeRequestStreams normalized.header.streamId
              } normalized.header.streamId
              let openState := {
                credited with
                activeRequestStreams := replaceActiveRequestStream
                  credited.activeRequestStreams active
              }
              .ok (if close then closedState else openState, {
                emitted := updates,
                requestFeeds := #[{
                  producer := active.producer,
                  messages := messages,
                  close := close
                }]
              })
          | .error status =>
              let resetState := removeInboundStreamState {
                credited with
                streams := removeStream credited.streams normalized.header.streamId,
                activeRequestStreams := removeActiveRequestStream
                  credited.activeRequestStreams normalized.header.streamId
              } normalized.header.streamId
              .ok (resetState, {
                emitted := updates,
                requestFeeds := #[{
                  producer := active.producer,
                  error := some status
                }]
              })

/-! ### Per-stream error containment

RFC 9113 §5.4 splits framing failures in two, and the distinction is the whole
point of this section.

* A *connection* error (§5.4.1) is "any error that prevents further processing
  of the frame layer or corrupts any connection state".  It is reported with
  GOAWAY and ends the connection.
* A *stream* error (§5.4.2) is "an error related to a specific stream that does
  not affect processing of other streams".  It is reported with RST_STREAM and
  the connection keeps serving.

Three cases implement the second kind. When the stream was open and the peer may
still have DATA in flight, they retain its id in drain-only mode
(`resetInboundStreams`) — because §5.4.2 continues: "after sending the
RST_STREAM, the sending endpoint MUST be prepared to receive and process
additional frames sent on the stream that might have been sent by the peer prior
to the arrival of the RST_STREAM", and §6.9 requires those frames'
flow-controlled bytes to stay accounted for. Reset drain-only mode is excluded
from active-stream and graceful-drain accounting; it exists only to refund
connection credit and to decompress any late field block.

* `resetClosedStreamData` (here) — DATA for a stream that has already closed.
* `rejectStreamAtHeaders` (above, reused by `authorizeRequestHeadersForStream`)
  — a stream refused at completed request headers, whether by the authorizer,
  or by `SETTINGS_MAX_CONCURRENT_STREAMS`.
* `resetStreamFlowControl` — DATA that fits the connection window but exceeds
  an otherwise valid open stream's receive window.

One constraint shapes every decision here: a stream error may only be raised
once the frame's field block (if any) has been decoded.  RFC 9113 §4.3 —
"A receiver MUST terminate the connection with a connection error
(Section 5.4.1) of type COMPRESSION_ERROR if it does not decompress a field
block" — makes the HPACK dynamic table connection-wide state, so skipping a
block desynchronises the decoder for every later stream.  That is why the
failures that prevent safe field-block processing (invalid padding, a truncated
priority section, oversized header block, CONTINUATION sequencing) stay
connection-fatal. Conversely, a concurrency or authorization refusal is
deferred until the complete block has been read.
-/

/-- A DATA frame naming a stream id that was opened earlier and has since
closed.

RFC 9113 §6.1: "If a DATA frame is received whose stream is not in the 'open'
or 'half-closed (local)' state, the recipient MUST respond with a stream error
(Section 5.4.2) of type STREAM_CLOSED."  This is the common case in practice —
a client that races an extra DATA frame against the END_STREAM it already sent,
or against our RST_STREAM. The error is scoped to that stream.

The frame is drained through `processResetInboundData` *before* the RST_STREAM
is emitted. Only the connection window is credited: the stream is already
closed, but RFC 9113 §5.4.2 still requires its in-flight bytes to count against
connection flow control.

An id *above* `lastClientStreamId` has never been opened (`idle`), and §5.1
says of that state: "Receiving any frame other than HEADERS or PRIORITY on a
stream in this state MUST be treated as a connection error (Section 5.4.1) of
type PROTOCOL_ERROR."  So `lastClientStreamId` is exactly the frontier between
the stream-scoped and the connection-scoped reading of the same symptom. -/
private def resetClosedStreamData (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  let streamId := frame.header.streamId
  let rst ← RstStream.frame streamId ErrorCode.streamClosed
  let cancelDispatches := activeDispatchesForStream state.activeDispatches streamId
  let cancelAuthorizations :=
    activeAuthorizationsForStream state.activeAuthorizations streamId
  let state := removeOutboundStreamState state streamId
  let (state, updates) ← processResetInboundData
    (drainResetInboundStreamBody state streamId) frame
  pure (state, {
    emitted := updates.push rst,
    cancelDispatches := cancelDispatches,
    cancelAuthorizations := cancelAuthorizations
  })

/-- DATA for a unary request: the body is buffered on the stream and both
windows are credited immediately, since the whole request is dispatched at
END_STREAM. -/
def processUnaryRequestData (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) :=
  match findStream? state.streams frame.header.streamId with
  | none => .error (Status.internal "HTTP/2 DATA frame arrived before request HEADERS")
  | some stream =>
    if !streamHeaderComplete stream then
      .error (Status.internal "HTTP/2 DATA frame arrived before END_HEADERS")
    else
      match consumeInboundDataWindow state frame with
      | .error status => .error status
      | .ok consumed =>
        match dataWindowUpdates frame with
        | .error status => .error status
        | .ok updates =>
          match stripPadding frame "DATA" with
          | .error status => .error status
          | .ok stripped =>
            let buffered := {
              replenishInboundDataWindow consumed frame with
              streams := appendStreamFrame
                (replenishInboundDataWindow consumed frame).streams stripped
            }
            if FrameFlag.has stripped.header.flags FrameFlag.endStream then
              match detachStreamForDispatch buffered stripped.header.streamId with
              | .error status => .error status
              | .ok (detachedState, detached) =>
                  .ok (detachedState, { emitted := updates, detached := some detached })
            else
              .ok (buffered, { emitted := updates })

def processDataShared (registry : Registry) (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) :=
  match requireClientStreamId frame.header.streamId "DATA" with
  | .error status => .error status
  | .ok () =>
    if drainsInboundStreamBody state frame.header.streamId then
      match processDrainingInboundData state frame with
      | .error status => .error status
      | .ok (drained, updates) => .ok (drained, { emitted := updates })
    else
      match findActiveRequestStream? state.activeRequestStreams frame.header.streamId with
      | some active => processActiveRequestData registry state frame active
      | none =>
        match findStream? state.streams frame.header.streamId with
        | some _ => processUnaryRequestData state frame
        | none =>
            -- No buffered stream, no incremental feed, not draining: either the
            -- id has already been opened and closed (RFC 9113 §6.1 stream error
            -- STREAM_CLOSED) or it was never opened at all (§5.1 `idle`, a
            -- connection error of type PROTOCOL_ERROR).
            if frame.header.streamId ≤ state.lastClientStreamId then
              resetClosedStreamData state frame
            else
              processUnaryRequestData state frame

/-- The pure shared-kernel step for every frame type that does not require the
`IO` authorizer (i.e. everything except HEADERS/CONTINUATION).  Factored out of
`processFrameShared` so the authorization-before-body properties (end of file)
can state trace theorems over arbitrary non-header frame steps. -/
def processNonHeaderFrameShared (registry : Registry) (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  match frame.header.frameType with
  | .settings =>
      let (state, emitted) ← processSettings state frame
      pure (state, { emitted := emitted })
  | .data => processDataShared registry state frame
  | .rstStream => processRstStreamShared state frame
  | .windowUpdate =>
      let (state, emitted) ← processWindowUpdate state frame
      pure (state, { emitted := emitted })
  | .ping =>
      let (state, emitted) ← processPing state frame
      pure (state, { emitted := emitted })
  | .priority =>
      let (state, emitted) ← processPriority state frame
      pure (state, { emitted := emitted })
  | .goAway =>
      let (state, emitted) ← processGoAway state frame
      pure (state, { emitted := emitted })
  | .pushPromise =>
      -- Connection error.  RFC 9113 §6.6: a server never enables push, and "a
      -- receiver MUST treat the receipt of a PUSH_PROMISE on a stream that is
      -- neither 'open' nor 'half-closed (local)' as a connection error
      -- (Section 5.4.1) of type PROTOCOL_ERROR"; no client-initiated stream can
      -- legally carry one here.
      throw (Status.unimplemented "HTTP/2 PUSH_PROMISE frames are not supported")
  | .unknown _ => pure (state, {})
  | .headers | .continuation =>
      throw (Status.internal "unreachable HTTP/2 header dispatch")

private def processFrameShared (registry : Registry) (state : State) (frame : Frame)
    (receivedAt : Option Nat := none) :
    IO (Except Status (State × SharedFrameResult)) := do
  let validated : Except Status Unit := do
    requireInboundFrameSize state frame
    requireClientSettingsFrame state frame
    requireHeaderBlockContinuation state frame
  match validated with
  | .error status => pure (.error status)
  | .ok () =>
    match frame.header.frameType with
    | .headers =>
        match normalizeHeadersFrame frame with
        | .error status => pure (.error status)
        | .ok frame =>
            if containsStreamId state.resetInboundStreams frame.header.streamId then
              match processResetHeaders state frame with
              | .error status => pure (.error status)
              | .ok (state, emitted) => pure (.ok (state, { emitted := emitted }))
            else
              processHeadersShared registry state frame receivedAt
    | .continuation =>
        if containsStreamId state.resetInboundStreams frame.header.streamId then
          match processResetContinuation state frame with
          | .error status => pure (.error status)
          | .ok (state, emitted) => pure (.ok (state, { emitted := emitted }))
        else
          processContinuationShared registry state frame receivedAt
    | _ => pure (processNonHeaderFrameShared registry state frame)

private def finishSharedFrameResult (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (result : SharedFrameResult) :
    Std.Async.Async (Except Status Unit) := do
  -- Select and signal a stream error first, then publish its wire frame.  User
  -- cleanup cannot suppress the peer-visible RST_STREAM; cleanup is still
  -- joined even when emission reports a transport error.
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

def processFrameSharedWithOwned (registry : Registry) (stateMutex : Std.Mutex State) (frame : Frame)
    (emit : Array Frame -> IO Unit) (receivedAt : Option Nat := none) :
    Std.Async.Async (Except Status Unit) := do
  match ← stateMutex.atomically (do
    let state ← get
    let validated : Except Status Unit := do
      requireInboundFrameSize state frame
      requireClientSettingsFrame state frame
      requireHeaderBlockContinuation state frame
    let step ←
      if state.closing then
        pure (.ok (state, {}))
      else match validated with
        | .error status => pure (.error status)
        | .ok () =>
          match containStreamError? state frame with
          | .error status => pure (.error status)
          | .ok (some result) => pure (.ok result)
          | .ok none => processFrameShared registry state frame receivedAt
    match step with
    | .error status => pure (Except.error status)
    | .ok (state, result) =>
        -- The pure transition has detached these stream owners. Mark them
        -- before publishing that state so late response registration observes
        -- cancellation and takes the same exactly-once callback path.
        for dispatch in result.cancelDispatches do
          dispatch.cancelled.set true
        for authorization in result.cancelAuthorizations do
          authorization.cancelled.set true
        set state
        let resetStream := frame.header.frameType == .rstStream
          || result.emitted.any (fun emitted =>
            emitted.header.frameType == .rstStream
              && emitted.header.streamId == frame.header.streamId)
        let timedBodyCompleted := frame.header.frameType == .data
          && result.detached.any (fun detached => detached.request.deadline.isSome)
        let completedHeaders :=
          (frame.header.frameType == .headers || frame.header.frameType == .continuation)
            && FrameFlag.has frame.header.flags FrameFlag.endHeaders
        let deadlineUpdate? : Option (DeadlineScheduler × Option Nat) := do
          let scheduler ← state.deadlineScheduler
          if resetStream || timedBodyCompleted then
            pure (scheduler, none)
          else if completedHeaders then
            let deadline ← pendingDeadlineForStream? state frame.header.streamId
            pure (scheduler, some deadline)
          else
            none
        pure (Except.ok (result, deadlineUpdate?))) with
  | .error status => pure (Except.error status)
  | .ok (result, deadlineUpdate?) =>
      -- Publish timer ownership before emission, stream feeding, or user IO.
      -- Untimed calls and unchanged body DATA avoid the scheduler mutex.
      match deadlineUpdate? with
      | none => pure ()
      | some (scheduler, deadline?) =>
          reconcilePendingBodyDeadline scheduler stateMutex emit
            frame.header.streamId deadline?
      match result.pendingAuthorization with
      | none => finishSharedFrameResult registry stateMutex emit result
      | some authorization =>
          -- The deadline winner is committed and enqueued before joining a
          -- cancelled callback.  Thus cooperative cancellation latency—or an
          -- uncooperative callback—cannot postpone the peer-visible status.
          let outcome ← try
              let decision ← runPendingAuthorization registry authorization
              match ← commitPendingAuthorization stateMutex authorization decision with
              | .error status => pure (.error status)
              | .ok resolved =>
                  -- Authorization may have made an aggregate request eligible
                  -- to wait for its body. Install that owner before any output
                  -- or handler publication can block this frame task.
                  reconcileCurrentPendingBodyDeadline stateMutex emit authorization.streamId
                  finishSharedFrameResult registry stateMutex emit resolved
            catch error =>
              cancelDeadlineChildRef authorization.active.deadlineChild
              pure (.error (Status.ofIOError error))
          try
            joinDeadlineChildRef authorization.active.deadlineChild
          catch _ =>
            pure ()
          retirePendingAuthorization stateMutex authorization
          pure outcome

/-- Synchronous compatibility wrapper around the connection-owner variant. -/
def processFrameSharedWith (registry : Registry) (stateMutex : Std.Mutex State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status Unit) :=
  Std.Async.Async.block (processFrameSharedWithOwned registry stateMutex frame emit)

private def processFrames (registry : Registry) (frames : Array Frame) (i : Nat)
    (state : State) (out : Array Frame) : IO (Except Status (State × Array Frame)) := do
  let mut state := state
  let mut out := out
  for j in [i:frames.size] do
    match ← processFrame registry state frames[j]! with
    | .error status => return .error status
    | .ok (nextState, emitted) =>
        state := nextState
        out := out.append emitted
  pure (.ok (state, out))

private def processFramesWith (registry : Registry) (frames : Array Frame) (i : Nat)
    (state : State) (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  let mut state := state
  for j in [i:frames.size] do
    match ← processFrameWith registry state frames[j]! emit with
    | .error status => return .error status
    | .ok nextState => state := nextState
  pure (.ok state)

private def processFramesSharedWith (registry : Registry) (stateMutex : Std.Mutex State)
    (frames : Array Frame) (i : Nat) (emit : Array Frame -> IO Unit)
    (receivedAt : Option Nat := none) :
    Std.Async.Async (Except Status Unit) := do
  for j in [i:frames.size] do
    match ← processFrameSharedWithOwned registry stateMutex frames[j]! emit receivedAt with
    | .error status => return .error status
    | .ok () => pure ()
  pure (.ok ())

def processBytes (registry : Registry) (state : State) (chunk : ByteArray) :
    IO (Except Status (State × Array Frame)) := do
  match consumePreface state chunk with
  | .error status => pure (.error status)
  | .ok (state, remaining) =>
      if remaining.isEmpty then
        pure (.ok (state, #[]))
      else
        match Frame.decodeChunk state.decoder remaining with
        | .error status => pure (.error status)
        | .ok decoded =>
            let state := { state with decoder := { buffered := decoded.buffered } }
            processFrames registry decoded.frames 0 state #[]

def processBytesWith (registry : Registry) (state : State) (chunk : ByteArray)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match consumePreface state chunk with
  | .error status => pure (.error status)
  | .ok (state, remaining) =>
      if remaining.isEmpty then
        pure (.ok state)
      else
        match Frame.decodeChunk state.decoder remaining with
        | .error status => pure (.error status)
        | .ok decoded =>
            let state := { state with decoder := { buffered := decoded.buffered } }
            processFramesWith registry decoded.frames 0 state emit

def processBytesSharedWithOwned (registry : Registry) (stateMutex : Std.Mutex State)
    (chunk : ByteArray)
    (emit : Array Frame -> IO Unit) : Std.Async.Async (Except Status Unit) := do
  -- All complete frames decoded from this receive chunk were already present
  -- at this instant.  Carry it through sequential frame processing so a slow
  -- earlier stream cannot extend a later stream's grpc-timeout.
  let receivedAt ← IO.monoNanosNow
  match ← stateMutex.atomically (do
    let state ← get
    match consumePreface state chunk with
    | .error status => pure (.error status)
    | .ok (state, remaining) =>
        if remaining.isEmpty then
          set state
          pure (Except.ok #[])
        else
          match Frame.decodeChunk state.decoder remaining with
          | .error status => pure (Except.error status)
          | .ok decoded =>
              set { state with decoder := { buffered := decoded.buffered } }
              pure (Except.ok decoded.frames)) with
  | .error status => pure (Except.error status)
  | .ok frames => processFramesSharedWith registry stateMutex frames 0 emit (some receivedAt)

/-- Synchronous compatibility wrapper around the connection-owner variant. -/
def processBytesSharedWith (registry : Registry) (stateMutex : Std.Mutex State) (chunk : ByteArray)
    (emit : Array Frame -> IO Unit) : IO (Except Status Unit) :=
  Std.Async.Async.block (processBytesSharedWithOwned registry stateMutex chunk emit)

def encodeFrames (frames : Array Frame) : Except Status ByteArray :=
  frames.foldlM (init := ByteArray.empty) fun out frame => do
    let bytes ← Frame.encode frame
    pure (out.append bytes)

def expirePendingDeadlinesEncodedSharedWith (stateMutex : Std.Mutex State)
    (emit : ByteArray -> IO Unit) : IO (Except Status Unit) :=
  expirePendingDeadlinesSharedWith stateMutex fun frames => do
    match encodeFrames frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

def processBytesEncodedWith (registry : Registry) (state : State) (chunk : ByteArray)
    (emit : ByteArray -> IO Unit) : IO (Except Status State) := do
  processBytesWith registry state chunk fun frames => do
    match encodeFrames frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

def processBytesEncodedSharedWithOwned (registry : Registry) (stateMutex : Std.Mutex State)
    (chunk : ByteArray) (emit : ByteArray -> IO Unit) :
    Std.Async.Async (Except Status Unit) := do
  processBytesSharedWithOwned registry stateMutex chunk fun frames => do
    match encodeFrames frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

/-- Synchronous compatibility wrapper around the connection-owner variant. -/
def processBytesEncodedSharedWith (registry : Registry) (stateMutex : Std.Mutex State)
    (chunk : ByteArray) (emit : ByteArray -> IO Unit) : IO (Except Status Unit) :=
  Std.Async.Async.block (processBytesEncodedSharedWithOwned registry stateMutex chunk emit)

def processBytesEncoded (registry : Registry) (state : State) (chunk : ByteArray) :
    IO (Except Status (State × ByteArray)) := do
  let bytesRef ← IO.mkRef ByteArray.empty
  match (← processBytesEncodedWith registry state chunk
      (fun bytes => bytesRef.modify fun out => out.append bytes)) with
  | .ok state => pure (.ok (state, ← bytesRef.get))
  | .error status => pure (.error status)

/-!
## Authorization-before-body properties

Trace property: over any frame sequence processed by a connection, a
stream whose request headers were rejected (authorization failure, invalid
headers, or unknown method) never feeds body bytes to a handler and never
dispatches one.

The rejection transition itself is the pure `rejectStreamAtHeaders` (used by
`authorizeRequestHeadersForStream`), and the pure kernel of body processing
is `processDataShared`.  Proved below, entirely against those real
implementations:

* `rejectStreamAtHeaders_rejected` / `rejectStreamAtHeaders_inert` — a
  rejection puts the stream in drain-only mode and makes it *inert*: no
  buffered frames, no incremental request feed, id already claimed.
* `processDataShared_rejected` — DATA for a drain-mode stream produces no
  request feed, no detached dispatch, no request-streaming dispatch and no
  cancellations, and cannot make the stream dispatchable again.
* `processDataShared_inert_reset` — DATA for an inert stream that is not in
  drain mode (e.g. after END_STREAM finished the drain, or after the stream
  was reset) is contained to that stream: RST_STREAM naming only that id, no
  request feed, no dispatch, nothing cancelled outside the id, and the stream
  goes back into drain mode.  The connection keeps serving.
* `DataTrace.inert_no_dispatch` / `rejectStreamAtHeaders_dataTrace_no_dispatch`
  — the trace-level statement: over any pure DATA trace for a rejected
  stream, every step is dispatch-free and the stream ends inert.

The shared kernel's other frame paths are covered by the following theorems
(`flushOutbound` is total, including for SETTINGS and WINDOW_UPDATE steps):

* `processNonHeaderFrameShared_inert` / `FrameTrace.inert_no_dispatch` /
  `rejectStreamAtHeaders_frameTrace_no_dispatch` — the generalized trace:
  over any successful sequence of SETTINGS, DATA, RST_STREAM, WINDOW_UPDATE,
  PING, PRIORITY, GOAWAY, and unknown steps whose DATA frames target the
  rejected stream, the stream stays inert and no step produces a request
  feed, detached dispatch, or request-streaming dispatch.
* `prepareHeadersShared_inert_error` / `processHeadersShared_inert_error` —
  a HEADERS frame naming an inert stream id is a connection error in the
  pure bookkeeping (`prepareHeadersShared`, factored out of the `IO`
  authorizer call): `requireNewClientStreamId` enforces id monotonicity and
  an inert id is already at or below `lastClientStreamId`.  The kernel tears
  the connection down without running the authorizer or dispatching.
* `appendContinuationFrame_inert_error` /
  `processContinuationShared_inert_error` — a CONTINUATION frame naming an
  inert stream id is likewise a connection error (no buffered header block).

Scope boundary for the full connection-level property:

* The `IO` layer (`processFrameSharedWith`) only spawns dispatch tasks for
  the `detached`/`requestStreaming`/`requestFeeds` artifacts shown empty
  above. The formal trace covers the pure results, not the task layer, because
  the spawn sites do not expose an `IO`-free event trace.
* DATA frames for *other* (live) streams legitimately produce request feeds
  for those streams. The trace conclusion excludes arbitrary interleaved DATA
  because `RequestStreamFeed` artifacts do not carry stream identity.
-/

/-- `true` when the connection is draining a request body without dispatch,
either after a headers rejection or after a locally generated RST_STREAM. -/
def State.rejectedAtHeaders (state : State) (streamId : Nat) : Bool :=
  drainsInboundStreamBody state streamId

/-- A stream id that can never reach a handler in this connection state: no
buffered header/body frames, no incremental request feed, and the id is
already claimed, so HTTP/2 stream-id monotonicity forbids reopening it. -/
structure State.StreamInert (state : State) (streamId : Nat) : Prop where
  notBuffered : ∀ stream ∈ state.streams, stream.streamId ≠ streamId
  notActive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId
  claimed : streamId ≤ state.lastClientStreamId

private theorem containsStreamId_pushUniqueStreamId (l : Array Nat) (id : Nat) :
    containsStreamId (pushUniqueStreamId l id) id = true := by
  unfold pushUniqueStreamId
  split
  next h => exact h
  next h => simp [containsStreamId]

private theorem removeStream_not_mem (streams : Array StreamState) (id : Nat) :
    ∀ s ∈ removeStream streams id, s.streamId ≠ id := by
  intro s hs
  have := (Array.mem_filter.mp hs).2
  simpa [bne_iff_ne] using this

private theorem removeActiveRequestStream_not_mem (streams : Array ActiveRequestStream)
    (id : Nat) : ∀ s ∈ removeActiveRequestStream streams id, s.streamId ≠ id := by
  intro s hs
  have := (Array.mem_filter.mp hs).2
  simpa [bne_iff_ne] using this

/-- A rejection whose request body is still open leaves the stream in
drain-only mode. -/
theorem rejectStreamAtHeaders_rejected (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) :
    (rejectStreamAtHeaders state streamId inboundHpack outboundHpack false).rejectedAtHeaders
      streamId = true := by
  unfold rejectStreamAtHeaders ignoreInboundStreamBody State.rejectedAtHeaders
    drainsInboundStreamBody
  simp only [Bool.false_eq_true, if_false]
  rw [containsStreamId_pushUniqueStreamId]
  rfl

/-- Rejecting a stream at headers makes it inert: its buffered frames are
gone, it never entered the incremental request path, and its id cannot be
reopened. -/
theorem rejectStreamAtHeaders_inert (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) (endStream : Bool)
    (hclaimed : streamId ≤ state.lastClientStreamId)
    (hactive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId) :
    (rejectStreamAtHeaders state streamId inboundHpack outboundHpack
      endStream).StreamInert streamId := by
  unfold rejectStreamAtHeaders
  split
  · exact {
      notBuffered := by
        intro s hs
        exact removeStream_not_mem _ _ s (by simpa [removeInboundStreamState] using hs)
      notActive := by
        intro s hs
        exact removeActiveRequestStream_not_mem _ _ s
          (by simpa [removeInboundStreamState] using hs)
      claimed := hclaimed
    }
  · exact {
      notBuffered := by
        intro s hs
        have hs' : s ∈ removeStream (removeStream state.streams streamId) streamId := by
          simpa [ignoreInboundStreamBody] using hs
        exact removeStream_not_mem _ _ s hs'
      notActive := by
        intro s hs
        exact hactive s (by simpa [ignoreInboundStreamBody] using hs)
      claimed := hclaimed
    }


private theorem consumeInboundDataWindow_ok {state state' : State} {frame : Frame}
    (h : consumeInboundDataWindow state frame = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.ignoredInboundStreams = state.ignoredInboundStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold consumeInboundDataWindow at h
  simp only [] at h
  split at h
  next =>
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  next =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next =>
        cases h
        simp [setInboundStreamWindow]

private theorem replenishInboundDataWindow_fields (state : State) (frame : Frame) :
    (replenishInboundDataWindow state frame).streams = state.streams
      ∧ (replenishInboundDataWindow state frame).activeRequestStreams
          = state.activeRequestStreams
      ∧ (replenishInboundDataWindow state frame).ignoredInboundStreams
          = state.ignoredInboundStreams
      ∧ (replenishInboundDataWindow state frame).lastClientStreamId
          = state.lastClientStreamId := by
  unfold replenishInboundDataWindow
  grind [setInboundStreamWindow]

private theorem removeInboundStreamState_fields (state : State) (streamId : Nat) :
    (removeInboundStreamState state streamId).streams = state.streams
      ∧ (removeInboundStreamState state streamId).lastClientStreamId
          = state.lastClientStreamId
      ∧ (∀ active ∈ (removeInboundStreamState state streamId).activeRequestStreams,
          active ∈ state.activeRequestStreams) := by
  refine ⟨rfl, rfl, ?_⟩
  intro active hactive
  exact (Array.mem_filter.mp hactive).1

private theorem processIgnoredInboundData_ok {state state' : State} {frame : Frame}
    {updates : Array Frame}
    (h : processIgnoredInboundData state frame = .ok (state', updates)) :
    state'.streams = state.streams
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams) := by
  unfold processIgnoredInboundData at h
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst,
    pure, Except.pure] at h
  split at h
  next => cases h
  next s1 hcons =>
    split at h
    next => cases h
    next updates1 hupd =>
      split at h
      next => cases h
      next frame1 hstrip =>
        split at h
        next => cases h
        next _u hnorm =>
          cases h
          obtain ⟨hs1, ha1, -, hl1⟩ := consumeInboundDataWindow_ok hcons
          obtain ⟨hs2, ha2, -, hl2⟩ := replenishInboundDataWindow_fields s1 frame
          split
          · obtain ⟨hs3, hl3, ha3⟩ := removeInboundStreamState_fields
              (replenishInboundDataWindow s1 frame) frame1.header.streamId
            refine ⟨hs3.trans (hs2.trans hs1), hl3.trans (hl2.trans hl1), ?_⟩
            intro active hmem
            have hmem' := ha3 active hmem
            rw [ha2, ha1] at hmem'
            exact hmem'
          · refine ⟨hs2.trans hs1, hl2.trans hl1, ?_⟩
            intro active hmem
            rw [ha2, ha1] at hmem
            exact hmem

private theorem processResetInboundData_state {state state' : State} {frame : Frame}
    {updates : Array Frame}
    (h : processResetInboundData state frame = .ok (state', updates)) :
    state' = state ∨ ∃ streamId, state' = removeInboundStreamState state streamId := by
  unfold processResetInboundData at h
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst,
    pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next =>
      split at h
      next => cases h
      next frame' hstrip =>
        split at h
        next => cases h
        next _ hnorm =>
          cases h
          split
          · exact .inr ⟨frame'.header.streamId, rfl⟩
          · exact .inl rfl
    next =>
      split at h
      next => cases h
      next update hupdate =>
        split at h
        next => cases h
        next frame' hstrip =>
          split at h
          next => cases h
          next _ hnorm =>
            cases h
            split
            · exact .inr ⟨frame'.header.streamId, rfl⟩
            · exact .inl rfl

private theorem processResetInboundData_ok {state state' : State} {frame : Frame}
    {updates : Array Frame}
    (h : processResetInboundData state frame = .ok (state', updates)) :
    state'.streams = state.streams
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams) := by
  rcases processResetInboundData_state h with rfl | ⟨streamId, rfl⟩
  · exact ⟨rfl, rfl, fun _ hactive => hactive⟩
  · exact removeInboundStreamState_fields state streamId

private theorem processDrainingInboundData_ok {state state' : State} {frame : Frame}
    {updates : Array Frame}
    (h : processDrainingInboundData state frame = .ok (state', updates)) :
    state'.streams = state.streams
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams) := by
  unfold processDrainingInboundData at h
  split at h
  · exact processResetInboundData_ok h
  · exact processIgnoredInboundData_ok h


/-- A DATA frame for a stream rejected at headers is drained: the step
produces no request feed, no detached dispatch, no request-streaming
dispatch, and no cancellations, and the stream cannot re-enter the
dispatchable state. -/
private theorem processDataShared_rejected {registry : Registry} {state state' : State}
    {frame : Frame} {result : SharedFrameResult}
    (hrej : state.rejectedAtHeaders frame.header.streamId = true)
    (h : processDataShared registry state frame = .ok (state', result)) :
    result.requestFeeds = #[] ∧ result.detached = none ∧ result.requestStreaming = none
      ∧ result.cancelDispatches = #[]
      ∧ state'.streams = state.streams
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams) := by
  unfold processDataShared at h
  split at h
  next => cases h
  next =>
    rw [show drainsInboundStreamBody state frame.header.streamId = true
      from hrej] at h
    simp only [if_true] at h
    split at h
    next => cases h
    next drained updates hproc =>
      cases h
      obtain ⟨hs, hl, ha⟩ := processDrainingInboundData_ok hproc
      exact ⟨rfl, rfl, rfl, rfl, hs, hl, ha⟩

/-- A DATA frame for an inert stream that is not in drain mode — the stream was
opened, ran to completion or was reset, and the peer is still sending on it — is
contained to that stream.  The step goes through `resetClosedStreamData`
(RFC 9113 §6.1 STREAM_CLOSED), so it produces no request feed, no detached
dispatch and no request-streaming dispatch; it cancels nothing belonging to any
*other* stream; it emits an RST_STREAM naming only this stream; and it puts the
id back in drain mode, leaving every other stream's state untouched.

This is the pure statement of per-stream error containment: the connection is
not torn down, and nothing outside `frame.header.streamId` moves. -/
theorem processDataShared_inert_reset {registry : Registry} {state state' : State}
    {frame : Frame} {result : SharedFrameResult}
    (hinert : state.StreamInert frame.header.streamId)
    (hnotrej : state.rejectedAtHeaders frame.header.streamId = false)
    (h : processDataShared registry state frame = .ok (state', result)) :
    result.requestFeeds = #[] ∧ result.detached = none ∧ result.requestStreaming = none
      ∧ (∀ dispatch ∈ result.cancelDispatches, dispatch.streamId = frame.header.streamId)
      ∧ state'.streams = removeStream state.streams frame.header.streamId
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams)
      ∧ (∃ rst ∈ result.emitted,
          rst.header.frameType = FrameType.rstStream
            ∧ rst.header.streamId = frame.header.streamId) := by
  unfold processDataShared at h
  split at h
  next => cases h
  next =>
    rw [show drainsInboundStreamBody state frame.header.streamId = false
      from hnotrej] at h
    simp only [Bool.false_eq_true, if_false] at h
    have hactive : findActiveRequestStream? state.activeRequestStreams
        frame.header.streamId = none := by
      unfold findActiveRequestStream?
      rw [Array.find?_eq_none]
      intro x hx
      simp [hinert.notActive x hx]
    have hstream : findStream? state.streams frame.header.streamId = none := by
      unfold findStream?
      rw [Array.find?_eq_none]
      intro x hx
      simp [hinert.notBuffered x hx]
    rw [hactive, hstream] at h
    simp only [] at h
    rw [if_pos hinert.claimed] at h
    unfold resetClosedStreamData at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    next => cases h
    next rst hrst =>
      split at h
      next => cases h
      next pair hproc =>
        obtain ⟨drained, updates⟩ := pair
        cases h
        obtain ⟨hs, hl, ha⟩ := processResetInboundData_ok hproc
        refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · intro dispatch hd
          have := (Array.mem_filter.mp hd).2
          simpa using this
        · rw [hs]
          simp [drainResetInboundStreamBody, removeOutboundStreamState]
        · rw [hl]; rfl
        · intro active hmem
          have hmem' := ha active hmem
          simpa [drainResetInboundStreamBody, removeOutboundStreamState] using hmem'
        · refine ⟨rst, Array.mem_push_self, ?_, ?_⟩
          · exact RstStream.frame_frameType hrst
          · exact RstStream.frame_streamId hrst


/-- A pure trace of the shared kernel's DATA-frame steps: each listed frame
is processed by `processDataShared` from the previous state and produces the
recorded `SharedFrameResult`. -/
inductive DataTrace (registry : Registry) :
    State -> List (Frame × SharedFrameResult) -> State -> Prop
  | nil (state : State) : DataTrace registry state [] state
  | step {state mid final : State} {frame : Frame} {result : SharedFrameResult}
      {rest : List (Frame × SharedFrameResult)}
      (h : processDataShared registry state frame = .ok (mid, result))
      (htail : DataTrace registry mid rest final) :
      DataTrace registry state ((frame, result) :: rest) final

private theorem DataTrace.inert_no_dispatch {registry : Registry}
    {state final : State} {steps : List (Frame × SharedFrameResult)}
    (trace : DataTrace registry state steps final) (streamId : Nat)
    (htarget : ∀ step ∈ steps, (step.1 : Frame).header.streamId = streamId)
    (hinert : state.StreamInert streamId) :
    final.StreamInert streamId
      ∧ ∀ step ∈ steps,
          (step.2 : SharedFrameResult).requestFeeds = #[] ∧ (step.2).detached = none
            ∧ (step.2).requestStreaming = none
            ∧ ∀ dispatch ∈ (step.2).cancelDispatches, dispatch.streamId = streamId := by
  induction steps generalizing state with
  | nil =>
      cases trace
      exact ⟨hinert, by simp⟩
  | cons head rest ih =>
      cases trace with
      | step h htail =>
        rename_i mid frame result
        have htargetHead : frame.header.streamId = streamId :=
          htarget (frame, result) List.mem_cons_self
        cases hrej : state.rejectedAtHeaders frame.header.streamId with
        | false =>
            obtain ⟨hfeeds, hdet, hstreaming, hcancel, hs, hl, ha, -⟩ :=
              processDataShared_inert_reset (htargetHead.symm ▸ hinert) hrej h
            have hmid : mid.StreamInert streamId := {
              notBuffered := fun s hs' =>
                htargetHead ▸ removeStream_not_mem _ _ s (hs ▸ hs'),
              notActive := fun a ha' => hinert.notActive a (ha a ha'),
              claimed := by rw [hl]; exact hinert.claimed
            }
            have ihres := ih htail
              (fun step hstep => htarget step (List.mem_cons_of_mem _ hstep)) hmid
            refine ⟨ihres.1, ?_⟩
            intro step hstep
            cases hstep with
            | head =>
                exact ⟨hfeeds, hdet, hstreaming,
                  fun d hd => htargetHead ▸ hcancel d hd⟩
            | tail _ hstep => exact ihres.2 step hstep
        | true =>
            obtain ⟨hfeeds, hdet, hstreaming, hcancel, hs, hl, ha⟩ :=
              processDataShared_rejected hrej h
            have hmid : mid.StreamInert streamId := {
              notBuffered := fun s hs' => hinert.notBuffered s (hs ▸ hs'),
              notActive := fun a ha' => hinert.notActive a (ha a ha'),
              claimed := by rw [hl]; exact hinert.claimed
            }
            have ihres := ih htail
              (fun step hstep => htarget step (List.mem_cons_of_mem _ hstep)) hmid
            refine ⟨ihres.1, ?_⟩
            intro step hstep
            cases hstep with
            | head =>
                refine ⟨hfeeds, hdet, hstreaming, ?_⟩
                rw [hcancel]
                simp
            | tail _ hstep => exact ihres.2 step hstep

/-- When request-header authorization rejects a stream
whose body is still open, any pure DATA trace for that stream drains without
producing any dispatch work, and the stream ends (and stays) inert. -/
private theorem rejectStreamAtHeaders_dataTrace_no_dispatch
    {registry : Registry} {state final : State}
    {steps : List (Frame × SharedFrameResult)}
    (streamId : Nat) (inboundHpack outboundHpack : Hpack.State) (endStream : Bool)
    (hclaimed : streamId ≤ state.lastClientStreamId)
    (hactive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId)
    (trace : DataTrace registry
      (rejectStreamAtHeaders state streamId inboundHpack outboundHpack endStream)
      steps final)
    (htarget : ∀ step ∈ steps, (step.1 : Frame).header.streamId = streamId) :
    final.StreamInert streamId
      ∧ ∀ step ∈ steps,
          (step.2 : SharedFrameResult).requestFeeds = #[] ∧ (step.2).detached = none
            ∧ (step.2).requestStreaming = none
            ∧ ∀ dispatch ∈ (step.2).cancelDispatches, dispatch.streamId = streamId :=
  trace.inert_no_dispatch streamId htarget
    (rejectStreamAtHeaders_inert state streamId inboundHpack outboundHpack endStream
      hclaimed hactive)

/-!
### Non-header frame steps

Every pure shared-kernel step other than HEADERS/CONTINUATION —
`processNonHeaderFrameShared`, covering SETTINGS, DATA, RST_STREAM,
WINDOW_UPDATE, PING, PRIORITY, GOAWAY, unknown — preserves the inertness of a
rejected stream and creates no dispatch work.  The field-preservation lemmas
below track the three inertness-relevant fields (`streams`,
`activeRequestStreams`, `lastClientStreamId`) through each processor,
including the totalized `flushOutbound`.
-/

private theorem State.StreamInert.of_fields {state state' : State} {streamId : Nat}
    (hinert : state.StreamInert streamId)
    (hstreams : ∀ s ∈ state'.streams, s ∈ state.streams)
    (hactive : ∀ a ∈ state'.activeRequestStreams, a ∈ state.activeRequestStreams)
    (hlast : state'.lastClientStreamId = state.lastClientStreamId) :
    state'.StreamInert streamId := {
  notBuffered := fun s hs => hinert.notBuffered s (hstreams s hs)
  notActive := fun a ha => hinert.notActive a (hactive a ha)
  claimed := by rw [hlast]; exact hinert.claimed
}

private theorem cleanupOutboundIfEndStream_streams (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).streams = state.streams := by
  unfold cleanupOutboundIfEndStream
  split <;> rfl

private theorem cleanupOutboundIfEndStream_activeRequestStreams (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).activeRequestStreams
      = state.activeRequestStreams := by
  unfold cleanupOutboundIfEndStream
  split <;> rfl

private theorem cleanupOutboundIfEndStream_lastClientStreamId (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).lastClientStreamId = state.lastClientStreamId := by
  unfold cleanupOutboundIfEndStream
  split <;> rfl

private theorem flushOutbound_fields (state : State) (emitted : Array Frame) :
    (flushOutbound state emitted).1.streams = state.streams
      ∧ (flushOutbound state emitted).1.activeRequestStreams = state.activeRequestStreams
      ∧ (flushOutbound state emitted).1.lastClientStreamId = state.lastClientStreamId := by
  fun_induction flushOutbound state emitted <;>
    simp_all +zetaDelta [cleanupOutboundIfEndStream_streams,
      cleanupOutboundIfEndStream_activeRequestStreams,
      cleanupOutboundIfEndStream_lastClientStreamId, setOutboundStreamWindow]

private theorem applyInitialWindowSize_ok {state state' : State} {value : Nat}
    (h : applyInitialWindowSize state value = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold applyInitialWindowSize at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next windows hmap =>
      cases h
      exact ⟨rfl, rfl, rfl⟩

private theorem applyMaxFrameSize_ok {state state' : State} {value : Nat}
    (h : applyMaxFrameSize state value = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold applyMaxFrameSize at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    cases h
    exact ⟨rfl, rfl, rfl⟩

private theorem applyPeerSetting_ok {state state' : State} {setting : Setting}
    (h : applyPeerSetting state setting = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold applyPeerSetting at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h; exact ⟨rfl, rfl, rfl⟩
  next =>
    split at h
    next => cases h; exact ⟨rfl, rfl, rfl⟩
    next => cases h
  next => exact applyInitialWindowSize_ok h
  next => exact applyMaxFrameSize_ok h
  next => cases h; exact ⟨rfl, rfl, rfl⟩
  next => cases h; exact ⟨rfl, rfl, rfl⟩
  next => cases h; exact ⟨rfl, rfl, rfl⟩

private theorem applyPeerSettings_ok {settings : Array Setting} {state state' : State}
    (h : applyPeerSettings state settings = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold applyPeerSettings at h
  rw [← Array.foldlM_toList] at h
  generalize settings.toList = l at h
  induction l generalizing state with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure] at h
      cases h
      exact ⟨rfl, rfl, rfl⟩
  | cons s rest ih =>
      simp only [List.foldlM_cons, bind, Except.bind] at h
      split at h
      next => cases h
      next mid hmid =>
        obtain ⟨h1, h2, h3⟩ := applyPeerSetting_ok hmid
        obtain ⟨g1, g2, g3⟩ := ih h
        exact ⟨g1.trans h1, g2.trans h2, g3.trans h3⟩

private theorem processSettings_ok {state : State} {frame : Frame} {res : State × Array Frame}
    (h : processSettings state frame = .ok res) :
    res.1.streams = state.streams
      ∧ res.1.activeRequestStreams = state.activeRequestStreams
      ∧ res.1.lastClientStreamId = state.lastClientStreamId := by
  unfold processSettings at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next settings hdec =>
    split at h
    next =>
      split at h
      next => cases h
      next => cases h; exact ⟨rfl, rfl, rfl⟩
    next =>
      split at h
      next => cases h
      next s1 happ =>
        split at h
        next => cases h
        next ack hack =>
          cases h
          obtain ⟨a1, a2, a3⟩ := applyPeerSettings_ok happ
          obtain ⟨f1, f2, f3⟩ :=
            flushOutbound_fields { s1 with clientSettingsReceived := true } #[]
          exact ⟨f1.trans a1, f2.trans a2, f3.trans a3⟩

private theorem applyWindowUpdate_ok {state state' : State} {frame : Frame}
    (h : applyWindowUpdate state frame = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold applyWindowUpdate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next increment hdec =>
    split at h
    next =>
      unfold addOutboundConnectionWindow at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      next => cases h
      next => cases h; exact ⟨rfl, rfl, rfl⟩
    next =>
      unfold addOutboundStreamWindow at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      next => cases h
      next => cases h; exact ⟨rfl, rfl, rfl⟩

private theorem processWindowUpdate_ok {state : State} {frame : Frame}
    {res : State × Array Frame} (h : processWindowUpdate state frame = .ok res) :
    res.1.streams = state.streams
      ∧ res.1.activeRequestStreams = state.activeRequestStreams
      ∧ res.1.lastClientStreamId = state.lastClientStreamId := by
  unfold processWindowUpdate at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- The outer split is on the `streamId != 0` guard; each branch then splits
  -- on `requireClientStreamId` (first branch only) and `applyWindowUpdate`.
  split at h
  next =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next s1 hupd =>
        cases h
        obtain ⟨a1, a2, a3⟩ := applyWindowUpdate_ok hupd
        obtain ⟨f1, f2, f3⟩ := flushOutbound_fields s1 #[]
        exact ⟨f1.trans a1, f2.trans a2, f3.trans a3⟩
  next =>
    split at h
    next => cases h
    next s1 hupd =>
      cases h
      obtain ⟨a1, a2, a3⟩ := applyWindowUpdate_ok hupd
      obtain ⟨f1, f2, f3⟩ := flushOutbound_fields s1 #[]
      exact ⟨f1.trans a1, f2.trans a2, f3.trans a3⟩

private theorem processPing_ok {state : State} {frame : Frame} {res : State × Array Frame}
    (h : processPing state frame = .ok res) :
    res.1.streams = state.streams
      ∧ res.1.activeRequestStreams = state.activeRequestStreams
      ∧ res.1.lastClientStreamId = state.lastClientStreamId := by
  unfold processPing at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next payload hdec =>
    split at h
    next =>
      cases h
      refine ⟨?_, ?_, ?_⟩ <;> (split <;> first | rfl | (split <;> rfl))
    next =>
      split at h
      next => cases h
      next => cases h; exact ⟨rfl, rfl, rfl⟩

private theorem processGoAway_ok {state : State} {frame : Frame} {res : State × Array Frame}
    (h : processGoAway state frame = .ok res) :
    res.1.streams = state.streams
      ∧ res.1.activeRequestStreams = state.activeRequestStreams
      ∧ res.1.lastClientStreamId = state.lastClientStreamId := by
  unfold processGoAway at h
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst, pure,
    Except.pure] at h
  split at h
  next => cases h
  next => cases h; exact ⟨rfl, rfl, rfl⟩

private theorem processPriority_ok {state : State} {frame : Frame} {res : State × Array Frame}
    (h : processPriority state frame = .ok res) :
    res.1.streams = state.streams
      ∧ res.1.activeRequestStreams = state.activeRequestStreams
      ∧ res.1.lastClientStreamId = state.lastClientStreamId := by
  unfold processPriority at h
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst, pure,
    Except.pure] at h
  split at h
  next => cases h
  next => cases h; exact ⟨rfl, rfl, rfl⟩

private theorem processRstStreamShared_ok {state : State} {frame : Frame}
    {res : State × SharedFrameResult}
    (h : processRstStreamShared state frame = .ok res) :
    (∀ s ∈ res.1.streams, s ∈ state.streams)
      ∧ (∀ a ∈ res.1.activeRequestStreams, a ∈ state.activeRequestStreams)
      ∧ res.1.lastClientStreamId = state.lastClientStreamId
      ∧ res.2.requestFeeds = #[] ∧ res.2.detached = none
      ∧ res.2.requestStreaming = none := by
  unfold processRstStreamShared at h
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst, pure,
    Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next =>
      cases h
      refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
      · intro s hs
        simp only [removeOutboundStreamState, removeInboundStreamState,
          removeStream] at hs
        exact (Array.mem_filter.mp hs).1
      · intro a ha
        simp only [removeOutboundStreamState, removeInboundStreamState,
          removeActiveRequestStream] at ha
        exact (Array.mem_filter.mp ha).1

/-- Any successful shared-kernel step for a non-header frame preserves the
inertness of a stream — provided any DATA frame targets that stream — and
creates no dispatch work: no request feed, no detached dispatch, no
request-streaming dispatch. -/
private theorem processNonHeaderFrameShared_inert {registry : Registry} {state : State}
    {frame : Frame} {res : State × SharedFrameResult} {streamId : Nat}
    (hinert : state.StreamInert streamId)
    (hdata : frame.header.frameType = FrameType.data → frame.header.streamId = streamId)
    (h : processNonHeaderFrameShared registry state frame = .ok res) :
    res.1.StreamInert streamId
      ∧ res.2.requestFeeds = #[] ∧ res.2.detached = none
      ∧ res.2.requestStreaming = none := by
  unfold processNonHeaderFrameShared at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  -- SETTINGS
  next =>
    split at h
    next => cases h
    next pair hset =>
      obtain ⟨s1, em⟩ := pair
      cases h
      obtain ⟨h1, h2, h3⟩ := processSettings_ok hset
      exact ⟨hinert.of_fields (fun s hs => h1 ▸ hs) (fun a ha => h2 ▸ ha) h3, rfl, rfl, rfl⟩
  -- DATA
  next htype =>
    have hsid : frame.header.streamId = streamId := hdata htype
    cases hrej : state.rejectedAtHeaders frame.header.streamId with
    | false =>
        obtain ⟨hfeeds, hdet, hstr, -, hs, hl, ha, -⟩ :=
          processDataShared_inert_reset (state' := res.1) (result := res.2)
            (hsid.symm ▸ hinert) hrej h
        refine ⟨?_, hfeeds, hdet, hstr⟩
        exact hinert.of_fields
          (fun s hmem => (Array.mem_filter.mp (hs ▸ hmem)).1) ha hl
    | true =>
        obtain ⟨hfeeds, hdet, hstr, _hcancel, hs, hl, ha⟩ :=
          processDataShared_rejected (state' := res.1) (result := res.2) hrej h
        exact ⟨hinert.of_fields (fun s hmem => hs ▸ hmem) ha hl, hfeeds, hdet, hstr⟩
  -- RST_STREAM
  next =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := processRstStreamShared_ok h
    exact ⟨hinert.of_fields h1 h2 h3, h4, h5, h6⟩
  -- WINDOW_UPDATE
  next =>
    split at h
    next => cases h
    next pair hupd =>
      obtain ⟨s1, em⟩ := pair
      cases h
      obtain ⟨h1, h2, h3⟩ := processWindowUpdate_ok hupd
      exact ⟨hinert.of_fields (fun s hs => h1 ▸ hs) (fun a ha => h2 ▸ ha) h3, rfl, rfl, rfl⟩
  -- PING
  next =>
    split at h
    next => cases h
    next pair hping =>
      obtain ⟨s1, em⟩ := pair
      cases h
      obtain ⟨h1, h2, h3⟩ := processPing_ok hping
      exact ⟨hinert.of_fields (fun s hs => h1 ▸ hs) (fun a ha => h2 ▸ ha) h3, rfl, rfl, rfl⟩
  -- PRIORITY
  next =>
    split at h
    next => cases h
    next pair hprio =>
      obtain ⟨s1, em⟩ := pair
      cases h
      obtain ⟨h1, h2, h3⟩ := processPriority_ok hprio
      exact ⟨hinert.of_fields (fun s hs => h1 ▸ hs) (fun a ha => h2 ▸ ha) h3, rfl, rfl, rfl⟩
  -- GOAWAY
  next =>
    split at h
    next => cases h
    next pair hgo =>
      obtain ⟨s1, em⟩ := pair
      cases h
      obtain ⟨h1, h2, h3⟩ := processGoAway_ok hgo
      exact ⟨hinert.of_fields (fun s hs => h1 ▸ hs) (fun a ha => h2 ▸ ha) h3, rfl, rfl, rfl⟩
  -- PUSH_PROMISE
  next => cases h
  -- unknown
  next =>
    cases h
    exact ⟨hinert, rfl, rfl, rfl⟩
  -- HEADERS/CONTINUATION (unreachable in this kernel; two matcher cases)
  next => cases h
  next => cases h

/-- A pure trace of shared-kernel steps over non-header frames: each listed
frame is processed by `processNonHeaderFrameShared` from the previous state
and produces the recorded `SharedFrameResult`. -/
inductive FrameTrace (registry : Registry) :
    State -> List (Frame × SharedFrameResult) -> State -> Prop
  | nil (state : State) : FrameTrace registry state [] state
  | step {state mid final : State} {frame : Frame} {result : SharedFrameResult}
      {rest : List (Frame × SharedFrameResult)}
      (h : processNonHeaderFrameShared registry state frame = .ok (mid, result))
      (htail : FrameTrace registry mid rest final) :
      FrameTrace registry state ((frame, result) :: rest) final

/-- Trace-level generalization of `DataTrace.inert_no_dispatch` to every
non-header frame type: over any successful sequence of SETTINGS, DATA,
RST_STREAM, WINDOW_UPDATE, PING, PRIORITY, GOAWAY, and unknown steps in which
DATA frames target the inert stream, the stream stays inert and no step
produces dispatch work. -/
private theorem FrameTrace.inert_no_dispatch {registry : Registry}
    {state final : State} {steps : List (Frame × SharedFrameResult)}
    (trace : FrameTrace registry state steps final) (streamId : Nat)
    (hdata : ∀ step ∈ steps, (step.1 : Frame).header.frameType = FrameType.data →
      (step.1).header.streamId = streamId)
    (hinert : state.StreamInert streamId) :
    final.StreamInert streamId
      ∧ ∀ step ∈ steps,
          (step.2 : SharedFrameResult).requestFeeds = #[] ∧ (step.2).detached = none
            ∧ (step.2).requestStreaming = none := by
  induction steps generalizing state with
  | nil =>
      cases trace
      exact ⟨hinert, by simp⟩
  | cons head rest ih =>
      cases trace with
      | step h htail =>
        rename_i mid frame result
        have hstep := processNonHeaderFrameShared_inert hinert
          (hdata (frame, result) List.mem_cons_self) h
        have ihres := ih htail
          (fun step hmem => hdata step (List.mem_cons_of_mem _ hmem)) hstep.1
        refine ⟨ihres.1, ?_⟩
        intro step hmem
        cases hmem with
        | head => exact hstep.2
        | tail _ hmem => exact ihres.2 step hmem

/-- Generalized headline: when request-header authorization rejects a stream
whose body is still open, any pure trace of non-header frames whose DATA
frames target that stream drains without producing any dispatch work, and the
stream ends (and stays) inert. -/
theorem rejectStreamAtHeaders_frameTrace_no_dispatch
    {registry : Registry} {state final : State}
    {steps : List (Frame × SharedFrameResult)}
    (streamId : Nat) (inboundHpack outboundHpack : Hpack.State) (endStream : Bool)
    (hclaimed : streamId ≤ state.lastClientStreamId)
    (hactive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId)
    (trace : FrameTrace registry
      (rejectStreamAtHeaders state streamId inboundHpack outboundHpack endStream)
      steps final)
    (hdata : ∀ step ∈ steps, (step.1 : Frame).header.frameType = FrameType.data →
      (step.1).header.streamId = streamId) :
    final.StreamInert streamId
      ∧ ∀ step ∈ steps,
          (step.2 : SharedFrameResult).requestFeeds = #[] ∧ (step.2).detached = none
            ∧ (step.2).requestStreaming = none :=
  trace.inert_no_dispatch streamId hdata
    (rejectStreamAtHeaders_inert state streamId inboundHpack outboundHpack endStream
      hclaimed hactive)

/-!
### HEADERS and CONTINUATION steps

An inert stream id can never be reopened: the pure bookkeeping of a HEADERS
step (`prepareHeadersShared`, factored out of the `IO` authorizer call in
`processHeadersShared`) refuses the frame with a connection error because the
id is at or below `lastClientStreamId`, and a CONTINUATION step refuses it
because the stream has no buffered header block.  Either way the connection
tears down before any authorizer or dispatch work happens.
-/

/-- A HEADERS frame naming an inert stream id is a connection error in the
pure bookkeeping, before the authorizer runs. -/
private theorem prepareHeadersShared_inert_error {state : State} {frame : Frame}
    (hinert : state.StreamInert frame.header.streamId) {res : State × Option Frame} :
    prepareHeadersShared state frame ≠ .ok res := by
  intro h
  unfold prepareHeadersShared at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next =>
      have herr : ∀ r, requireNewClientStreamId state frame.header.streamId ≠ .ok r := by
        intro r hok
        unfold requireNewClientStreamId at hok
        simp only [bind, Except.bind, pure, Except.pure] at hok
        split at hok
        next => cases hok
        next =>
          split at hok
          next => cases hok
          next hcond => exact hcond hinert.claimed
      split at h
      next => cases h
      next _u hnew => exact herr _ hnew

/-- `processHeadersShared` on a HEADERS frame naming an inert stream id fails
with a connection error and performs no `IO`: the action is literally
`pure (.error status)`. -/
private theorem processHeadersShared_inert_error (registry : Registry) {state : State}
    {frame : Frame} (hinert : state.StreamInert frame.header.streamId) :
    ∃ status, processHeadersShared registry state frame = pure (.error status) := by
  obtain ⟨status, herr⟩ : ∃ status, prepareHeadersShared state frame = .error status := by
    cases hcase : prepareHeadersShared state frame with
    | error status => exact ⟨status, rfl⟩
    | ok res => exact absurd hcase (prepareHeadersShared_inert_error hinert)
  refine ⟨status, ?_⟩
  unfold processHeadersShared
  rw [herr]

private theorem appendContinuationFrame_inert_error {state : State} {frame : Frame}
    (hinert : state.StreamInert frame.header.streamId) {streams' : Array StreamState} :
    appendContinuationFrame state.streams frame ≠ .ok streams' := by
  intro h
  unfold appendContinuationFrame at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    have hnone : findStream? state.streams frame.header.streamId = none := by
      unfold findStream?
      rw [Array.find?_eq_none]
      intro x hx
      simp [hinert.notBuffered x hx]
    split at h
    next stream hfind =>
      rw [hnone] at hfind
      cases hfind
    next => cases h

/-- `processContinuationShared` on a CONTINUATION frame naming an inert stream
id fails with a connection error and performs no `IO`. -/
private theorem processContinuationShared_inert_error (registry : Registry) {state : State}
    {frame : Frame} (hinert : state.StreamInert frame.header.streamId) :
    ∃ status, processContinuationShared registry state frame = pure (.error status) := by
  obtain ⟨status, herr⟩ :
      ∃ status, appendContinuationFrame state.streams frame = .error status := by
    cases hcase : appendContinuationFrame state.streams frame with
    | error status => exact ⟨status, rfl⟩
    | ok streams => exact absurd hcase (appendContinuationFrame_inert_error hinert)
  refine ⟨status, ?_⟩
  unfold processContinuationShared
  rw [herr]

/-!
## Connection well-formedness

`WellFormed` is the pure structural invariant of a served connection: the
stream-id discipline (client parity, monotone claiming, so a closed stream is
never reactivated), CONTINUATION sequencing (at most one header block is open,
and it belongs to the newest stream), the 31-bit bounds on every outbound
flow-control window, and the HPACK dynamic tables staying inside their
negotiated limits.

It is preserved by all three pure frame transitions:

* `processNonHeaderFrameShared_wellFormed` — SETTINGS, DATA, RST_STREAM,
  WINDOW_UPDATE, PING, PRIORITY, GOAWAY and unknown frames;
* `prepareHeadersShared_wellFormed` — the pure bookkeeping of a HEADERS frame;
* `appendContinuationFrame_wellFormed` — a CONTINUATION frame.

The `IO` halves of the HEADERS/CONTINUATION steps (header decoding,
authorization, dispatch spawning) are outside this statement.
-/

/-- Pure well-formedness of a server connection state. -/
structure WellFormed (state : State) : Prop where
  /-- Every buffered stream is client-initiated and has already been claimed,
  so its id can never be opened again (`requireNewClientStreamId` demands a
  strictly larger id). -/
  streamIds : ∀ stream ∈ state.streams,
    isClientStreamId stream.streamId = true ∧ stream.streamId ≤ state.lastClientStreamId
  /-- CONTINUATION sequencing: an open header block can only belong to the most
  recently opened stream, so at most one is open at a time. -/
  pendingHeaders : ∀ stream ∈ state.streams,
    streamHeaderPending stream = true → stream.streamId = state.lastClientStreamId
  /-- The advertised initial window fits the 31-bit field. -/
  outboundInitial : state.outboundInitialStreamWindow ≤ maxStreamId
  /-- The outbound connection window fits the 31-bit field. -/
  outboundConnection : state.outboundConnectionWindow ≤ maxStreamId
  /-- Every outbound stream window fits the 31-bit field.  (It may be negative:
  RFC 9113 §6.9.2 allows SETTINGS to shrink a window below zero.) -/
  outboundStreams : ∀ window ∈ state.outboundStreamWindows,
    window.window ≤ (maxStreamId : Int)
  /-- The peer's HPACK dynamic table is within the size we encode against. -/
  outboundTable : Hpack.dynamicSize state.outboundHpack.dynamic ≤ state.outboundHpack.maxSize
  /-- Our HPACK dynamic table is within the size we advertised. -/
  inboundTable : Hpack.dynamicSize state.hpack.dynamic ≤ state.hpack.maxSize

/-- A fresh connection state is well formed. -/
theorem initialState_wellFormed (maxConcurrentStreams maxHeaderListSize : Option Nat)
    (initialWindowSize : Nat) :
    WellFormed (initialState maxConcurrentStreams maxHeaderListSize initialWindowSize) where
  streamIds := by
    intro s hs
    rw [show (initialState maxConcurrentStreams maxHeaderListSize initialWindowSize).streams
        = #[] from rfl] at hs
    simp at hs
  pendingHeaders := by
    intro s hs
    rw [show (initialState maxConcurrentStreams maxHeaderListSize initialWindowSize).streams
        = #[] from rfl] at hs
    simp at hs
  outboundInitial := by
    show initialFlowControlWindow ≤ maxStreamId
    unfold initialFlowControlWindow maxStreamId
    decide
  outboundConnection := by
    show initialFlowControlWindow ≤ maxStreamId
    unfold initialFlowControlWindow maxStreamId
    decide
  outboundStreams := by
    intro w hw
    rw [show (initialState maxConcurrentStreams maxHeaderListSize
        initialWindowSize).outboundStreamWindows = #[] from rfl] at hw
    simp at hw
  outboundTable := by
    change Hpack.dynamicSize (Hpack.withoutDynamicTable {}).dynamic
      ≤ (Hpack.withoutDynamicTable {}).maxSize
    rw [Hpack.dynamicSize_withoutDynamicTable, Hpack.maxSize_withoutDynamicTable]
    exact Nat.zero_le 0
  inboundTable := by
    show Hpack.dynamicSize #[] ≤ _
    rw [Hpack.dynamicSize_empty]
    exact Nat.zero_le _

/-! ### Membership lemmas for the stream containers -/

private theorem mem_removeStream {streams : Array StreamState} {streamId : Nat}
    {s : StreamState} (h : s ∈ removeStream streams streamId) : s ∈ streams :=
  (Array.mem_filter.mp h).1

private theorem findStream?_streamId {streams : Array StreamState} {streamId : Nat}
    {s : StreamState} (h : findStream? streams streamId = some s) :
    s ∈ streams ∧ s.streamId = streamId := by
  unfold findStream? at h
  refine ⟨Array.mem_of_find?_eq_some h, ?_⟩
  have := Array.find?_eq_some_iff_getElem.mp h
  exact eq_of_beq this.1

/-- Appending a frame to an existing stream leaves every other stream alone and
replaces that one by the same record with the frame pushed. -/
private theorem mem_appendStreamFrame_of_found {streams : Array StreamState} {frame : Frame}
    {old : StreamState} (hfind : findStream? streams frame.header.streamId = some old)
    {s : StreamState} (h : s ∈ appendStreamFrame streams frame) :
    s ∈ streams ∨ s = { old with frames := old.frames.push frame } := by
  unfold appendStreamFrame at h
  rw [hfind] at h
  cases Array.mem_push.mp h with
  | inl hmem => exact Or.inl (mem_removeStream hmem)
  | inr heq => exact Or.inr heq

/-- Appending a frame for a stream id that is not buffered yet creates exactly
that one new stream. -/
private theorem mem_appendStreamFrame_of_new {streams : Array StreamState} {frame : Frame}
    (hfind : findStream? streams frame.header.streamId = none)
    {s : StreamState} (h : s ∈ appendStreamFrame streams frame) :
    s ∈ streams ∨ s = { streamId := frame.header.streamId, frames := #[frame] } := by
  unfold appendStreamFrame at h
  rw [hfind] at h
  cases Array.mem_push.mp h with
  | inl hmem => exact Or.inl (mem_removeStream hmem)
  | inr heq => exact Or.inr heq

private theorem mem_replaceStream {streams : Array StreamState} {stream : StreamState}
    {s : StreamState} (h : s ∈ replaceStream streams stream) :
    s ∈ streams ∨ s = stream := by
  unfold replaceStream at h
  cases Array.mem_push.mp h with
  | inl hmem => exact Or.inl (mem_removeStream hmem)
  | inr heq => exact Or.inr heq

private theorem mem_removeOutboundStreamWindow {windows : Array OutboundStreamWindow}
    {streamId : Nat} {w : OutboundStreamWindow}
    (h : w ∈ removeOutboundStreamWindow windows streamId) : w ∈ windows :=
  (Array.mem_filter.mp h).1

private theorem mem_setOutboundStreamWindow {state : State} {streamId : Nat} {window : Int}
    {w : OutboundStreamWindow}
    (h : w ∈ (setOutboundStreamWindow state streamId window).outboundStreamWindows) :
    w ∈ state.outboundStreamWindows ∨ w.window = window := by
  simp only [setOutboundStreamWindow] at h
  cases Array.mem_push.mp h with
  | inl hmem => exact Or.inl (mem_removeOutboundStreamWindow hmem)
  | inr heq => exact Or.inr (by rw [heq])

/-- No stream is buffered with an open header block. -/
private theorem streamHeaderPending_of_pendingHeaderStream?_none
    {streams : Array StreamState} (h : pendingHeaderStream? streams = none)
    {s : StreamState} (hs : s ∈ streams) : streamHeaderPending s = false := by
  unfold pendingHeaderStream? at h
  have hnone := Array.findSome?_eq_none_iff.mp h s hs
  cases hp : streamHeaderPending s with
  | false => rfl
  | true =>
      rw [hp] at hnone
      simp at hnone

/-! ### Decomposing the invariant

Most pure steps touch only the inbound bookkeeping.  `SameOutbound` records
that a step left every field `WellFormed` constrains outside the stream table
alone, which turns preservation for those steps into one lemma. -/

/-- The step left the outbound flow-control bookkeeping and both HPACK dynamic
tables at or below where they were: the initial window and the tables are
unchanged, the connection window did not grow, and no stream window was
invented. -/
private def SameOutbound (state' state : State) : Prop :=
  state'.outboundInitialStreamWindow = state.outboundInitialStreamWindow
    ∧ state'.outboundConnectionWindow ≤ state.outboundConnectionWindow
    ∧ (∀ w ∈ state'.outboundStreamWindows, w ∈ state.outboundStreamWindows)
    ∧ state'.outboundHpack = state.outboundHpack
    ∧ state'.hpack = state.hpack

private theorem SameOutbound.refl (state : State) : SameOutbound state state :=
  ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem SameOutbound.trans {a b c : State} (hab : SameOutbound a b)
    (hbc : SameOutbound b c) : SameOutbound a c :=
  ⟨hab.1.trans hbc.1, Nat.le_trans hab.2.1 hbc.2.1,
    fun w hw => hbc.2.2.1 w (hab.2.2.1 w hw),
    hab.2.2.2.1.trans hbc.2.2.2.1, hab.2.2.2.2.trans hbc.2.2.2.2⟩

/-- The general preservation shape: the outbound side only shrank, and every
buffered stream of the new state satisfies the stream-id and CONTINUATION laws
against the old claimed id. -/
private theorem WellFormed.ofStreams {state state' : State} (h : WellFormed state)
    (hsame : SameOutbound state' state)
    (hlast : state'.lastClientStreamId = state.lastClientStreamId)
    (hstreams : ∀ s ∈ state'.streams,
      (isClientStreamId s.streamId = true ∧ s.streamId ≤ state.lastClientStreamId)
        ∧ (streamHeaderPending s = true → s.streamId = state.lastClientStreamId)) :
    WellFormed state' where
  streamIds := by
    intro s hs
    obtain ⟨⟨hid, hle⟩, -⟩ := hstreams s hs
    exact ⟨hid, by rw [hlast]; exact hle⟩
  pendingHeaders := by
    intro s hs hp
    rw [hlast]
    exact (hstreams s hs).2 hp
  outboundInitial := by rw [hsame.1]; exact h.outboundInitial
  outboundConnection := Nat.le_trans hsame.2.1 h.outboundConnection
  outboundStreams := fun w hw => h.outboundStreams w (hsame.2.2.1 w hw)
  outboundTable := by rw [hsame.2.2.2.1]; exact h.outboundTable
  inboundTable := by rw [hsame.2.2.2.2]; exact h.inboundTable

/-- Preservation for any step that leaves the outbound side alone and never
invents a buffered stream or lowers the claimed id. -/
private theorem WellFormed.ofSame {state state' : State} (h : WellFormed state)
    (hsame : SameOutbound state' state)
    (hsub : ∀ s ∈ state'.streams, s ∈ state.streams)
    (hlast : state'.lastClientStreamId = state.lastClientStreamId) :
    WellFormed state' :=
  h.ofStreams hsame hlast fun s hs =>
    ⟨h.streamIds s (hsub s hs), h.pendingHeaders s (hsub s hs)⟩

/-- Preservation for a step that only rewrites fields the invariant ignores. -/
private theorem WellFormed.ofFields {state state' : State} (h : WellFormed state)
    (hsame : SameOutbound state' state)
    (hstreams : state'.streams = state.streams)
    (hlast : state'.lastClientStreamId = state.lastClientStreamId) :
    WellFormed state' :=
  h.ofSame hsame (fun _ hs => hstreams ▸ hs) hlast

/-! ### Outbound flow-control bounds -/

private theorem outboundStreamWindow_le {state : State} (h : WellFormed state) (streamId : Nat) :
    outboundStreamWindow state streamId ≤ (maxStreamId : Int) := by
  unfold outboundStreamWindow
  split
  next w hw => exact h.outboundStreams w (Array.mem_of_find?_eq_some hw)
  next => exact Int.ofNat_le.mpr h.outboundInitial

private theorem cleanupOutboundIfEndStream_same (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).outboundInitialStreamWindow
        = state.outboundInitialStreamWindow
      ∧ (cleanupOutboundIfEndStream state frame).outboundConnectionWindow
        = state.outboundConnectionWindow
      ∧ (∀ w ∈ (cleanupOutboundIfEndStream state frame).outboundStreamWindows,
          w ∈ state.outboundStreamWindows)
      ∧ (cleanupOutboundIfEndStream state frame).outboundHpack = state.outboundHpack
      ∧ (cleanupOutboundIfEndStream state frame).hpack = state.hpack := by
  unfold cleanupOutboundIfEndStream
  split
  · exact ⟨rfl, rfl, fun w hw => mem_removeOutboundStreamWindow hw, rfl, rfl⟩
  · exact ⟨rfl, rfl, fun _ hw => hw, rfl, rfl⟩

/-- Setting one outbound stream window to a bounded value keeps the whole
table bounded. -/
private theorem setOutboundStreamWindow_bounded {state : State} {streamId : Nat} {window : Int}
    (hwin : ∀ w ∈ state.outboundStreamWindows, w.window ≤ (maxStreamId : Int))
    (hw : window ≤ (maxStreamId : Int)) :
    ∀ w ∈ (setOutboundStreamWindow state streamId window).outboundStreamWindows,
      w.window ≤ (maxStreamId : Int) := by
  intro w hmem
  rcases mem_setOutboundStreamWindow hmem with hmem' | heq
  · exact hwin w hmem'
  · rw [heq]; exact hw

private theorem outboundStreamWindow_le' {state : State}
    (hinit : state.outboundInitialStreamWindow ≤ maxStreamId)
    (hwin : ∀ w ∈ state.outboundStreamWindows, w.window ≤ (maxStreamId : Int))
    (streamId : Nat) : outboundStreamWindow state streamId ≤ (maxStreamId : Int) := by
  unfold outboundStreamWindow
  split
  next w hw => exact hwin w (Array.mem_of_find?_eq_some hw)
  next => exact Int.ofNat_le.mpr hinit

private theorem sub_le_maxStreamId {a : Int} {n : Nat} (h : a ≤ (maxStreamId : Int)) :
    a - (n : Int) ≤ (maxStreamId : Int) := by omega

/-- Flushing the outbound queue keeps every outbound window inside the 31-bit
range: it only ever debits windows. -/
private theorem flushOutbound_bounded : ∀ (state : State) (emitted : Array Frame),
    state.outboundInitialStreamWindow ≤ maxStreamId →
    state.outboundConnectionWindow ≤ maxStreamId →
    (∀ w ∈ state.outboundStreamWindows, w.window ≤ (maxStreamId : Int)) →
    (flushOutbound state emitted).1.outboundInitialStreamWindow ≤ maxStreamId
      ∧ (flushOutbound state emitted).1.outboundConnectionWindow ≤ maxStreamId
      ∧ (∀ w ∈ (flushOutbound state emitted).1.outboundStreamWindows,
          w.window ≤ (maxStreamId : Int)) := by
  intro state emitted
  fun_induction flushOutbound state emitted
  case case1 => intro hinit hconn hwin; exact ⟨hinit, hconn, hwin⟩
  case case3 => intro hinit hconn hwin; exact ⟨hinit, hconn, hwin⟩
  case case2 =>
    rename_i ih
    intro hinit hconn hwin
    refine ih ?_ ?_ ?_ <;> simp +zetaDelta only [cleanupOutboundIfEndStream] <;> split
    · exact hinit
    · exact hinit
    · exact hconn
    · exact hconn
    · intro w hmem; exact hwin w (mem_removeOutboundStreamWindow hmem)
    · exact hwin
  case case4 =>
    rename_i ih
    intro hinit hconn hwin
    have hbound := outboundStreamWindow_le' hinit hwin
    refine ih ?_ ?_ ?_ <;> simp +zetaDelta only [cleanupOutboundIfEndStream] <;> split
    · exact hinit
    · exact hinit
    · exact Nat.le_trans (Nat.sub_le _ _) hconn
    · exact Nat.le_trans (Nat.sub_le _ _) hconn
    · intro w hmem
      exact setOutboundStreamWindow_bounded hwin (sub_le_maxStreamId (hbound _)) w
        (mem_removeOutboundStreamWindow hmem)
    · exact setOutboundStreamWindow_bounded hwin (sub_le_maxStreamId (hbound _))
  case case5 =>
    intro hinit hconn hwin
    have hbound := outboundStreamWindow_le' hinit hwin
    exact ⟨hinit, Nat.le_trans (Nat.sub_le _ _) hconn,
      setOutboundStreamWindow_bounded hwin (sub_le_maxStreamId (hbound _))⟩

private theorem cleanupOutboundIfEndStream_outboundHpack (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).outboundHpack = state.outboundHpack := by
  unfold cleanupOutboundIfEndStream; split <;> rfl

private theorem cleanupOutboundIfEndStream_hpack (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).hpack = state.hpack := by
  unfold cleanupOutboundIfEndStream; split <;> rfl

private theorem flushOutbound_tables (state : State) (emitted : Array Frame) :
    (flushOutbound state emitted).1.outboundHpack = state.outboundHpack
      ∧ (flushOutbound state emitted).1.hpack = state.hpack := by
  fun_induction flushOutbound state emitted <;>
    simp_all +zetaDelta [cleanupOutboundIfEndStream_outboundHpack,
      cleanupOutboundIfEndStream_hpack, setOutboundStreamWindow]

private theorem flushOutbound_wellFormed {state : State} (h : WellFormed state)
    (emitted : Array Frame) : WellFormed (flushOutbound state emitted).1 := by
  obtain ⟨hi, hc, hw⟩ := flushOutbound_bounded state emitted h.outboundInitial
    h.outboundConnection h.outboundStreams
  obtain ⟨ho, hin⟩ := flushOutbound_tables state emitted
  obtain ⟨hs, -, hl⟩ := flushOutbound_fields state emitted
  exact {
    streamIds := by
      intro s hs'
      rw [hs] at hs'
      obtain ⟨hid, hle⟩ := h.streamIds s hs'
      exact ⟨hid, by rw [hl]; exact hle⟩
    pendingHeaders := by
      intro s hs' hp
      rw [hs] at hs'
      rw [hl]
      exact h.pendingHeaders s hs' hp
    outboundInitial := hi
    outboundConnection := hc
    outboundStreams := hw
    outboundTable := by rw [ho]; exact h.outboundTable
    inboundTable := by rw [hin]; exact h.inboundTable
  }

/-! ### Single-field updates -/

private theorem WellFormed.withOutboundConnection {state : State} (h : WellFormed state)
    {window : Nat} (hw : window ≤ maxStreamId) :
    WellFormed { state with outboundConnectionWindow := window } where
  streamIds := h.streamIds
  pendingHeaders := h.pendingHeaders
  outboundInitial := h.outboundInitial
  outboundConnection := hw
  outboundStreams := h.outboundStreams
  outboundTable := h.outboundTable
  inboundTable := h.inboundTable

private theorem WellFormed.withOutboundStreamWindow {state : State} (h : WellFormed state)
    (streamId : Nat) {window : Int} (hw : window ≤ (maxStreamId : Int)) :
    WellFormed (setOutboundStreamWindow state streamId window) where
  streamIds := h.streamIds
  pendingHeaders := h.pendingHeaders
  outboundInitial := h.outboundInitial
  outboundConnection := h.outboundConnection
  outboundStreams := setOutboundStreamWindow_bounded h.outboundStreams hw
  outboundTable := h.outboundTable
  inboundTable := h.inboundTable

private theorem WellFormed.withPendingOutbound {state : State} (h : WellFormed state)
    (frames : Array Frame) : WellFormed { state with pendingOutbound := frames } where
  streamIds := h.streamIds
  pendingHeaders := h.pendingHeaders
  outboundInitial := h.outboundInitial
  outboundConnection := h.outboundConnection
  outboundStreams := h.outboundStreams
  outboundTable := h.outboundTable
  inboundTable := h.inboundTable

/-- Appending an outbound batch and flushing it preserves the connection's
structural and 31-bit flow-control invariant. -/
theorem queueOutbound_wellFormed (state : State) (frames : Array Frame)
    (h : WellFormed state) : WellFormed (queueOutbound state frames).1 := by
  unfold queueOutbound
  exact flushOutbound_wellFormed
    (h.withPendingOutbound (state.pendingOutbound.append frames)) #[]

/-! ### SETTINGS and WINDOW_UPDATE -/

private theorem adjustOutboundWindowStep_le {old new : Nat}
    {acc acc' : Array OutboundStreamWindow} {window : OutboundStreamWindow}
    (h : adjustOutboundWindowStep old new acc window = .ok acc')
    (hacc : ∀ x ∈ acc, x.window ≤ (maxStreamId : Int)) :
    ∀ x ∈ acc', x.window ≤ (maxStreamId : Int) := by
  unfold adjustOutboundWindowStep at h
  split at h
  next => cases h
  next hle =>
    cases h
    intro x hx
    cases Array.mem_push.mp hx with
    | inl hm => exact hacc x hm
    | inr heq => rw [heq]; exact Int.not_lt.mp hle

private theorem adjustOutboundWindows_le {old new : Nat}
    {windows windows' : Array OutboundStreamWindow}
    (h : adjustOutboundWindows old new windows = .ok windows') :
    ∀ x ∈ windows', x.window ≤ (maxStreamId : Int) := by
  unfold adjustOutboundWindows at h
  rw [← Array.foldlM_toList] at h
  generalize windows.toList = l at h
  suffices hgen : ∀ (l : List OutboundStreamWindow) (acc : Array OutboundStreamWindow),
      (∀ x ∈ acc, x.window ≤ (maxStreamId : Int)) →
      l.foldlM (adjustOutboundWindowStep old new) acc = .ok windows' →
      ∀ x ∈ windows', x.window ≤ (maxStreamId : Int) from
    hgen l #[] (by intro x hx; simp at hx) h
  intro l
  induction l with
  | nil =>
      intro acc hacc hfold
      simp only [List.foldlM_nil, pure, Except.pure] at hfold
      cases hfold
      exact hacc
  | cons w rest ih =>
      intro acc hacc hfold
      simp only [List.foldlM_cons, bind, Except.bind] at hfold
      split at hfold
      next => cases hfold
      next mid hmid => exact ih mid (adjustOutboundWindowStep_le hmid hacc) hfold

private theorem applyInitialWindowSize_wellFormed {state state' : State} {value : Nat}
    (h : WellFormed state) (heq : applyInitialWindowSize state value = .ok state') :
    WellFormed state' := by
  unfold applyInitialWindowSize at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next hle =>
    split at heq
    next => cases heq
    next windows hadj =>
      cases heq
      exact {
        streamIds := h.streamIds
        pendingHeaders := h.pendingHeaders
        outboundInitial := Nat.not_lt.mp hle
        outboundConnection := h.outboundConnection
        outboundStreams := adjustOutboundWindows_le hadj
        outboundTable := h.outboundTable
        inboundTable := h.inboundTable
      }

private theorem applyMaxFrameSize_wellFormed {state state' : State} {value : Nat}
    (h : WellFormed state) (heq : applyMaxFrameSize state value = .ok state') :
    WellFormed state' := by
  unfold applyMaxFrameSize at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    cases heq
    exact h.ofSame (SameOutbound.refl state) (fun _ hs => hs) rfl

private theorem applyPeerSetting_wellFormed {state state' : State} {setting : Setting}
    (h : WellFormed state) (heq : applyPeerSetting state setting = .ok state') :
    WellFormed state' := by
  unfold applyPeerSetting at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next =>
      cases heq
      exact {
        streamIds := h.streamIds
        pendingHeaders := h.pendingHeaders
        outboundInitial := h.outboundInitial
        outboundConnection := h.outboundConnection
        outboundStreams := h.outboundStreams
        outboundTable := by
          rw [Hpack.maxSize_setMaxAllowedSizeWithoutDynamicTable]
          exact Hpack.dynamicSize_setMaxAllowedSizeWithoutDynamicTable
            state.outboundHpack setting.value
        inboundTable := h.inboundTable
      }
  next =>
      split at heq
      next => cases heq; exact h.ofSame (SameOutbound.refl state) (fun _ hs => hs) rfl
      next => cases heq
  next => exact applyInitialWindowSize_wellFormed h heq
  next => exact applyMaxFrameSize_wellFormed h heq
  next => cases heq; exact h.ofSame (SameOutbound.refl state) (fun _ hs => hs) rfl
  next => cases heq; exact h.ofSame (SameOutbound.refl state) (fun _ hs => hs) rfl
  next => cases heq; exact h.ofSame (SameOutbound.refl state) (fun _ hs => hs) rfl

private theorem applyPeerSettings_wellFormed {settings : Array Setting} {state state' : State}
    (h : WellFormed state) (heq : applyPeerSettings state settings = .ok state') :
    WellFormed state' := by
  unfold applyPeerSettings at heq
  rw [← Array.foldlM_toList] at heq
  generalize settings.toList = l at heq
  induction l generalizing state with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure] at heq
      cases heq
      exact h
  | cons setting rest ih =>
      simp only [List.foldlM_cons, bind, Except.bind] at heq
      split at heq
      next => cases heq
      next mid hmid => exact ih (applyPeerSetting_wellFormed h hmid) heq

private theorem processSettings_wellFormed {state : State} {frame : Frame}
    {res : State × Array Frame} (h : WellFormed state)
    (heq : processSettings state frame = .ok res) : WellFormed res.1 := by
  unfold processSettings at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next =>
      split at heq
      next => cases heq
      next => cases heq; exact h
    next =>
      split at heq
      next => cases heq
      next s1 happ =>
        split at heq
        next => cases heq
        next =>
          cases heq
          have h1 := applyPeerSettings_wellFormed h happ
          have h2 : WellFormed { s1 with clientSettingsReceived := true } :=
            h1.ofSame (SameOutbound.refl s1) (fun _ hs => hs) rfl
          exact flushOutbound_wellFormed h2 #[]

private theorem applyWindowUpdate_wellFormed {state state' : State} {frame : Frame}
    (h : WellFormed state) (heq : applyWindowUpdate state frame = .ok state') :
    WellFormed state' := by
  unfold applyWindowUpdate at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next increment hdec =>
    split at heq
    next =>
      unfold addOutboundConnectionWindow at heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      next => cases heq
      next hv =>
        cases heq
        split at hv
        next => cases hv
        next hle => cases hv; exact h.withOutboundConnection (Nat.not_lt.mp hle)
    next =>
      unfold addOutboundStreamWindow at heq
      simp only [bind, Except.bind, pure, Except.pure] at heq
      split at heq
      next => cases heq
      next hv =>
        cases heq
        split at hv
        next => cases hv
        next hle =>
          cases hv
          exact h.withOutboundStreamWindow frame.header.streamId (Int.not_lt.mp hle)

private theorem processWindowUpdate_wellFormed {state : State} {frame : Frame}
    {res : State × Array Frame} (h : WellFormed state)
    (heq : processWindowUpdate state frame = .ok res) : WellFormed res.1 := by
  unfold processWindowUpdate at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next s1 hupd =>
        cases heq
        exact flushOutbound_wellFormed (applyWindowUpdate_wellFormed h hupd) #[]
  next =>
    split at heq
    next => cases heq
    next s1 hupd =>
      cases heq
      exact flushOutbound_wellFormed (applyWindowUpdate_wellFormed h hupd) #[]

/-! ### PING, GOAWAY, PRIORITY, RST_STREAM -/

private theorem processPing_wellFormed {state : State} {frame : Frame}
    {res : State × Array Frame} (h : WellFormed state)
    (heq : processPing state frame = .ok res) : WellFormed res.1 := by
  unfold processPing at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next =>
      cases heq
      split
      · split
        · exact h.ofFields (SameOutbound.refl _) rfl rfl
        · exact h
      · exact h
    next =>
      split at heq
      next => cases heq
      next => cases heq; exact h

private theorem processGoAway_wellFormed {state : State} {frame : Frame}
    {res : State × Array Frame} (h : WellFormed state)
    (heq : processGoAway state frame = .ok res) : WellFormed res.1 := by
  unfold processGoAway at heq
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst, pure,
    Except.pure] at heq
  split at heq
  next => cases heq
  next => cases heq; exact h

private theorem processPriority_wellFormed {state : State} {frame : Frame}
    {res : State × Array Frame} (h : WellFormed state)
    (heq : processPriority state frame = .ok res) : WellFormed res.1 := by
  unfold processPriority at heq
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst, pure,
    Except.pure] at heq
  split at heq
  next => cases heq
  next => cases heq; exact h

private theorem removeInboundStreamState_same (state : State) (streamId : Nat) :
    SameOutbound (removeInboundStreamState state streamId) state :=
  ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem removeOutboundStreamState_same (state : State) (streamId : Nat) :
    SameOutbound (removeOutboundStreamState state streamId) state :=
  ⟨rfl, Nat.le_refl _, fun _ hw => mem_removeOutboundStreamWindow hw, rfl, rfl⟩

private theorem ignoreInboundStreamBody_same (state : State) (streamId : Nat) :
    SameOutbound (ignoreInboundStreamBody state streamId) state :=
  ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem drainResetInboundStreamBody_same (state : State) (streamId : Nat) :
    SameOutbound (drainResetInboundStreamBody state streamId) state :=
  ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem processRstStreamShared_wellFormed {state : State} {frame : Frame}
    {res : State × SharedFrameResult} (h : WellFormed state)
    (heq : processRstStreamShared state frame = .ok res) : WellFormed res.1 := by
  obtain ⟨hsub, -, hlast, -⟩ := processRstStreamShared_ok heq
  refine h.ofSame ?_ hsub hlast
  unfold processRstStreamShared at heq
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst, pure,
    Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next =>
      cases heq
      exact SameOutbound.trans (removeOutboundStreamState_same _ _)
        (removeInboundStreamState_same _ _)

/-! ### DATA -/

private theorem consumeInboundDataWindow_same {state state' : State} {frame : Frame}
    (heq : consumeInboundDataWindow state frame = .ok state') : SameOutbound state' state := by
  unfold consumeInboundDataWindow at heq
  simp only [] at heq
  split at heq
  next => cases heq; exact SameOutbound.refl _
  next =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next => cases heq; exact ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem replenishInboundDataWindow_same (state : State) (frame : Frame) :
    SameOutbound (replenishInboundDataWindow state frame) state := by
  unfold replenishInboundDataWindow
  simp only []
  split
  · exact SameOutbound.refl _
  · exact ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem replenishInboundConnectionWindow_fields (state : State) (size : Nat) :
    (replenishInboundConnectionWindow state size).streams = state.streams
      ∧ (replenishInboundConnectionWindow state size).lastClientStreamId
          = state.lastClientStreamId := by
  unfold replenishInboundConnectionWindow
  split <;> exact ⟨rfl, rfl⟩

private theorem replenishInboundStreamWindowBy_fields (state : State) (streamId size : Nat) :
    (replenishInboundStreamWindowBy state streamId size).streams = state.streams
      ∧ (replenishInboundStreamWindowBy state streamId size).lastClientStreamId
          = state.lastClientStreamId := by
  unfold replenishInboundStreamWindowBy
  split <;> exact ⟨rfl, rfl⟩

private theorem replenishInboundConnectionWindow_same (state : State) (size : Nat) :
    SameOutbound (replenishInboundConnectionWindow state size) state := by
  unfold replenishInboundConnectionWindow
  split
  · exact SameOutbound.refl _
  · exact ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem replenishInboundStreamWindowBy_same (state : State) (streamId size : Nat) :
    SameOutbound (replenishInboundStreamWindowBy state streamId size) state := by
  unfold replenishInboundStreamWindowBy
  split
  · exact SameOutbound.refl _
  · exact ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩

private theorem processIgnoredInboundData_wellFormed {state state' : State} {frame : Frame}
    {updates : Array Frame} (h : WellFormed state)
    (heq : processIgnoredInboundData state frame = .ok (state', updates)) :
    WellFormed state' := by
  obtain ⟨hstreams, hlast, -⟩ := processIgnoredInboundData_ok heq
  refine h.ofFields ?_ hstreams hlast
  unfold processIgnoredInboundData at heq
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst,
    pure, Except.pure] at heq
  split at heq
  next => cases heq
  next s1 hcons =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next =>
        split at heq
        next => cases heq
        next =>
          cases heq
          have hbase := SameOutbound.trans (replenishInboundDataWindow_same s1 frame)
            (consumeInboundDataWindow_same hcons)
          split
          · exact SameOutbound.trans (removeInboundStreamState_same _ _) hbase
          · exact hbase

private theorem processResetInboundData_same {state state' : State} {frame : Frame}
    {updates : Array Frame}
    (heq : processResetInboundData state frame = .ok (state', updates)) :
    SameOutbound state' state := by
  rcases processResetInboundData_state heq with rfl | ⟨streamId, rfl⟩
  · exact SameOutbound.refl _
  · exact removeInboundStreamState_same _ streamId

private theorem processResetInboundData_wellFormed {state state' : State} {frame : Frame}
    {updates : Array Frame} (h : WellFormed state)
    (heq : processResetInboundData state frame = .ok (state', updates)) :
    WellFormed state' := by
  obtain ⟨hstreams, hlast, -⟩ := processResetInboundData_ok heq
  exact h.ofFields (processResetInboundData_same heq) hstreams hlast

private theorem processDrainingInboundData_wellFormed {state state' : State}
    {frame : Frame} {updates : Array Frame} (h : WellFormed state)
    (heq : processDrainingInboundData state frame = .ok (state', updates)) :
    WellFormed state' := by
  unfold processDrainingInboundData at heq
  split at heq
  · exact processResetInboundData_wellFormed h heq
  · exact processIgnoredInboundData_wellFormed h heq

private theorem stripPadding_streamId {frame frame' : Frame} {frameName : String}
    (heq : stripPadding frame frameName = .ok frame') :
    frame'.header.streamId = frame.header.streamId := by
  unfold stripPadding at heq
  simp only [] at heq
  split at heq
  next => cases heq; rfl
  next =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next => cases heq; rfl

private theorem streamHeaderPending_push {stream : StreamState} (frame : Frame)
    (hcomplete : streamHeaderComplete stream = true) :
    streamHeaderPending { stream with frames := stream.frames.push frame } = false := by
  unfold streamHeaderComplete at hcomplete
  unfold streamHeaderPending
  split at hcomplete
  next headersFrame hfirst =>
    have hpos : 0 < stream.frames.size := (Array.getElem?_eq_some_iff.mp hfirst).1
    have hpush : (stream.frames.push frame)[0]? = some headersFrame := by
      rw [Array.getElem?_push_lt hpos]
      rw [(Array.getElem?_eq_some_iff.mp hfirst).2]
    show (match (stream.frames.push frame)[0]? with
      | some f => f.header.frameType == FrameType.headers && !headerComplete f
      | none => false) = false
    rw [hpush]
    simp [hcomplete]
  next => exact absurd hcomplete (by simp)

/-- The unary DATA path appends to a stream that is already past END_HEADERS,
so the stream-id and CONTINUATION laws survive. -/
private theorem appendStreamFrame_wellFormed {state : State} (h : WellFormed state)
    {frame appended : Frame} {old : StreamState}
    (hfind : findStream? state.streams frame.header.streamId = some old)
    (hcomplete : streamHeaderComplete old = true)
    (hid : appended.header.streamId = frame.header.streamId) :
    ∀ s ∈ appendStreamFrame state.streams appended,
      (isClientStreamId s.streamId = true ∧ s.streamId ≤ state.lastClientStreamId)
        ∧ (streamHeaderPending s = true → s.streamId = state.lastClientStreamId) := by
  have hfind' : findStream? state.streams appended.header.streamId = some old := by
    rw [hid]; exact hfind
  intro s hs
  rcases mem_appendStreamFrame_of_found hfind' hs with hmem | heq
  · exact ⟨h.streamIds s hmem, h.pendingHeaders s hmem⟩
  · obtain ⟨hold, holdId⟩ := findStream?_streamId hfind
    subst heq
    refine ⟨?_, ?_⟩
    · exact h.streamIds old hold
    · intro hp
      rw [streamHeaderPending_push appended hcomplete] at hp
      exact absurd hp (by simp)

private theorem detachStreamForDispatch_wellFormed {state state' : State} {streamId : Nat}
    {detached : DetachedDispatch} (h : WellFormed state)
    (heq : detachStreamForDispatch state streamId = .ok (state', detached)) :
    WellFormed state' := by
  unfold detachStreamForDispatch at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next =>
      cases heq
      refine h.ofSame ⟨rfl, Nat.le_refl _, fun _ hw => hw, rfl, rfl⟩ ?_ rfl
      intro s hs
      exact mem_removeStream hs

/-- A streaming-request DATA step preserves well-formedness. -/
private theorem processActiveRequestData_wellFormed {registry : Registry} {state : State}
    {frame : Frame} {active : ActiveRequestStream} {res : State × SharedFrameResult}
    (h : WellFormed state)
    (heq : processActiveRequestData registry state frame active = .ok res) :
    WellFormed res.1 := by
  unfold processActiveRequestData at heq
  split at heq
  next => cases heq
  next consumed hcons =>
    split at heq
    next => cases heq
    next stripped hstrip =>
      split at heq
      next => cases heq
      next =>
        split at heq
        next => cases heq
        next normalized hnorm =>
          have hcredited : WellFormed
              (replenishInboundStreamWindowBy
                (replenishInboundConnectionWindow consumed frame.payload.size)
                stripped.header.streamId (frame.payload.size - stripped.payload.size)) :=
            h.ofFields
              (SameOutbound.trans (replenishInboundStreamWindowBy_same _ _ _)
                (SameOutbound.trans (replenishInboundConnectionWindow_same _ _)
                  (consumeInboundDataWindow_same hcons)))
              ((replenishInboundStreamWindowBy_fields _ _ _).1.trans
                ((replenishInboundConnectionWindow_fields _ _).1.trans
                  (consumeInboundDataWindow_ok hcons).1))
              ((replenishInboundStreamWindowBy_fields _ _ _).2.trans
                ((replenishInboundConnectionWindow_fields _ _).2.trans
                  (consumeInboundDataWindow_ok hcons).2.2.2))
          split at heq
          next =>
            cases heq
            simp only []
            split
            · exact hcredited.ofSame (removeInboundStreamState_same _ _)
                (fun s hs => mem_removeStream hs) rfl
            · exact hcredited.ofSame (SameOutbound.refl _) (fun _ hs => hs) rfl
          next =>
            cases heq
            exact hcredited.ofSame (removeInboundStreamState_same _ _)
              (fun s hs => mem_removeStream hs) rfl

/-- A unary-request DATA step preserves well-formedness: the frame is appended
to a stream that is already past END_HEADERS, so no header block reopens. -/
private theorem processUnaryRequestData_wellFormed {state : State} {frame : Frame}
    {res : State × SharedFrameResult} (h : WellFormed state)
    (heq : processUnaryRequestData state frame = .ok res) : WellFormed res.1 := by
  unfold processUnaryRequestData at heq
  split at heq
  next => cases heq
  next stream hfind =>
    split at heq
    next => cases heq
    next hnot =>
      have hcomplete : streamHeaderComplete stream = true := by
        simpa using hnot
      split at heq
      next => cases heq
      next consumed hcons =>
        split at heq
        next => cases heq
        next =>
          split at heq
          next => cases heq
          next stripped hstrip =>
            have hbuffered : WellFormed {
                replenishInboundDataWindow consumed frame with
                streams := appendStreamFrame
                  (replenishInboundDataWindow consumed frame).streams stripped } := by
              obtain ⟨hs, -, -, hl⟩ := consumeInboundDataWindow_ok hcons
              obtain ⟨hs2, -, -, hl2⟩ := replenishInboundDataWindow_fields consumed frame
              refine h.ofStreams
                (SameOutbound.trans (replenishInboundDataWindow_same consumed frame)
                  (consumeInboundDataWindow_same hcons))
                (hl2.trans hl) ?_
              intro s hmem
              replace hmem : s ∈ appendStreamFrame
                (replenishInboundDataWindow consumed frame).streams stripped := hmem
              rw [hs2.trans hs] at hmem
              exact appendStreamFrame_wellFormed h hfind hcomplete
                (stripPadding_streamId hstrip) s hmem
            simp only [] at heq
            split at heq
            next =>
              split at heq
              next => cases heq
              next detachedState detached hdet =>
                cases heq
                exact detachStreamForDispatch_wellFormed hbuffered hdet
            next => cases heq; exact hbuffered

/-- Resetting a closed stream preserves well-formedness: it only drops the
stream's bookkeeping and drains the frame, so no buffered stream and no
outbound window is invented. -/
private theorem resetClosedStreamData_wellFormed {state : State} {frame : Frame}
    {res : State × SharedFrameResult} (h : WellFormed state)
    (heq : resetClosedStreamData state frame = .ok res) : WellFormed res.1 := by
  unfold resetClosedStreamData at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next pair hproc =>
      obtain ⟨drained, updates⟩ := pair
      cases heq
      refine processResetInboundData_wellFormed ?_ hproc
      refine h.ofSame ?_ ?_ rfl
      · exact SameOutbound.trans
          (drainResetInboundStreamBody_same _ _) (removeOutboundStreamState_same _ _)
      · intro s hs
        have hs' : s ∈ removeStream (removeOutboundStreamState state frame.header.streamId).streams
            frame.header.streamId := hs
        exact (Array.mem_filter.mp hs').1

/-- Every pure DATA step preserves well-formedness. -/
private theorem processDataShared_wellFormed {registry : Registry} {state : State}
    {frame : Frame} {res : State × SharedFrameResult} (h : WellFormed state)
    (heq : processDataShared registry state frame = .ok res) : WellFormed res.1 := by
  unfold processDataShared at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next =>
      split at heq
      next => cases heq
      next drained updates hproc =>
        cases heq
        exact processDrainingInboundData_wellFormed h hproc
    next =>
      split at heq
      next => exact processActiveRequestData_wellFormed h heq
      next =>
        split at heq
        next => exact processUnaryRequestData_wellFormed h heq
        next =>
          split at heq
          next => exact resetClosedStreamData_wellFormed h heq
          next => exact processUnaryRequestData_wellFormed h heq

/-- Every pure non-header frame step preserves well-formedness. -/
theorem processNonHeaderFrameShared_wellFormed {registry : Registry} {state : State}
    {frame : Frame} {res : State × SharedFrameResult} (h : WellFormed state)
    (heq : processNonHeaderFrameShared registry state frame = .ok res) :
    WellFormed res.1 := by
  unfold processNonHeaderFrameShared at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next =>
    split at heq
    next => cases heq
    next pair hset => obtain ⟨s1, emitted⟩ := pair; cases heq; exact processSettings_wellFormed h hset
  next => exact processDataShared_wellFormed h heq
  next => exact processRstStreamShared_wellFormed h heq
  next =>
    split at heq
    next => cases heq
    next pair hupd =>
      obtain ⟨s1, emitted⟩ := pair; cases heq; exact processWindowUpdate_wellFormed h hupd
  next =>
    split at heq
    next => cases heq
    next pair hping =>
      obtain ⟨s1, emitted⟩ := pair; cases heq; exact processPing_wellFormed h hping
  next =>
    split at heq
    next => cases heq
    next pair hprio =>
      obtain ⟨s1, emitted⟩ := pair; cases heq; exact processPriority_wellFormed h hprio
  next =>
    split at heq
    next => cases heq
    next pair hgo =>
      obtain ⟨s1, emitted⟩ := pair; cases heq; exact processGoAway_wellFormed h hgo
  next => cases heq
  next => cases heq; exact h
  next => cases heq
  next => cases heq

/-! ### HEADERS and CONTINUATION -/

private theorem requireClientStreamId_ok {streamId : Nat} {frameName : String} {u : Unit}
    (h : requireClientStreamId streamId frameName = .ok u) :
    isClientStreamId streamId = true := by
  unfold requireClientStreamId at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next hc => simpa using hc

private theorem requireNewClientStreamId_ok {state : State} {streamId : Nat} {u : Unit}
    (h : requireNewClientStreamId state streamId = .ok u) :
    isClientStreamId streamId = true ∧ state.lastClientStreamId < streamId := by
  unfold requireNewClientStreamId at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next _u hreq =>
    split at h
    next => cases h
    next hcond => exact ⟨requireClientStreamId_ok hreq, Nat.lt_of_not_le hcond⟩

/-- A HEADERS frame is only accepted with a stream id strictly above every id
the connection has already claimed. -/
private theorem prepareHeadersShared_gt_lastClientStreamId {state : State} {frame : Frame}
    {res : State × Option Frame} (heq : prepareHeadersShared state frame = .ok res) :
    state.lastClientStreamId < frame.header.streamId := by
  unfold prepareHeadersShared at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next _u hnew => exact (requireNewClientStreamId_ok hnew).2

/-- Closed streams stay closed.  Every id the connection has claimed is at or
below `lastClientStreamId`, and a HEADERS frame is only accepted strictly
above it, so a stream that was reset, drained or dispatched away can never be
reopened on the same connection. -/
theorem prepareHeadersShared_no_reopen {state : State} {frame : Frame}
    {res : State × Option Frame} (heq : prepareHeadersShared state frame = .ok res)
    {claimed : Nat} (hclaimed : claimed ≤ state.lastClientStreamId) :
    frame.header.streamId ≠ claimed := by
  intro hcontra
  have := prepareHeadersShared_gt_lastClientStreamId heq
  omega

/-- `SETTINGS_MAX_CONCURRENT_STREAMS` bounds what can be served while treating
an excess stream as a stream error: a HEADERS frame that opens a stream either
arrives with the number of active inbound streams strictly below the advertised
limit, or the stream it opens is marked for RST_STREAM(REFUSED_STREAM).

RFC 9113 §5.1.2 prescribes the stream error; the stream is opened only so its
field block reaches the HPACK decoder, which §4.3 requires of every field block
whether or not the stream survives.  `authorizeRequestHeadersForStream` resets
a marked stream as soon as the block is decoded, so a marked stream never
reaches a handler. -/
theorem prepareHeadersShared_concurrency {state state' : State} {frame : Frame}
    {limit : Nat} (hlimit : state.inboundMaxConcurrentStreams = some limit)
    (heq : prepareHeadersShared state frame = .ok (state', none)) :
    activeInboundStreamCount state < limit
      ∨ containsStreamId state'.refusedInboundStreams frame.header.streamId = true := by
  unfold prepareHeadersShared at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next =>
        split at heq
        next => cases heq
        next reject hreject =>
          split at heq
          next => cases heq
          next =>
            split at heq
            next hrefuse =>
              cases heq
              exact Or.inr (containsStreamId_pushUniqueStreamId _ _)
            next hrefuse =>
              cases heq
              refine Or.inl ?_
              by_cases hlt : limit ≤ activeInboundStreamCount state
              · exact absurd (by unfold inboundStreamCapacityRefusal?; simp [hlimit, hlt]) hrefuse
              · omega

/-- The pure bookkeeping of a HEADERS frame preserves well-formedness: the new
stream carries the id it just claimed, and the CONTINUATION guard rules out a
second open header block. -/
theorem prepareHeadersShared_wellFormed {state : State} {frame : Frame}
    {res : State × Option Frame} (h : WellFormed state)
    (hpending : pendingHeaderStream? state.streams = none)
    (heq : prepareHeadersShared state frame = .ok res) : WellFormed res.1 := by
  unfold prepareHeadersShared at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next hnotfound =>
      have hfindnone : findStream? state.streams frame.header.streamId = none := by
        cases hcase : findStream? state.streams frame.header.streamId with
        | none => rfl
        | some s => exact absurd (by rw [hcase]; rfl) hnotfound
      split at heq
      next => cases heq
      next _u hnew =>
        obtain ⟨hclient, hlt⟩ := requireNewClientStreamId_ok hnew
        split at heq
        next => cases heq
        next reject hreject =>
          split at heq
          next => cases heq; exact h
          next =>
            -- Whether or not the stream is marked for refusal, the stream table
            -- and every field `WellFormed` constrains take the same shape.
            split at heq <;>
              (cases heq
               exact {
                streamIds := by
                  intro s hs
                  rcases mem_appendStreamFrame_of_new hfindnone hs with hmem | hnew'
                  · obtain ⟨hid, hle⟩ := h.streamIds s hmem
                    exact ⟨hid, Nat.le_of_lt (Nat.lt_of_le_of_lt hle hlt)⟩
                  · rw [hnew']; exact ⟨hclient, Nat.le_refl _⟩
                pendingHeaders := by
                  intro s hs hp
                  rcases mem_appendStreamFrame_of_new hfindnone hs with hmem | hnew'
                  · rw [streamHeaderPending_of_pendingHeaderStream?_none hpending hmem] at hp
                    exact absurd hp (by simp)
                  · rw [hnew']
                outboundInitial := h.outboundInitial
                outboundConnection := h.outboundConnection
                outboundStreams := h.outboundStreams
                outboundTable := h.outboundTable
                inboundTable := h.inboundTable
              })

/-- Merging a CONTINUATION fragment preserves well-formedness: the stream keeps
its id, and its header block was already the open one, so it is still the newest
stream. -/
theorem appendContinuationFrame_wellFormed {state : State} {frame : Frame}
    {streams' : Array StreamState} (h : WellFormed state)
    (heq : appendContinuationFrame state.streams frame = .ok streams') :
    WellFormed { state with streams := streams' } := by
  unfold appendContinuationFrame at heq
  simp only [bind, Except.bind, pure, Except.pure] at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next stream hfind =>
      split at heq
      next headersFrame hfirst =>
        split at heq
        next => cases heq
        next hty =>
          split at heq
          next => cases heq
          next hopen =>
            split at heq
            next => cases heq
            next =>
              cases heq
              obtain ⟨hmemStream, hidStream⟩ := findStream?_streamId hfind
              have hpendingStream : streamHeaderPending stream = true := by
                simp only [streamHeaderPending, hfirst, Bool.and_eq_true, Bool.not_eq_true']
                exact ⟨by simpa using hty, by simpa using hopen⟩
              have hlast : stream.streamId = state.lastClientStreamId :=
                h.pendingHeaders stream hmemStream hpendingStream
              refine h.ofStreams (SameOutbound.refl _) rfl ?_
              intro s hs
              rcases mem_replaceStream hs with hmem | hrepl
              · exact ⟨h.streamIds s hmem, h.pendingHeaders s hmem⟩
              · rw [hrepl]
                exact ⟨⟨(h.streamIds stream hmemStream).1, Nat.le_of_eq hlast⟩,
                  fun _ => hlast⟩
      next => cases heq
    next => cases heq

/-!
## Flow-control conservation

The bounds in `WellFormed` say windows stay inside the 31-bit field; these
theorems say the arithmetic is *exact*.

* `consumeInboundDataWindow_conserves` — a DATA frame debits both the
  connection and stream receive windows by exactly its payload size, and the
  `Nat` subtraction never truncates (the equation `w' + n = w` forces
  `n ≤ w`), so a window can never go negative from our own updates.
* `processUnaryRequestData_windows` — the unary path credits back exactly what
  it debited: both windows come out unchanged.
* `processActiveRequestData_windows` — the streaming path restores the
  connection window exactly and leaves the stream window short by exactly the
  post-padding payload, i.e. by the bytes whose credit is deferred.
* `decodeActiveRequestData_conserves` — those deferred bytes are accounted for
  exactly: queued credits plus still-buffered bytes grow by the frame payload,
  so credit returned on consume equals bytes consumed and the effective window
  never creeps past the advertised one.
* `takeRequestStreamCredit_conserves` — consuming a message returns exactly the
  credit that was queued for it.
* `flushOutbound_conserves` — every flow-controlled byte we put on the wire is
  debited from the outbound connection window, and nothing else is.
* `defaultStreamWindow_admits_max_message` / `inboundWindow_pos_of_incomplete` —
  deadlock freedom: a maximum-size message fits in one stream window, so an
  incomplete message always leaves a strictly positive window once the handler
  has caught up.
-/

private theorem findInboundStreamWindow?_remove (windows : Array InboundStreamWindow)
    (streamId : Nat) :
    findInboundStreamWindow? (removeInboundStreamWindow windows streamId) streamId = none := by
  unfold findInboundStreamWindow? removeInboundStreamWindow
  rw [Array.find?_eq_none]
  intro x hx
  have hne := (Array.mem_filter.mp hx).2
  simp only [bne_iff_ne, ne_eq] at hne
  simpa using hne

private theorem inboundStreamWindow_set (state : State) (streamId window : Nat) :
    inboundStreamWindow (setInboundStreamWindow state streamId window) streamId = window := by
  unfold inboundStreamWindow setInboundStreamWindow
  show (match findInboundStreamWindow?
      ((removeInboundStreamWindow state.inboundStreamWindows streamId).push
        { streamId := streamId, window := window }) streamId with
    | some w => w.window
    | none => state.inboundInitialStreamWindow) = window
  unfold findInboundStreamWindow?
  rw [Array.find?_push]
  rw [show Array.find? (fun w => w.streamId == streamId)
      (removeInboundStreamWindow state.inboundStreamWindows streamId) = none from
    findInboundStreamWindow?_remove state.inboundStreamWindows streamId]
  simp

/-- A DATA frame debits both receive windows by exactly its payload size; the
`Nat` equations also witness that neither subtraction truncated. -/
theorem consumeInboundDataWindow_conserves {state state' : State} {frame : Frame}
    (h : consumeInboundDataWindow state frame = .ok state') :
    state'.inboundConnectionWindow + frame.payload.size = state.inboundConnectionWindow
      ∧ inboundStreamWindow state' frame.header.streamId + frame.payload.size
          = inboundStreamWindow state frame.header.streamId := by
  unfold consumeInboundDataWindow at h
  simp only [] at h
  split at h
  next hzero =>
    cases h
    have hsize : frame.payload.size = 0 := by simpa using hzero
    rw [hsize]
    exact ⟨Nat.add_zero _, Nat.add_zero _⟩
  next =>
    split at h
    next => cases h
    next hconn =>
      split at h
      next => cases h
      next hstream =>
        cases h
        refine ⟨?_, ?_⟩
        · show state.inboundConnectionWindow - frame.payload.size + frame.payload.size
            = state.inboundConnectionWindow
          omega
        · rw [inboundStreamWindow_set]
          omega

private theorem replenishInboundDataWindow_restores {state state' : State} {frame : Frame}
    (h : consumeInboundDataWindow state frame = .ok state') :
    (replenishInboundDataWindow state' frame).inboundConnectionWindow
        = state.inboundConnectionWindow
      ∧ inboundStreamWindow (replenishInboundDataWindow state' frame) frame.header.streamId
          = inboundStreamWindow state frame.header.streamId := by
  obtain ⟨hconn, hstream⟩ := consumeInboundDataWindow_conserves h
  unfold replenishInboundDataWindow
  simp only []
  split
  next hzero =>
    have hsize : frame.payload.size = 0 := by simpa using hzero
    rw [hsize] at hconn hstream
    exact ⟨by omega, by omega⟩
  next =>
    refine ⟨?_, ?_⟩
    · show state'.inboundConnectionWindow + frame.payload.size = state.inboundConnectionWindow
      exact hconn
    · rw [inboundStreamWindow_set]
      exact hstream

private theorem replenishInboundConnectionWindow_window (state : State) (size : Nat) :
    (replenishInboundConnectionWindow state size).inboundConnectionWindow
      = state.inboundConnectionWindow + size := by
  unfold replenishInboundConnectionWindow
  split
  next hzero => have : size = 0 := by simpa using hzero
                omega
  next => rfl

private theorem replenishInboundStreamWindowBy_window (state : State) (streamId size : Nat) :
    inboundStreamWindow (replenishInboundStreamWindowBy state streamId size) streamId
      = inboundStreamWindow state streamId + size := by
  unfold replenishInboundStreamWindowBy
  split
  next hzero => have : size = 0 := by simpa using hzero
                omega
  next => rw [inboundStreamWindow_set]

private theorem replenishInboundStreamWindowBy_connection (state : State) (streamId size : Nat) :
    (replenishInboundStreamWindowBy state streamId size).inboundConnectionWindow
      = state.inboundConnectionWindow := by
  unfold replenishInboundStreamWindowBy
  split <;> rfl

private theorem stripPadding_size_le {frame frame' : Frame} {frameName : String}
    (h : stripPadding frame frameName = .ok frame') :
    frame'.payload.size ≤ frame.payload.size := by
  unfold stripPadding at h
  simp only [] at h
  split at h
  next => cases h; exact Nat.le_refl _
  next =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next =>
        cases h
        show (((frame.payload.extract 1 frame.payload.size).extract 0
          ((frame.payload.extract 1 frame.payload.size).size - frame.payload[0]!.toNat))).size
          ≤ frame.payload.size
        simp only [ByteArray.size_extract]
        omega

/-- The unary DATA path credits back exactly what it debited: both receive
windows come out of the step unchanged. -/
theorem processUnaryRequestData_windows {state : State} {frame : Frame}
    {res : State × SharedFrameResult}
    (heq : processUnaryRequestData state frame = .ok res) :
    res.1.inboundConnectionWindow = state.inboundConnectionWindow
      ∧ (res.2.detached = none →
          inboundStreamWindow res.1 frame.header.streamId
            = inboundStreamWindow state frame.header.streamId) := by
  unfold processUnaryRequestData at heq
  split at heq
  next => cases heq
  next =>
    split at heq
    next => cases heq
    next =>
      split at heq
      next => cases heq
      next consumed hcons =>
        obtain ⟨hconn, hstream⟩ := replenishInboundDataWindow_restores hcons
        split at heq
        next => cases heq
        next =>
          split at heq
          next => cases heq
          next stripped hstrip =>
            simp only [] at heq
            split at heq
            next =>
              split at heq
              next => cases heq
              next detachedState detached hdet =>
                cases heq
                refine ⟨?_, fun hcontra => absurd hcontra (by simp)⟩
                unfold detachStreamForDispatch at hdet
                split at hdet
                next => cases hdet
                next =>
                  split at hdet
                  next => cases hdet
                  next => cases hdet; exact hconn
            next => cases heq; exact ⟨hconn, fun _ => hstream⟩

/-- The streaming DATA path restores the connection window exactly and leaves
the stream window short by exactly the post-padding payload — the bytes whose
credit is deferred until the handler consumes the messages they carry. -/
theorem processActiveRequestData_windows {registry : Registry} {state : State}
    {frame : Frame} {active : ActiveRequestStream} {res : State × SharedFrameResult}
    (heq : processActiveRequestData registry state frame active = .ok res) :
    res.1.inboundConnectionWindow = state.inboundConnectionWindow := by
  unfold processActiveRequestData at heq
  split at heq
  next => cases heq
  next consumed hcons =>
    obtain ⟨hconn, -⟩ := consumeInboundDataWindow_conserves hcons
    split at heq
    next => cases heq
    next stripped hstrip =>
      split at heq
      next => cases heq
      next =>
        split at heq
        next => cases heq
        next normalized hnorm =>
          have hcredited : (replenishInboundStreamWindowBy
              (replenishInboundConnectionWindow consumed frame.payload.size)
              stripped.header.streamId
              (frame.payload.size - stripped.payload.size)).inboundConnectionWindow
              = state.inboundConnectionWindow := by
            rw [replenishInboundStreamWindowBy_connection,
              replenishInboundConnectionWindow_window]
            omega
          split at heq
          next =>
            cases heq
            simp only []
            split <;> exact hcredited
          next => cases heq; exact hcredited

/-! ### Credit-on-consume conservation -/

/-- Total bytes of stream-window credit queued for messages the handler has
not consumed yet. -/
def creditSum (credits : Array Nat) : Nat := credits.foldl (· + ·) 0

private theorem foldl_add_init : ∀ (l : List Nat) (init : Nat),
    l.foldl (· + ·) init = init + l.foldl (· + ·) 0 := by
  intro l
  induction l with
  | nil => intro init; simp
  | cons x rest ih =>
      intro init
      simp only [List.foldl_cons]
      rw [ih (init + x), ih (0 + x)]
      omega

private theorem creditSum_append (a b : Array Nat) :
    creditSum (a ++ b) = creditSum a + creditSum b := by
  unfold creditSum
  rw [← Array.foldl_toList, ← Array.foldl_toList, ← Array.foldl_toList,
    Array.toList_append, List.foldl_append, foldl_add_init]

private theorem creditSum_messages (messages : Array Message) :
    creditSum (messages.map (fun message => Message.prefixLength + message.data.size))
      = Message.messagesWireSize messages := by
  unfold creditSum
  rw [Message.messagesWireSize_eq_foldl, ← Array.foldl_toList, ← Array.foldl_toList,
    Array.toList_map, List.foldl_map]

/-- Nothing is lost between the wire and the deferred-credit queue: every byte
the DATA frame delivered is either queued as credit for a message the decoder
completed, or still buffered as the prefix of an incomplete one. -/
theorem decodeActiveRequestData_conserves {registry : Registry}
    {active active' : ActiveRequestStream} {frame : Frame}
    {messages : Array ByteArray} {close : Bool}
    (h : decodeActiveRequestData registry active frame = .ok (active', messages, close)) :
    creditSum active'.pendingRequestCredits + active'.decodeState.buffered.size
      = creditSum active.pendingRequestCredits + active.decodeState.buffered.size
        + frame.payload.size := by
  unfold decodeActiveRequestData at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next decoded hdecode =>
      have hcons := Message.decodeChunkWithLimit_conserves hdecode
      split at h
      next => cases h
      next =>
        split at h
        next => cases h
        next =>
          split at h
          next => cases h
          next =>
            cases h
            show creditSum (active.pendingRequestCredits ++
                decoded.messages.map
                  (fun message => Message.prefixLength + message.data.size))
              + decoded.buffered.size = _
            rw [creditSum_append, creditSum_messages]
            omega

/-- Consuming one message returns exactly the credit that was queued for it:
the stream's receive window grows by the amount the WINDOW_UPDATE carries, and
by nothing else. -/
theorem takeRequestStreamCredit_conserves (state : State) (streamId : Nat) :
    inboundStreamWindow (takeRequestStreamCredit state streamId).1 streamId
      = inboundStreamWindow state streamId + (takeRequestStreamCredit state streamId).2 := by
  unfold takeRequestStreamCredit
  split
  next => exact (Nat.add_zero _).symm
  next =>
    split
    next => exact (Nat.add_zero _).symm
    next credit hcredit => exact replenishInboundStreamWindowBy_window state streamId credit

/-- The credit handed back is one of the per-message credits the decoder
queued — never an amount we invented. -/
private theorem takeRequestStreamCredit_queued {state : State} {streamId : Nat}
    {active : ActiveRequestStream}
    (h : findActiveRequestStream? state.activeRequestStreams streamId = some active) :
    (takeRequestStreamCredit state streamId).2 = 0
      ∨ active.pendingRequestCredits[0]? = some (takeRequestStreamCredit state streamId).2 := by
  unfold takeRequestStreamCredit
  simp only [h]
  split
  next => exact Or.inl rfl
  next credit hcredit => exact Or.inr hcredit

/-! ### Outbound conservation -/

/-- Flow-controlled bytes in one frame: only DATA consumes peer credit. -/
private def frameDataPayloadBytes (frame : Frame) : Nat :=
  if frame.header.frameType == FrameType.data then frame.payload.size else 0

/-- Flow-controlled bytes in a batch of frames: only DATA is flow-controlled. -/
def dataPayloadBytes (frames : Array Frame) : Nat :=
  frames.foldl (fun total frame => total + frameDataPayloadBytes frame) 0

private theorem dataPayloadBytes_push (frames : Array Frame) (frame : Frame) :
    dataPayloadBytes (frames.push frame)
      = dataPayloadBytes frames
        + frameDataPayloadBytes frame := by
  simp only [dataPayloadBytes, Array.foldl_push]

private theorem cleanupOutboundIfEndStream_outboundConnectionWindow (state : State)
    (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).outboundConnectionWindow
      = state.outboundConnectionWindow := by
  unfold cleanupOutboundIfEndStream
  split <;> rfl

/-- Outbound conservation: every flow-controlled byte the connection puts on
the wire is debited from the outbound connection window, and nothing else is.
The `Nat` equation also witnesses that the window subtraction never truncated,
so we never send more than the peer granted. -/
theorem flushOutbound_conserves : ∀ (state : State) (emitted : Array Frame),
    (flushOutbound state emitted).1.outboundConnectionWindow
        + dataPayloadBytes (flushOutbound state emitted).2
      = state.outboundConnectionWindow + dataPayloadBytes emitted := by
  intro state emitted
  fun_induction flushOutbound state emitted
  case case1 => rfl
  case case3 => rfl
  case case2 =>
    rename_i ih
    rw [ih, cleanupOutboundIfEndStream_outboundConnectionWindow, dataPayloadBytes_push]
    clear ih
    simp_all +zetaDelta [frameDataPayloadBytes]
    try omega
  case case4 =>
    rename_i ih
    rw [ih, cleanupOutboundIfEndStream_outboundConnectionWindow, dataPayloadBytes_push]
    clear ih
    simp_all +zetaDelta [frameDataPayloadBytes, dataFrameWithPayload, setOutboundStreamWindow]
    try omega
  case case5 =>
    rw [dataPayloadBytes_push]
    simp_all +zetaDelta [frameDataPayloadBytes, dataFrameWithPayload, withoutEndStream,
      setOutboundStreamWindow]
    try omega

/-- Queue-level outbound conservation follows directly from the single flush
path: every emitted DATA byte is debited once from the connection window. -/
theorem queueOutbound_conserves (state : State) (frames : Array Frame) :
    (queueOutbound state frames).1.outboundConnectionWindow
        + dataPayloadBytes (queueOutbound state frames).2
      = state.outboundConnectionWindow := by
  unfold queueOutbound
  simpa using (flushOutbound_conserves
    { state with pendingOutbound := state.pendingOutbound.append frames } #[])

/-! ### Deadlock freedom -/

/-- The advertised stream window admits a maximum-size gRPC message whole: the
default 4 MiB payload cap plus the 5-byte length prefix still fit.  This is the
side condition the credit-on-consume scheme needs, because the stream window is
only replenished once the handler consumes a *complete* message. -/
theorem defaultStreamWindow_admits_max_message :
    Message.prefixLength + Message.defaultMaxDecompressedSize ≤ defaultStreamWindow := by
  decide

/-- Deadlock freedom.  Suppose the receive window plus the bytes still buffered
for an incomplete message account for the whole advertised window (the handler
has consumed everything available, so no credit is outstanding), and the
advertised window admits the message whole.  Then the window is strictly
positive: the peer can always send the bytes that complete the message, and the
completed message then returns its credit. -/
theorem inboundWindow_pos_of_incomplete {state : State} {streamId : Nat}
    {buffered messageWireSize : Nat}
    (hbalance : inboundStreamWindow state streamId + buffered
      = state.inboundInitialStreamWindow)
    (hfits : messageWireSize ≤ state.inboundInitialStreamWindow)
    (hincomplete : buffered < messageWireSize) :
    0 < inboundStreamWindow state streamId := by
  omega

end Connection
end Http2
end Grpc
