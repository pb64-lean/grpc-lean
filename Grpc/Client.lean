module

public import Std.Async.TCP
public import Std.Async.Timer
public import Std.Sync.CancellationToken
public import Std.Sync.Notify
public import Std.Sync.Channel

public import Http2.CancellationToken
public import Http2.Client
public import Http2.Connection
public import Http2.Tls.Session
public import Grpc.Protocol

public section

/-! # gRPC client

A gRPC-over-HTTP/2 client on `Std.Async.TCP` supporting unary, server-streaming,
client-streaming, and bidirectional RPCs, with concurrent calls multiplexed over
one connection.

Architecture: a background reader task owns the socket's receive side, decodes
frames, and demultiplexes them into per-stream `CallRecord`s guarded by the
connection mutex; a background writer task owns the send side, draining an
outbound channel, so socket writes never happen under the mutex.

The call API (`start` / `Call.send` / `Call.recv?` / `Call.closeSend` /
`Call.finish` / `Call.cancel` and the `call` / `serverStreaming` / `callRaw`
wrappers) is in the `Async` monad: when a call must wait (for send-window credit,
an inbound message, or terminal state) it awaits a `Std.Notify` signal that the
reader fires on every state change, suspending cooperatively and returning its
worker to the pool rather than parking a thread. This lets thousands of calls be
in flight concurrently (e.g. via `Async.concurrentlyAll`) on a small pool; drive
one to completion synchronously with `Async.block`. Connection setup (`connect` /
`connectTls`) stays in `IO`; `close` is cooperative `Async` like the call API.

Flow control is handled in both directions: sends wait for server window credit,
and received data is credited back at the stream level only as the application
consumes messages (the connection level is credited on arrival), bounding
unconsumed buffering per stream to one stream window.

gzip: requests advertise `grpc-accept-encoding: identity,gzip` and compressed
response messages are transparently inflated; request messages are sent
uncompressed.
-/

namespace Grpc
namespace Client

private def ofHttp2 {α} (result : Except _root_.Http2.Error α) : Except Status α :=
  match result with
  | .ok value => .ok value
  | .error error => .error (Status.ofHttp2Error error)

open Std
open Std.Net
open Std.Async

/-- Conservative default cap for one encoded request or decoded response message. -/
def defaultMaxMessageSize : Nat := Message.defaultMaxDecompressedSize

structure Config where
  address : SocketAddress := .v4 {
    addr := IPv4Addr.ofParts 127 0 0 1,
    port := 50051
  }
  authority : String := "localhost"
  scheme : String := "http"
  readSize : UInt64 := 16384
  /-- Maximum uncompressed bytes accepted by one `Call.send`. -/
  maxSendMessageSize : Nat := defaultMaxMessageSize
  /--
  Maximum bytes accepted for one response message, both on the wire and after
  decompression. The length prefix is rejected before its payload is buffered.
  The stream receive window also bounds the aggregate normalized response bytes
  retained while the application has not yet consumed them.
  -/
  maxReceiveMessageSize : Nat := defaultMaxMessageSize
  deriving Inhabited

structure CallOptions where
  metadata : _root_.Http2.Headers := _root_.Http2.Headers.empty
  /-- Raw grpc-timeout header value, e.g. "5S" or "250m". -/
  timeout : Option String := none

namespace CallOptions

/-- Set the call's deadline from a `Timeout`, rather than a raw header value. -/
def withTimeout (options : CallOptions) (timeout : Timeout) : CallOptions :=
  { options with timeout := some timeout.render }

/-- Give this call the time still left on an inbound request's deadline.

A handler serving a request with a `grpc-timeout` receives the request's
absolute deadline as `request.deadline` (or `context.deadline` for a typed
handler registered with `register*CodecWithContext`); passing it here sends the
*remaining* time as the downstream `grpc-timeout`, so the downstream server
cannot outlive the caller's own deadline.

`.error DEADLINE_EXCEEDED` when nothing is left: issuing the call would only
burn a connection on work whose result can no longer be used, and a handler
should return that status instead.  A request with no deadline propagates none,
leaving `options.timeout` untouched. -/
def propagating (options : CallOptions) (deadline? : Option Nat) :
    IO (Except Status CallOptions) := do
  match ← Deadline.remaining? deadline? with
  | .unbounded => pure (.ok options)
  | .remaining timeout => pure (.ok (options.withTimeout timeout))
  | .exceeded => pure (.error Deadline.exceededStatus)

end CallOptions

structure CallResult where
  headers : _root_.Http2.Headers := _root_.Http2.Headers.empty
  trailers : _root_.Http2.Headers := _root_.Http2.Headers.empty
  messages : Array ByteArray := #[]
  status : Status := Status.ok

/-- Per-stream client-side state, mutated by the connection reader task and
polled by call handles under the connection mutex. -/
structure CallRecord where
  streamId : Nat
  decode : Message.DecodeState := {}
  /-- Decoded (and decompressed) inbound messages awaiting `recv?`. -/
  inbound : Array ByteArray := #[]
  /-- Wire size of each inbound message; the stream WINDOW_UPDATE for a
  message is sent when `recv?` consumes it. -/
  pendingRecvCredits : Array Nat := #[]
  /-- Normalized identity-framed bytes retained by each queued response. This
  is parallel to `inbound` and lets consumption release the decoded-memory
  budget independently of the compressed wire credit. -/
  pendingRecvDecodedBytes : Array Nat := #[]
  /-- Total normalized identity-framed bytes currently retained in `inbound`. -/
  retainedDecodedBytes : Nat := 0
  headers : _root_.Http2.Headers := _root_.Http2.Headers.empty
  seenHeaders : Bool := false
  responseGzip : Bool := false
  trailers : Option _root_.Http2.Headers := none
  failure : Option Status := none

private def retainedDecodedResponseLimit (maxReceiveMessageSize : Nat) : Nat :=
  maxReceiveMessageSize + Message.prefixLength + 65536

private def clientInitialStreamWindow (config : Config) : Nat :=
  retainedDecodedResponseLimit config.maxReceiveMessageSize

private def clientSettings (config : Config) : _root_.Http2.Connection.Settings := {
  enablePush := false
  initialWindowSize := clientInitialStreamWindow config
}

structure ConnState where
  /-- Generic RFC 9113 framing, HPACK, settings, stream, and flow-control state. -/
  protocol : _root_.Http2.Connection.State
  /-- Set when the connection is unusable; new and pending calls fail with it. -/
  dead : Option Status := none
  calls : Array CallRecord := #[]
  deriving Inhabited

private structure BackgroundTasks where
  writer : Option (AsyncTask Unit) := none
  reader : Option (AsyncTask Unit) := none

/-- One FIFO item owned by the connection writer. -/
structure OutboundWrite where
  bytes : ByteArray
  private completion : Option (IO.Promise (Except IO.Error Unit)) := none

structure Connection where
  socket : TCP.Socket.Client
  config : Config
  state : Std.Mutex ConnState
  /-- Outbound frame bytes, drained by a single writer task so socket writes never
  happen while the state mutex is held (avoids stalling the reader and app calls
  behind a blocked write). Preserves frame order via FIFO with one consumer. -/
  outbound : Std.CloseableChannel OutboundWrite
  /-- Signalled by the reader on any state change (window credit, message delivery,
  terminal state, death) to wake waiters in `send`/`recv?`/`finish` without polling. -/
  wakeup : Std.Notify
  /-- Cancelled by `close` to stop the background reader task's blocked `recv?`. -/
  stopToken : Std.CancellationToken
  /-- First failure of the sole outbound writer.  The writer publishes here and
  cancels `writerFailureToken`; the reader remains the single owner that marks
  calls dead and retires the transport. -/
  writerFailure : IO.Ref (Option IO.Error)
  /-- Sticky wakeup for a plaintext or outer TLS writer failure.  Keeping this
  distinct from `stopToken` preserves the transport error as the close cause. -/
  writerFailureToken : Std.CancellationToken
  /--
  Exact background task handles. Construction publishes a `Connection` only
  after both handles have been installed; `close` awaits each up to its bounded
  drain deadline and cancels a task that cannot finish because the peer is stuck.
  -/
  private background : IO.Ref BackgroundTasks
  /-- Elects the one owner permitted to retire background tasks and the
  underlying transport. Concurrent and repeated close calls only wait. -/
  private closeClaimed : Std.Mutex Bool
  /-- Resolved exactly once after the elected close owner finishes transport
  retirement, so every competing close observes the same completion point. -/
  private closed : IO.Promise Unit
  /-- When present, the connection runs over TLS: outbound bytes are sealed and
  inbound raw bytes are decrypted through this session. `none` is plaintext. -/
  tls : Option _root_.Http2.Tls.ClientSession := none

/-- Non-blocking lifecycle diagnostic: `true` once both exact background owners
have terminated (or before either was installed).  This exposes no task handle
and is useful for asserting that transport failure did not leave a hidden reader. -/
def backgroundTasksFinished (connection : Connection) : IO Bool := do
  let background ← connection.background.get
  let writerFinished ← match background.writer with
    | none => pure true
    | some writer => IO.hasFinished writer
  let readerFinished ← match background.reader with
    | none => pure true
    | some reader => IO.hasFinished reader
  pure (writerFinished && readerFinished)

/-- Handle for one RPC on a `Connection`. -/
structure Call where
  connection : Connection
  streamId : Nat

private def ofStatus (result : Except Status α) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

/-- Enqueue raw bytes for the writer task. Non-blocking (unbounded channel); the
returned send task is ignored since ordering is guaranteed by the single writer. -/
private def enqueueBytes (connection : Connection) (bytes : ByteArray) : BaseIO Unit := do
  if bytes.isEmpty then pure () else discard <| connection.outbound.send { bytes := bytes }

private def enqueueFrames (connection : Connection)
    (frames : Array _root_.Http2.Frame) : BaseIO Unit := do
  unless frames.isEmpty do
    match ofHttp2 <| _root_.Http2.Frame.encodeBatch frames with
    | .ok bytes => enqueueBytes connection bytes
    | .error _ => pure ()

private structure OutboundTicket where
  completion : IO.Promise (Except IO.Error Unit)

/-- Enqueue bytes in FIFO order and return the exact writer completion ticket.
The synchronous channel operation only performs unbounded queue admission; the
ticket is resolved after the plaintext socket write or inner TLS record write. -/
private def enqueueBytesAcknowledged (connection : Connection) (bytes : ByteArray) :
    IO (Except Status OutboundTicket) := do
  let completion : IO.Promise (Except IO.Error Unit) ← IO.Promise.new
  if bytes.isEmpty then
    completion.resolve (.ok ())
    pure (.ok { completion := completion })
  else
    let admitted ← (Std.CloseableChannel.Sync.send connection.outbound {
      bytes := bytes,
      completion := some completion
    }).toBaseIO
    match admitted with
    | .ok () => pure (.ok { completion := completion })
    | .error _ =>
        let error := (← connection.writerFailure.get).getD
          (IO.userError "connection writer is closed")
        pure (.error (Status.ofIOError error))

private def awaitOutboundTicket (ticket : OutboundTicket) : Async (Except Status Unit) := do
  match ← Async.ofTask ticket.completion.result? with
  | some (.ok ()) => pure (.ok ())
  | some (.error error) => pure (.error (Status.ofIOError error))
  | none => pure (.error (Status.error .unavailable
      "connection writer dropped a send acknowledgement"))

/-- Wake all waiters after a state change so they re-check their predicate. -/
private def wake (connection : Connection) : BaseIO Unit :=
  connection.wakeup.notify

/-- Suspend (cooperatively, freeing the worker) until the next `wake`, tolerating a
dropped notification. Unlike `AsyncTask.block`, awaiting the task inside `Async` yields
the worker back to the pool, so thousands of calls can wait concurrently without a
thread each. -/
private def awaitWaiter (waiter : AsyncTask Unit) : Async Unit := do
  try
    Async.ofAsyncTask waiter
  catch _ =>
    pure ()

private def findCall? (calls : Array CallRecord) (streamId : Nat) : Option CallRecord :=
  calls.find? (fun call => call.streamId == streamId)

private def replaceCall (calls : Array CallRecord) (call : CallRecord) : Array CallRecord :=
  (calls.filter (fun existing => existing.streamId != call.streamId)).push call

private def removeCall (calls : Array CallRecord) (streamId : Nat) : Array CallRecord :=
  calls.filter (fun call => call.streamId != streamId)

private def peerStreamCapacityAvailable (state : ConnState) : Bool :=
  match state.protocol.peerSettings.maxConcurrentStreams with
  | none => true
  | some limit =>
      let active := state.protocol.streams.foldl (init := 0) fun count stream =>
        if state.protocol.role.isLocalStreamId stream.id && stream.phase != .closed then
          count + 1
        else
          count
      active < limit

private def failCallRecord (status : Status) (call : CallRecord) : CallRecord :=
  if call.failure.isSome || call.trailers.isSome then
    call
  else
    { call with failure := some status }

/-- Mark the connection dead (keeping the first cause) and fail every call
that has not already reached a terminal state. -/
private def failStateLocked (state : ConnState) (status : Status) : ConnState :=
  {
    state with
    dead := some (state.dead.getD status),
    calls := state.calls.map (failCallRecord status)
  }

private def failConnection (connection : Connection) (status : Status) : IO Unit := do
  connection.state.atomically do
    modify fun state => failStateLocked state status
  wake connection

private def requestMetadata (connection : Connection) (path : String)
    (options : CallOptions) : _root_.Http2.Headers :=
  let base := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" connection.config.scheme
    |>.insert ":path" path
    |>.insert ":authority" connection.config.authority
    |>.insert "te" "trailers"
    |>.insert "content-type" "application/grpc"
    |>.insert "grpc-accept-encoding" Headers.acceptedEncodings
  let base := match options.timeout with
    | none => base
    | some timeout => base.insert "grpc-timeout" timeout
  base.append options.metadata

private def responseGzipOf (metadata : _root_.Http2.Headers) : Bool :=
  metadata.get? "grpc-encoding" == some Headers.gzipEncoding

/-- Decode DATA payload into gRPC messages, recording both each message's wire
size and its normalized retained size. The cumulative decoded queue uses the
same finite bound as the advertised stream receive window, so compression can
never turn bounded peer credit into unbounded client memory. -/
private def processCallData
    (maxReceiveMessageSize : Nat) (call : CallRecord) (payload : ByteArray) :
    Except Status CallRecord := do
  let decoded ← Message.decodeChunkWithLimit (some maxReceiveMessageSize)
    { buffered := call.decode.buffered } payload
  let limit := retainedDecodedResponseLimit maxReceiveMessageSize
  let mut inbound := call.inbound
  let mut pendingRecvCredits := call.pendingRecvCredits
  let mut pendingRecvDecodedBytes := call.pendingRecvDecodedBytes
  let mut retainedDecodedBytes := call.retainedDecodedBytes
  for encoded in decoded.messages do
    let wireCredit := Message.prefixLength + encoded.data.size
    let message ← Message.decompress call.responseGzip maxReceiveMessageSize encoded
    let decodedBytes := Message.prefixLength + message.data.size
    if retainedDecodedBytes + decodedBytes > limit then
      throw (Status.resourceExhausted
        s!"gRPC response queue exceeds retained decoded-byte limit {limit}")
    inbound := inbound.push message.data
    pendingRecvCredits := pendingRecvCredits.push wireCredit
    pendingRecvDecodedBytes := pendingRecvDecodedBytes.push decodedBytes
    retainedDecodedBytes := retainedDecodedBytes + decodedBytes
  pure {
    call with
    decode := { buffered := decoded.buffered },
    inbound := inbound,
    pendingRecvCredits := pendingRecvCredits,
    pendingRecvDecodedBytes := pendingRecvDecodedBytes,
    retainedDecodedBytes := retainedDecodedBytes
  }

private structure PoppedInboundMessage where
  data : ByteArray
  wireCredit : Nat
  call : CallRecord

/-- Remove one queued response and release exactly its decoded-memory budget. -/
private def popInboundMessage? (call : CallRecord) : Option PoppedInboundMessage := do
  let data ← call.inbound[0]?
  let wireCredit := call.pendingRecvCredits[0]?.getD 0
  let decodedBytes := call.pendingRecvDecodedBytes[0]?.getD
    (Message.prefixLength + data.size)
  pure {
    data := data
    wireCredit := wireCredit
    call := {
      call with
      inbound := call.inbound.extract 1 call.inbound.size,
      pendingRecvCredits :=
        call.pendingRecvCredits.extract 1 call.pendingRecvCredits.size,
      pendingRecvDecodedBytes :=
        call.pendingRecvDecodedBytes.extract 1 call.pendingRecvDecodedBytes.size,
      retainedDecodedBytes := call.retainedDecodedBytes - decodedBytes
    }
  }

private def responseDataFailureResetCode (status : Status) : _root_.Http2.ErrorCode :=
  if status.code == .resourceExhausted then .enhanceYourCalm else .cancel

private def rstStatus (code : _root_.Http2.ErrorCode) : Status :=
  match code with
  | .cancel => Status.cancelled "stream cancelled by server"
  | .refusedStream => Status.error .unavailable "stream refused by server"
  | .enhanceYourCalm => Status.resourceExhausted "server requested backoff"
  | code => Status.internal s!"stream reset by server (HTTP/2 error {code.toNat})"

private def informationalResponse (headers : _root_.Http2.Headers) : Bool :=
  match (headers.get? ":status").bind String.toNat? with
  | some status => status < 200
  | none => false

private def resetProtocolStream (state : ConnState) (streamId : Nat)
    (code : _root_.Http2.ErrorCode) : Except Status (ConnState × Array _root_.Http2.Frame) := do
  let (protocol, reset?) ← ofHttp2 <|
    _root_.Http2.Connection.resetStream state.protocol streamId code
  let frames := match reset? with
    | some frame => #[frame]
    | none => #[]
  pure ({ state with protocol }, frames)

/-- Drop application ownership of a terminal call and close any request side
the peer completed before the application half-closed it. -/
private def retireCallLocked (connection : Connection) (state : ConnState)
    (streamId : Nat) : BaseIO ConnState := do
  let state := { state with calls := removeCall state.calls streamId }
  if state.dead.isSome then
    pure state
  else
    match _root_.Http2.Connection.resetStream state.protocol streamId .cancel with
    | .error _ => pure state
    | .ok (protocol, reset?) =>
        if let some reset := reset? then enqueueFrames connection #[reset]
        pure { state with protocol }

private def handleHeadersEvent (state : ConnState) (streamId : Nat)
    (headers : _root_.Http2.Headers) (endStream trailers : Bool) : ConnState :=
  match findCall? state.calls streamId with
  | none => state
  | some call =>
      if call.failure.isSome || call.trailers.isSome || informationalResponse headers then
        state
      else
        let call :=
          if trailers || endStream then
            if call.decode.buffered.isEmpty then
              { call with trailers := some headers }
            else
              failCallRecord (Status.internal
                "server ended the response with an incomplete gRPC message") call
          else
            {
              call with
              seenHeaders := true
              headers
              responseGzip := responseGzipOf headers
            }
        { state with calls := replaceCall state.calls call }

private def handleProtocolEvent (maxReceiveMessageSize : Nat) (state : ConnState)
    (outbound : Array _root_.Http2.Frame) (event : _root_.Http2.Connection.Event) :
    Except Status (ConnState × Array _root_.Http2.Frame) := do
  match event with
  | .headers streamId headers endStream trailers =>
      pure (handleHeadersEvent state streamId headers endStream trailers, outbound)
  | .data streamId payload endStream =>
      match findCall? state.calls streamId with
      | none => pure (state, outbound)
      | some call =>
          if call.failure.isSome || call.trailers.isSome then
            pure (state, outbound)
          else if endStream then
            let status := Status.internal "server ended stream without gRPC trailers"
            let state := { state with
              calls := replaceCall state.calls (failCallRecord status call) }
            let (state, reset) ← resetProtocolStream state streamId .protocolError
            pure (state, outbound ++ reset)
          else
            match processCallData maxReceiveMessageSize call payload with
            | .ok call =>
                pure ({ state with calls := replaceCall state.calls call }, outbound)
            | .error status =>
                let state := { state with
                  calls := replaceCall state.calls (failCallRecord status call) }
                let (state, reset) ← resetProtocolStream state streamId
                  (responseDataFailureResetCode status)
                pure (state, outbound ++ reset)
  | .reset streamId code =>
      let calls := match findCall? state.calls streamId with
        | none => state.calls
        | some call => replaceCall state.calls (failCallRecord (rstStatus code) call)
      pure ({ state with calls }, outbound)
  | .streamError streamId code message =>
      let status := match code with
        | .cancel => Status.cancelled message
        | .refusedStream => Status.error .unavailable message
        | .enhanceYourCalm => Status.resourceExhausted message
        | _ => Status.internal message
      let calls := match findCall? state.calls streamId with
        | none => state.calls
        | some call => replaceCall state.calls (failCallRecord status call)
      pure ({ state with calls }, outbound)
  | .goAway lastStreamId _ _ =>
      pure ({ state with
        calls := state.calls.map fun call =>
          if call.streamId > lastStreamId then
            failCallRecord
              (Status.error .unavailable "connection is shutting down (GOAWAY)") call
          else
            call
      }, outbound)
  | .settingsChanged _ | .settingsAcknowledged | .pingAcknowledged _ | .priority _ =>
      pure (state, outbound)

private def shutdownSocket (socket : TCP.Socket.Client) : Async Unit := do
  try
    Async.race
      socket.shutdown
      (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 200))
  catch _ =>
    pure ()

namespace TestSupport

structure ResponseDataObservation where
  messageCount : Nat
  retainedDecodedBytes : Nat
  retainedAfterOneReceive : Nat
  deriving Inhabited, Repr

/-- Exercise the production response decoder and production queue-pop
accounting without a socket. -/
def processResponseDataForTest (maxReceiveMessageSize : Nat) (responseGzip : Bool)
    (payload : ByteArray) : Except Status ResponseDataObservation := do
  let call ← processCallData maxReceiveMessageSize {
    streamId := 1
    responseGzip := responseGzip
  } payload
  let retainedAfterOneReceive :=
    (popInboundMessage? call).map (·.call.retainedDecodedBytes)
      |>.getD call.retainedDecodedBytes
  pure {
    messageCount := call.inbound.size
    retainedDecodedBytes := call.retainedDecodedBytes
    retainedAfterOneReceive := retainedAfterOneReceive
  }

def retainedDecodedResponseLimitForTest (maxReceiveMessageSize : Nat) : Nat :=
  retainedDecodedResponseLimit maxReceiveMessageSize

def responseDataFailureResetCodeForTest (status : Status) : _root_.Http2.ErrorCode :=
  responseDataFailureResetCode status

/-- Test-only fault injection: retire the socket write side, then verify that
an exact writer ticket reports failure instead of an earlier queue-admission
success. The connection is unusable afterwards. -/
def acknowledgedWriteAfterSocketShutdown (connection : Connection) :
    Async (Except Status Unit) := do
  shutdownSocket connection.socket
  match ← enqueueBytesAcknowledged connection (ByteArray.mk #[0]) with
  | .error status => pure (.error status)
  | .ok ticket => awaitOutboundTicket ticket

end TestSupport

private inductive ReaderEvent where
  | received (chunk? : Option ByteArray)
  | stop
  | writerFailed (status : Status)

private def nextReaderEvent (connection : Connection) : Async ReaderEvent :=
  let transportCases := #[
      Selectable.case (connection.socket.recvSelector connection.config.readSize) fun chunk? =>
        pure (ReaderEvent.received chunk?),
      Selectable.case connection.stopToken.selector fun _ =>
        pure ReaderEvent.stop,
      Selectable.case connection.writerFailureToken.selector fun _ => do
        let error? ← connection.writerFailure.get
        let error := error?.getD (IO.userError "connection writer failed")
        pure (ReaderEvent.writerFailed (Status.ofIOError error))
    ]
  match connection.tls with
  | none => Selectable.one transportCases
  | some session =>
      Selectable.one <| transportCases.push <|
        Selectable.case session.writerFailureSelector fun _ => do
          let error? ← session.writerFailure?
          let error := error?.getD (IO.userError "TLS record writer failed")
          pure (ReaderEvent.writerFailed (Status.ofIOError error))

/-- Feed one decrypted chunk through the shared HTTP/2 state machine, then
translate its semantic events into gRPC call state. `true` means the reader
should continue. Shared by the socket path and TLS handshake leftovers. -/
private def processInboundChunk (connection : Connection) (chunk : ByteArray) :
    Async Bool := do
  let keepGoing ← connection.state.atomically do
    let state ← get
    if state.dead.isSome then
      pure false
    else
      match _root_.Http2.Connection.processBytes state.protocol chunk with
      | .error error =>
          set (failStateLocked state (Status.ofHttp2Error error))
          pure false
      | .ok processed =>
          let mut state := { state with protocol := processed.state }
          let mut outbound := processed.outbound
          let mut applicationError? : Option Status := none
          for event in processed.events do
            if applicationError?.isNone then
              match handleProtocolEvent connection.config.maxReceiveMessageSize
                  state outbound event with
              | .ok (next, frames) =>
                  state := next
                  outbound := frames
              | .error status => applicationError? := some status
          let protocolError? := processed.error?
          if let some error := protocolError? then
            match _root_.Http2.Connection.beginGoAway state.protocol error.code
                error.message.toUTF8 with
            | .ok (protocol, goAway) =>
                state := { state with protocol }
                outbound := outbound.push goAway
            | .error _ => pure ()
          let terminal? := applicationError?.orElse fun _ =>
            protocolError?.map Status.ofHttp2Error
          if let some status := terminal? then
            state := failStateLocked state status
          set state
          enqueueFrames connection outbound
          pure terminal?.isNone
  wake connection
  pure keepGoing

/-- Resolve every completion-aware item left behind after the sole writer
fails. Closing the channel preserves queued items for this drain. -/
private partial def failQueuedOutboundWrites (connection : Connection)
    (error : IO.Error) : Async Unit := do
  match ← await (← connection.outbound.recv) with
  | none => pure ()
  | some request =>
      if let some completion := request.completion then
        completion.resolve (.error error)
      failQueuedOutboundWrites connection error

/-- Drain the outbound channel from one cooperative writer.  In particular the
plaintext path awaits `socket.send` in `Async`; it never parks a worker with
`.block`, and FIFO ownership preserves frame order. -/
private partial def writerLoop (connection : Connection) : Async Unit := do
  match ← await (← connection.outbound.recv) with
  | none => pure ()
  | some request =>
      try
        match connection.tls with
        | some session => session.sendAcknowledged request.bytes
        | none => connection.socket.send request.bytes
        if let some completion := request.completion then
          completion.resolve (.ok ())
        writerLoop connection
      catch err =>
        if let some completion := request.completion then
          completion.resolve (.error err)
        -- Do not mutate connection state here.  Publishing through a sticky
        -- selector wakes the exact reader even while the peer keeps its write
        -- side open; that reader remains the sole failure/retirement owner.
        if (← connection.writerFailure.get).isNone then
          connection.writerFailure.set (some err)
        discard <| connection.outbound.close.toBaseIO
        failQueuedOutboundWrites connection err
        discard <| _root_.Http2.CancellationToken.cancel connection.writerFailureToken
          (reason := Std.CancellationReason.shutdown)

private def awaitBackgroundTask (task : AsyncTask Unit) : Async Unit := do
  let finished ← Async.race
    (do
      try Async.ofAsyncTask task catch _ => pure ()
      pure true)
    (do
      Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 200)
      pure false)
  unless finished do
    IO.cancel task

private def joinBackgroundTasks (connection : Connection) : Async Unit := do
  let background ← connection.background.get
  match background.writer with
  | some writer => awaitBackgroundTask writer
  | none => pure ()
  match background.reader with
  | some reader =>
      -- The reader converts transport errors into connection state before it
      -- terminates. A task-level error must not skip the other join.
      awaitBackgroundTask reader
  | none => pure ()

private def shutdownConnection (connection : Connection) : Async Unit := do
  failConnection connection (Status.cancelled "connection closed locally")
  discard <| _root_.Http2.CancellationToken.cancel connection.stopToken
    (reason := Std.CancellationReason.shutdown)
  discard <| connection.outbound.close.toBaseIO
  match connection.tls with
  | some session =>
      -- The outer writer only seals and enqueues TLS records, so stop it and
      -- the reader before closing the TLS queue. `session.close` then drains
      -- and joins the inner record writer before shutting down the socket.
      joinBackgroundTasks connection
      session.close
  | none =>
      -- Interrupt a plaintext writer that may be blocked in a socket send,
      -- then join both exact background handles.
      shutdownSocket connection.socket
      joinBackgroundTasks connection

private def closeConnection (connection : Connection) : Async Unit := do
  let owner ← connection.closeClaimed.atomically do
    if ← get then
      pure false
    else
      set true
      pure true
  if owner then
    try
      shutdownConnection connection
    finally
      connection.closed.resolve ()
  else
    match ← Async.ofTask connection.closed.result? with
    | some () => pure ()
    | none => pure ()

/-- Start the elected close owner without making the reader join itself. The
spawned owner closes the outbound queue and transport, waits for this reader to
return, and resolves the shared completion promise for every close caller. -/
private def requestTransportRetirement (connection : Connection) : IO Unit := do
  discard <| Async.toIO (closeConnection connection)

/-- Connection reader. Runs in `Async`: while idle (no inbound bytes) it suspends
cooperatively instead of parking a worker thread, so open-but-idle connections are
free. Frame handling in the body is ordinary `IO`.  `pending?` carries decrypted
application bytes that arrived before the reader existed (the TLS handshake
leftover); they enter exactly where a decrypted socket chunk would. -/
private partial def readerLoop (connection : Connection)
    (pending? : Option ByteArray := none) : Async Unit := do
  if let some chunk := pending? then
    if ← processInboundChunk connection chunk then
      readerLoop connection none
    else
      requestTransportRetirement connection
    return
  let event ← try
      Except.ok <$> nextReaderEvent connection
    catch err =>
      pure (Except.error (Status.ofIOError err))
  -- `.stop` (this side closing the connection) and a peer EOF both end the
  -- loop, but they are very different diagnoses, so they are not collapsed into
  -- one status: a report of "connection closed" then always means the peer went
  -- away, never that we shut ourselves down.
  let localStop : Bool := match event with
    | .ok .stop => true
    | _ => false
  let chunk? : Except Status (Option ByteArray) := match event with
    | .error status => .error status
    | .ok .stop => .ok none
    | .ok (.writerFailed status) => .error status
    | .ok (.received chunk?) => .ok chunk?
  -- Over TLS, decrypt the raw chunk into application bytes first; `none` means the
  -- peer closed (close_notify or EOF). A `some #[]` (control-only record) decodes to
  -- no frames and loops, exactly like an empty plaintext read.
  let chunk? : Except Status (Option ByteArray) ← do
    match chunk?, connection.tls with
    | .ok (some raw), some session =>
        match ← (session.feedInbound raw).toBaseIO with
        | .ok plaintext => pure (.ok plaintext)
        | .error err => pure (.error (Status.ofIOError err))
    | other, _ => pure other
  match chunk? with
  | .error status =>
      failConnection connection status
      requestTransportRetirement connection
  | .ok none =>
      if localStop then
        failConnection connection (Status.error .unavailable "connection shut down locally")
      else
        failConnection connection (Status.error .unavailable "connection closed by peer")
        requestTransportRetirement connection
  | .ok (some chunk) =>
      if ← processInboundChunk connection chunk then
        readerLoop connection none
      else
        requestTransportRetirement connection

private def startBackgroundTasks (connection : Connection)
    (initialInbound : ByteArray := ByteArray.empty) : IO Unit := do
  let pending? := if initialInbound.isEmpty then none else some initialInbound
  let reader ← Async.toIO (readerLoop connection pending?)
  connection.background.set { reader := some reader }
  let writer ← Async.toIO (writerLoop connection)
  connection.background.set { writer := some writer, reader := some reader }

private def clientOpening (config : Config) : IO
    (_root_.Http2.Connection.State × ByteArray) := do
  if config.readSize == 0 then
    throw (IO.userError "HTTP/2 client readSize must be positive")
  let initialWindowSize := clientInitialStreamWindow config
  if initialWindowSize > _root_.Http2.Connection.maximumWindowSize then
    throw (IO.userError
      "maxReceiveMessageSize exceeds the largest safe HTTP/2 stream receive window")
  let protocol := _root_.Http2.Connection.initial .client (clientSettings config)
  let wire ← ofStatus <| ofHttp2 <| _root_.Http2.Connection.initialWireBytes protocol
  pure (protocol, wire)

private def initializeConnection
    (socket : TCP.Socket.Client) (config : Config)
    (protocol : _root_.Http2.Connection.State) (prefaceWire : ByteArray)
    (tls : Option _root_.Http2.Tls.ClientSession := none)
    (initialInbound : ByteArray := ByteArray.empty) :
    IO Connection := do
  let connection : Connection := {
    socket := socket,
    config := config,
    state := ← Std.Mutex.new {
      protocol := protocol
    },
    outbound := ← Std.CloseableChannel.new,
    wakeup := ← Std.Notify.new,
    stopToken := ← Std.CancellationToken.new,
    writerFailure := ← IO.mkRef (none : Option IO.Error),
    writerFailureToken := ← Std.CancellationToken.new,
    background := ← IO.mkRef {},
    closeClaimed := ← Std.Mutex.new false,
    closed := ← IO.Promise.new,
    tls := tls
  }
  try
    -- The connection preface must be the first bytes this endpoint puts on the
    -- wire (RFC 9113 §3.4), and the outbound channel is the only thing that
    -- orders them.  So the preface is enqueued *before* the reader exists: the
    -- server sends its own SETTINGS without waiting for ours, and a reader
    -- started first can decode that SETTINGS and enqueue its ACK before this
    -- line runs.  The peer then reads a SETTINGS ACK where the preface must be
    -- and kills the connection — a race whose window is exactly the scheduling
    -- delay between spawning the reader and enqueuing here, so it appears only
    -- under load and only on some connections.
    enqueueBytes connection prefaceWire
    -- TLS-handshake-leftover bytes (the server's 0.5-RTT SETTINGS riding behind
    -- its Finished flight) are handed to the reader, which processes them before
    -- its first socket read; enqueueing our preface first preserves §3.4 order.
    startBackgroundTasks connection initialInbound
    pure connection
  catch error =>
    Async.block (shutdownConnection connection)
    throw error

private def openingCancelled (cancellation? : Option Std.CancellationToken) : BaseIO Bool :=
  match cancellation? with
  | none => pure false
  | some cancellation => cancellation.isCancelled

private def openingCancelledError (phase : String) : IO.Error :=
  IO.userError s!"{phase} cancelled"

/-- Asynchronously connect, perform the HTTP/2 client preface exchange, and
start the writer and reader tasks. Socket waits suspend cooperatively. The
optional token is the cleanup boundary for opening timeouts: after it is
cancelled, this operation retains its exact native operation until libuv
settles, retires the socket, and then returns an error. Forced task cancellation
is not a cleanup boundary in `Std.Async`. -/
def connectAsync (config : Config := {})
    (cancellation? : Option Std.CancellationToken := none) : Async Connection := do
  -- Finish all pure framing work before acquiring a socket.
  let (protocol, prefaceWire) ← clientOpening config
  if ← openingCancelled cancellation? then
    throw (openingCancelledError "HTTP/2 connection opening")
  let socket ← TCP.Socket.Client.mk
  try
    socket.connect config.address
    if ← openingCancelled cancellation? then
      shutdownSocket socket
      throw (openingCancelledError "HTTP/2 connection opening")
    socket.noDelay
    let connection ← initializeConnection socket config protocol prefaceWire
    if ← openingCancelled cancellation? then
      shutdownConnection connection
      throw (openingCancelledError "HTTP/2 connection opening")
    pure connection
  catch error =>
    -- Once `connect` has returned or thrown, there is no pending receive owned
    -- by this adapter. Shut down every socket that was not transferred into a
    -- successfully returned `Connection`; finalization then releases its handle.
    shutdownSocket socket
    throw error

/-- Synchronous compatibility wrapper for `connectAsync`. -/
def connect (config : Config := {}) : IO Connection :=
  Async.block (connectAsync config)

private def transportConfig (config : Config) : _root_.Http2.Client.Config := {
  address := config.address
  authority := config.authority
  scheme := config.scheme
  readSize := config.readSize
  initialWindowSize := clientInitialStreamWindow config
}

/-- Connect over TLS 1.3, then run the gRPC client exactly as `connect` does but
with every byte sealed/opened through the TLS session. Fresh ECDHE and random
values are generated internally. -/
def connectTlsAsync (config : Config := {})
    (tlsConfig : _root_.Http2.Client.TlsConfig := {})
    (cancellation? : Option Std.CancellationToken := none) : Async Connection := do
  -- Finish gRPC-specific settings validation before the shared transport owns a
  -- socket. The transport bootstrap performs the generic HTTP/2 and TLS policy
  -- validation, handshake, chain validation, and hostname verification.
  let (protocol, prefaceWire) ← clientOpening config
  let bootstrap ← _root_.Http2.Client.bootstrapTlsAsync
    (transportConfig config) tlsConfig cancellation?
  let transferred ← IO.mkRef false
  try
    unless (← bootstrap.session.alpnSelected) == some "h2" do
      throw (IO.userError "TLS peer did not negotiate the h2 ALPN protocol")
    if ← openingCancelled cancellation? then
      throw (openingCancelledError "HTTP/2 TLS adoption")
    -- `initializeConnection` owns and retires the session from this point,
    -- including on an initialization error.
    transferred.set true
    let connection ← initializeConnection bootstrap.session.socket config protocol prefaceWire
      (some bootstrap.session) bootstrap.initialInbound
    if ← openingCancelled cancellation? then
      shutdownConnection connection
      throw (openingCancelledError "HTTP/2 TLS adoption")
    pure connection
  catch error =>
    unless ← transferred.get do
      bootstrap.close
    throw error

/-- Synchronous compatibility wrapper for `connectTlsAsync`. -/
def connectTls (config : Config := {})
    (tlsConfig : _root_.Http2.Client.TlsConfig := {}) : IO Connection :=
  Async.block (connectTlsAsync config tlsConfig)

/-- Cooperatively close the connection and retire its exact reader and writer tasks.

The socket API exposes a write-side shutdown rather than an explicit handle
close. The FIN lets a peer observe EOF; each drain and shutdown wait is bounded,
so a non-reading peer cannot make `close` hang or park a worker. `Async.race`
does not cancel its losing branch: when the timer wins, the native shutdown
promise and descriptor reference can remain suspended until the OS settles it.
A hard `uv_close` is not exposed; finalization releases the native handle after
remaining `Connection`/promise references are gone.
-/
def close (connection : Connection) : Async Unit :=
  closeConnection connection

private inductive StartStep where
  | opened (call : Call)
  | wait (waiter : AsyncTask Unit)
  | failed (status : Status)

private partial def startLoop (connection : Connection) (path : String)
    (options : CallOptions) : Async (Except Status Call) := do
  let step ← connection.state.atomically do
    let state ← get
    match state.dead with
    | some status => pure (StartStep.failed status)
    | none =>
      match state.protocol.peerGoAwayLastStream? with
      | some _ => pure (StartStep.failed
          (Status.error .unavailable "connection is shutting down (GOAWAY)"))
      | none =>
          if !peerStreamCapacityAvailable state then
            let waiter ← connection.wakeup.wait
            pure (StartStep.wait waiter)
          else
            let metadata := requestMetadata connection path options
            match ofHttp2 <| _root_.Http2.Connection.openStream state.protocol metadata with
            | .error status => pure (StartStep.failed status)
            | .ok (protocol, streamId, frames) =>
                let record : CallRecord := { streamId }
                set {
                  state with
                  protocol
                  calls := state.calls.push record
                }
                enqueueFrames connection frames
                pure (StartStep.opened { connection := connection, streamId := streamId })
  match step with
  | .opened call => pure (.ok call)
  | .failed status => pure (.error status)
  | .wait waiter =>
      awaitWaiter waiter
      startLoop connection path options

/-- Open a stream: send request HEADERS and register the call. The request
body is streamed afterwards with `Call.send` / `Call.closeSend`. When the peer
advertises a concurrent-stream limit, opening waits for capacity. -/
def start (connection : Connection) (path : String) (options : CallOptions := {}) :
    Async (Except Status Call) :=
  startLoop connection path options

namespace Call

private inductive SendStep where
  | wait (waiter : AsyncTask Unit)
  | sent (bytes : Nat)
  | failed (status : Status)

/-- The terminal status of a call whose server already finished: its failure,
or the decoded trailer status when the server completed the RPC early. -/
private def earlyTerminalStatus (record : CallRecord) : Status :=
  match record.failure with
  | some status => status
  | none =>
      match record.trailers with
      | none => Status.internal "gRPC call is not finished"
      | some trailers =>
          match Headers.statusFromTrailers trailers with
          | .error status => status
          | .ok status =>
              if status.isOk then
                Status.internal "server already completed the call"
              else
                status

private partial def sendChunks (call : Call) (payload : ByteArray) (offset : Nat) :
    Async (Except Status Unit) := do
  if offset >= payload.size then
    pure (.ok ())
  else
    let step ← call.connection.state.atomically do
      let state ← get
      match state.dead with
      | some status => pure (SendStep.failed status)
      | none =>
        match findCall? state.calls call.streamId with
        | none => pure (SendStep.failed (Status.internal "gRPC call is no longer active"))
        | some record =>
            if record.failure.isSome || record.trailers.isSome then
              pure (SendStep.failed (earlyTerminalStatus record))
            else
              match _root_.Http2.Connection.stream? state.protocol call.streamId with
              | none => pure (SendStep.failed
                  (Status.internal "gRPC HTTP/2 stream is no longer active"))
              | some stream =>
                  if !stream.phase.localOpen then
                    pure (SendStep.failed (Status.internal "send after closeSend"))
                  else
                    let available := _root_.Http2.Connection.outboundCredit?
                      state.protocol call.streamId |>.getD 0
                    if available == 0 then
                      let waiter ← call.connection.wakeup.wait
                      pure (SendStep.wait waiter)
                    else
                      let sendSize := Nat.min available (payload.size - offset)
                      let chunk := payload.extract offset (offset + sendSize)
                      match ofHttp2 <| _root_.Http2.Connection.sendData
                          state.protocol call.streamId chunk with
                      | .error status => pure (SendStep.failed status)
                      | .ok (protocol, frames) =>
                          set { state with protocol }
                          enqueueFrames call.connection frames
                          pure (SendStep.sent sendSize)
    match step with
    | .wait waiter => do
        awaitWaiter waiter
        sendChunks call payload offset
    | .sent bytes => sendChunks call payload (offset + bytes)
    | .failed status => pure (.error status)

/-- Send one request message, waiting for flow-control window as needed. -/
def send (call : Call) (message : ByteArray) : Async (Except Status Unit) := do
  if message.size > call.connection.config.maxSendMessageSize then
    pure (.error (Status.resourceExhausted
      s!"gRPC request message exceeds configured size limit \
        {call.connection.config.maxSendMessageSize}"))
  else
    match Message.encode { data := message } with
    | .error status => pure (.error status)
    | .ok encoded => sendChunks call encoded 0

/-- Half-close the request side (empty DATA frame with END_STREAM). -/
def closeSend (call : Call) : Async (Except Status Unit) := do
  call.connection.state.atomically do
    let state ← get
    match state.dead with
    | some status => pure (.error status)
    | none =>
      match findCall? state.calls call.streamId with
      | none => pure (.error (Status.internal "gRPC call is no longer active"))
      | some record =>
          match record.failure with
          | some status => pure (.error status)
          | none =>
              match _root_.Http2.Connection.stream? state.protocol call.streamId with
              | none => pure (.error
                  (Status.internal "gRPC HTTP/2 stream is no longer active"))
              | some stream =>
                  if !stream.phase.localOpen then
                    pure (.ok ())
                  else
                    match ofHttp2 <| _root_.Http2.Connection.sendData
                        state.protocol call.streamId ByteArray.empty true with
                    | .error status => pure (.error status)
                    | .ok (protocol, frames) =>
                        set { state with protocol }
                        enqueueFrames call.connection frames
                        pure (.ok ())

private inductive RecvStep where
  | message (data : ByteArray)
  | done
  | wait (waiter : AsyncTask Unit)
  | failed (status : Status)

private partial def recvLoop (call : Call) : Async (Except Status (Option ByteArray)) := do
  let step ← call.connection.state.atomically do
    let state ← get
    match findCall? state.calls call.streamId with
    | none =>
        pure (RecvStep.failed (state.dead.getD (Status.internal "gRPC call is no longer active")))
    | some record =>
      match popInboundMessage? record with
      | some popped =>
          let data := popped.data
          let credit := popped.wireCredit
          let terminal := record.failure.isSome || record.trailers.isSome
          let record := popped.call
          if credit > 0 && !terminal then
            match ofHttp2 <| _root_.Http2.Connection.acknowledgeData
                state.protocol call.streamId credit with
            | .error status =>
                let record := failCallRecord status record
                set { state with calls := replaceCall state.calls record }
                pure (RecvStep.message data)
            | .ok (protocol, frames) =>
                set {
                  state with
                  protocol
                  calls := replaceCall state.calls record
                }
                enqueueFrames call.connection frames
                pure (RecvStep.message data)
          else
            set { state with calls := replaceCall state.calls record }
            pure (RecvStep.message data)
      | none =>
          match record.failure with
          | some status => pure (RecvStep.failed status)
          | none =>
              if record.trailers.isSome then
                pure RecvStep.done
              else
                match state.dead with
                  | some status => pure (RecvStep.failed status)
                  | none =>
                      let waiter ← call.connection.wakeup.wait
                      pure (RecvStep.wait waiter)
  match step with
  | .message data => pure (.ok (some data))
  | .done => pure (.ok none)
  | .wait waiter => do
      awaitWaiter waiter
      recvLoop call
  | .failed status => pure (.error status)

/-- Receive the next response message; `none` after the server's trailers.
Buffered messages are delivered before any failure is reported. -/
def recv? (call : Call) : Async (Except Status (Option ByteArray)) :=
  recvLoop call

private inductive FinishStep where
  | finished (headers : _root_.Http2.Headers) (trailers : _root_.Http2.Headers)
  | failed (status : Status)
  | wait (waiter : AsyncTask Unit)

/-- Wait for the call's terminal state and remove it from the connection.
Returns the server's gRPC status plus initial headers and trailers; transport
failures (RST_STREAM, GOAWAY, connection loss) surface as the error case. -/
partial def finish (call : Call) : Async (Except Status (Status × _root_.Http2.Headers × _root_.Http2.Headers)) := do
  let step ← call.connection.state.atomically do
    let state ← get
    match findCall? state.calls call.streamId with
    | none =>
        pure (FinishStep.failed (state.dead.getD (Status.internal "gRPC call is no longer active")))
    | some record =>
        match record.failure with
        | some status =>
            set (← retireCallLocked call.connection state call.streamId)
            pure (FinishStep.failed status)
        | none =>
            match record.trailers with
            | some trailers =>
                set (← retireCallLocked call.connection state call.streamId)
                pure (FinishStep.finished record.headers trailers)
            | none =>
                match state.dead with
                | some status =>
                    set (← retireCallLocked call.connection state call.streamId)
                    pure (FinishStep.failed status)
                | none =>
                    let waiter ← call.connection.wakeup.wait
                    pure (FinishStep.wait waiter)
  match step with
  | .finished headers trailers =>
      match Headers.statusFromTrailers trailers with
      | .ok status => pure (.ok (status, headers, trailers))
      | .error status => pure (.error status)
  | .failed status => pure (.error status)
  | .wait waiter => do
      awaitWaiter waiter
      finish call

/-- Cancel the call locally and reset the stream on the server. -/
def cancel (call : Call) : Async Unit := do
  call.connection.state.atomically do
    let state ← get
    match findCall? state.calls call.streamId with
    | none => pure ()
    | some record =>
        if record.failure.isSome || record.trailers.isSome then
          pure ()
        else do
          let record := { record with
            failure := some (Status.cancelled "call cancelled locally") }
          match _root_.Http2.Connection.resetStream
              state.protocol call.streamId .cancel with
          | .error _ =>
              set { state with calls := replaceCall state.calls record }
          | .ok (protocol, reset?) =>
              set { state with protocol, calls := replaceCall state.calls record }
              if let some reset := reset? then enqueueFrames call.connection #[reset]
  wake call.connection

end Call

private partial def collectResponses (call : Call) (out : Array ByteArray) :
    Async (Array ByteArray) := do
  match ← call.recv? with
  | .ok (some message) => collectResponses call (out.push message)
  | .ok none => pure out
  | .error _ => pure out

/-- Issue one RPC with a fixed request-message list and collect the full
response. Works for unary, server-streaming, and batch client-streaming
shapes; transport-level failures throw, server statuses land in the result. -/
def callRaw (connection : Connection) (path : String) (requests : Array ByteArray)
    (options : CallOptions := {}) : Async CallResult := do
  let call ← ofStatus (← start connection path options)
  let mut sendFailure : Option Status := none
  for request in requests do
    if sendFailure.isNone then
      match ← call.send request with
      | .ok () => pure ()
      | .error status => sendFailure := some status
  match sendFailure with
  | some status =>
      -- A locally rejected message (for example, one above the configured
      -- send limit) never put END_STREAM on the wire. Reset and reap the call
      -- instead of waiting forever for a response that the peer cannot send.
      call.cancel
      discard <| call.finish
      pure { status := status }
  | none =>
      match ← call.closeSend with
      | .error status =>
          call.cancel
          discard <| call.finish
          pure { status := status }
      | .ok () =>
          let messages ← collectResponses call #[]
          match ← call.finish with
          | .ok (status, headers, trailers) =>
              pure {
                headers := headers
                trailers := trailers
                messages := messages
                status := status
              }
          | .error status => throw (IO.userError status.messageD)

/-- Unary call: exactly one request and one response message. -/
def call (connection : Connection) (path : String) (request : ByteArray)
    (options : CallOptions := {}) : Async (Except Status (_root_.Http2.Headers × ByteArray)) := do
  try
    let result ← callRaw connection path #[request] options
    if result.status.code != Code.ok then
      pure (.error result.status)
    else if h : result.messages.size = 1 then
      pure (.ok (result.trailers, result.messages[0]))
    else
      pure (.error (Status.internal
        s!"expected exactly one response message, got {result.messages.size}"))
  catch err =>
    pure (.error (Status.ofIOError err))

/-- Server-streaming call: one request message, any number of responses. -/
def serverStreaming (connection : Connection) (path : String) (request : ByteArray)
    (options : CallOptions := {}) : Async CallResult :=
  callRaw connection path #[request] options

end Client
end Grpc
