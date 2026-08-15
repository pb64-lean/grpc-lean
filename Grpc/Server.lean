module

public import Grpc.Protocol
import Std.Async.Timer

public section

namespace Grpc

/-- Per-call hook used by a transport to retain the exact child currently
executing a deadline-controlled handler or stream receive.  A managed HTTP/2
transport also owns the deadline timer, multiplexing all active calls onto its
independent per-connection scheduler; standalone callers leave
`externalTimer` false and use the local native-timer fallback.  The returned
action releases a normally completed child.  A cancelled child stays
registered until the transport has emitted its terminal status and joins it. -/
structure DeadlineRuntime where
  externalTimer : Bool := false
  registerTask : Nat -> IO Unit -> IO Unit -> Std.Async.Async Unit -> IO (IO Unit)

abbrev UnaryHandler := UnaryRequest -> GrpcM UnaryResponse
abbrev ServerStreamingHandler := UnaryRequest -> GrpcM ServerStreamingResponse
abbrev ServerStreamingStreamHandler := UnaryRequest -> GrpcM ServerStreamingStreamResponse
abbrev ClientStreamingHandler := ClientStreamingRequest -> GrpcM UnaryResponse
abbrev ClientStreamingStreamHandler := ClientStreamingStreamRequest -> GrpcM UnaryResponse
abbrev BidirectionalStreamingHandler := ClientStreamingRequest -> GrpcM ServerStreamingResponse
abbrev BidirectionalStreamingStreamHandler :=
  ClientStreamingStreamRequest -> GrpcM ServerStreamingStreamResponse

abbrev TypedUnaryHandler (α β : Type) := α -> GrpcM β
abbrev TypedServerStreamingHandler (α β : Type) := α -> GrpcM (Array β)
abbrev TypedClientStreamingHandler (α β : Type) := Array α -> GrpcM β
abbrev TypedBidirectionalStreamingHandler (α β : Type) := Array α -> GrpcM (Array β)
abbrev TypedServerStreamingStreamHandler (α β : Type) := α -> GrpcM (MessageStream β)
abbrev TypedClientStreamingStreamHandler (α β : Type) := MessageStream α -> GrpcM β
abbrev TypedBidirectionalStreamingStreamHandler (α β : Type) :=
  MessageStream α -> GrpcM (MessageStream β)

/-- What a typed handler knows about the call it is serving, beyond the decoded
message: the method, the request metadata, and the deadline.

A raw handler reads these off its `UnaryRequest`/`ClientStreamingRequest`; a
typed handler is handed only the decoded message, so the `*WithContext`
registration variants pass this record alongside it.  `deadline` is the same
absolute instant the server enforces, so `context.remainingDeadline` is exactly
the time a downstream call may still take. -/
structure RequestContext where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  /-- Absolute deadline on `IO.monoNanosNow`'s clock, or `none` when the
  request carried no `grpc-timeout`. -/
  deadline : Option Nat := none

namespace RequestContext

def ofUnaryRequest (request : UnaryRequest) : RequestContext :=
  {
    method := request.method,
    metadata := request.metadata,
    timeout := request.timeout,
    deadline := request.deadline
  }

def ofClientStreamingRequest (request : ClientStreamingRequest) : RequestContext :=
  {
    method := request.method,
    metadata := request.metadata,
    timeout := request.timeout,
    deadline := request.deadline
  }

def ofClientStreamingStreamRequest (request : ClientStreamingStreamRequest) :
    RequestContext :=
  {
    method := request.method,
    metadata := request.metadata,
    timeout := request.timeout,
    deadline := request.deadline
  }

/-- What is left of this call's deadline, ready to be sent as a downstream
`grpc-timeout` (see `Grpc.Deadline.Remaining`). -/
def remainingDeadline (context : RequestContext) : IO Deadline.Remaining :=
  Deadline.remaining? context.deadline

end RequestContext

/-- Typed handlers that also see the call's metadata and deadline.  These are
additive: `TypedUnaryHandler` and friends keep their shapes, and generated
service code is unaffected. -/
abbrev TypedUnaryContextHandler (α β : Type) := RequestContext -> α -> GrpcM β
abbrev TypedServerStreamingContextHandler (α β : Type) :=
  RequestContext -> α -> GrpcM (Array β)
abbrev TypedClientStreamingContextHandler (α β : Type) :=
  RequestContext -> Array α -> GrpcM β
abbrev TypedBidirectionalStreamingContextHandler (α β : Type) :=
  RequestContext -> Array α -> GrpcM (Array β)
abbrev TypedServerStreamingStreamContextHandler (α β : Type) :=
  RequestContext -> α -> GrpcM (MessageStream β)
abbrev TypedClientStreamingStreamContextHandler (α β : Type) :=
  RequestContext -> MessageStream α -> GrpcM β
abbrev TypedBidirectionalStreamingStreamContextHandler (α β : Type) :=
  RequestContext -> MessageStream α -> GrpcM (MessageStream β)

/--
The seven RPC shapes a registered method handler may have.  The `*Stream`
shapes consume or produce incremental `MessageStream`s; the others use
aggregate request/response values.
-/
inductive RpcShape where
  | unary
  | serverStreaming
  | serverStreamingStream
  | clientStreaming
  | clientStreamingStream
  | bidirectionalStreaming
  | bidirectionalStreamingStream
  deriving Repr, DecidableEq, Inhabited

/--
The handler type for each RPC shape.  Indexing handlers by shape lets a
registry entry carry exactly one correctly shaped handler, so shape agreement
between registration, authorization, and dispatch is structural rather than a
runtime check.
-/
@[expose] def Handler : RpcShape -> Type
  | .unary => UnaryHandler
  | .serverStreaming => ServerStreamingHandler
  | .serverStreamingStream => ServerStreamingStreamHandler
  | .clientStreaming => ClientStreamingHandler
  | .clientStreamingStream => ClientStreamingStreamHandler
  | .bidirectionalStreaming => BidirectionalStreamingHandler
  | .bidirectionalStreamingStream => BidirectionalStreamingStreamHandler

/-- A registered RPC method: a name, a shape, and a handler of exactly that
shape.  A handler of the wrong shape for the entry is unrepresentable. -/
structure MethodEntry where
  name : MethodName
  shape : RpcShape
  handler : Handler shape

/-- The handler of `entry` at `shape`, when `entry` has that shape. -/
def MethodEntry.handlerFor? (entry : MethodEntry) (shape : RpcShape) :
    Option (Handler shape) :=
  if h : entry.shape = shape then some (h ▸ entry.handler) else none

/--
The result of authorizing a completed request header block against the
registry entry resolved for the request method.  `accept` must supply a
handler of the entry's exact shape — usually `entry.handler`, or a capability
handler that captures authorization state resolved from those headers.
Capturing the state in a handler avoids global/task-local side channels and
ensures dispatch uses the exact object that was authorized before the request
body was read.  Because the result is indexed by the entry, an accepted
handler of the wrong shape is unrepresentable and dispatch needs no runtime
shape check.
-/
inductive AuthorizationResult (entry : MethodEntry) where
  | reject (status : Status)
  | accept (handler : Handler entry.shape)

/-- Accept the entry's registered handler unchanged. -/
def AuthorizationResult.acceptRegistered (entry : MethodEntry) :
    AuthorizationResult entry :=
  .accept entry.handler

/-- A bounded, non-blocking request-header authorizer.  Its accepted handler
remains indexed by the looked-up entry's exact RPC shape, just like the
effectful authorizer below. -/
abbrev PureRequestHeaderAuthorizer :=
  (entry : MethodEntry) -> Metadata -> AuthorizationResult entry

/--
Request-header authorization runs after gRPC method/header validation and
method lookup, and before request DATA is accumulated or framed.  It may
perform `IO` (for example, a mutex-protected live-session lookup); callers
should keep it bounded because the connection preserves request ordering
while it runs.  Throwing a `Status` is equivalent to returning `.reject`.
-/
abbrev RequestHeaderAuthorizer :=
  (entry : MethodEntry) -> Metadata -> GrpcM (AuthorizationResult entry)

/-- Registration rejected because the method name is already registered. -/
structure DuplicateMethod where
  name : MethodName
  deriving Repr, DecidableEq

structure Registry where
  maxReceiveMessageSize : Option Nat := none
  maxSendMessageSize : Option Nat := none
  /-- Whether responses may use gzip when the peer advertises it. Request
  decompression remains available independently. -/
  enableResponseCompression : Bool := true
  private pureRequestHeaderAuthorizer : Option PureRequestHeaderAuthorizer := none
  private requestHeaderAuthorizer : RequestHeaderAuthorizer := fun entry _ =>
    pure (.accept entry.handler)
  entries : Array MethodEntry := #[]
  /-- Lets the transport keep the zero-overhead registered-handler fast path
  while deadline-racing only user-installed authorization IO. -/
  private customRequestHeaderAuthorizer : Bool := false

namespace Registry

def empty : Registry := {}

def withMaxReceiveMessageSize (registry : Registry) (size : Nat) : Registry :=
  { registry with maxReceiveMessageSize := some size }

def withMaxSendMessageSize (registry : Registry) (size : Nat) : Registry :=
  { registry with maxSendMessageSize := some size }

/-- Enable or disable negotiated response compression for every registered
method. Disabling it does not change accepted request encodings. -/
def withResponseCompression (registry : Registry) (enabled : Bool) : Registry :=
  { registry with enableResponseCompression := enabled }

/-- Install the callback that authorizes complete request headers. -/
def withRequestHeaderAuthorizer (registry : Registry)
    (authorizer : RequestHeaderAuthorizer) : Registry :=
  {
    registry with
    pureRequestHeaderAuthorizer := none,
    requestHeaderAuthorizer := authorizer,
    customRequestHeaderAuthorizer := true
  }

/-- Install a bounded pure callback that authorizes complete request headers.
Pure callbacks run inline and must not block or perform hidden effects. -/
def withPureRequestHeaderAuthorizer (registry : Registry)
    (authorizer : PureRequestHeaderAuthorizer) : Registry :=
  {
    registry with
    pureRequestHeaderAuthorizer := some authorizer,
    requestHeaderAuthorizer := fun entry metadata => pure (authorizer entry metadata),
    customRequestHeaderAuthorizer := false
  }

/-- Whether header authorization contains user IO that must share the call's
deadline.  The backing fields are private so installing a callback cannot
silently bypass this invariant; use `withRequestHeaderAuthorizer` or
`withPureRequestHeaderAuthorizer`. -/
def usesCustomRequestHeaderAuthorizer (registry : Registry) : Bool :=
  registry.customRequestHeaderAuthorizer

/-- The installed bounded pure authorizer, when authorization can run inline
without entering the effectful task/cancellation lifecycle. -/
def pureRequestHeaderAuthorizer? (registry : Registry) :
    Option PureRequestHeaderAuthorizer :=
  registry.pureRequestHeaderAuthorizer

/-- Run the installed request-header authorizer for a looked-up entry. -/
def authorizeRequestHeaders (registry : Registry) (entry : MethodEntry)
    (metadata : Metadata) : GrpcM (AuthorizationResult entry) :=
  registry.requestHeaderAuthorizer entry metadata

/-- Append a method entry.  Lookup is first-match-wins, so an entry never
shadows an earlier registration of the same name. -/
def register (registry : Registry) (entry : MethodEntry) : Registry :=
  { registry with entries := registry.entries.push entry }

/-- Registration that rejects duplicate method names instead of appending a
shadowed entry.  `Registry.WellFormed` is preserved by construction. -/
def registerChecked (registry : Registry) (entry : MethodEntry) :
    Except DuplicateMethod Registry :=
  match registry.entries.find? (fun existing => existing.name == entry.name) with
  | some _ => .error { name := entry.name }
  | none => .ok (registry.register entry)

/-- Transform every registered entry, keeping the installed request-header
authorizer and its custom flag intact.  This is the server-interceptor idiom:
after all services are registered, rewrite each entry wholesale, for example
wrapping every handler with cross-cutting authorization.  Mapping keeps
registration order and entry count, so first-match-wins lookup resolves the
same position as before.  `Registry.WellFormed` (name uniqueness) is
preserved when `f` preserves each entry's `name`
(`Registry.mapEntries_wellFormed`). -/
def mapEntries (registry : Registry) (f : MethodEntry -> MethodEntry) : Registry :=
  { registry with entries := registry.entries.map f }

def registerUnary (registry : Registry) (name : MethodName) (handler : UnaryHandler) : Registry :=
  registry.register { name := name, shape := .unary, handler := handler }

def registerServerStreaming (registry : Registry) (name : MethodName)
    (handler : ServerStreamingHandler) : Registry :=
  registry.register { name := name, shape := .serverStreaming, handler := handler }

def registerServerStreamingStream (registry : Registry) (name : MethodName)
    (handler : ServerStreamingStreamHandler) : Registry :=
  registry.register { name := name, shape := .serverStreamingStream, handler := handler }

def registerClientStreaming (registry : Registry) (name : MethodName)
    (handler : ClientStreamingHandler) : Registry :=
  registry.register { name := name, shape := .clientStreaming, handler := handler }

def registerClientStreamingStream (registry : Registry) (name : MethodName)
    (handler : ClientStreamingStreamHandler) : Registry :=
  registry.register { name := name, shape := .clientStreamingStream, handler := handler }

def registerBidirectionalStreaming (registry : Registry) (name : MethodName)
    (handler : BidirectionalStreamingHandler) : Registry :=
  registry.register { name := name, shape := .bidirectionalStreaming, handler := handler }

def registerBidirectionalStreamingStream (registry : Registry) (name : MethodName)
    (handler : BidirectionalStreamingStreamHandler) : Registry :=
  registry.register { name := name, shape := .bidirectionalStreamingStream, handler := handler }

def registerUnaryCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedUnaryContextHandler α β) : Registry :=
  registry.registerUnary name fun request => do
    let input ← GrpcM.ofExcept <|
      match decode request.data with
      | .ok value => .ok value
      | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let output ← handler (RequestContext.ofUnaryRequest request) input
    let data ← GrpcM.ofExcept <|
      match encode output with
      | .ok value => .ok value
      | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      data := data,
      status := Status.ok
    }

def registerUnaryCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedUnaryHandler α β) : Registry :=
  registry.registerUnaryCodecWithContext name decode encode (fun _ input => handler input)

def registerServerStreamingCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedServerStreamingContextHandler α β) : Registry :=
  registry.registerServerStreaming name fun request => do
    let input ← GrpcM.ofExcept <|
      match decode request.data with
      | .ok value => .ok value
      | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler (RequestContext.ofUnaryRequest request) input
    let messages ← outputs.mapM fun output =>
      GrpcM.ofExcept <|
        match encode output with
        | .ok value => .ok value
        | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      messages := messages,
      status := Status.ok
    }

def registerServerStreamingCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedServerStreamingHandler α β) : Registry :=
  registry.registerServerStreamingCodecWithContext name decode encode (fun _ input => handler input)

def registerServerStreamingStreamCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedServerStreamingStreamContextHandler α β) : Registry :=
  registry.registerServerStreamingStream name fun request => do
    let input ← GrpcM.ofExcept <|
      match decode request.data with
      | .ok value => .ok value
      | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler (RequestContext.ofUnaryRequest request) input
    let messages := outputs.mapM fun output =>
      GrpcM.ofExcept <|
        match encode output with
        | .ok value => .ok value
        | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      messages := messages,
      status := Status.ok
    }

def registerServerStreamingStreamCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedServerStreamingStreamHandler α β) : Registry :=
  registry.registerServerStreamingStreamCodecWithContext name decode encode (fun _ input => handler input)

def registerClientStreamingCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedClientStreamingContextHandler α β) : Registry :=
  registry.registerClientStreaming name fun request => do
    let inputs ← request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let output ← handler (RequestContext.ofClientStreamingRequest request) inputs
    let data ← GrpcM.ofExcept <|
      match encode output with
      | .ok value => .ok value
      | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      data := data,
      status := Status.ok
    }

def registerClientStreamingCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedClientStreamingHandler α β) : Registry :=
  registry.registerClientStreamingCodecWithContext name decode encode (fun _ input => handler input)

def registerClientStreamingStreamCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedClientStreamingStreamContextHandler α β) : Registry :=
  registry.registerClientStreamingStream name fun request => do
    let inputs := request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let output ← handler (RequestContext.ofClientStreamingStreamRequest request) inputs
    let data ← GrpcM.ofExcept <|
      match encode output with
      | .ok value => .ok value
      | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      data := data,
      status := Status.ok
    }

def registerClientStreamingStreamCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedClientStreamingStreamHandler α β) : Registry :=
  registry.registerClientStreamingStreamCodecWithContext name decode encode (fun _ input => handler input)

def registerBidirectionalStreamingCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedBidirectionalStreamingContextHandler α β) : Registry :=
  registry.registerBidirectionalStreaming name fun request => do
    let inputs ← request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler (RequestContext.ofClientStreamingRequest request) inputs
    let messages ← outputs.mapM fun output =>
      GrpcM.ofExcept <|
        match encode output with
        | .ok value => .ok value
        | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      messages := messages,
      status := Status.ok
    }

def registerBidirectionalStreamingCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedBidirectionalStreamingHandler α β) : Registry :=
  registry.registerBidirectionalStreamingCodecWithContext name decode encode (fun _ input => handler input)

def registerBidirectionalStreamingStreamCodecWithContext [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedBidirectionalStreamingStreamContextHandler α β) : Registry :=
  registry.registerBidirectionalStreamingStream name fun request => do
    let inputs := request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler (RequestContext.ofClientStreamingStreamRequest request) inputs
    let messages := outputs.mapM fun output =>
      GrpcM.ofExcept <|
        match encode output with
        | .ok value => .ok value
        | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      messages := messages,
      status := Status.ok
    }

def registerBidirectionalStreamingStreamCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedBidirectionalStreamingStreamHandler α β) : Registry :=
  registry.registerBidirectionalStreamingStreamCodecWithContext name decode encode (fun _ input => handler input)

/-- The first registered entry with the given name, regardless of shape. -/
def findEntry? (registry : Registry) (name : MethodName) : Option MethodEntry :=
  registry.entries.find? (fun entry => entry.name == name)

/-- The first registered handler with the given name and shape. -/
def findHandler? (registry : Registry) (shape : RpcShape) (name : MethodName) :
    Option (Handler shape) :=
  registry.entries.findSome? fun entry =>
    if entry.name == name then entry.handlerFor? shape else none

def findUnary? (registry : Registry) (name : MethodName) : Option UnaryHandler :=
  registry.findHandler? .unary name

def findServerStreaming? (registry : Registry) (name : MethodName) : Option ServerStreamingHandler :=
  registry.findHandler? .serverStreaming name

def findServerStreamingStream? (registry : Registry) (name : MethodName) :
    Option ServerStreamingStreamHandler :=
  registry.findHandler? .serverStreamingStream name

def findClientStreaming? (registry : Registry) (name : MethodName) : Option ClientStreamingHandler :=
  registry.findHandler? .clientStreaming name

def findClientStreamingStream? (registry : Registry) (name : MethodName) :
    Option ClientStreamingStreamHandler :=
  registry.findHandler? .clientStreamingStream name

def findBidirectionalStreaming? (registry : Registry) (name : MethodName) :
    Option BidirectionalStreamingHandler :=
  registry.findHandler? .bidirectionalStreaming name

def findBidirectionalStreamingStream? (registry : Registry) (name : MethodName) :
    Option BidirectionalStreamingStreamHandler :=
  registry.findHandler? .bidirectionalStreamingStream name

private inductive DeadlineResult (α : Type) where
  | completed : Except Status α -> DeadlineResult α
  | expired : DeadlineResult α
  | failed : IO.Error -> DeadlineResult α
  deriving Inhabited

private def deadlineFromNow? : Option Timeout -> IO (Option Nat)
  | none => pure none
  | some timeout => do
      let now ← IO.monoNanosNow
      pure (some (now + timeout.toNanoseconds))

/-- Use the transport's header-time instant when it has one; direct Registry
callers have no header lifecycle, so they start the timeout at decode time. -/
private def deadlineForTimeout (timeout : Option Timeout) (headerDeadline : Option Nat) :
    IO (Option Nat) :=
  match timeout with
  | none => pure none
  | some _ =>
      match headerDeadline with
      | some deadline => pure (some deadline)
      | none => deadlineFromNow? timeout

private def remainingUntilDeadlineMilliseconds (deadlineNanoseconds : Nat) : IO Nat := do
  let now ← IO.monoNanosNow
  if deadlineNanoseconds <= now then
    pure 0
  else
    pure ((deadlineNanoseconds - now + 999999) / 1000000)

private def deadlineExceededAt (deadlineNanoseconds : Nat) : IO Bool := do
  let now ← IO.monoNanosNow
  pure (deadlineNanoseconds <= now)

private def runHandler (action : GrpcM α) : IO (Except Status α) := do
  try
    action.run
  catch err =>
    pure (.error (Status.ofIOError err))

/-
`IO.waitAny` blocks a Lean scheduler worker and does not provision a replacement
worker (unlike `Task.get`).  In the old implementation every timed RPC blocked
its dispatch worker while a handler task and an `IO.sleep` task were queued;
enough concurrent calls could therefore occupy the whole pool before any
handler ran.  This race is continuation based: the dispatch task depends on a
winner promise and returns its worker while the handler and libuv timer run.
-/
/-- Run one call phase against an absolute monotonic deadline without parking
a scheduler worker.  Managed transports supply `runtime?` to retain the exact
child across cancellation; callers that install custom authorization use the
same primitive and join its retained child before returning. -/
def runWithDeadlineUntilAsync (deadline? : Option Nat) (action : GrpcM α)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status α) := do
  match deadline? with
  | none => runHandler action
  | some deadline => do
      let externalTimer := runtime?.any (fun runtime => runtime.externalTimer)
      -- A managed scheduler already owns the absolute instant.  Only the
      -- standalone fallback needs a clock read here to size its relative UV
      -- timer; the handler still checks the absolute instant before and after
      -- arbitrary IO in both modes.
      let remainingMilliseconds ←
        if externalTimer then pure 0
        else remainingUntilDeadlineMilliseconds deadline
      if !externalTimer && remainingMilliseconds == 0 then
        return .error Deadline.exceededStatus
      let winner ← IO.Promise.new
      -- Standalone calls get one native timer. Managed transports register
      -- the absolute instant with their independent per-connection scheduler,
      -- so allocating and then cancelling another UV timer per RPC is pure
      -- overhead there.
      let stopDeadlineTimer : IO Unit ←
        if externalTimer then
          pure (pure ())
        else do
          -- Arm before starting arbitrary handler IO.  A timer-allocation
          -- failure therefore cannot strand an already-running child.
          let sleeper ← Std.Async.Sleep.mk
            (Std.Time.Millisecond.Offset.ofNat remainingMilliseconds)
          let deadlineTask ← Std.Async.Async.toIO sleeper.wait
          BaseIO.chainTask deadlineTask (sync := true) fun
            | .ok () => winner.resolve (.expired : DeadlineResult α)
            | .error error => winner.resolve (.failed error)
          pure do
            IO.cancel deadlineTask
            try
              sleeper.stop
            catch _ =>
              pure ()
      -- `IO.asTask` is `BaseIO`, so once this binding returns the catch below
      -- always owns an exact task handle; no auxiliary publication Ref is
      -- needed on the hot timed-call path.
      let handlerTask ← IO.asTask do
        if ← deadlineExceededAt deadline then
          winner.resolve (.expired : DeadlineResult α)
          pure ()
        else
          let result ← runHandler action
          if ← deadlineExceededAt deadline then
            winner.resolve (.expired : DeadlineResult α)
          else
            winner.resolve (.completed result)
          pure ()
      -- A managed transport retains this exact join through `runtime?` and
      -- deliberately performs it only after publishing the terminal response.
      -- Standalone callers have no later lifecycle owner, so they must finish
      -- cancellation before this primitive returns instead of orphaning an
      -- uncooperative handler/stream receive.
      let joinHandlerIfUnmanaged : Std.Async.Async Unit := do
        if runtime?.isNone then
          try
            discard <| Std.Async.Async.ofAsyncTask handlerTask
          catch _ =>
            pure ()
      try
        -- Resolve at the actual handler completion point.  A callback queued
        -- after the timer would otherwise turn a pre-deadline completion into
        -- a false timeout under scheduler load.
        let unregister ← match runtime? with
          | none => pure (pure ())
          | some runtime =>
              let cancel : IO Unit := do
                winner.resolve (.failed (IO.userError Status.dispatchCancelledMessage))
                IO.cancel handlerTask
              let expire : IO Unit := do
                winner.resolve (.expired : DeadlineResult α)
                IO.cancel handlerTask
              let join : Std.Async.Async Unit := do
                try
                  discard <| Std.Async.Async.ofAsyncTask handlerTask
                catch _ =>
                  pure ()
              runtime.registerTask deadline cancel expire join
        let selected ← Std.Async.Async.ofAsyncTask
          (Std.Async.AsyncTask.ofPurePromise winner
            (error := "the promise linked to the Async was dropped"))
        -- `Sleep.stop` drops its waiter; cancelling the converted task first
        -- makes that cleanup explicit and keeps no losing timer continuation.
        stopDeadlineTimer
        match selected with
        | .completed result =>
            unregister
            pure result
        | .expired =>
            IO.cancel handlerTask
            joinHandlerIfUnmanaged
            pure (.error Deadline.exceededStatus)
        | .failed error =>
            IO.cancel handlerTask
            joinHandlerIfUnmanaged
            pure (.error (Status.ofIOError error))
      catch error =>
        IO.cancel handlerTask
        try
          discard <| Std.Async.Async.ofAsyncTask handlerTask
        catch _ =>
          pure ()
        stopDeadlineTimer
        pure (.error (Status.ofIOError error))

private def runWithDeadlineUntil (deadline? : Option Nat) (action : GrpcM α) : GrpcM α :=
  match deadline? with
  | none => ExceptT.mk (runHandler action)
  | some deadline => ExceptT.mk <|
      Std.Async.Async.block (runWithDeadlineUntilAsync (some deadline) action)

private def checkSendDataSize (registry : Registry) (data : ByteArray) : GrpcM Unit := do
  match registry.maxSendMessageSize with
  | none => pure ()
  | some maxSize =>
      if data.size > maxSize then
        throw (Status.resourceExhausted s!"gRPC response message exceeds configured size limit {maxSize}")
      else
        pure ()

private def validateStatusDetailsTrailer (status : Status) (trailers : Metadata) : GrpcM Unit := do
  if status.isOk && (trailers.get? "grpc-status-details-bin").isSome then
    throw (Status.internal "grpc-status-details-bin is only valid for non-OK statuses")
  else
    pure ()

private def validateUnaryResponse (registry : Registry) (response : UnaryResponse) :
    GrpcM UnaryResponse := do
  GrpcM.ofExcept (Headers.validateResponseMetadata response.metadata)
  GrpcM.ofExcept (Headers.validateResponseTrailers response.trailers)
  validateStatusDetailsTrailer response.status response.trailers
  if response.status.isOk then
    checkSendDataSize registry response.data
  pure response

private def validateServerStreamingResponse (registry : Registry)
    (response : ServerStreamingResponse) : GrpcM ServerStreamingResponse := do
  GrpcM.ofExcept (Headers.validateResponseMetadata response.metadata)
  GrpcM.ofExcept (Headers.validateResponseTrailers response.trailers)
  validateStatusDetailsTrailer response.status response.trailers
  for message in response.messages do
    checkSendDataSize registry message
  pure response

private def validateServerStreamingStreamResponse (registry : Registry)
    (response : ServerStreamingStreamResponse) : GrpcM ServerStreamingStreamResponse := do
  GrpcM.ofExcept (Headers.validateResponseMetadata response.metadata)
  GrpcM.ofExcept (Headers.validateResponseTrailers response.trailers)
  validateStatusDetailsTrailer response.status response.trailers
  let messages := response.messages.mapM fun message => do
    checkSendDataSize registry message
    pure message
  pure { response with messages := messages }

private def streamResponseOfAggregate (response : ServerStreamingResponse) :
    GrpcM ServerStreamingStreamResponse := do
  let messages ← MessageStream.ofArray response.messages
  pure {
    metadata := response.metadata,
    messages := messages,
    status := response.status,
    trailers := response.trailers
  }

private def collectServerStreamingStreamResponse (response : ServerStreamingStreamResponse) :
    GrpcM ServerStreamingResponse := do
  let messages ← response.messages.collect
  pure {
    metadata := response.metadata,
    messages := messages,
    status := response.status,
    trailers := response.trailers
  }

private def cancelAfterDeadline (stream : MessageStream α) : IO Unit := do
  try
    discard <| stream.cancel.run
  catch _ =>
    pure ()

private def withDeadlineUntil (deadline? : Option Nat) (stream : MessageStream α) :
    MessageStream α :=
  {
    recv? := ExceptT.mk do
      match ← (runWithDeadlineUntil deadline? stream.recv?).run with
      | .ok value => pure (.ok value)
      | .error status =>
          if status.code == Code.deadlineExceeded then
            cancelAfterDeadline stream
          pure (.error status),
    cancel := stream.cancel
  }

private def decodeUnaryRequest (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (headerDeadline : Option Nat := none)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM UnaryRequest := do
  let (method, timeout, deadline?) ← match trustedPreflight? with
    | none => do
        let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
        let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
        GrpcM.ofExcept (Headers.validateContentLength metadata body.size)
        pure (method, timeout, ← deadlineForTimeout timeout headerDeadline)
    | some preflight => do
        GrpcM.ofExcept (Headers.validateContentLengthValue preflight.contentLength body.size)
        pure (preflight.method, preflight.timeout, headerDeadline)
  let messages : Array Message ← GrpcM.ofExcept (Message.decodeAllWithLimit registry.maxReceiveMessageSize body)
  if messages.size != 1 then
    throw (Status.invalidArgument s!"unary request expected one message, got {messages.size}")
  let message : Message := messages[0]!
  if message.compressed != CompressionFlag.identity then
    throw (Status.unimplemented "compressed requests are not supported")
  pure {
    method := method,
    metadata := metadata,
    timeout := timeout,
    deadline := deadline?,
    data := message.data
  }

private def decodeClientStreamingRequest (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (headerDeadline : Option Nat := none)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM ClientStreamingRequest := do
  let (method, timeout, deadline?) ← match trustedPreflight? with
    | none => do
        let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
        let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
        GrpcM.ofExcept (Headers.validateContentLength metadata body.size)
        pure (method, timeout, ← deadlineForTimeout timeout headerDeadline)
    | some preflight => do
        GrpcM.ofExcept (Headers.validateContentLengthValue preflight.contentLength body.size)
        pure (preflight.method, preflight.timeout, headerDeadline)
  let messages : Array Message ← GrpcM.ofExcept (Message.decodeAllWithLimit registry.maxReceiveMessageSize body)
  for message in messages do
    if message.compressed != CompressionFlag.identity then
      throw (Status.unimplemented "compressed requests are not supported")
  pure {
    method := method,
    metadata := metadata,
    timeout := timeout,
    deadline := deadline?,
    messages := messages.map (fun message => message.data)
  }

private def decodeClientStreamingStreamRequest (metadata : Metadata)
    (messages : MessageStream ByteArray) (headerDeadline : Option Nat := none)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM (ClientStreamingStreamRequest × Option Nat) := do
  let (method, timeout, deadline?) ← match trustedPreflight? with
    | none => do
        let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
        let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
        pure (method, timeout, ← deadlineForTimeout timeout headerDeadline)
    | some preflight =>
        pure (preflight.method, preflight.timeout, headerDeadline)
  pure ({
    method := method,
    metadata := metadata,
    timeout := timeout,
    deadline := deadline?,
    messages := messages
  }, deadline?)

private def clientStreamingRequestOfStream (request : ClientStreamingStreamRequest) :
    GrpcM ClientStreamingRequest := do
  let messages ← request.messages.collect
  pure {
    method := request.method,
    metadata := request.metadata,
    timeout := request.timeout,
    deadline := request.deadline,
    messages := messages
  }

/-- Adapt an aggregate server-streaming handler to the incremental shape. -/
def streamHandlerOfServerStreaming (handler : ServerStreamingHandler) :
    ServerStreamingStreamHandler :=
  fun request => do streamResponseOfAggregate (← handler request)

/-- Adapt an aggregate client-streaming handler to the incremental shape. -/
def streamHandlerOfClientStreaming (handler : ClientStreamingHandler) :
    ClientStreamingStreamHandler :=
  fun request => do handler (← clientStreamingRequestOfStream request)

/-- Adapt an aggregate bidirectional-streaming handler to the incremental
shape. -/
def streamHandlerOfBidirectionalStreaming (handler : BidirectionalStreamingHandler) :
    BidirectionalStreamingStreamHandler :=
  fun request => do
    streamResponseOfAggregate (← handler (← clientStreamingRequestOfStream request))

private structure PreparedDispatch (α : Type) where
  deadline : Option Nat
  action : GrpcM α

private def runPreparedDispatchAsync (prepared : PreparedDispatch α)
    (cancelOnDeadline : IO Unit := pure ()) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status α) := do
  let result ← runWithDeadlineUntilAsync prepared.deadline prepared.action runtime?
  match result with
  | .error status =>
      if status.code == Code.deadlineExceeded then
        cancelOnDeadline
      pure (.error status)
  | .ok value => pure (.ok value)

private def runPreparedDispatch (prepared : PreparedDispatch α)
    (cancelOnDeadline : IO Unit := pure ()) : GrpcM α :=
  ExceptT.mk do
    let result ← (runWithDeadlineUntil prepared.deadline prepared.action).run
    match result with
    | .error status =>
        if status.code == Code.deadlineExceeded then
          cancelOnDeadline
        pure (.error status)
    | .ok value => pure (.ok value)

private def prepareUnaryDispatch (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option UnaryHandler) (headerDeadline : Option Nat)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM (PreparedDispatch UnaryResponse) := do
  let request ← decodeUnaryRequest registry metadata body headerDeadline trustedPreflight?
  let handler ← match handler? with
    | some handler => pure handler
    | none =>
        match registry.findUnary? request.method with
        | some handler => pure handler
        | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  pure {
    deadline := request.deadline,
    action := do
      let response ← handler request
      validateUnaryResponse registry response
  }

private def prepareServerStreamingStreamDispatch (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (handler? : Option ServerStreamingStreamHandler)
    (headerDeadline : Option Nat)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM (PreparedDispatch ServerStreamingStreamResponse) := do
  let request ← decodeUnaryRequest registry metadata body headerDeadline trustedPreflight?
  let handler ← match handler? with
    | some handler => pure handler
    | none =>
        match registry.findServerStreamingStream? request.method with
        | some handler => pure handler
        | none =>
            match registry.findServerStreaming? request.method with
            | some handler => pure (streamHandlerOfServerStreaming handler)
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  pure {
    deadline := request.deadline,
    action := do
      let response ← handler request
      validateServerStreamingStreamResponse registry response
  }

private def prepareClientStreamingDispatch (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray) (handler? : Option ClientStreamingStreamHandler)
    (headerDeadline : Option Nat)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM (PreparedDispatch UnaryResponse) := do
  let (request, deadline?) ←
    decodeClientStreamingStreamRequest metadata messages headerDeadline trustedPreflight?
  let handler ← match handler? with
    | some handler => pure handler
    | none =>
        match registry.findClientStreamingStream? request.method with
        | some handler => pure handler
        | none =>
            match registry.findClientStreaming? request.method with
            | some handler => pure (streamHandlerOfClientStreaming handler)
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  pure {
    deadline := deadline?,
    action := do
      let response ← handler request
      validateUnaryResponse registry response
  }

private def prepareBidirectionalStreamingDispatch (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray) (handler? : Option BidirectionalStreamingStreamHandler)
    (headerDeadline : Option Nat)
    (trustedPreflight? : Option Headers.RequestPreflight := none) :
    GrpcM (PreparedDispatch ServerStreamingStreamResponse) := do
  let (request, deadline?) ←
    decodeClientStreamingStreamRequest metadata messages headerDeadline trustedPreflight?
  let handler ← match handler? with
    | some handler => pure handler
    | none =>
        match registry.findBidirectionalStreamingStream? request.method with
        | some handler => pure handler
        | none =>
            match registry.findBidirectionalStreaming? request.method with
            | some handler => pure (streamHandlerOfBidirectionalStreaming handler)
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  pure {
    deadline := deadline?,
    action := do
      let response ← handler request
      validateServerStreamingStreamResponse registry response
  }

def dispatchUnary (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option UnaryHandler := none) (headerDeadline : Option Nat := none) :
    GrpcM UnaryResponse := do
  let prepared ← prepareUnaryDispatch registry metadata body handler? headerDeadline
  runPreparedDispatch prepared

/-- Async-native managed-server dispatch.  The no-deadline branch executes
inline; a timed call owns one cancellable handler task while a managed
transport supplies its shared deadline scheduler. -/
def dispatchUnaryAsync (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option UnaryHandler := none) (headerDeadline : Option Nat := none)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryResponse) := do
  match ← runHandler (prepareUnaryDispatch registry metadata body handler? headerDeadline) with
  | .error status => pure (.error status)
  | .ok prepared => runPreparedDispatchAsync prepared (runtime? := runtime?)

/-- Managed-transport dispatch for a request whose original metadata has
already produced the supplied preflight and authorized handler capability. -/
def dispatchManagedUnaryAsync (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (preflight : Headers.RequestPreflight) (handler : UnaryHandler)
    (deadline : Option Nat) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryResponse) := do
  match ← runHandler
      (prepareUnaryDispatch registry metadata body (some handler) deadline (some preflight)) with
  | .error status => pure (.error status)
  | .ok prepared => runPreparedDispatchAsync prepared (runtime? := runtime?)

def dispatchServerStreamingStream (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ServerStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM ServerStreamingStreamResponse := do
  let prepared ←
    prepareServerStreamingStreamDispatch registry metadata body handler? headerDeadline
  let response ← runPreparedDispatch prepared
  pure { response with messages := withDeadlineUntil prepared.deadline response.messages }

/-- Returns the unwrapped stream together with the one absolute deadline.  The
Async HTTP/2 encoder races each receive against that same instant. -/
def dispatchServerStreamingStreamAsync (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (handler? : Option ServerStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (ServerStreamingStreamResponse × Option Nat)) := do
  match ← runHandler <|
      prepareServerStreamingStreamDispatch registry metadata body handler? headerDeadline with
  | .error status => pure (.error status)
  | .ok prepared =>
      match ← runPreparedDispatchAsync prepared (runtime? := runtime?) with
      | .error status => pure (.error status)
      | .ok response => pure (.ok (response, prepared.deadline))

def dispatchManagedServerStreamingStreamAsync (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (preflight : Headers.RequestPreflight)
    (handler : ServerStreamingStreamHandler) (deadline : Option Nat)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (ServerStreamingStreamResponse × Option Nat)) := do
  match ← runHandler <|
      prepareServerStreamingStreamDispatch registry metadata body (some handler) deadline
        (some preflight) with
  | .error status => pure (.error status)
  | .ok prepared =>
      match ← runPreparedDispatchAsync prepared (runtime? := runtime?) with
      | .error status => pure (.error status)
      | .ok response => pure (.ok (response, prepared.deadline))

def dispatchServerStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ServerStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM ServerStreamingResponse := do
  let response ← registry.dispatchServerStreamingStream metadata body handler? headerDeadline
  collectServerStreamingStreamResponse response

def dispatchClientStreamingMessageStream (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray)
    (handler? : Option ClientStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM UnaryResponse := do
  let prepared ←
    prepareClientStreamingDispatch registry metadata messages handler? headerDeadline
  runPreparedDispatch prepared (cancelAfterDeadline messages)

def dispatchClientStreamingMessageStreamAsync (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray)
    (handler? : Option ClientStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryResponse) := do
  match ← runHandler <|
      prepareClientStreamingDispatch registry metadata messages handler? headerDeadline with
  | .error status => pure (.error status)
  | .ok prepared =>
      runPreparedDispatchAsync prepared (cancelAfterDeadline messages) runtime?

def dispatchManagedClientStreamingMessageStreamAsync (registry : Registry)
    (metadata : Metadata) (messages : MessageStream ByteArray)
    (preflight : Headers.RequestPreflight) (handler : ClientStreamingStreamHandler)
    (deadline : Option Nat) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryResponse) := do
  match ← runHandler <|
      prepareClientStreamingDispatch registry metadata messages (some handler) deadline
        (some preflight) with
  | .error status => pure (.error status)
  | .ok prepared =>
      runPreparedDispatchAsync prepared (cancelAfterDeadline messages) runtime?

def dispatchClientStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ClientStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM UnaryResponse := do
  let request ← decodeClientStreamingRequest registry metadata body headerDeadline
  let messages ← MessageStream.ofArray request.messages
  registry.dispatchClientStreamingMessageStream metadata messages handler? request.deadline

def dispatchClientStreamingAsync (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ClientStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryResponse) := do
  match ← runHandler (decodeClientStreamingRequest registry metadata body headerDeadline) with
  | .error status => pure (.error status)
  | .ok request =>
      match ← runHandler (MessageStream.ofArray request.messages) with
      | .error status => pure (.error status)
      | .ok messages =>
          registry.dispatchClientStreamingMessageStreamAsync
            metadata messages handler? request.deadline runtime?

def dispatchManagedClientStreamingAsync (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (preflight : Headers.RequestPreflight)
    (handler : ClientStreamingStreamHandler) (deadline : Option Nat)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryResponse) := do
  match ← runHandler
      (decodeClientStreamingRequest registry metadata body deadline (some preflight)) with
  | .error status => pure (.error status)
  | .ok request =>
      match ← runHandler (MessageStream.ofArray request.messages) with
      | .error status => pure (.error status)
      | .ok messages =>
          registry.dispatchManagedClientStreamingMessageStreamAsync
            metadata messages preflight handler deadline runtime?

def dispatchBidirectionalStreamingMessageStream (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray)
    (handler? : Option BidirectionalStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM ServerStreamingStreamResponse := do
  let prepared ←
    prepareBidirectionalStreamingDispatch registry metadata messages handler? headerDeadline
  let response ← runPreparedDispatch prepared (cancelAfterDeadline messages)
  let combinedMessages : MessageStream ByteArray := {
    recv? := response.messages.recv?,
    cancel := do
      response.messages.cancel
      messages.cancel
  }
  let responseMessages := withDeadlineUntil prepared.deadline combinedMessages
  pure {
    response with
    messages := responseMessages
  }

def dispatchBidirectionalStreamingMessageStreamAsync (registry : Registry)
    (metadata : Metadata) (messages : MessageStream ByteArray)
    (handler? : Option BidirectionalStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (ServerStreamingStreamResponse × Option Nat)) := do
  match ← runHandler <|
      prepareBidirectionalStreamingDispatch registry metadata messages handler? headerDeadline with
  | .error status => pure (.error status)
  | .ok prepared =>
      match ← runPreparedDispatchAsync prepared (cancelAfterDeadline messages) runtime? with
      | .error status => pure (.error status)
      | .ok response =>
          let response := {
            response with
            messages := {
              recv? := response.messages.recv?,
              cancel := do
                response.messages.cancel
                messages.cancel
            }
          }
          pure (.ok (response, prepared.deadline))

def dispatchManagedBidirectionalStreamingMessageStreamAsync (registry : Registry)
    (metadata : Metadata) (messages : MessageStream ByteArray)
    (preflight : Headers.RequestPreflight) (handler : BidirectionalStreamingStreamHandler)
    (deadline : Option Nat) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (ServerStreamingStreamResponse × Option Nat)) := do
  match ← runHandler <|
      prepareBidirectionalStreamingDispatch registry metadata messages (some handler) deadline
        (some preflight) with
  | .error status => pure (.error status)
  | .ok prepared =>
      match ← runPreparedDispatchAsync prepared (cancelAfterDeadline messages) runtime? with
      | .error status => pure (.error status)
      | .ok response =>
          let response := {
            response with
            messages := {
              recv? := response.messages.recv?,
              cancel := do
                response.messages.cancel
                messages.cancel
            }
          }
          pure (.ok (response, prepared.deadline))

def dispatchBidirectionalStreamingStream (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (handler? : Option BidirectionalStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM ServerStreamingStreamResponse := do
  let request ← decodeClientStreamingRequest registry metadata body headerDeadline
  let messages ← MessageStream.ofArray request.messages
  registry.dispatchBidirectionalStreamingMessageStream
    metadata messages handler? request.deadline

def dispatchBidirectionalStreamingStreamAsync (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (handler? : Option BidirectionalStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (ServerStreamingStreamResponse × Option Nat)) := do
  match ← runHandler (decodeClientStreamingRequest registry metadata body headerDeadline) with
  | .error status => pure (.error status)
  | .ok request =>
      match ← runHandler (MessageStream.ofArray request.messages) with
      | .error status => pure (.error status)
      | .ok messages =>
          registry.dispatchBidirectionalStreamingMessageStreamAsync
            metadata messages handler? request.deadline runtime?

def dispatchManagedBidirectionalStreamingStreamAsync (registry : Registry)
    (metadata : Metadata) (body : ByteArray) (preflight : Headers.RequestPreflight)
    (handler : BidirectionalStreamingStreamHandler) (deadline : Option Nat)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (ServerStreamingStreamResponse × Option Nat)) := do
  match ← runHandler
      (decodeClientStreamingRequest registry metadata body deadline (some preflight)) with
  | .error status => pure (.error status)
  | .ok request =>
      match ← runHandler (MessageStream.ofArray request.messages) with
      | .error status => pure (.error status)
      | .ok messages =>
          registry.dispatchManagedBidirectionalStreamingMessageStreamAsync
            metadata messages preflight handler deadline runtime?

def dispatchBidirectionalStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option BidirectionalStreamingStreamHandler := none)
    (headerDeadline : Option Nat := none) :
    GrpcM ServerStreamingResponse := do
  let response ←
    registry.dispatchBidirectionalStreamingStream metadata body handler? headerDeadline
  collectServerStreamingStreamResponse response

/-- Await one stream element without parking the managed server's dispatch
worker.  Expiry is reported immediately: the owner that turns this status into
a terminal response must publish that response before running arbitrary stream
cleanup.  The synchronous Registry streaming API retains its existing
cancel-before-return behavior through `withDeadlineUntil`. -/
def recvWithDeadlineUntilAsync (deadline? : Option Nat) (stream : MessageStream α)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (Option α)) :=
  runWithDeadlineUntilAsync deadline? stream.recv? runtime?

/-! ## Registry well-formedness -/

/-- The registered method names, in registration order. -/
def names (registry : Registry) : List MethodName :=
  registry.entries.toList.map MethodEntry.name

/-- A registry is well formed when no method name is registered twice, so
name lookup identifies a unique entry. -/
def WellFormed (registry : Registry) : Prop :=
  registry.names.Nodup

theorem empty_wellFormed : Registry.empty.WellFormed := by
  simp [WellFormed, names, empty]

/-- `registerChecked` succeeds exactly when the name is not yet registered. -/
theorem registerChecked_ok_elim {registry registry' : Registry} {entry : MethodEntry}
    (h : registry.registerChecked entry = .ok registry') :
    registry'.entries = registry.entries.push entry
      ∧ registry.findEntry? entry.name = none := by
  unfold registerChecked at h
  split at h
  next => cases h
  next hnone => cases h; exact ⟨rfl, hnone⟩


private theorem findEntry?_toList {registry : Registry} {name : MethodName} :
    registry.findEntry? name
      = registry.entries.toList.find? (fun entry => entry.name == name) := by
  simp [findEntry?, Array.find?_toList]

/-- Checked registration preserves well-formedness. -/
theorem registerChecked_wellFormed {registry registry' : Registry} {entry : MethodEntry}
    (hwf : registry.WellFormed) (h : registry.registerChecked entry = .ok registry') :
    registry'.WellFormed := by
  obtain ⟨hentries, hnone⟩ := registerChecked_ok_elim h
  rw [findEntry?_toList, List.find?_eq_none] at hnone
  simp only [WellFormed, names, hentries, Array.toList_push, List.map_append,
    List.map_cons, List.map_nil, List.nodup_append] at *
  refine ⟨hwf, by simp, ?_⟩
  intro a ha b hb
  simp only [List.mem_singleton] at hb
  subst hb
  simp only [List.mem_map] at ha
  obtain ⟨existing, hmem, hname⟩ := ha
  have := hnone existing hmem
  simp only [beq_iff_eq] at this
  exact hname ▸ this

private theorem mapEntries_names {registry : Registry} {f : MethodEntry -> MethodEntry}
    (hf : ∀ entry, (f entry).name = entry.name) :
    (registry.mapEntries f).names = registry.names := by
  simp only [names, mapEntries, Array.toList_map, List.map_map, Function.comp_def]
  exact List.map_congr_left fun entry _ => hf entry

/-- Mapping entries with a name-preserving `f` preserves well-formedness. -/
theorem mapEntries_wellFormed {registry : Registry} {f : MethodEntry -> MethodEntry}
    (hf : ∀ entry, (f entry).name = entry.name) (hwf : registry.WellFormed) :
    (registry.mapEntries f).WellFormed := by
  unfold WellFormed at hwf ⊢
  rw [mapEntries_names hf]
  exact hwf

/-- After successful checked registration, looking up the new name finds the
new entry. -/
theorem registerChecked_findEntry_self {registry registry' : Registry} {entry : MethodEntry}
    (h : registry.registerChecked entry = .ok registry') :
    registry'.findEntry? entry.name = some entry := by
  obtain ⟨hentries, hnone⟩ := registerChecked_ok_elim h
  rw [findEntry?_toList] at hnone ⊢
  rw [hentries, Array.toList_push, List.find?_append, hnone]
  simp

/-- Checked registration does not change lookups of other names. -/
theorem registerChecked_findEntry_other {registry registry' : Registry} {entry : MethodEntry}
    {name : MethodName} (h : registry.registerChecked entry = .ok registry')
    (hne : name ≠ entry.name) :
    registry'.findEntry? name = registry.findEntry? name := by
  obtain ⟨hentries, -⟩ := registerChecked_ok_elim h
  rw [findEntry?_toList, findEntry?_toList (registry := registry)]
  rw [hentries, Array.toList_push, List.find?_append]
  have hne' : (entry.name == name) = false := by
    simp [beq_eq_false_iff_ne, Ne.symm hne]
  have : [entry].find? (fun e => e.name == name) = none := by
    simp [List.find?, hne']
  rw [this, Option.or_none]

private theorem nodup_names_unique {l : List MethodEntry}
    (h : (l.map MethodEntry.name).Nodup) :
    ∀ e₁ ∈ l, ∀ e₂ ∈ l, e₁.name = e₂.name → e₁ = e₂ := by
  induction l with
  | nil => intro e₁ h₁; cases h₁
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at h
      obtain ⟨hhead, htail⟩ := h
      intro e₁ h₁ e₂ h₂ hname
      cases h₁ with
      | head =>
          cases h₂ with
          | head => rfl
          | tail _ h₂ =>
              exact absurd (List.mem_map.mpr ⟨e₂, h₂, hname.symm⟩) hhead
      | tail _ h₁ =>
          cases h₂ with
          | head =>
              exact absurd (List.mem_map.mpr ⟨e₁, h₁, hname⟩) hhead
          | tail _ h₂ => exact ih htail e₁ h₁ e₂ h₂ hname

/-- In a well-formed registry an entry is uniquely determined by its name. -/
theorem wellFormed_entry_unique {registry : Registry} {e₁ e₂ : MethodEntry}
    (hwf : registry.WellFormed) (h₁ : e₁ ∈ registry.entries)
    (h₂ : e₂ ∈ registry.entries) (hname : e₁.name = e₂.name) : e₁ = e₂ :=
  nodup_names_unique hwf e₁ (Array.mem_def.mp h₁) e₂ (Array.mem_def.mp h₂) hname

/-- In a well-formed registry, lookup of a registered entry's name finds
exactly that entry. -/
theorem wellFormed_findEntry_of_mem {registry : Registry} {entry : MethodEntry}
    (hwf : registry.WellFormed) (hmem : entry ∈ registry.entries) :
    registry.findEntry? entry.name = some entry := by
  rw [findEntry?_toList]
  have hmem' := Array.mem_def.mp hmem
  have hfound : ∃ found, registry.entries.toList.find?
      (fun e => e.name == entry.name) = some found := by
    match hf : registry.entries.toList.find? (fun e => e.name == entry.name) with
    | some found => exact ⟨found, hf⟩
    | none =>
        rw [List.find?_eq_none] at hf
        exact absurd (by simp : (entry.name == entry.name) = true) (hf entry hmem')
  obtain ⟨found, hf⟩ := hfound
  have hfmem : found ∈ registry.entries.toList := List.mem_of_find?_eq_some hf
  have hfname : found.name = entry.name := by
    have := List.find?_some hf
    simpa using this
  rw [hf]
  exact congrArg some (nodup_names_unique hwf found hfmem entry hmem' hfname)

end Registry

/--
View of a method entry as the dispatch family it belongs to, with the handler
carried at the family's incremental shape.  This is the single place where an
entry's shape is matched, so every dispatch path receives a handler whose
type already agrees with the wire protocol it drives.
-/
inductive DispatchHandler where
  | unary (handler : UnaryHandler)
  | serverStreaming (handler : ServerStreamingStreamHandler)
  | clientStreaming (handler : ClientStreamingStreamHandler)
  | bidirectionalStreaming (handler : BidirectionalStreamingStreamHandler)

/-- Classify an entry into its dispatch family, adapting aggregate handlers
to the family's incremental shape. -/
def MethodEntry.dispatchHandler (entry : MethodEntry) : DispatchHandler :=
  match entry with
  | { shape := .unary, handler, .. } => .unary handler
  | { shape := .serverStreaming, handler, .. } =>
      .serverStreaming (Registry.streamHandlerOfServerStreaming handler)
  | { shape := .serverStreamingStream, handler, .. } => .serverStreaming handler
  | { shape := .clientStreaming, handler, .. } =>
      .clientStreaming (Registry.streamHandlerOfClientStreaming handler)
  | { shape := .clientStreamingStream, handler, .. } => .clientStreaming handler
  | { shape := .bidirectionalStreaming, handler, .. } =>
      .bidirectionalStreaming (Registry.streamHandlerOfBidirectionalStreaming handler)
  | { shape := .bidirectionalStreamingStream, handler, .. } =>
      .bidirectionalStreaming handler

end Grpc
