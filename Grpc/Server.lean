module

public import Grpc.Protocol

public section

namespace Grpc

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
  requestHeaderAuthorizer : RequestHeaderAuthorizer := fun entry _ =>
    pure (.accept entry.handler)
  entries : Array MethodEntry := #[]

namespace Registry

def empty : Registry := {}

def withMaxReceiveMessageSize (registry : Registry) (size : Nat) : Registry :=
  { registry with maxReceiveMessageSize := some size }

def withMaxSendMessageSize (registry : Registry) (size : Nat) : Registry :=
  { registry with maxSendMessageSize := some size }

/-- Install the callback that authorizes complete request headers. -/
def withRequestHeaderAuthorizer (registry : Registry)
    (authorizer : RequestHeaderAuthorizer) : Registry :=
  { registry with requestHeaderAuthorizer := authorizer }

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

private def maxDeadlineSleepChunkMilliseconds : Nat := 50

private partial def sleepUntilDeadline (remainingMilliseconds : Nat) : IO Unit := do
  if remainingMilliseconds == 0 then
    pure ()
  else if ← IO.checkCanceled then
    pure ()
  else
    let chunk := Nat.min remainingMilliseconds maxDeadlineSleepChunkMilliseconds
    IO.sleep (UInt32.ofNat chunk)
    sleepUntilDeadline (remainingMilliseconds - chunk)

private def deadlineFromNow? : Option Timeout -> IO (Option Nat)
  | none => pure none
  | some timeout => do
      let now ← IO.monoNanosNow
      pure (some (now + timeout.toNanoseconds))

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

private def runWithDeadlineUntil (deadline? : Option Nat) (action : GrpcM α) : GrpcM α :=
  match deadline? with
  | none => ExceptT.mk (runHandler action)
  | some deadline =>
      ExceptT.mk do
        let remainingMilliseconds ← remainingUntilDeadlineMilliseconds deadline
        if remainingMilliseconds == 0 then
          return .error (Status.deadlineExceeded "gRPC deadline exceeded")
        let handlerTask ← IO.asTask do
          let result ← runHandler action
          pure (DeadlineResult.completed result)
        let deadlineTask ← IO.asTask do
          sleepUntilDeadline remainingMilliseconds
          pure (DeadlineResult.expired : DeadlineResult α)
        match (← IO.waitAny [handlerTask, deadlineTask]) with
        | .error err =>
            IO.cancel handlerTask
            IO.cancel deadlineTask
            pure (.error (Status.ofIOError err))
        | .ok (.completed result) =>
            IO.cancel deadlineTask
            if ← deadlineExceededAt deadline then
              pure (.error (Status.deadlineExceeded "gRPC deadline exceeded"))
            else
              pure result
        | .ok .expired =>
            IO.cancel handlerTask
            pure (.error (Status.deadlineExceeded "gRPC deadline exceeded"))

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

private def decodeUnaryRequest (registry : Registry) (metadata : Metadata) (body : ByteArray) :
    GrpcM UnaryRequest := do
  let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
  let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
  GrpcM.ofExcept (Headers.validateContentLength metadata body.size)
  let messages : Array Message ← GrpcM.ofExcept (Message.decodeAllWithLimit registry.maxReceiveMessageSize body)
  if messages.size != 1 then
    throw (Status.invalidArgument s!"unary request expected one message, got {messages.size}")
  let message : Message := messages[0]!
  if message.compressed != CompressionFlag.identity then
    throw (Status.unimplemented "compressed requests are not supported")
  let deadline? ← deadlineFromNow? timeout
  pure {
    method := method,
    metadata := metadata,
    timeout := timeout,
    deadline := deadline?,
    data := message.data
  }

private def decodeClientStreamingRequest (registry : Registry) (metadata : Metadata) (body : ByteArray) :
    GrpcM ClientStreamingRequest := do
  let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
  let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
  GrpcM.ofExcept (Headers.validateContentLength metadata body.size)
  let messages : Array Message ← GrpcM.ofExcept (Message.decodeAllWithLimit registry.maxReceiveMessageSize body)
  for message in messages do
    if message.compressed != CompressionFlag.identity then
      throw (Status.unimplemented "compressed requests are not supported")
  let deadline? ← deadlineFromNow? timeout
  pure {
    method := method,
    metadata := metadata,
    timeout := timeout,
    deadline := deadline?,
    messages := messages.map (fun message => message.data)
  }

private def decodeClientStreamingStreamRequest (metadata : Metadata)
    (messages : MessageStream ByteArray) :
    GrpcM (ClientStreamingStreamRequest × Option Nat) := do
  let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
  let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
  let deadline? ← deadlineFromNow? timeout
  pure ({
    method := method,
    metadata := metadata,
    timeout := timeout,
    deadline := deadline?,
    messages := withDeadlineUntil deadline? messages
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

def dispatchUnary (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option UnaryHandler := none) :
    GrpcM UnaryResponse := do
  let request ← decodeUnaryRequest registry metadata body
  let handler ← match handler? with
    | some handler => pure handler
    | none =>
        match registry.findUnary? request.method with
        | some handler => pure handler
        | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  -- Enforce the same instant the handler is told about, so
  -- `request.deadline` is authoritative for propagation.
  let response ← runWithDeadlineUntil request.deadline (handler request)
  validateUnaryResponse registry response

def dispatchServerStreamingStream (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ServerStreamingStreamHandler := none) :
    GrpcM ServerStreamingStreamResponse := do
  let request ← decodeUnaryRequest registry metadata body
  let deadline? := request.deadline
  let response ← match handler? with
    | some handler => runWithDeadlineUntil deadline? (handler request)
    | none =>
        match registry.findServerStreamingStream? request.method with
        | some handler =>
            runWithDeadlineUntil deadline? (handler request)
        | none =>
            match registry.findServerStreaming? request.method with
            | some handler => do
                let response ← runWithDeadlineUntil deadline? (handler request)
                streamResponseOfAggregate response
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  validateServerStreamingStreamResponse registry {
    response with
    messages := withDeadlineUntil deadline? response.messages
  }

def dispatchServerStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ServerStreamingStreamHandler := none) :
    GrpcM ServerStreamingResponse := do
  let response ← registry.dispatchServerStreamingStream metadata body handler?
  collectServerStreamingStreamResponse response

def dispatchClientStreamingMessageStream (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray)
    (handler? : Option ClientStreamingStreamHandler := none) :
    GrpcM UnaryResponse := do
  let (request, deadline?) ← decodeClientStreamingStreamRequest metadata messages
  let response ← match handler? with
    | some handler => runWithDeadlineUntil deadline? (handler request)
    | none =>
        match registry.findClientStreamingStream? request.method with
        | some handler =>
            runWithDeadlineUntil deadline? (handler request)
        | none =>
            match registry.findClientStreaming? request.method with
            | some handler => do
                let aggregateRequest ← clientStreamingRequestOfStream request
                runWithDeadlineUntil deadline? (handler aggregateRequest)
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  validateUnaryResponse registry response

def dispatchClientStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option ClientStreamingStreamHandler := none) :
    GrpcM UnaryResponse := do
  let request ← decodeClientStreamingRequest registry metadata body
  let messages ← MessageStream.ofArray request.messages
  registry.dispatchClientStreamingMessageStream metadata messages handler?

def dispatchBidirectionalStreamingMessageStream (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray)
    (handler? : Option BidirectionalStreamingStreamHandler := none) :
    GrpcM ServerStreamingStreamResponse := do
  let (request, deadline?) ← decodeClientStreamingStreamRequest metadata messages
  let response ← match handler? with
    | some handler => runWithDeadlineUntil deadline? (handler request)
    | none =>
        match registry.findBidirectionalStreamingStream? request.method with
        | some handler =>
            runWithDeadlineUntil deadline? (handler request)
        | none =>
            match registry.findBidirectionalStreaming? request.method with
            | some handler => do
                let aggregateRequest ← clientStreamingRequestOfStream request
                let response ← runWithDeadlineUntil deadline? (handler aggregateRequest)
                streamResponseOfAggregate response
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
  validateServerStreamingStreamResponse registry {
    response with
    messages := withDeadlineUntil deadline? response.messages
  }

def dispatchBidirectionalStreamingStream (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (handler? : Option BidirectionalStreamingStreamHandler := none) :
    GrpcM ServerStreamingStreamResponse := do
  let request ← decodeClientStreamingRequest registry metadata body
  let messages ← MessageStream.ofArray request.messages
  registry.dispatchBidirectionalStreamingMessageStream metadata messages handler?

def dispatchBidirectionalStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (handler? : Option BidirectionalStreamingStreamHandler := none) :
    GrpcM ServerStreamingResponse := do
  let response ← registry.dispatchBidirectionalStreamingStream metadata body handler?
  collectServerStreamingStreamResponse response

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
