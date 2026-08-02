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

/--
The result of authorizing a completed request header block.  An authorizer may
simply accept the registry's normal handler, or return a handler capability
that captures authorization state resolved from those headers.  Capturing the
state in a handler avoids global/task-local side channels and ensures dispatch
uses the exact object that was authorized before the request body was read.
-/
inductive HeaderAuthorization where
  | accept
  | unary (handler : UnaryHandler)
  | serverStreaming (handler : ServerStreamingHandler)
  | serverStreamingStream (handler : ServerStreamingStreamHandler)
  | clientStreaming (handler : ClientStreamingHandler)
  | clientStreamingStream (handler : ClientStreamingStreamHandler)
  | bidirectionalStreaming (handler : BidirectionalStreamingHandler)
  | bidirectionalStreamingStream (handler : BidirectionalStreamingStreamHandler)
  deriving Inhabited

/--
Request-header authorization runs after gRPC method/header validation and
before request DATA is accumulated or framed.  It may perform `IO` (for
example, a mutex-protected live-session lookup); callers should keep it
bounded because the connection preserves request ordering while it runs.
-/
abbrev RequestHeaderAuthorizer :=
  MethodName -> Metadata -> GrpcM HeaderAuthorization

structure ServiceMethod where
  name : MethodName
  unary : UnaryHandler

structure ServerStreamingMethod where
  name : MethodName
  stream : ServerStreamingHandler

structure ServerStreamingStreamMethod where
  name : MethodName
  stream : ServerStreamingStreamHandler

structure ClientStreamingMethod where
  name : MethodName
  collect : ClientStreamingHandler

structure ClientStreamingStreamMethod where
  name : MethodName
  stream : ClientStreamingStreamHandler

structure BidirectionalStreamingMethod where
  name : MethodName
  bidi : BidirectionalStreamingHandler

structure BidirectionalStreamingStreamMethod where
  name : MethodName
  bidi : BidirectionalStreamingStreamHandler

structure Registry where
  maxReceiveMessageSize : Option Nat := none
  maxSendMessageSize : Option Nat := none
  requestHeaderAuthorizer : RequestHeaderAuthorizer := fun _ _ => pure .accept
  methods : Array ServiceMethod := #[]
  serverStreamingMethods : Array ServerStreamingMethod := #[]
  serverStreamingStreamMethods : Array ServerStreamingStreamMethod := #[]
  clientStreamingMethods : Array ClientStreamingMethod := #[]
  clientStreamingStreamMethods : Array ClientStreamingStreamMethod := #[]
  bidirectionalStreamingMethods : Array BidirectionalStreamingMethod := #[]
  bidirectionalStreamingStreamMethods : Array BidirectionalStreamingStreamMethod := #[]

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

def authorizeRequestHeaders (registry : Registry) (method : MethodName)
    (metadata : Metadata) : GrpcM HeaderAuthorization :=
  registry.requestHeaderAuthorizer method metadata

def registerUnary (registry : Registry) (name : MethodName) (handler : UnaryHandler) : Registry :=
  { registry with methods := registry.methods.push { name := name, unary := handler } }

def registerServerStreaming (registry : Registry) (name : MethodName)
    (handler : ServerStreamingHandler) : Registry :=
  {
    registry with
    serverStreamingMethods := registry.serverStreamingMethods.push { name := name, stream := handler }
  }

def registerServerStreamingStream (registry : Registry) (name : MethodName)
    (handler : ServerStreamingStreamHandler) : Registry :=
  {
    registry with
    serverStreamingStreamMethods :=
      registry.serverStreamingStreamMethods.push { name := name, stream := handler }
  }

def registerClientStreaming (registry : Registry) (name : MethodName)
    (handler : ClientStreamingHandler) : Registry :=
  {
    registry with
    clientStreamingMethods := registry.clientStreamingMethods.push { name := name, collect := handler }
  }

def registerClientStreamingStream (registry : Registry) (name : MethodName)
    (handler : ClientStreamingStreamHandler) : Registry :=
  {
    registry with
    clientStreamingStreamMethods :=
      registry.clientStreamingStreamMethods.push { name := name, stream := handler }
  }

def registerBidirectionalStreaming (registry : Registry) (name : MethodName)
    (handler : BidirectionalStreamingHandler) : Registry :=
  {
    registry with
    bidirectionalStreamingMethods :=
      registry.bidirectionalStreamingMethods.push { name := name, bidi := handler }
  }

def registerBidirectionalStreamingStream (registry : Registry) (name : MethodName)
    (handler : BidirectionalStreamingStreamHandler) : Registry :=
  {
    registry with
    bidirectionalStreamingStreamMethods :=
      registry.bidirectionalStreamingStreamMethods.push { name := name, bidi := handler }
  }

def registerUnaryCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedUnaryHandler α β) : Registry :=
  registry.registerUnary name fun request => do
    let input ← GrpcM.ofExcept <|
      match decode request.data with
      | .ok value => .ok value
      | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let output ← handler input
    let data ← GrpcM.ofExcept <|
      match encode output with
      | .ok value => .ok value
      | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      data := data,
      status := Status.ok
    }

def registerServerStreamingCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedServerStreamingHandler α β) : Registry :=
  registry.registerServerStreaming name fun request => do
    let input ← GrpcM.ofExcept <|
      match decode request.data with
      | .ok value => .ok value
      | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler input
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

def registerServerStreamingStreamCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedServerStreamingStreamHandler α β) : Registry :=
  registry.registerServerStreamingStream name fun request => do
    let input ← GrpcM.ofExcept <|
      match decode request.data with
      | .ok value => .ok value
      | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler input
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

def registerClientStreamingCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedClientStreamingHandler α β) : Registry :=
  registry.registerClientStreaming name fun request => do
    let inputs ← request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let output ← handler inputs
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
  registry.registerClientStreamingStream name fun request => do
    let inputs := request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let output ← handler inputs
    let data ← GrpcM.ofExcept <|
      match encode output with
      | .ok value => .ok value
      | .error err => .error (Status.internal s!"failed to encode response: {err}")
    pure {
      metadata := Metadata.empty,
      data := data,
      status := Status.ok
    }

def registerBidirectionalStreamingCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedBidirectionalStreamingHandler α β) : Registry :=
  registry.registerBidirectionalStreaming name fun request => do
    let inputs ← request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler inputs
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

def registerBidirectionalStreamingStreamCodec [ToString ε] (registry : Registry) (name : MethodName)
    (decode : ByteArray -> Except ε α) (encode : β -> Except ε ByteArray)
    (handler : TypedBidirectionalStreamingStreamHandler α β) : Registry :=
  registry.registerBidirectionalStreamingStream name fun request => do
    let inputs := request.messages.mapM fun message =>
      GrpcM.ofExcept <|
        match decode message with
        | .ok value => .ok value
        | .error err => .error (Status.invalidArgument s!"failed to decode request: {err}")
    let outputs ← handler inputs
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

def findUnary? (registry : Registry) (name : MethodName) : Option UnaryHandler :=
  registry.methods.findSome? fun method =>
    if method.name == name then some method.unary else none

def findServerStreaming? (registry : Registry) (name : MethodName) : Option ServerStreamingHandler :=
  registry.serverStreamingMethods.findSome? fun method =>
    if method.name == name then some method.stream else none

def findServerStreamingStream? (registry : Registry) (name : MethodName) :
    Option ServerStreamingStreamHandler :=
  registry.serverStreamingStreamMethods.findSome? fun method =>
    if method.name == name then some method.stream else none

def findClientStreaming? (registry : Registry) (name : MethodName) : Option ClientStreamingHandler :=
  registry.clientStreamingMethods.findSome? fun method =>
    if method.name == name then some method.collect else none

def findClientStreamingStream? (registry : Registry) (name : MethodName) :
    Option ClientStreamingStreamHandler :=
  registry.clientStreamingStreamMethods.findSome? fun method =>
    if method.name == name then some method.stream else none

def findBidirectionalStreaming? (registry : Registry) (name : MethodName) :
    Option BidirectionalStreamingHandler :=
  registry.bidirectionalStreamingMethods.findSome? fun method =>
    if method.name == name then some method.bidi else none

def findBidirectionalStreamingStream? (registry : Registry) (name : MethodName) :
    Option BidirectionalStreamingStreamHandler :=
  registry.bidirectionalStreamingStreamMethods.findSome? fun method =>
    if method.name == name then some method.bidi else none

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

private def runWithDeadline (timeout? : Option Timeout) (action : GrpcM α) : GrpcM α :=
  ExceptT.mk do
    let deadline? ← deadlineFromNow? timeout?
    (runWithDeadlineUntil deadline? action).run

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
  pure { method := method, metadata := metadata, timeout := timeout, data := message.data }

private def decodeClientStreamingRequest (registry : Registry) (metadata : Metadata) (body : ByteArray) :
    GrpcM ClientStreamingRequest := do
  let method ← GrpcM.ofExcept (Headers.validateUnaryRequestHeaders metadata)
  let timeout ← GrpcM.ofExcept (Headers.timeout? metadata)
  GrpcM.ofExcept (Headers.validateContentLength metadata body.size)
  let messages : Array Message ← GrpcM.ofExcept (Message.decodeAllWithLimit registry.maxReceiveMessageSize body)
  for message in messages do
    if message.compressed != CompressionFlag.identity then
      throw (Status.unimplemented "compressed requests are not supported")
  pure {
    method := method,
    metadata := metadata,
    timeout := timeout,
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
    messages := withDeadlineUntil deadline? messages
  }, deadline?)

private def clientStreamingRequestOfStream (request : ClientStreamingStreamRequest) :
    GrpcM ClientStreamingRequest := do
  let messages ← request.messages.collect
  pure {
    method := request.method,
    metadata := request.metadata,
    timeout := request.timeout,
    messages := messages
  }

private def authorizationShapeMismatch (method : MethodName) : Status :=
  Status.internal s!"request-header authorizer selected an incompatible handler for {method.path}"

def dispatchUnary (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (authorization : HeaderAuthorization := .accept) :
    GrpcM UnaryResponse := do
  let request ← decodeUnaryRequest registry metadata body
  let handler ← match authorization with
    | .accept =>
        match registry.findUnary? request.method with
        | some handler => pure handler
        | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
    | .unary handler => pure handler
    | _ => throw (authorizationShapeMismatch request.method)
  let response ← runWithDeadline request.timeout (handler request)
  validateUnaryResponse registry response

def dispatchServerStreamingStream (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (authorization : HeaderAuthorization := .accept) :
    GrpcM ServerStreamingStreamResponse := do
  let request ← decodeUnaryRequest registry metadata body
  let deadline? ← deadlineFromNow? request.timeout
  let response ← match authorization with
    | .accept =>
        match registry.findServerStreamingStream? request.method with
        | some handler =>
            runWithDeadlineUntil deadline? (handler request)
        | none =>
            match registry.findServerStreaming? request.method with
            | some handler => do
                let response ← runWithDeadlineUntil deadline? (handler request)
                streamResponseOfAggregate response
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
    | .serverStreamingStream handler =>
        runWithDeadlineUntil deadline? (handler request)
    | .serverStreaming handler => do
        let response ← runWithDeadlineUntil deadline? (handler request)
        streamResponseOfAggregate response
    | _ => throw (authorizationShapeMismatch request.method)
  validateServerStreamingStreamResponse registry {
    response with
    messages := withDeadlineUntil deadline? response.messages
  }

def dispatchServerStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (authorization : HeaderAuthorization := .accept) :
    GrpcM ServerStreamingResponse := do
  let response ← registry.dispatchServerStreamingStream metadata body authorization
  collectServerStreamingStreamResponse response

def dispatchClientStreamingMessageStream (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray) (authorization : HeaderAuthorization := .accept) :
    GrpcM UnaryResponse := do
  let (request, deadline?) ← decodeClientStreamingStreamRequest metadata messages
  let response ← match authorization with
    | .accept =>
        match registry.findClientStreamingStream? request.method with
        | some handler =>
            runWithDeadlineUntil deadline? (handler request)
        | none =>
            match registry.findClientStreaming? request.method with
            | some handler => do
                let aggregateRequest ← clientStreamingRequestOfStream request
                runWithDeadlineUntil deadline? (handler aggregateRequest)
            | none => throw (Status.unimplemented s!"unknown gRPC method {request.method.path}")
    | .clientStreamingStream handler =>
        runWithDeadlineUntil deadline? (handler request)
    | .clientStreaming handler => do
        let aggregateRequest ← clientStreamingRequestOfStream request
        runWithDeadlineUntil deadline? (handler aggregateRequest)
    | _ => throw (authorizationShapeMismatch request.method)
  validateUnaryResponse registry response

def dispatchClientStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (authorization : HeaderAuthorization := .accept) :
    GrpcM UnaryResponse := do
  let request ← decodeClientStreamingRequest registry metadata body
  let messages ← MessageStream.ofArray request.messages
  registry.dispatchClientStreamingMessageStream metadata messages authorization

def dispatchBidirectionalStreamingMessageStream (registry : Registry) (metadata : Metadata)
    (messages : MessageStream ByteArray) (authorization : HeaderAuthorization := .accept) :
    GrpcM ServerStreamingStreamResponse := do
  let (request, deadline?) ← decodeClientStreamingStreamRequest metadata messages
  let response ← match authorization with
    | .accept =>
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
    | .bidirectionalStreamingStream handler =>
        runWithDeadlineUntil deadline? (handler request)
    | .bidirectionalStreaming handler => do
        let aggregateRequest ← clientStreamingRequestOfStream request
        let response ← runWithDeadlineUntil deadline? (handler aggregateRequest)
        streamResponseOfAggregate response
    | _ => throw (authorizationShapeMismatch request.method)
  validateServerStreamingStreamResponse registry {
    response with
    messages := withDeadlineUntil deadline? response.messages
  }

def dispatchBidirectionalStreamingStream (registry : Registry) (metadata : Metadata)
    (body : ByteArray) (authorization : HeaderAuthorization := .accept) :
    GrpcM ServerStreamingStreamResponse := do
  let request ← decodeClientStreamingRequest registry metadata body
  let messages ← MessageStream.ofArray request.messages
  registry.dispatchBidirectionalStreamingMessageStream metadata messages authorization

def dispatchBidirectionalStreaming (registry : Registry) (metadata : Metadata) (body : ByteArray)
    (authorization : HeaderAuthorization := .accept) :
    GrpcM ServerStreamingResponse := do
  let response ← registry.dispatchBidirectionalStreamingStream metadata body authorization
  collectServerStreamingStreamResponse response

end Registry

end Grpc
