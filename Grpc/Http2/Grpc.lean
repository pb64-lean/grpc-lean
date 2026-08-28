module

public import Grpc.Framing
public import Grpc.Protocol
public import Grpc.Server
public import Http2.Header

public section

namespace Grpc
namespace Http2
namespace Transport

/-- An aggregate request whose HTTP/2 field decoding, stream validation, and
authorization have already completed. -/
structure ManagedRequest where
  streamId : Nat
  metadata : _root_.Http2.Headers
  body : ByteArray
  deadline : Option Nat

/-- Application-level result of validating and resolving request headers.
This contains no compression or frame state; the connection owner performs all
HTTP/2 output transitions after the decision is known. -/
inductive RequestPreflightDecision where
  | accept (entry : MethodEntry) (preflight : Headers.RequestPreflight)
  | rejectGrpc (status : Status)
  | rejectHttp (statusCode : String)

/-- Validate request headers and resolve their method without performing an
HTTP/2 output transition. -/
def preflightRequest (registry : Registry) (metadata : _root_.Http2.Headers) :
    RequestPreflightDecision :=
  match Headers.validateRequestHeaderPreflight metadata with
  | .unsupportedContentType => .rejectHttp "415"
  | .reject status => .rejectGrpc status
  | .accept preflight =>
      match registry.findEntry? preflight.method with
      | some entry => .accept entry preflight
      | none => .rejectGrpc
          (Status.unimplemented s!"unknown gRPC method {preflight.method.path}")

/-- A managed handler result before HTTP/2 encoding. -/
inductive ManagedResponse where
  | unary (response : UnaryResponse)
  | streaming (response : ServerStreamingStreamResponse) (deadline : Option Nat)

/-- Dispatch an already validated and authorized aggregate request. The result
remains at the gRPC application layer; the connection that owns the HTTP/2
state performs header compression, framing, and flow control. -/
def dispatchManagedRequestWithAsync (registry : Registry) (request : ManagedRequest)
    (entry : MethodEntry) (preflight : Headers.RequestPreflight)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status ManagedResponse) := do
  let unaryError (status : Status) : ManagedResponse :=
    .unary { status := status, data := ByteArray.empty }
  let emptyStreaming (status : Status) : ManagedResponse :=
    .streaming { messages := { recv? := pure none }, status := status } none
  match entry.dispatchHandler with
  | .unary handler =>
      match ← registry.dispatchManagedUnaryTransportBodyAsync request.metadata
          request.body preflight handler request.deadline runtime? with
      | .ok response => pure (.ok (.unary response))
      | .error status => pure (.ok (unaryError status))
  | .serverStreaming handler =>
      match Message.decompressBody preflight.requestUsesGzip
          registry.maxReceiveMessageSize request.body with
      | .error status => pure (.ok (unaryError status))
      | .ok body =>
          match ← registry.dispatchManagedServerStreamingStreamAsync
              request.metadata body preflight handler request.deadline runtime? with
          | .ok (response, deadline) => pure (.ok (.streaming response deadline))
          | .error status => pure (.ok (emptyStreaming status))
  | .clientStreaming handler =>
      match Message.decompressBody preflight.requestUsesGzip
          registry.maxReceiveMessageSize request.body with
      | .error status => pure (.ok (unaryError status))
      | .ok body =>
          match ← registry.dispatchManagedClientStreamingAsync request.metadata body
              preflight handler request.deadline runtime? with
          | .ok response => pure (.ok (.unary response))
          | .error status => pure (.ok (unaryError status))
  | .bidirectionalStreaming handler =>
      match Message.decompressBody preflight.requestUsesGzip
          registry.maxReceiveMessageSize request.body with
      | .error status => pure (.ok (unaryError status))
      | .ok body =>
          match ← registry.dispatchManagedBidirectionalStreamingStreamAsync
              request.metadata body preflight handler request.deadline runtime? with
          | .ok (response, deadline) => pure (.ok (.streaming response deadline))
          | .error status => pure (.ok (emptyStreaming status))

end Transport
end Http2
end Grpc
