# Protocol architecture

`grpc-lean` implements the gRPC wire protocol over a pure-Lean HTTP/2 stack.
It does not use `Std.Http` as its protocol layer because `Std.Http` implements
HTTP/1.1, while gRPC uses HTTP/2 HEADERS, DATA, and trailers. HTTP/2 DATA frame
boundaries are independent of gRPC message boundaries, so the message decoder
maintains its own buffer across frames.

## Layering

1. **HTTP/2 transport**

   `Grpc.Http2.Frame`, `Grpc.Http2.Hpack`, and `Grpc.Http2.Connection` provide
   the connection preface, SETTINGS negotiation, frame codecs, HPACK,
   multiplexed stream state, and connection- and stream-level flow control.
   The transport supports prior-knowledge h2c and TLS 1.3 with ALPN `h2`.

2. **gRPC protocol**

   The request path validates `:method`, `:path`, `content-type`, `te`, and
   gRPC metadata. `Grpc.Framing` decodes and encodes the five-byte gRPC message
   prefix and reassembles messages across arbitrary DATA-frame boundaries.
   Responses consist of HTTP/2 headers, framed DATA messages, and final
   trailers carrying `grpc-status` and optional `grpc-message`.

3. **Status, metadata, and deadlines**

   The runtime implements ASCII metadata, base64-encoded `-bin` metadata,
   percent-encoded status messages, trailers-only failures, `grpc-timeout`,
   cancellation, and exception-to-status mapping.

4. **Generated service bindings**

   `lean_proto_library` generates typed Lean message and service bindings.
   Each service exposes handlers for unary, server-streaming, client-streaming,
   and bidirectional RPCs, plus registration and codec wrappers keyed by the
   fully qualified `/package.Service/Method` path.

5. **Streaming and compression**

   Batched and incremental `MessageStream` APIs cover all four RPC shapes with
   backpressure, half-close handling, cancellation, and deadline propagation.
   Identity and gzip encoding operate per gRPC message rather than across the
   HTTP/2 stream.

6. **Server integration and validation**

   `Grpc.Server` owns the async TCP/TLS connection lifecycle and dispatches
   requests through `Grpc.Registry`. The repository test suite covers frame
   fragmentation, trailers-only responses, deadlines, binary metadata,
   message limits, streaming, h2c, TLS, and interoperability with grpcurl.

The exact supported surface, validation contract, assurance boundary, and
known limitations are documented in [README.md](README.md).
