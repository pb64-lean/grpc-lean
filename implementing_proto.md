Standard gRPC still needs an HTTP/2 server. Std.Http helps with async server structure, TCP handling, cancellation, and handler patterns, but
its current server/protocol implementation is explicitly HTTP/1.1/H1, while gRPC’s wire protocol is defined over HTTP/2
HEADERS/DATA/trailers. The gRPC spec also makes a key point: HTTP/2 DATA frame boundaries do not align with gRPC message boundaries, so this
cannot be treated as “HTTP body chunks are protobuf messages.” (raw.githubusercontent.com
(https://raw.githubusercontent.com/leanprover/lean4/master/src/Std/Http/Server.lean)) (raw.githubusercontent.com
(https://raw.githubusercontent.com/leanprover/lean4/master/src/Std/Http/Protocol/H1.lean)) (github.com
(https://github.com/grpc/grpc/blob/master/doc/PROTOCOL-HTTP2.md))

Remaining components, in practical order:

1. HTTP/2 transport in Lean
    - Connection preface and SETTINGS negotiation.
    - Frame parser/writer: HEADERS, CONTINUATION, DATA, RST_STREAM, WINDOW_UPDATE, PING, GOAWAY.
    - HPACK header compression/decompression.
    - Per-stream state machine and multiplexing.
    - Flow control at connection and stream levels.
    - Cleartext h2c first is probably the fastest validation path; TLS + ALPN can come later unless production interoperability is required
      immediately.

2. gRPC protocol layer
    - Validate request headers: :method POST, :path /pkg.Service/Method, content-type: application/grpc or application/grpc+proto, te:
      trailers.

    - Parse grpc-timeout into Lean cancellation/deadline handling.
    - Decode/encode the 5-byte gRPC message prefix: compression flag + big-endian message length.
    - Reassemble gRPC messages across arbitrary HTTP/2 DATA frames.
    - Emit response headers, DATA messages, and final trailers with grpc-status and optional grpc-message.

3. Metadata and status runtime
    - ASCII metadata and -bin binary metadata with base64 rules.
    - Percent encoding/decoding for grpc-message.
    - Lean representation of gRPC status codes.
    - Mapping Lean exceptions/cancellations/deadlines to gRPC status.
    - Support trailers-only responses for early failures.

4. Generated service bindings
    - Extend the pure-Lean protoc-gen-lean4 path beyond message generation to service generation.
    - Generate a Lean server interface per service, with methods for unary and streaming shapes.
    - Generate registration/dispatch tables keyed by /fully.qualified.Service/Method.
    - Generate codec wrappers that decode request protobuf bytes, call typed Lean handlers, and encode response protobuf bytes.

5. Streaming abstractions
    - Unary is the MVP.
    - Then server-streaming, client-streaming, and bidirectional streaming.
    - Need a stream API over Async/channels with backpressure, cancellation, half-close handling, and deadline propagation.

6. Compression
    - identity support is required.
    - gzip is the likely first optional codec for compatibility.
    - Compression is per gRPC message, not across the whole stream.

7. Server integration
    - A pure Lean Grpc.Server analogous to Std.Http.Server, but backed by an HTTP/2 connection machine instead of H1.
    - Reuse Std.Async, TCP, cancellation, and possibly transport/body concepts where they fit.
    - Keep service transport and dispatch entirely in Lean.

8. Validation
    - A new pure Lean server example using lean_proto_library.
    - Interop tests with a standard gRPC client, probably grpcurl -plaintext against h2c first.
    - Tests for fragmented DATA frames, trailers-only errors, deadlines, binary metadata, and message size limits.

The MVP I’d target is: HTTP/2 h2c server + unary gRPC + pure Lean generated service stubs + one example callable by grpcurl -plaintext.
Streaming, TLS/ALPN, gzip, and richer status details can follow once unary interop is solid.
