# grpc-lean

[![CI](https://github.com/pb64-lean/grpc-lean/actions/workflows/ci.yml/badge.svg?branch=main)](https://github.com/pb64-lean/grpc-lean/actions/workflows/ci.yml) [![Assurance](https://github.com/pb64-lean/grpc-lean/actions/workflows/assurance.yml/badge.svg?branch=main)](https://github.com/pb64-lean/grpc-lean/actions/workflows/assurance.yml)

Protocol Buffers and gRPC for Lean 4: a pure-Lean gRPC client/server runtime
over HTTP/2, protobuf codegen wired into Bazel, TLS 1.3 termination via the
sibling [`tls13-lean`](https://github.com/pb64-lean/tls13-lean), and health +
reflection services. The Bazel module is named **`rules_lean_grpc`**.

The protocol stack — HTTP/2 framing, HPACK, flow control, gRPC message
framing, metadata, deadlines, cancellation — is implemented in Lean. The only
C in this repository is a small zlib shim for gzip message compression; TLS
cryptography is HACL\* via `tls13-lean`'s C shim.

```mermaid
flowchart TB
    subgraph codegen [Build time]
        P[".proto files"] --> PL["protoc + protoc-gen-lean4<br/>(lean_proto_library)"]
        PL --> GEN["Generated Lean:<br/>messages + typed service structures"]
    end
    subgraph runtime [Runtime]
        GEN --> REG["Grpc.Registry<br/>unary / server / client / bidi handlers"]
        REG --> H2["Grpc.Http2: connection state machine,<br/>HPACK, flow control, keepalive"]
        H2 --> TCP["Std.Async TCP (plaintext h2c)"]
        H2 --> TLS["Grpc.Tls sessions → tls13-lean → HACL*"]
        CL["Grpc.Client<br/>reader/writer tasks, per-call handles"] --> H2
        SVC["Grpc.Services.Health<br/>Grpc.Services.Reflection"] --> REG
    end
```

## Feature surface

| Area | Status |
| --- | --- |
| RPC shapes | Unary, server-streaming, client-streaming, bidirectional — each in a batched (`Array`) and an incremental `MessageStream` variant, with raw-`ByteArray` and typed-codec registration (`registerUnary` … `registerBidirectionalStreamingStreamCodec`) |
| Deadlines | Server-enforced from `grpc-timeout`: expiry cancels the handler task and returns `DEADLINE_EXCEEDED`. The absolute deadline reaches the handler as `request.deadline` (or `context.deadline`, via the additive `register*CodecWithContext` variants for typed handlers), and `CallOptions.propagating` turns what is left of it into a downstream call's `grpc-timeout` — or `DEADLINE_EXCEEDED` when nothing is left. No default deadline: a request without `grpc-timeout` still runs unbounded |
| Early authorization | `Registry.withRequestHeaderAuthorizer` runs after header validation and **before any request body is accepted**; rejected streams get a trailers-only status while the body is drained without dispatch |
| Message limits | Per-registry and per-client send/receive caps (`RESOURCE_EXHAUSTED`); 4 MiB default |
| Compression | gzip both directions (see below) |
| Metadata | ASCII + `-bin` base64 binary metadata, full validation (pseudo-header rules, forbidden connection headers, reserved response/trailer names) |
| Health | `grpc.health.v1.Health` `Check` + `Watch`, per-service status, terminal shutdown |
| Reflection | `grpc.reflection.v1` and `v1alpha` `ServerReflectionInfo`; `ListServices` is derived from the registry automatically. `lean_proto_library` codegen embeds each file's serialized `FileDescriptorProto` (source info stripped) as `fileDescriptors`, so `registerWith { files := Generated.fileDescriptors }` answers `FileByFilename`, `FileContainingSymbol`, `FileContainingExtension` and `AllExtensionNumbersOfType` — each response carries the transitive import closure, which is what schema-less clients need to resolve imported messages. Files you do not pass in `Reflection.Config` still answer `NOT_FOUND` |
| Keepalive | Opt-in server PING keepalive with ack timeout (plaintext managed path) |
| Graceful shutdown | `shutdown` sends GOAWAY(NO_ERROR), refuses newer streams with `REFUSED_STREAM`, `wait` drains with a timeout — over both h2c and TLS |
| Connection lifecycle | No managed connection dies silently, plaintext or TLS: every teardown records a `CloseCause` (peer close, shutdown, keepalive timeout, connection error, connection-task failure), the peer gets a GOAWAY carrying that cause before the socket is retired — sealed through the TLS session where there is one — and the last 64 causes are readable from `Grpc.Server.closedConnections`. `acceptFailure?`/`checkAccepting` expose the accept loop while the server runs |
| Cancellation | RST_STREAM and peer disconnect cancel in-flight dispatches and their streams; handler exceptions become gRPC statuses |
| Error scope | Framing failures are split per RFC 9113 §5.4. A stream error (a DATA frame on a stream that has closed, a HEADERS frame over `MAX_CONCURRENT_STREAMS`) answers RST_STREAM and the connection keeps serving every other stream; a connection error (preface violation, CONTINUATION sequencing, stream-id monotonicity, flow-control overflow, an undecodable field block) still ends the connection with GOAWAY. Every connection-scoped framing check carries a comment naming the RFC rule it follows, including the two places where a rule that would permit a stream error is deliberately widened to a connection error and why |

## Server

```lean
import Grpc

def registry : Grpc.Registry :=
  NoteService.register Grpc.Registry.empty {
    handleEcho := fun request => ...   -- typed handlers, generated per service
    ...
  }

def main : IO Unit := do
  let server ← Grpc.Server.serve registry { address := Grpc.Server.anyIPv4 50051 }
  Grpc.Server.wait server
```

Entry points: `serve` (managed accept loop with connection registry, keepalive,
and shutdown bookkeeping), `serveTls`, `serveForever`/`acceptOne` (unmanaged),
and `serveClient`/`serveClientWithState` for bring-your-own-socket or shared
`Std.Mutex` frame-driver embedding. `Grpc.Server.Config` covers address,
backlog, read size, `TCP_NODELAY`, `maxConcurrentStreams`, `maxHeaderListSize`,
and keepalive interval/timeout.

A managed connection never dies silently. Every teardown path records a
`CloseCause` — peer close, server shutdown, keepalive timeout, connection error,
or a failure of the connection task itself. The peer is told: unless it has
already gone, it receives a GOAWAY whose debug data is that cause, emitted
before the socket is retired, so the EOF that follows is attributable rather
than a bare disconnect. Locally the last 64 causes are readable from
`Grpc.Server.closedConnections`. `Grpc.Server.acceptFailure?` /
`checkAccepting` expose the accept loop while the server runs, so a dead accept
loop is a reportable failure instead of clients hanging on connect.

For every cause the peer was told about, teardown then retires the socket in
`Async`, racing the write-side shutdown against a short timer: a peer that has
stopped reading cannot stall it, and no worker thread is parked. (A peer that
closed first already sent its FIN, so that path skips the shutdown.) When the
timer wins, `Async.race` leaves the shutdown task running — bounded at one
suspended task per stalled peer, holding no worker — and the file descriptor is
released by finalization when `uv_shutdown` eventually settles. Lean 4.31's
`Std.Internal.UV.TCP.Socket` offers `shutdown` but no `close`, so prompt FIN is
reachable and deterministic fd release is not; a single `Socket.close` over
`uv_close` would remove both residues, and the rationale in
`Grpc/Http2/Server.lean` states that ask in full.

A complete server (all four RPC shapes plus reflection) is
`examples/lean_proto/NoteServer.lean`:

```sh
bazel run //examples/lean_proto:note_server -- 50051
```

## Client

`Grpc.Client.connect` / `connectTls` return a `Connection` multiplexing calls
over one HTTP/2 connection (background reader + writer tasks). On top of it:

- `Client.call` — unary; `Client.serverStreaming`; `Client.callRaw` — batched
  any-shape;
- `Client.start` returning a `Call` handle with `send`, `closeSend`, `recv?`,
  `finish`, `cancel` — this covers all four shapes incrementally.

`CallOptions` carry request metadata and a raw `grpc-timeout` value (e.g.
`"5S"`); `CallOptions.withTimeout` sets it from a `Timeout`, and
`CallOptions.propagating request.deadline` sets it to the time left on the
deadline of the request a handler is currently serving. The client advertises `grpc-accept-encoding: identity,gzip` and
transparently inflates gzip responses; it never compresses requests.
`Test/ClientTest.lean` and `Test/StreamingTest.lean` are the reference usage.

## Codegen

```starlark
load("@rules_proto//proto:defs.bzl", "proto_library")
load("@rules_lean_grpc//:defs.bzl", "lean_proto_library")

proto_library(name = "note_proto", srcs = ["note.proto"])
lean_proto_library(
    name = "note_lean_proto",
    proto = ":note_proto",
    module_prefix = "LeanProtoExample",   # Lean namespace for generated code
)
```

`lean_proto_library` runs `protoc` with the vendored
`protoc-gen-lean4` plugin (`third_party/Lean-zh/protobuf`, which also provides
the Lean protobuf runtime) and compiles the result with `rules_lean`. For each
proto3 `service` it generates a structure of typed handlers plus a
`register : Grpc.Registry → Service → Grpc.Registry`; cross-file imports are
wired with `proto_deps`. Only Lean is emitted — no C++ adapter code.

## HTTP/2 and HPACK scope

Implemented and tested:

- Connection preface, SETTINGS exchange and ACK, PING/ACK, WINDOW_UPDATE,
  RST_STREAM, CONTINUATION sequencing (header blocks capped at 1 MiB), DATA
  padding and HEADERS priority-prefix stripping, stream-id validity and
  monotonicity, `MAX_CONCURRENT_STREAMS` enforcement on inbound streams.
- Flow control in both directions at both connection and stream level.
  Streaming request bodies use credit-on-consume: stream window credit is
  granted as the handler consumes messages, giving real backpressure; the
  advertised 4 MiB initial stream window guarantees one maximum-size message
  always fits. Outbound buffering above 4 MiB fails the RPC with
  `RESOURCE_EXHAUSTED`.
- HPACK with the full RFC 7541 static table, dynamic table with eviction and
  size-update handling, Huffman encoding and decoding;
  `authorization`/`proxy-authorization` are always emitted never-indexed.

Deliberately out of scope or ignored (a candid list):

- `PUSH_PROMISE` is rejected (`UNIMPLEMENTED`); the client fails the
  connection if a server pushes.
- `PRIORITY` frames are parsed, validated, and ignored — no priority tree.
- Inbound GOAWAY is ignored by the server (the client honors it and fails
  affected calls with `UNAVAILABLE`).
- Peer `MAX_CONCURRENT_STREAMS` / `MAX_HEADER_LIST_SIZE` settings are
  accepted but not enforced against outbound work.
- Malformed framing is connection-fatal: the server answers
  GOAWAY(INTERNAL_ERROR) rather than containing the error per-stream.
- No HTTP/1.1 → h2c upgrade; plaintext is prior-knowledge h2c only.
- The server never half-closes the TCP write side (documented rationale in
  `Grpc/Http2/Server.lean`: a peer that stops reading would leak a worker per
  connection).

## Compression

- Requests/responses with `grpc-encoding: gzip` are decompressed before
  dispatch (per message on streaming paths), guarded by a 4 MiB
  decompression-size limit in the zlib C shim. Any other `grpc-encoding`
  value is rejected with `UNIMPLEMENTED`.
- Responses are gzip-compressed per message (≥ 1 KiB) when the client
  advertised gzip; the client itself sends requests uncompressed.
- The dispatch layer (`Registry.dispatch*`) rejects messages that still carry
  the compressed flag with `UNIMPLEMENTED "compressed requests are not
  supported"` — reachable only when driving the registry directly, since the
  HTTP/2 server path decompresses first. A compressed flag without a declared
  encoding is `INTERNAL` per the gRPC spec.

## TLS

`Grpc.Server.serveTls` terminates TLS 1.3 with ALPN `"h2"` given a DER
certificate chain and a raw Ed25519 signing key. `Client.connectTls` validates
the peer chain and hostname against `trustAnchorsPEM` (leaving it `none` skips
validation — test use only). `Grpc.Tls.Rest` additionally provides a minimal
HTTP/1.1 JSON server over the same TLS stack (one request per connection; not
a general HTTP server).

The server negotiates a single suite — TLS_CHACHA20_POLY1305_SHA256, X25519
(P-256 only when configured), Ed25519 — but selects it from the client's
offered overlap per RFC 8446, so mainstream clients interoperate:
`//examples/lean_proto:note_grpcurl_tls_interop_test` completes real
handshakes with **grpcurl** (Go `crypto/tls`) and **OpenSSL `s_client`**,
negotiating ALPN `h2` and running gRPC over the result (see
[Interoperability status](#interoperability-status)).

Current limitations:

- One suite, one group, one signature algorithm: a client that offers none of
  them (for example an FIPS-restricted or TLS 1.2-only client) gets a
  handshake failure rather than a fallback.
- Server-initiated keepalive PINGs are plaintext-only: `keepaliveIntervalMs`
  is not yet armed on the TLS accept path (its PING would have to be sealed
  through the session). Cause-carrying teardown, connection registration and
  the graceful-shutdown drain do apply to TLS.

## Interoperability status

Honest summary: there is no official gRPC interop-suite or h2spec run yet.

- `//examples/lean_proto:note_grpcurl_interop_test` drives the Lean server
  with **grpcurl** (grpc-go) over plaintext h2c: reflection `list`, then
  `describe` and RPC invocation resolved entirely from the server's embedded
  descriptors (no `-proto` or `-import-path` flags), including a message
  defined in an imported file, plus unary calls with enum/map/optional
  fields, `DEADLINE_EXCEEDED` via client deadline, error mapping, a 90 kB
  payload, and server-, client- and bidi-streaming calls. It is tagged
  `manual` and `requires-grpcurl`, so `bazel test //...` skips it — run it
  explicitly, with grpcurl on `PATH`, to reproduce those results.
- `//examples/lean_proto:note_grpcurl_tls_interop_test` drives the same server
  through `Grpc.Server.serveTls` — TLS 1.3 terminated by `../tls13-lean`,
  ALPN `h2`, HTTP/2 and gRPC by this repo — with **grpcurl** and **OpenSSL
  `s_client`**. It asserts `ALPN protocol: h2` and chain verification at the
  TLS layer (so a gRPC failure could not be mistaken for a TLS one), that a
  wrong `-servername` is rejected, then repeats the reflection-only
  `list`/`describe`/invoke flow, error mapping, a 90 kB payload that spans
  many 16 kB TLS records, and server-, client- and bidi-streaming over one
  encrypted connection. Also `manual` and `requires-grpcurl`; run it with
  grpcurl and openssl on `PATH`.
- Wire behaviors (trailers-only responses, percent-encoded `grpc-message`,
  `-bin` metadata, status mapping) follow the gRPC over HTTP/2 spec and are
  covered by the in-repo test suite.

## Building and testing

This repo is part of a six-repository ecosystem built with Bazel and sibling
checkouts (Bzlmod `local_path_override ../rules_lean`, `../tls13-lean`):

```sh
for r in rules_lean grpc-lean tls13-lean; do
  git clone "https://github.com/pb64-lean/$r"
done
cd grpc-lean
bazel test //...
```

Prerequisites: Bazel 8.5 (`.bazelversion`) and **Nix** — the Lean toolchain
(4.31.0-pre, pinned by `third_party/Lean-zh/protobuf/nixpkgs.{nix,json}`) is
built by Nix. `lakefile.lean` is an IDE/LSP project model only; `lake build`
is not a supported build. Run `tools/link-lean-nix-toolchain.sh` once to give
your editor the same nix-built Lean that Bazel uses.

`bazel test //...` runs the hermetic suite: the ~69-case runtime test
(protocol validation, all four dispatch shapes, HTTP/2 frame codecs, flow
control, live h2c loopback servers), plus dedicated HPACK, hardening
(padding/CONTINUATION/keepalive/crash paths), early-authentication, client,
streaming (including an 80-connection stress case), connection-lifecycle
(cause-carrying GOAWAY before teardown, over both h2c and a real TLS 1.3
session), server-ownership, health, zlib, TLS
handshake, gRPC-over-TLS, REST-over-TLS, and generated-code tests, and the two
`lean_assurance_test` audits below. `examples/grpc_service/` (a standalone module demonstrating a
PostgreSQL-backed service and in-process proof checking of client-supplied
Lean terms) and the vendored `third_party` modules are excluded from `//...`
by `.bazelignore`.

## Assurance and trusted boundary

No end-to-end formal-verification claim is made for this repository: nothing
is proved about the socket-facing I/O, concurrency, or the server loop.

Everything claimed below is checked mechanically, not by review. `bazel test
//:grpc_assurance` audits the compiled `Environment` while the test binary is
compiled: each principal theorem named in that target must exist, be a theorem,
and close over no axiom outside `propext`, `Classical.choice`, `Quot.sound`; no
constant under `Grpc.*` or `Zlib.*` may reach `sorryAx`; and `@[extern]` may
appear only in `Zlib.Gzip`. **No non-standard axiom is allowed and none is
used**: no proof here uses `bv_decide`, so unlike some sibling repositories
there is no generated LRAT-certificate axiom (`…._native.bv_decide.ax_1_5`) in
the allowed set — a proof that introduced one would fail the audit.
`//:grpc_tls_assurance` makes the same `@[extern]` statement about `Grpc.Tls.*`.

What holds today:

- **Lean protocol code** (HTTP/2, HPACK, gRPC framing, metadata, dispatch):
  implemented in Lean; the I/O paths, dispatch and concurrency are evidenced
  by the test suite described above.
- **Kernel-checked laws over the pure codecs and registry** (no `sorry`,
  no `native_decide`), a growing set rather than a complete one:
  - `Grpc.Framing` — message-frame encode/decode inversion with residual
    bytes (`decodeAll_encode_append`), and that a successful size-limited
    decode never yields an oversized message (`decodeAllWithLimit_size_le`);
  - `Grpc.Http2.Frame` — frame header and whole-frame inversion with
    residual bytes (`decodeHeader_encodeHeader_append`,
    `decodeAll_encode_append`);
  - `Grpc.Http2.Hpack` — integer roundtrip (`decodeInteger_encodeInteger`),
    literal-string roundtrip in both representations
    (`decodeString_encodeString`), the Huffman coder roundtrip
    (`decodeHuffman_encodeHuffman`, resting on prefix-freeness of the
    257-entry table, `huffmanPrefixFree`), and the dynamic-table size
    invariant (`dynamicSize_*_le`);
  - `Grpc.Protocol` — `grpc-timeout` render/parse (`Timeout.parse?_render`),
    including every duration a propagated deadline can produce
    (`Timeout.ofNanoseconds_bounds`, `Timeout.parse?_render_ofNanoseconds`),
    and `grpc-message` percent-coding (`Percent.decode_encode`);
  - `Grpc.Metadata` — base64 roundtrips behind `-bin` metadata
    (`Base64.decodeBytes_encodeBytes`, `…_encodeBytesUnpadded`);
  - `Grpc.Server` — registry well-formedness and lookup uniqueness;
  - `Grpc.Http2.Connection` — rejected streams stay inert;
    `Connection.WellFormed`, the pure connection invariant (client stream-id
    parity and monotone claiming, CONTINUATION sequencing, 31-bit outbound
    window bounds, HPACK tables inside their negotiated limits), holds of
    `initialState` and is preserved by every pure frame transition —
    `prepareHeadersShared_wellFormed`, `appendContinuationFrame_wellFormed`
    and `processNonHeaderFrameShared_wellFormed` (SETTINGS, DATA,
    RST_STREAM, WINDOW_UPDATE, PING, PRIORITY, GOAWAY, unknown), with
    `prepareHeadersShared_no_reopen` (a claimed stream id can never be
    reopened) and `prepareHeadersShared_concurrency`
    (`MAX_CONCURRENT_STREAMS` gates admission: a HEADERS frame either arrives
    below the limit or opens a stream marked for `REFUSED_STREAM`) as
    corollaries; per-stream error containment is
    `processDataShared_inert_reset` — a DATA frame for a stream that has
    already closed produces no request feed, no dispatch, cancels nothing
    outside that stream, emits an RST_STREAM naming only it, and leaves the
    connection serving;
  - `Grpc.Http2.Connection` flow control — conservation, not just bounds:
    `consumeInboundDataWindow_conserves` (a DATA frame debits both receive
    windows by exactly its payload, and the `Nat` equation witnesses that
    neither subtraction truncated), `processUnaryRequestData_windows` and
    `processActiveRequestData_windows`, `decodeActiveRequestData_conserves`
    plus `takeRequestStreamCredit_conserves` (credit returned on consume
    equals bytes consumed, so the effective window never creeps past the
    advertised one), `flushOutbound_conserves` (bytes put on the wire are
    exactly what the outbound connection window is debited), and
    `defaultStreamWindow_admits_max_message` /
    `inboundWindow_pos_of_incomplete` — the deadlock-freedom argument for
    credit-on-consume, previously only a code comment.

  Not proved: the HPACK header-block loop, the `IO` halves of the
  HEADERS/CONTINUATION steps (header decoding, authorization, dispatch
  spawning), and everything above the codecs.
- **C in the trusted computing base**: the zlib shim
  (`Zlib/shim/zlib_shim.c`, with an explicit output-size bound) — and nothing
  else first-party, which is what `//:grpc_assurance` confirms by allowing
  `@[extern]` in `Zlib.Gzip` and nowhere else under `Grpc.*`/`Zlib.*` — and,
  via `tls13-lean`, the HACL\* shim. The HACL\* cryptographic primitives
  themselves carry externally machine-verified correctness proofs; the shim
  and `@[extern]` bindings do not.
- **External dependencies**: zlib (Bazel module), the vendored
  [Lean-zh/protobuf](https://github.com/Lean-zh/protobuf) runtime/plugin
  (Apache-2.0, `third_party/Lean-zh/`), and the Lean compiler/runtime.

## License

Apache-2.0. Vendored third-party code retains its own notices under
`third_party/`.
