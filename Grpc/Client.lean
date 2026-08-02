module

public import Std.Async.TCP
public import Std.Sync.CancellationToken
public import Std.Sync.Notify
public import Std.Sync.Channel

public import Grpc.CancellationToken
public import Grpc.Http2.Connection
public import Grpc.Tls.Session

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
one to completion synchronously with `Async.block`. `connect` and `close` stay in
`IO`.

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
  -/
  maxReceiveMessageSize : Nat := defaultMaxMessageSize
  deriving Inhabited

structure CallOptions where
  metadata : Metadata := Metadata.empty
  /-- Raw grpc-timeout header value, e.g. "5S" or "250m". -/
  timeout : Option String := none

structure CallResult where
  headers : Metadata := Metadata.empty
  trailers : Metadata := Metadata.empty
  messages : Array ByteArray := #[]
  status : Status := Status.ok

/-- Per-stream client-side state, mutated by the connection reader task and
polled by call handles under the connection mutex. -/
structure CallRecord where
  streamId : Nat
  /-- Outbound credit granted by the server; `Int` because a SETTINGS
  `INITIAL_WINDOW_SIZE` reduction can drive it negative (RFC 9113 §6.9.2). -/
  streamSendWindow : Int
  decode : Message.DecodeState := {}
  /-- Decoded (and decompressed) inbound messages awaiting `recv?`. -/
  inbound : Array ByteArray := #[]
  /-- Wire size of each inbound message; the stream WINDOW_UPDATE for a
  message is sent when `recv?` consumes it. -/
  pendingRecvCredits : Array Nat := #[]
  headers : Metadata := Metadata.empty
  seenHeaders : Bool := false
  responseGzip : Bool := false
  trailers : Option Metadata := none
  failure : Option Status := none
  sendClosed : Bool := false

structure ConnState where
  decoder : Http2.Frame.DecodeState := {}
  hpackEncode : Http2.Hpack.State := {}
  hpackDecode : Http2.Hpack.State := {}
  nextStreamId : Nat := 1
  connectionSendWindow : Nat := Http2.Connection.initialFlowControlWindow
  initialStreamSendWindow : Nat := Http2.Connection.initialFlowControlWindow
  maxFrameSize : Nat := Http2.defaultMaxFramePayloadLength
  /-- A server header block awaiting CONTINUATION frames:
  (stream id, accumulated block, END_STREAM flag from the HEADERS frame). -/
  pendingHeaders : Option (Nat × ByteArray × Bool) := none
  goAway : Option Http2.GoAway.Decoded := none
  /-- Set when the connection is unusable; new and pending calls fail with it. -/
  dead : Option Status := none
  calls : Array CallRecord := #[]
  deriving Inhabited

private structure BackgroundTasks where
  writer : Option (Task Unit) := none
  reader : Option (AsyncTask Unit) := none

structure Connection where
  socket : TCP.Socket.Client
  config : Config
  state : Std.Mutex ConnState
  /-- Outbound frame bytes, drained by a single writer task so socket writes never
  happen while the state mutex is held (avoids stalling the reader and app calls
  behind a blocked write). Preserves frame order via FIFO with one consumer. -/
  outbound : Std.CloseableChannel ByteArray
  /-- Signalled by the reader on any state change (window credit, message delivery,
  terminal state, death) to wake waiters in `send`/`recv?`/`finish` without polling. -/
  wakeup : Std.Notify
  /-- Cancelled by `close` to stop the background reader task's blocked `recv?`. -/
  stopToken : Std.CancellationToken
  /--
  Exact background task handles. Construction publishes a `Connection` only
  after both handles have been installed; `close` joins both before returning.
  -/
  private background : IO.Ref BackgroundTasks
  /-- When present, the connection runs over TLS: outbound bytes are sealed and
  inbound raw bytes are decrypted through this session. `none` is plaintext. -/
  tls : Option Tls.ClientSession := none

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
  if bytes.isEmpty then pure () else discard <| connection.outbound.send bytes

/-- Encode and enqueue a frame. Encoding only fails for malformed frames, which we
never construct here; such a frame is dropped rather than corrupting the stream. -/
private def enqueueFrame (connection : Connection) (frame : Http2.Frame) : BaseIO Unit := do
  match Http2.Frame.encode frame with
  | .ok bytes => enqueueBytes connection bytes
  | .error _ => pure ()

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
    (options : CallOptions) : Metadata :=
  let base := Metadata.empty
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

private def applyServerSetting (state : ConnState) (setting : Http2.Setting) : ConnState :=
  match setting.id with
  | .maxFrameSize => { state with maxFrameSize := setting.value }
  | .initialWindowSize =>
      let delta : Int := Int.ofNat setting.value - Int.ofNat state.initialStreamSendWindow
      {
        state with
        initialStreamSendWindow := setting.value,
        calls := state.calls.map fun call =>
          { call with streamSendWindow := call.streamSendWindow + delta }
      }
  | _ => state

private def responseGzipOf (metadata : Metadata) : Bool :=
  metadata.get? "grpc-encoding" == some Headers.gzipEncoding

/-- Route a fully reassembled server header block. Every block must be decoded
in arrival order — even for unknown or finished streams — to keep the shared
HPACK dynamic table in sync with the server's encoder. -/
private def routeHeaderBlock (state : ConnState) (streamId : Nat) (block : ByteArray)
    (endStream : Bool) : Except Status ConnState := do
  let decoded ← Http2.Hpack.decodeHeaderBlock state.hpackDecode block
  let state := { state with hpackDecode := decoded.state }
  match findCall? state.calls streamId with
  | none => pure state
  | some call =>
      if call.failure.isSome || call.trailers.isSome then
        pure state
      else
        let call :=
          if !call.seenHeaders && !endStream then
            {
              call with
              seenHeaders := true,
              headers := decoded.headers,
              responseGzip := responseGzipOf decoded.headers
            }
          else
            { call with trailers := some decoded.headers }
        pure { state with calls := replaceCall state.calls call }

/-- Decode DATA payload into gRPC messages, recording each message's wire size
so its stream flow-control credit can be granted on consumption. -/
private def processCallData
    (maxReceiveMessageSize : Nat) (call : CallRecord) (payload : ByteArray) :
    Except Status CallRecord := do
  let decoded ← Message.decodeChunkWithLimit (some maxReceiveMessageSize)
    { buffered := call.decode.buffered } payload
  let credits := decoded.messages.map fun message => Message.prefixLength + message.data.size
  let messages ← decoded.messages.mapM fun message => do
    let message ← Message.decompress call.responseGzip maxReceiveMessageSize message
    pure message.data
  pure {
    call with
    decode := { buffered := decoded.buffered },
    inbound := call.inbound.append messages,
    pendingRecvCredits := call.pendingRecvCredits.append credits
  }

private def rstStatus (code : Http2.ErrorCode) : Status :=
  match code with
  | .cancel => Status.cancelled "stream cancelled by server"
  | .refusedStream => Status.error .unavailable "stream refused by server"
  | .enhanceYourCalm => Status.resourceExhausted "server requested backoff"
  | code => Status.internal s!"stream reset by server (HTTP/2 error {code.toNat})"

private def handleInboundFrame (connection : Connection) (frame : Http2.Frame) : IO Unit := do
  connection.state.atomically do
    let state ← get
    match state.pendingHeaders with
    | some (pendingStreamId, buffered, endStream) =>
        -- A header block in progress must be continued before anything else.
        if frame.header.frameType == Http2.FrameType.continuation
            && frame.header.streamId == pendingStreamId then
          let block := buffered.append frame.payload
          if block.size > Http2.Connection.maxHeaderBlockSize then
            set (failStateLocked state
              (Status.internal "server header block exceeds the maximum supported size"))
          else if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
            match routeHeaderBlock { state with pendingHeaders := none }
                pendingStreamId block endStream with
            | .ok state => set state
            | .error status => set (failStateLocked state status)
          else
            set { state with pendingHeaders := some (pendingStreamId, block, endStream) }
        else
          set (failStateLocked state
            (Status.internal "server violated HTTP/2 CONTINUATION sequencing"))
    | none =>
      match frame.header.frameType with
      | .settings =>
          if Http2.Settings.isAck frame then
            pure ()
          else
            match Http2.Settings.decode frame with
            | .error status => set (failStateLocked state status)
            | .ok settings =>
                set (settings.foldl applyServerSetting state)
                match Http2.Settings.frame #[] (ack := true) with
                | .ok ack => enqueueFrame connection ack
                | .error _ => pure ()
      | .ping =>
          if Http2.Ping.isAck frame then
            pure ()
          else
            match Http2.Ping.decode frame with
            | .error status => set (failStateLocked state status)
            | .ok payload =>
                match Http2.Ping.frame payload (ack := true) with
                | .ok ack => enqueueFrame connection ack
                | .error _ => pure ()
      | .windowUpdate =>
          match Http2.WindowUpdate.decode frame with
          | .error status => set (failStateLocked state status)
          | .ok increment =>
              if frame.header.streamId == 0 then
                set { state with
                  connectionSendWindow := state.connectionSendWindow + increment }
              else
                match findCall? state.calls frame.header.streamId with
                | none => pure ()
                | some call =>
                    let call := { call with
                      streamSendWindow := call.streamSendWindow + Int.ofNat increment }
                    set { state with calls := replaceCall state.calls call }
      | .goAway =>
          match Http2.GoAway.decode frame with
          | .error status => set (failStateLocked state status)
          | .ok decoded =>
              set {
                state with
                goAway := some decoded,
                calls := state.calls.map fun (call : CallRecord) =>
                  if call.streamId > decoded.lastStreamId then
                    failCallRecord
                      (Status.error .unavailable "connection is shutting down (GOAWAY)") call
                  else
                    call
              }
      | .rstStream =>
          match Http2.RstStream.decode frame with
          | .error status => set (failStateLocked state status)
          | .ok code =>
              match findCall? state.calls frame.header.streamId with
              | none => pure ()
              | some call =>
                  set { state with
                    calls := replaceCall state.calls (failCallRecord (rstStatus code) call) }
      | .headers =>
          match Http2.Transport.normalizeHeadersFrame frame with
          | .error status => set (failStateLocked state status)
          | .ok frame =>
              let endStream := Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
              if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
                match routeHeaderBlock state frame.header.streamId frame.payload endStream with
                | .ok state => set state
                | .error status => set (failStateLocked state status)
              else
                set { state with
                  pendingHeaders := some (frame.header.streamId, frame.payload, endStream) }
      | .continuation =>
          set (failStateLocked state (Status.internal "unexpected HTTP/2 CONTINUATION from server"))
      | .data =>
          match Http2.Transport.normalizeDataFrame frame with
          | .error status => set (failStateLocked state status)
          | .ok normalized =>
              -- Credit the connection window for the full padded frame right
              -- away; stream credit for the payload waits for consumption.
              (if frame.payload.size > 0 then
                match Http2.WindowUpdate.frame 0 frame.payload.size with
                | .ok update => enqueueFrame connection update
                | .error _ => pure ()
              else
                pure ())
              let paddingBytes := frame.payload.size - normalized.payload.size
              (if paddingBytes > 0 then
                match Http2.WindowUpdate.frame frame.header.streamId paddingBytes with
                | .ok update => enqueueFrame connection update
                | .error _ => pure ()
              else
                pure ())
              match findCall? state.calls frame.header.streamId with
              | none => pure ()
              | some call =>
                  if call.failure.isSome || call.trailers.isSome then
                    pure ()
                  else if Http2.FrameFlag.has normalized.header.flags Http2.FrameFlag.endStream then
                    -- gRPC servers half-close via trailers, never via DATA.
                    set { state with calls := replaceCall state.calls (failCallRecord
                      (Status.internal "server ended stream without gRPC trailers") call) }
                  else
                    match processCallData
                        connection.config.maxReceiveMessageSize call normalized.payload with
                    | .ok call =>
                        set { state with calls := replaceCall state.calls call }
                    | .error status =>
                        -- Stop the peer from continuing a response that this
                        -- stream has rejected (notably an oversized message).
                        match Http2.RstStream.frame
                            frame.header.streamId Http2.ErrorCode.cancel with
                        | .ok rst => enqueueFrame connection rst
                        | .error _ => pure ()
                        set { state with
                          calls := replaceCall state.calls (failCallRecord status call) }
      | .pushPromise =>
          set (failStateLocked state
            (Status.internal "server sent PUSH_PROMISE although push is disabled"))
      | .priority => pure ()
      | .unknown _ => pure ()
  wake connection

private inductive ReaderEvent where
  | received (chunk? : Option ByteArray)
  | stop

private def nextReaderEvent (connection : Connection) : Async ReaderEvent :=
  Selectable.one #[
    Selectable.case (connection.socket.recvSelector connection.config.readSize) fun chunk? =>
      pure (ReaderEvent.received chunk?),
    Selectable.case connection.stopToken.selector fun _ =>
      pure ReaderEvent.stop
  ]

/-- Connection reader. Runs in `Async`: while idle (no inbound bytes) it suspends
cooperatively instead of parking a worker thread, so open-but-idle connections are
free. Frame handling in the body is ordinary `IO`. -/
private partial def readerLoop (connection : Connection) : Async Unit := do
  let event ← try
      Except.ok <$> nextReaderEvent connection
    catch err =>
      pure (Except.error (Status.ofIOError err))
  let chunk? : Except Status (Option ByteArray) := match event with
    | .error status => .error status
    | .ok .stop => .ok none
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
  | .error status => failConnection connection status
  | .ok none => failConnection connection (Status.error .unavailable "connection closed")
  | .ok (some chunk) =>
      let frames? ← connection.state.atomically do
        let state ← get
        if state.dead.isSome then
          pure none
        else
          match Http2.Frame.decodeChunk state.decoder chunk with
          | .error status =>
              set (failStateLocked state status)
              pure none
          | .ok decoded =>
              set { state with decoder := { buffered := decoded.buffered } }
              pure (some decoded.frames)
      match frames? with
      | none => pure ()
      | some frames => do
          for frame in frames do
            handleInboundFrame connection frame
          readerLoop connection

/-- Drain the outbound channel to the socket. Runs as its own task so socket writes
never block the reader or app calls; a write error kills the connection. Over TLS the
bytes are sealed by the session (which serializes seal+send). -/
private def writerBody (connection : Connection) (bytes : ByteArray) : BaseIO Unit := do
  let sent : IO Unit :=
    match connection.tls with
    | some session => session.send bytes
    | none => (connection.socket.send bytes).block
  match ← sent.toBaseIO with
  | .ok () => pure ()
  | .error err =>
      connection.state.atomically do
        modify fun state => failStateLocked state (Status.ofIOError err)
      wake connection
      discard <| connection.outbound.close.toBaseIO

private def startBackgroundTasks (connection : Connection) : IO Unit := do
  let reader ← Async.toIO (readerLoop connection)
  connection.background.set { reader := some reader }
  let writer ← connection.outbound.forAsync (writerBody connection)
  connection.background.set { writer := some writer, reader := some reader }

private def joinBackgroundTasks (connection : Connection) : IO Unit := do
  let background ← connection.background.get
  match background.writer with
  | some writer => discard <| IO.wait writer
  | none => pure ()
  match background.reader with
  | some reader =>
      -- The reader converts transport errors into connection state before it
      -- terminates. A task-level error must not skip the other join.
      discard <| IO.wait reader
  | none => pure ()

private def shutdownSocket (socket : TCP.Socket.Client) : IO Unit := do
  try
    socket.shutdown.block
  catch _ =>
    pure ()

private def shutdownConnection (connection : Connection) : IO Unit := do
  failConnection connection (Status.cancelled "connection closed locally")
  discard <| Grpc.CancellationToken.cancel connection.stopToken
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

private def clientPrefaceWire : IO ByteArray := do
  let settings ← ofStatus
    (Http2.Settings.frame #[
      { id := Http2.SettingId.enablePush, value := 0 },
      { id := Http2.SettingId.initialWindowSize, value := Http2.Connection.defaultStreamWindow }
    ])
  let settingsWire ← ofStatus (Http2.Frame.encode settings)
  pure (Http2.connectionPreface.append settingsWire)

private def initializeConnection
    (socket : TCP.Socket.Client) (config : Config)
    (prefaceWire : ByteArray) (tls : Option Tls.ClientSession := none) :
    IO Connection := do
  let connection : Connection := {
    socket := socket,
    config := config,
    state := ← Std.Mutex.new {},
    outbound := ← Std.CloseableChannel.new,
    wakeup := ← Std.Notify.new,
    stopToken := ← Std.CancellationToken.new,
    background := ← IO.mkRef {},
    tls := tls
  }
  try
    startBackgroundTasks connection
    enqueueBytes connection prefaceWire
    pure connection
  catch error =>
    shutdownConnection connection
    throw error

/-- Connect, perform the HTTP/2 client preface exchange (preface string +
SETTINGS with server push disabled), and start the writer and reader tasks. -/
def connect (config : Config := {}) : IO Connection := do
  -- Finish all pure framing work before acquiring a socket.
  let prefaceWire ← clientPrefaceWire
  let socket ← TCP.Socket.Client.mk
  try
    (socket.connect config.address).block
    socket.noDelay
    initializeConnection socket config prefaceWire
  catch error =>
    -- Once `connect` has returned or thrown, there is no pending receive owned
    -- by this adapter. Shut down every socket that was not transferred into a
    -- successfully returned `Connection`; finalization then releases its handle.
    shutdownSocket socket
    throw error

/-- TLS options for a gRPC-over-TLS client connection. -/
structure TlsConfig where
  /-- SNI host and the identity checked during hostname verification. -/
  serverName : Option String := none
  /-- ALPN protocols to offer; gRPC requires "h2". -/
  alpnProtocols : Array String := #["h2"]
  /-- PEM trust anchors for X.509 chain validation. `none` skips chain and
  hostname validation (development / self-signed peers); the TLS engine still
  cryptographically verifies the server's CertificateVerify either way. -/
  trustAnchorsPEM : Option String := none
  /-- Verify the leaf certificate identity against `serverName` (needs anchors). -/
  verifyHostname : Bool := true

private def verifyTlsPeer
    (session : Tls.ClientSession)
    (trustStore? : Option TLS13.X509.Chain.TrustStore)
    (tlsConfig : TlsConfig) : IO Unit := do
  match trustStore? with
  | none => pure ()
  | some trustStore =>
      let certificates ← session.peerCertificates
      let some leaf := certificates[0]?
        | throw (IO.userError "TLS peer sent no certificate")
      let presented := certificates.extract 1 certificates.size
      let now := (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.toInt
      let verified ← match TLS13.X509.Chain.validate now leaf presented trustStore with
        | .ok verified => pure verified
        | .error failure => throw (IO.userError s!"TLS certificate chain: {repr failure}")
      if tlsConfig.verifyHostname then
        match tlsConfig.serverName with
        | none => pure ()
        | some host =>
            match TLS13.X509.Hostname.verifyHostname host verified.leaf with
            | .ok () => pure ()
            | .error failure => throw (IO.userError s!"TLS hostname: {repr failure}")

private def connectTlsOnSocket
    (socket : TCP.Socket.Client)
    (config : Config) (tlsConfig : TlsConfig)
    (trustStore? : Option TLS13.X509.Chain.TrustStore)
    (prefaceWire : ByteArray) : IO Connection := do
  (socket.connect config.address).block
  socket.noDelay
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Tls.Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := tlsConfig.serverName
    alpnProtocols := tlsConfig.alpnProtocols
  }
  let session ← Async.block
    (Tls.ClientSession.establish socket clientConfig config.readSize)
  try
    verifyTlsPeer session trustStore? tlsConfig
    initializeConnection socket config prefaceWire (some session)
  catch error =>
    session.close
    throw error

/-- Connect over TLS 1.3, then run the gRPC client exactly as `connect` does but
with every byte sealed/opened through the TLS session. Fresh ECDHE and random
values are generated internally. -/
def connectTls (config : Config := {}) (tlsConfig : TlsConfig := {}) : IO Connection := do
  -- Parse local policy and frame constants before any network effect.
  let prefaceWire ← clientPrefaceWire
  let trustStore? ← match tlsConfig.trustAnchorsPEM with
    | none => pure none
    | some pem =>
        match TLS13.X509.Chain.TrustStore.decodePEM pem with
        | .ok store => pure (some store)
        | .error message => throw (IO.userError s!"TLS trust anchors: {message}")
  let socket ← TCP.Socket.Client.mk
  try
    connectTlsOnSocket socket config tlsConfig trustStore? prefaceWire
  catch error =>
    shutdownSocket socket
    throw error

/-- Close the connection and join all of its exact reader and writer tasks.

The socket API exposes a write-side shutdown rather than an explicit handle
close. The FIN lets a peer observe EOF; after the HTTP/2 tasks (and, for TLS,
the record writer) have terminated, the native handle is quiescent and is
released by finalization with the remaining `Connection` references.
-/
def close (connection : Connection) : IO Unit := do
  shutdownConnection connection

private def chunkFlags (isLast : Bool) : UInt8 :=
  if isLast then Http2.FrameFlag.endHeaders else 0

/-- Split a request header block into HEADERS + CONTINUATION frames bounded by
the server's max frame size. -/
private def headerBlockRequestFrames (streamId : Nat) (block : ByteArray)
    (maxFrameSize : Nat) : Array Http2.Frame := Id.run do
  let chunkSize := Nat.max 1 maxFrameSize
  let mut frames : Array Http2.Frame := #[]
  let mut offset := 0
  let mut first := true
  while first || offset < block.size do
    let chunk := block.extract offset (Nat.min block.size (offset + chunkSize))
    let isLast := offset + chunkSize >= block.size
    frames := frames.push {
      header := {
        length := chunk.size,
        frameType := if first then Http2.FrameType.headers else Http2.FrameType.continuation,
        flags := chunkFlags isLast,
        streamId := streamId
      },
      payload := chunk
    }
    offset := offset + chunkSize
    first := false
  pure frames

/-- Open a stream: send request HEADERS and register the call. The request
body is streamed afterwards with `Call.send` / `Call.closeSend`. -/
def start (connection : Connection) (path : String) (options : CallOptions := {}) :
    Async (Except Status Call) := do
  connection.state.atomically do
    let state ← get
    match state.dead with
    | some status => pure (.error status)
    | none =>
      match state.goAway with
      | some _ => pure (.error (Status.error .unavailable "connection is shutting down (GOAWAY)"))
      | none =>
          let streamId := state.nextStreamId
          let metadata := requestMetadata connection path options
          match Http2.Hpack.encodeHeaderBlock state.hpackEncode metadata with
          | .error status => pure (.error status)
          | .ok encoded =>
              let frames := headerBlockRequestFrames streamId encoded.1 state.maxFrameSize
              let record : CallRecord := {
                streamId := streamId,
                streamSendWindow := Int.ofNat state.initialStreamSendWindow
              }
              set {
                state with
                nextStreamId := streamId + 2,
                hpackEncode := encoded.2,
                calls := state.calls.push record
              }
              for frame in frames do
                enqueueFrame connection frame
              pure (.ok { connection := connection, streamId := streamId })

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
            else if record.sendClosed then
              pure (SendStep.failed (Status.internal "send after closeSend"))
            else
              let streamAvailable := record.streamSendWindow.toNat
              let available := Nat.min state.connectionSendWindow streamAvailable
              if available == 0 then
                let waiter ← call.connection.wakeup.wait
                pure (SendStep.wait waiter)
              else do
                let sendSize := Nat.min (Nat.min available state.maxFrameSize)
                  (payload.size - offset)
                let chunk := payload.extract offset (offset + sendSize)
                let frame : Http2.Frame := {
                  header := {
                    length := chunk.size,
                    frameType := Http2.FrameType.data,
                    streamId := call.streamId
                  },
                  payload := chunk
                }
                let record := { record with
                  streamSendWindow := record.streamSendWindow - Int.ofNat sendSize }
                enqueueFrame call.connection frame
                set {
                  state with
                  connectionSendWindow := state.connectionSendWindow - sendSize,
                  calls := replaceCall state.calls record
                }
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
              if record.sendClosed then
                pure (.ok ())
              else
                let frame : Http2.Frame := {
                  header := {
                    length := 0,
                    frameType := Http2.FrameType.data,
                    flags := Http2.FrameFlag.endStream,
                    streamId := call.streamId
                  }
                }
                let record := { record with sendClosed := true }
                enqueueFrame call.connection frame
                set { state with calls := replaceCall state.calls record }
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
        match record.inbound[0]? with
        | some data =>
            let credit := record.pendingRecvCredits[0]?.getD 0
            let terminal := record.failure.isSome || record.trailers.isSome
            let record := {
              record with
              inbound := record.inbound.extract 1 record.inbound.size,
              pendingRecvCredits :=
                record.pendingRecvCredits.extract 1 record.pendingRecvCredits.size
            }
            set { state with calls := replaceCall state.calls record }
            (if credit > 0 && !terminal then
              match Http2.WindowUpdate.frame call.streamId credit with
              | .ok update => enqueueFrame call.connection update
              | .error _ => pure ()
            else
              pure ())
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
  | finished (headers : Metadata) (trailers : Metadata)
  | failed (status : Status)
  | wait (waiter : AsyncTask Unit)

/-- Wait for the call's terminal state and remove it from the connection.
Returns the server's gRPC status plus initial headers and trailers; transport
failures (RST_STREAM, GOAWAY, connection loss) surface as the error case. -/
partial def finish (call : Call) : Async (Except Status (Status × Metadata × Metadata)) := do
  let step ← call.connection.state.atomically do
    let state ← get
    match findCall? state.calls call.streamId with
    | none =>
        pure (FinishStep.failed (state.dead.getD (Status.internal "gRPC call is no longer active")))
    | some record =>
        match record.failure with
        | some status =>
            set { state with calls := removeCall state.calls call.streamId }
            pure (FinishStep.failed status)
        | none =>
            match record.trailers with
            | some trailers =>
                set { state with calls := removeCall state.calls call.streamId }
                pure (FinishStep.finished record.headers trailers)
            | none =>
                match state.dead with
                | some status =>
                    set { state with calls := removeCall state.calls call.streamId }
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
          set { state with calls := replaceCall state.calls record }
          match Http2.RstStream.frame call.streamId Http2.ErrorCode.cancel with
          | .ok rst => enqueueFrame call.connection rst
          | .error _ => pure ()
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
    (options : CallOptions := {}) : Async (Except Status (Metadata × ByteArray)) := do
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
