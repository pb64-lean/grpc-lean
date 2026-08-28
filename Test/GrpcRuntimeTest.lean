import Std.Async.TCP

import Grpc

open Grpc

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectExceptOk (result : Except String α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err)

def expectStatusOk [Repr ε] (result : Except ε α) : IO α := do
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (repr error).pretty)

def expectStatusError (result : Except Status α) : IO Status := do
  match result with
  | .ok _ => throw (IO.userError "expected gRPC status error")
  | .error status => pure status

def expectHttp2Error (result : Except _root_.Http2.Error α) : IO _root_.Http2.Error := do
  match result with
  | .ok _ => throw (IO.userError "expected HTTP/2 error")
  | .error error => pure error

def expectProtoOk (result : Except Protobuf.Encoding.ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

def bytes (xs : List Nat) : ByteArray :=
  xs.foldl (fun out n => out.push (UInt8.ofNat n)) ByteArray.empty

partial def repeatByte (n : Nat) (byte : UInt8) (out : ByteArray := ByteArray.empty) : ByteArray :=
  if n == 0 then
    out
  else
    repeatByte (n - 1) byte (out.push byte)

def dataPayloads (frames : Array _root_.Http2.Frame) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun out frame =>
    if frame.header.frameType == _root_.Http2.FrameType.data then
      out.append frame.payload
    else
      out

partial def takeHeaderBlockFramesFrom (frames : Array _root_.Http2.Frame) (i : Nat)
    (out : Array _root_.Http2.Frame := #[]) : Array _root_.Http2.Frame :=
  if i >= frames.size then
    out
  else
    let frame := frames[i]!
    if out.isEmpty then
      if frame.header.frameType != _root_.Http2.FrameType.headers then
        out
      else
        let out := out.push frame
        if _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endHeaders then
          out
        else
          takeHeaderBlockFramesFrom frames (i + 1) out
    else if frame.header.frameType != _root_.Http2.FrameType.continuation then
      out
    else
      let out := out.push frame
      if _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endHeaders then
        out
      else
        takeHeaderBlockFramesFrom frames (i + 1) out

def headerBlockPayload (frames : Array _root_.Http2.Frame) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun out frame => out.append frame.payload

/-- Decodes every server-emitted header block in emission order with a single
threaded HPACK decoder state, mirroring what a real client does. Returns the
decode result of each block in order. -/
def decodeServerHeaderBlocks (frames : Array _root_.Http2.Frame) :
    IO (Array _root_.Http2.Hpack.DecodeResult) := do
  let mut state : _root_.Http2.Hpack.State := {}
  let mut out := #[]
  let mut block := ByteArray.empty
  let mut inBlock := false
  for frame in frames do
    if inBlock then
      block := block.append frame.payload
      if _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endHeaders then
        let decoded ← expectStatusOk (_root_.Http2.Hpack.decodeHeaderBlock state block)
        state := decoded.state
        out := out.push decoded
        inBlock := false
    else if frame.header.frameType == _root_.Http2.FrameType.headers then
      if _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endHeaders then
        let decoded ← expectStatusOk (_root_.Http2.Hpack.decodeHeaderBlock state frame.payload)
        state := decoded.state
        out := out.push decoded
      else
        inBlock := true
        block := frame.payload
  pure out

/-- Decodes all server-emitted header blocks in order and returns the last one
(the trailers of the most recent response). -/
def decodeLastServerHeaderBlock (frames : Array _root_.Http2.Frame) (msg : String) :
    IO _root_.Http2.Hpack.DecodeResult := do
  let blocks ← decodeServerHeaderBlocks frames
  match blocks.back? with
  | some block => pure block
  | none => throw (IO.userError msg)

def largeAsciiString (size : Nat) : String :=
  String.ofList (List.replicate size 'a')

def awaitIoTask (task : Task (Except IO.Error α)) : IO α :=
  match task.get with
  | .ok value => pure value
  | .error err => throw err

partial def waitUntil (message : String) (remainingMilliseconds : Nat) (check : IO Bool) :
    IO Unit := do
  if ← check then
    pure ()
  else if remainingMilliseconds == 0 then
    throw (IO.userError message)
  else
    IO.sleep 1
    waitUntil message (remainingMilliseconds - 1) check

/-- Deadline for observing an asynchronous transition. Every wait below polls
for the observable condition and returns the moment it holds, so a generous
budget costs nothing on an idle machine and only bounds how long a genuine
failure takes to report. CI runners execute other repositories' suites
concurrently, so short fixed windows are not safe here. -/
def observeTimeoutMs : Nat := 5000

/-- Wait for `task`, polling so that the deadline costs nothing when the task
finishes early. Racing against a sleeping timeout task would instead keep a
worker asleep for the whole budget after the race is already decided. -/
partial def awaitTaskWithin (task : Task (Except IO.Error α)) (remainingMilliseconds : Nat) :
    IO (Option α) := do
  if ← IO.hasFinished task then
    match task.get with
    | .ok value => pure (some value)
    | .error err => throw err
  else if remainingMilliseconds == 0 then
    pure none
  else
    IO.sleep 1
    awaitTaskWithin task (remainingMilliseconds - 1)

partial def drainToEof (client : Std.Async.TCP.Socket.Client) : IO Unit := do
  match ← (client.recv? 8192).block with
  | none => pure ()
  | some _ => drainToEof client

/-- Wait for the peer's write side to close. Frames already in flight (a final
GOAWAY, a trailing RST_STREAM) are drained first: the observable guarantee is
that the stream ends, not that no bytes follow the last assertion. -/
def expectWriteSideClosed (client : Std.Async.TCP.Socket.Client) (message : String) :
    IO Unit := do
  let eofTask ← IO.asTask (drainToEof client)
  match ← awaitTaskWithin eofTask observeTimeoutMs with
  | some _ => pure ()
  | none =>
      IO.cancel eofTask
      throw (IO.userError message)

partial def readHttp2FramesFromSocket (client : Std.Async.TCP.Socket.Client)
    (decoder : _root_.Http2.Frame.DecodeState) (frames : Array _root_.Http2.Frame) (wanted : Nat) :
    IO (Array _root_.Http2.Frame) := do
  if frames.size >= wanted then
    pure frames
  else
    let chunk? ← (client.recv? 8192).block
    match chunk? with
    | none => pure frames
    | some chunk =>
        let decoded ← expectStatusOk (_root_.Http2.Frame.decodeChunk decoder chunk)
        readHttp2FramesFromSocket client { buffered := decoded.buffered } (frames.append decoded.frames) wanted

structure ReadHttp2FrameState where
  decoder : _root_.Http2.Frame.DecodeState := {}
  frames : Array _root_.Http2.Frame := #[]

partial def readHttp2FramesUntilFromSocket (client : Std.Async.TCP.Socket.Client)
    (state : ReadHttp2FrameState) (done : Array _root_.Http2.Frame -> Bool) :
    IO ReadHttp2FrameState := do
  if done state.frames then
    pure state
  else
    let chunk? ← (client.recv? 8192).block
    match chunk? with
    | none => pure state
    | some chunk =>
        let decoded ← expectStatusOk (_root_.Http2.Frame.decodeChunk state.decoder chunk)
        readHttp2FramesUntilFromSocket client
          { decoder := { buffered := decoded.buffered }, frames := state.frames.append decoded.frames }
          done

def readHttp2FramesUntilWithTimeout (client : Std.Async.TCP.Socket.Client)
    (state : ReadHttp2FrameState) (done : Array _root_.Http2.Frame -> Bool)
    (timeoutMs : Nat) (message : String) : IO ReadHttp2FrameState := do
  let readTask ← IO.asTask (readHttp2FramesUntilFromSocket client state done)
  match ← awaitTaskWithin readTask timeoutMs with
  | some state => pure state
  | none =>
      IO.cancel readTask
      throw (IO.userError message)

def runGrpcM (action : GrpcM α) : IO α := do
  match (← action.run) with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def expectGrpcMError (action : GrpcM α) : IO Status := do
  match (← action.run) with
  | .ok _ => throw (IO.userError "expected gRPC status error")
  | .error status => pure status

def throwGrpcIo {α} (message : String) : GrpcM α :=
  ExceptT.mk (throw (IO.userError message) : IO (Except Status α))

def rawByteCodec (data : ByteArray) : Except String ByteArray :=
  .ok data

partial def cancelledRecvLoop (seen : IO.Ref Bool) : GrpcM (Option ByteArray) := do
  if ← IO.checkCanceled then
    seen.set true
    throw (Status.cancelled "stream cancelled")
  IO.sleep 1
  cancelledRecvLoop seen

def testStatus : IO Unit := do
  expectEq (Code.ofString? "0") (some Code.ok) "grpc-status 0 should parse as OK"
  expectEq (Code.ofString? "16") (some Code.unauthenticated) "grpc-status 16 should parse"
  expectEq (Code.ofString? "17") none "unknown grpc-status code should reject"
  expectEq Code.internal.toHeaderValue "13" "internal status header value should be 13"
  let dispatchCancelled := Status.ofIOError (IO.userError Status.dispatchCancelledMessage)
  expectEq dispatchCancelled.code Code.cancelled "runtime dispatch cancellation should map to CANCELLED"
  expectEq dispatchCancelled.message (some Status.dispatchCancelledMessage)
    "runtime dispatch cancellation should preserve its status message"
  let handlerFailed := Status.ofIOError (IO.userError "handler exploded")
  expectEq handlerFailed.code Code.unknown "arbitrary handler IO errors should remain UNKNOWN"

def testMetadata : IO Unit := do
  let metadata := Grpc.Metadata.insertBinary
    (_root_.Http2.Headers.empty
      |>.insert "Content-Type" "application/grpc+proto"
      |>.insert "te" "trailers")
    "trace-bin" (bytes [1, 2, 3, 4])
  expectEq (metadata.get? "content-type") (some "application/grpc+proto") "metadata lookup should be case-normalized"
  expect (metadata.contains "TE" "trailers") "metadata should retain values"
  expectEq (metadata.get? "trace-bin") (some "AQIDBA")
    "binary metadata should be emitted without base64 padding"
  let binary ← expectExceptOk (Grpc.Metadata.getBinary? metadata "trace-bin")
  expectEq binary (some (bytes [1, 2, 3, 4])) "binary metadata should base64 round-trip"
  let mixedCaseBinaryMetadata := Grpc.Metadata.insertBinary
    _root_.Http2.Headers.empty "Trace-Bin" (bytes [5, 6])
  expectEq (mixedCaseBinaryMetadata.get? "trace-bin") (some "BQY")
    "binary metadata insertion should normalize mixed-case -bin suffixes"
  expectEq (mixedCaseBinaryMetadata.get? "trace-bin-bin") none
    "binary metadata insertion should not append a duplicate -bin suffix after normalization"
  let mixedCaseBinary ← expectExceptOk
    (Grpc.Metadata.getBinary? mixedCaseBinaryMetadata "Trace-Bin")
  expectEq mixedCaseBinary (some (bytes [5, 6]))
    "binary metadata lookup should normalize mixed-case -bin suffixes"
  let singleByteMetadata := Grpc.Metadata.insertBinary
    _root_.Http2.Headers.empty "single-bin" (bytes [255])
  expectEq (singleByteMetadata.get? "single-bin") (some "/w")
    "single-byte binary metadata should omit base64 padding"
  let unpaddedMetadata := _root_.Http2.Headers.empty.insert "trace-bin" "AQIDBA"
  let unpaddedBinary ← expectExceptOk
    (Grpc.Metadata.getBinary? unpaddedMetadata "trace-bin")
  expectEq unpaddedBinary (some (bytes [1, 2, 3, 4]))
    "binary metadata should accept unpadded base64 values"
  let joinedMetadata := _root_.Http2.Headers.empty.insert "trace-bin" "AQI,AwQ="
  let joinedBinary ← expectExceptOk
    (Grpc.Metadata.getBinaryAll joinedMetadata "trace-bin")
  expectEq joinedBinary #[bytes [1, 2], bytes [3, 4]]
    "binary metadata should split comma-joined base64 values"
  let duplicateMetadata := _root_.Http2.Headers.empty.insert "trace-bin" "AQI"
    |>.insert "trace-bin" "AwQ="
  let duplicateBinary ← expectExceptOk
    (Grpc.Metadata.getBinaryAll duplicateMetadata "trace-bin")
  expectEq duplicateBinary #[bytes [1, 2], bytes [3, 4]]
    "binary metadata should preserve duplicate header values"

def testFraming : IO Unit := do
  let first : Message := { data := bytes [1, 2, 3] }
  let second : Message := { data := bytes [4, 5] }
  let firstWire ← expectStatusOk first.encode
  let secondWire ← expectStatusOk second.encode
  let combined := firstWire.append secondWire
  let all ← expectStatusOk (Message.decodeAll combined)
  expectEq all.size 2 "two framed messages should decode"
  expectEq all[0]!.data first.data "first message payload should match"
  expectEq all[1]!.data second.data "second message payload should match"

  let splitAt := firstWire.size + 2
  let state0 : Message.DecodeState := {}
  let state1 ← expectStatusOk (Message.decodeChunk state0 (combined.extract 0 splitAt))
  expectEq state1.messages.size 1 "first fragmented chunk should emit complete first message"
  expectEq state1.buffered.size 2 "first fragmented chunk should keep partial second message"
  let state2 ← expectStatusOk (Message.decodeChunk state1 (combined.extract splitAt combined.size))
  expectEq state2.messages.size 1 "second fragmented chunk should emit second message"
  expectEq state2.messages[0]!.data second.data "fragmented second payload should match"
  expectEq state2.buffered.size 0 "final fragmented state should have empty buffer"

def requestHeadersForPath (path : String) : _root_.Http2.Headers :=
  _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

def requestHeaders : _root_.Http2.Headers :=
  requestHeadersForPath "/lean.example.proto.NoteService/Echo"

def testProtocol : IO Unit := do
  let method ← expectStatusOk (Headers.validateUnaryRequestHeaders requestHeaders)
  expectEq method.service "lean.example.proto.NoteService" "service name should parse from path"
  expectEq method.method "Echo" "method name should parse from path"
  let timeoutHeaders := requestHeaders.insert "grpc-timeout" "250m"
  let timeout ← expectStatusOk (Headers.timeout? timeoutHeaders)
  expectEq (timeout.map Timeout.toNanoseconds) (some 250000000)
    "grpc-timeout should parse millisecond values"
  discard <| expectStatusOk (Headers.validateUnaryRequestHeaders timeoutHeaders)
  let tooManyDigitsStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-timeout" "123456789S")
  expectEq tooManyDigitsStatus.code Code.invalidArgument
    "grpc-timeout values longer than eight digits should reject"
  let invalidUnitStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-timeout" "1x")
  expectEq invalidUnitStatus.code Code.invalidArgument
    "grpc-timeout values with unknown units should reject"
  let missingSchemeHeaders := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let missingSchemeStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders missingSchemeHeaders
  expectEq missingSchemeStatus.code Code.invalidArgument
    "missing :scheme should reject"
  let unsupportedSchemeStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (missingSchemeHeaders.insert ":scheme" "ftp")
  expectEq unsupportedSchemeStatus.code Code.invalidArgument
    "unsupported :scheme should reject"
  let duplicatePseudoHeaders := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":scheme" "https"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let duplicatePseudoStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders duplicatePseudoHeaders
  expectEq duplicatePseudoStatus.code Code.invalidArgument
    "duplicate HTTP/2 pseudo-headers should reject"
  let responsePseudoHeaders := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":status" "200"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let responsePseudoStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders responsePseudoHeaders
  expectEq responsePseudoStatus.code Code.invalidArgument
    "request headers should reject response-only :status pseudo-header"
  let latePseudoHeaders := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert "content-type" "application/grpc"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "te" "trailers"
  let latePseudoStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders latePseudoHeaders
  expectEq latePseudoStatus.code Code.invalidArgument
    "HTTP/2 pseudo-headers after regular metadata should reject"
  let connectionHeaderStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "connection" "keep-alive")
  expectEq connectionHeaderStatus.code Code.invalidArgument
    "HTTP/2 connection-specific headers should reject"
  let transferEncodingStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "transfer-encoding" "chunked")
  expectEq transferEncodingStatus.code Code.invalidArgument
    "HTTP/2 transfer-encoding headers should reject"
  let duplicateContentTypeStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "content-type" "application/grpc+proto")
  expectEq duplicateContentTypeStatus.code Code.invalidArgument
    "duplicate content-type headers should reject"
  let protoContentTypeHeaders := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc+proto"
    |>.insert "te" "trailers"
  discard <| expectStatusOk (Headers.validateUnaryRequestHeaders protoContentTypeHeaders)
  let jsonContentTypeHeaders := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc+json"
    |>.insert "te" "trailers"
  let jsonContentTypeStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders jsonContentTypeHeaders
  expectEq jsonContentTypeStatus.code Code.invalidArgument
    "non-protobuf gRPC content-type values should reject"
  let duplicateTeStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "te" "trailers")
  expectEq duplicateTeStatus.code Code.invalidArgument
    "duplicate te headers should reject"
  let duplicateTimeoutStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-timeout" "1S" |>.insert "grpc-timeout" "2S")
  expectEq duplicateTimeoutStatus.code Code.invalidArgument
    "duplicate grpc-timeout headers should reject"
  let duplicateEncodingStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-encoding" "identity" |>.insert "grpc-encoding" "identity")
  expectEq duplicateEncodingStatus.code Code.invalidArgument
    "duplicate grpc-encoding headers should reject"
  let contentLength ← expectStatusOk (Headers.contentLength? (requestHeaders.insert "content-length" "5"))
  expectEq contentLength (some 5) "content-length should parse decimal byte counts"
  let invalidContentLengthStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "content-length" "bad")
  expectEq invalidContentLengthStatus.code Code.invalidArgument
    "invalid content-length headers should reject"
  let duplicateContentLengthStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "content-length" "1" |>.insert "content-length" "1")
  expectEq duplicateContentLengthStatus.code Code.invalidArgument
    "duplicate content-length headers should reject"
  discard <| expectStatusOk (Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-encoding" "identity"))
  discard <| expectStatusOk
    (Headers.validateUnaryRequestHeaders (requestHeaders.push (_root_.Http2.Header.of "trace-bin" "AQIDBA")))
  discard <| expectStatusOk
    (Headers.validateUnaryRequestHeaders (requestHeaders.push (_root_.Http2.Header.of "trace-bin" "AQI,AwQ=")))
  discard <| expectStatusOk (Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-encoding" "gzip"))
  let unsupportedEncodingStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.insert "grpc-encoding" "deflate")
  expectEq unsupportedEncodingStatus.code Code.unimplemented
    "unsupported grpc-encoding values should reject"
  let badNameStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.push { name := "bad header", value := "x" })
  expectEq badNameStatus.code Code.invalidArgument
    "metadata names with spaces should reject"
  let badAsciiValueStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.push (_root_.Http2.Header.of "x-meta" "bad\nvalue"))
  expectEq badAsciiValueStatus.code Code.invalidArgument
    "ASCII metadata values with control characters should reject"
  let badBinaryValueStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.push (_root_.Http2.Header.of "trace-bin" "bad!"))
  expectEq badBinaryValueStatus.code Code.invalidArgument
    "binary metadata values with invalid base64 should reject"
  let badBinaryLengthStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.push (_root_.Http2.Header.of "trace-bin" "A"))
  expectEq badBinaryLengthStatus.code Code.invalidArgument
    "binary metadata values with invalid base64 length should reject"
  let trailers := Headers.trailers (Status.error .invalidArgument "bad input")
  expectEq (trailers.get? "grpc-status") (some "3") "trailers should contain grpc-status"
  expectEq (trailers.get? "grpc-message") (some "bad input") "simple grpc-message should pass through"
  let parsedTrailers ← expectStatusOk (Headers.statusFromTrailers trailers)
  expectEq parsedTrailers (Status.error .invalidArgument "bad input")
    "trailers should parse back into a gRPC status"
  let escapedTrailers := Headers.trailers (Status.error .internal "line 1\n100% failed")
  expectEq (escapedTrailers.get? "grpc-message") (some "line 1%0A100%25 failed")
    "grpc-message should percent-encode control characters and percent signs"
  let parsedEscapedTrailers ← expectStatusOk (Headers.statusFromTrailers escapedTrailers)
  expectEq parsedEscapedTrailers (Status.error .internal "line 1\n100% failed")
    "grpc-message parser should percent-decode trailer values"
  let missingGrpcStatus ← expectStatusError (Headers.statusFromTrailers _root_.Http2.Headers.empty)
  expectEq missingGrpcStatus.code Code.unknown "missing grpc-status trailer should reject"
  let invalidGrpcStatus ← expectStatusError
    (Headers.statusFromTrailers (_root_.Http2.Headers.empty.insert "grpc-status" "17"))
  expectEq invalidGrpcStatus.code Code.unknown "invalid grpc-status trailer should reject"
  let invalidGrpcMessage ← expectStatusError
    (Headers.statusFromTrailers (_root_.Http2.Headers.empty.insert "grpc-status" "13" |>.insert "grpc-message" "%"))
  expectEq invalidGrpcMessage.code Code.unknown "invalid grpc-message trailer should reject"
  let duplicateGrpcStatus ← expectStatusError
    (Headers.statusFromTrailers (_root_.Http2.Headers.empty.insert "grpc-status" "0" |>.insert "grpc-status" "13"))
  expectEq duplicateGrpcStatus.code Code.invalidArgument "duplicate grpc-status trailers should reject"

def testDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "lean",
      data := request.data,
      status := Status.ok
    }
  let requestMessage : Message := { data := bytes [9, 8, 7] }
  let body ← expectStatusOk requestMessage.encode
  let response ← runGrpcM (registry.dispatchUnary requestHeaders body)
  expectEq response.status.code Code.ok "unary response status should be OK"
  expectEq response.data requestMessage.data "unary response should echo payload"
  expectEq (response.metadata.get? "handled-by") (some "lean") "unary handler metadata should be preserved"
  let lengthResponse ← runGrpcM
    (registry.dispatchUnary (requestHeaders.insert "content-length" (toString body.size)) body)
  expectEq lengthResponse.status.code Code.ok "matching content-length should be accepted"
  let lengthStatus ← expectGrpcMError <|
    registry.dispatchUnary (requestHeaders.insert "content-length" (toString (body.size + 1))) body
  expectEq lengthStatus.code Code.invalidArgument "mismatched unary content-length should reject"

def testServerStreamingDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "List" }
  let registry := Registry.empty.registerServerStreaming method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "server-streaming",
      messages := #[request.data, (bytes [4, 5, 6])],
      status := Status.ok
    }
  let requestMessage : Message := { data := bytes [1, 2, 3] }
  let body ← expectStatusOk requestMessage.encode
  let headers := requestHeadersForPath "/lean.example.proto.NoteService/List"
  let response ← runGrpcM (registry.dispatchServerStreaming headers body)
  expectEq response.status.code Code.ok "server-streaming response status should be OK"
  expectEq response.messages.size 2 "server-streaming response should contain two messages"
  expectEq response.messages[0]! requestMessage.data "first streamed response should echo payload"
  expectEq response.messages[1]! (bytes [4, 5, 6]) "second streamed response should preserve payload"
  expectEq (response.metadata.get? "handled-by") (some "server-streaming")
    "server-streaming handler metadata should be preserved"

def testClientStreamingDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Collect" }
  let registry := Registry.empty.registerClientStreaming method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "client-streaming",
      data := request.messages.foldl (fun out message => out.append message) ByteArray.empty,
      status := Status.ok
    }
  let first : Message := { data := bytes [1, 2] }
  let second : Message := { data := bytes [3, 4] }
  let firstBody ← expectStatusOk first.encode
  let secondBody ← expectStatusOk second.encode
  let requestBody := firstBody.append secondBody
  let headers := requestHeadersForPath "/lean.example.proto.NoteService/Collect"
  let response ← runGrpcM (registry.dispatchClientStreaming headers requestBody)
  expectEq response.status.code Code.ok "client-streaming response status should be OK"
  expectEq response.data (bytes [1, 2, 3, 4])
    "client-streaming handler should receive all request messages"
  expectEq (response.metadata.get? "handled-by") (some "client-streaming")
    "client-streaming handler metadata should be preserved"
  let lengthResponse ← runGrpcM
    (registry.dispatchClientStreaming (headers.insert "content-length" (toString requestBody.size)) requestBody)
  expectEq lengthResponse.status.code Code.ok "matching client-streaming content-length should be accepted"
  let lengthStatus ← expectGrpcMError <|
    registry.dispatchClientStreaming (headers.insert "content-length" (toString (requestBody.size - 1))) requestBody
  expectEq lengthStatus.code Code.invalidArgument
    "mismatched client-streaming content-length should reject"

def testBidirectionalStreamingDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Chat" }
  let registry := Registry.empty.registerBidirectionalStreaming method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "bidirectional-streaming",
      messages := request.messages.map (fun message => message.append (bytes [9])),
      status := Status.ok
    }
  let first : Message := { data := bytes [1, 2] }
  let second : Message := { data := bytes [3, 4] }
  let firstBody ← expectStatusOk first.encode
  let secondBody ← expectStatusOk second.encode
  let headers := requestHeadersForPath "/lean.example.proto.NoteService/Chat"
  let response ← runGrpcM (registry.dispatchBidirectionalStreaming headers (firstBody.append secondBody))
  expectEq response.status.code Code.ok "bidirectional-streaming response status should be OK"
  expectEq response.messages.size 2 "bidirectional-streaming response should contain two messages"
  expectEq response.messages[0]! (bytes [1, 2, 9])
    "first bidirectional-streaming response should transform first request"
  expectEq response.messages[1]! (bytes [3, 4, 9])
    "second bidirectional-streaming response should transform second request"
  expectEq (response.metadata.get? "handled-by") (some "bidirectional-streaming")
    "bidirectional-streaming handler metadata should be preserved"

def reflectionBody (request : Services.Reflection.Request) : IO ByteArray := do
  let data ← expectProtoOk (Services.Reflection.Request.encode request)
  expectStatusOk (Message.encode { data := data })

def dispatchReflection (registry : Registry) (serviceName : String)
    (request : Services.Reflection.Request) : IO Services.Reflection.Response := do
  let body ← reflectionBody request
  let method := Services.Reflection.methodNameForService serviceName
  let response ← runGrpcM (registry.dispatchBidirectionalStreaming
    (requestHeadersForPath method.path) body)
  expectEq response.messages.size 1 "reflection request should emit one response"
  expectProtoOk (Services.Reflection.Response.decode response.messages[0]!)

def testReflectionService : IO Unit := do
  let echoMethod : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry :=
    Services.Reflection.register <|
      Registry.empty.registerUnary echoMethod fun request => do
        pure { data := request.data }

  for reflectionService in Services.Reflection.reflectionServiceNames do
    let response ← dispatchReflection registry reflectionService {
      kind := some (.listServices "")
    }
    match response.kind with
    | some (.listServicesResponse services) =>
        let names := services.service.map (fun service => service.name)
        expect (names.contains "lean.example.proto.NoteService")
          "reflection list_services should include registered application services"
        expect (names.contains Services.Reflection.v1ServiceName)
          "reflection list_services should include the v1 reflection service"
        expect (names.contains Services.Reflection.v1alphaServiceName)
          "reflection list_services should include the v1alpha reflection service"
    | _ => throw (IO.userError "reflection list_services returned the wrong response kind")

  let stableRegistry := Services.Reflection.registerV1With {
    serviceNames := #[Services.Reflection.v1alphaServiceName]
  } <| Registry.empty.registerUnary echoMethod fun request => do
    pure { data := request.data }
  let stableResponse ← dispatchReflection stableRegistry Services.Reflection.v1ServiceName {
    kind := some (.listServices "")
  }
  match stableResponse.kind with
  | some (.listServicesResponse services) =>
      let names := services.service.map (fun service => service.name)
      expect (names.contains "lean.example.proto.NoteService")
        "stable reflection list_services omitted an application service"
      expect (names.contains Services.Reflection.v1ServiceName)
        "stable reflection list_services omitted v1"
      expect (!names.contains Services.Reflection.v1alphaServiceName)
        "stable reflection advertised configured v1alpha"
  | _ => throw (IO.userError "stable reflection list_services returned the wrong response kind")
  let alphaBody ← reflectionBody { kind := some (.listServices "") }
  let alphaResult ← (stableRegistry.dispatchBidirectionalStreaming
    (requestHeadersForPath Services.Reflection.v1alphaMethodName.path) alphaBody).run
  let alphaStatus ← expectStatusError alphaResult
  expectEq alphaStatus.code Code.unimplemented
    "stable reflection unexpectedly registered the v1alpha route"

  let rootDescriptor := bytes [1, 2, 3]
  let dependencyDescriptor := bytes [4, 5, 6]
  let registry := Services.Reflection.registerWith {
    serviceNames := #["lean.example.proto.NoteService"],
    files := #[
      {
        name := "common.proto",
        symbols := #["lean.example.proto.NoteMeta"],
        fileDescriptorProto := dependencyDescriptor
      },
      {
        name := "note.proto",
        symbols := #["lean.example.proto.NoteService", "lean.example.proto.Note"],
        dependencies := #["common.proto"],
        extensions := #[
          {
            containingType := "lean.example.proto.Note",
            extensionNumber := 100
          }
        ],
        fileDescriptorProto := rootDescriptor
      }
    ]
  } Registry.empty

  let descriptorRequest : Services.Reflection.Request := {
    host := "reflection.test"
    kind := some (.fileByFilename "note.proto")
  }
  let descriptorResponse ← dispatchReflection registry Services.Reflection.v1ServiceName
    descriptorRequest
  expectEq descriptorResponse.validHost descriptorRequest.host
    "reflection responses should preserve the requested host"
  expectEq descriptorResponse.originalRequest descriptorRequest
    "reflection responses should preserve the original request"
  match descriptorResponse.kind with
  | some (.fileDescriptorResponse files) =>
      expectEq files.fileDescriptorProto.size 2
        "reflection file_by_filename should include the requested descriptor and dependency"
      expectEq files.fileDescriptorProto[0]! rootDescriptor
        "reflection file_by_filename should return the requested descriptor first"
      expectEq files.fileDescriptorProto[1]! dependencyDescriptor
        "reflection file_by_filename should return transitive dependencies"
  | _ => throw (IO.userError "reflection file_by_filename returned the wrong response kind")

  let extensionDescriptorResponse ← dispatchReflection registry Services.Reflection.v1ServiceName {
    kind := some (.fileContainingExtension {
      containingType := "lean.example.proto.Note",
      extensionNumber := 100
    })
  }
  match extensionDescriptorResponse.kind with
  | some (.fileDescriptorResponse files) =>
      expectEq files.fileDescriptorProto[0]! rootDescriptor
        "reflection file_containing_extension should return the declaring descriptor"
  | _ => throw (IO.userError "reflection file_containing_extension returned the wrong response kind")

  let extensionNumbersResponse ← dispatchReflection registry Services.Reflection.v1ServiceName {
    kind := some (.allExtensionNumbersOfType "lean.example.proto.Note")
  }
  match extensionNumbersResponse.kind with
  | some (.allExtensionNumbersResponse numbers) =>
      expectEq numbers.baseTypeName "lean.example.proto.Note"
        "reflection all_extension_numbers_of_type should preserve the type name"
      expect (numbers.extensionNumber.contains 100)
        "reflection all_extension_numbers_of_type should include configured extensions"
  | _ => throw (IO.userError "reflection all_extension_numbers_of_type returned the wrong response kind")

  let missingResponse ← dispatchReflection registry Services.Reflection.v1ServiceName {
    host := "missing.test"
    kind := some (.fileContainingSymbol "missing.Symbol")
  }
  match missingResponse.kind with
  | some (.errorResponse err) =>
      expectEq missingResponse.validHost "missing.test"
        "reflection errors should preserve the requested host"
      expectEq err.errorCode (Int32.ofInt (Int.ofNat Code.notFound.toNat))
        "missing reflection symbols should return NOT_FOUND"
  | _ => throw (IO.userError "missing reflection symbol should return an error response")

  let unsetResponse ← dispatchReflection registry Services.Reflection.v1ServiceName {
    host := "unset.test"
  }
  match unsetResponse.kind with
  | some (.errorResponse err) =>
      expectEq unsetResponse.validHost "unset.test"
        "unset reflection errors should preserve the requested host"
      expectEq err.errorCode (Int32.ofInt (Int.ofNat Code.unimplemented.toNat))
        "unset reflection requests should match grpc-java UNIMPLEMENTED"
      expectEq err.errorMessage "not implemented MESSAGE_REQUEST_NOT_SET"
        "unset reflection requests should match grpc-java's error description"
  | _ => throw (IO.userError "unset reflection request should return an error response")

def testStreamNativeDispatch : IO Unit := do
  let listMethod : MethodName := { service := "lean.example.proto.NoteService", method := "StreamList" }
  let collectMethod : MethodName := { service := "lean.example.proto.NoteService", method := "StreamCollect" }
  let chatMethod : MethodName := { service := "lean.example.proto.NoteService", method := "StreamChat" }
  let incrementalCollectMethod : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "IncrementalStreamCollect"
  }
  let lazyChatMethod : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "LazyStreamChat"
  }
  let asyncListMethod : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "AsyncStreamList"
  }

  let serverStreamingRegistry := Registry.empty.registerServerStreamingStreamCodec
    listMethod rawByteCodec rawByteCodec fun input => do
      MessageStream.ofArray #[input.append (bytes [9]), bytes [4, 5, 6]]
  let requestMessage : Message := { data := bytes [1, 2, 3] }
  let body ← expectStatusOk requestMessage.encode
  let listHeaders := requestHeadersForPath "/lean.example.proto.NoteService/StreamList"
  let listResponse ← runGrpcM (serverStreamingRegistry.dispatchServerStreaming listHeaders body)
  expectEq listResponse.status.code Code.ok "stream-native server-streaming status should be OK"
  expectEq listResponse.messages.size 2 "stream-native server-streaming should emit two messages"
  expectEq listResponse.messages[0]! (bytes [1, 2, 3, 9])
    "stream-native server-streaming should transform the unary request"
  expectEq listResponse.messages[1]! (bytes [4, 5, 6])
    "stream-native server-streaming should emit subsequent stream values"

  let clientStreamingRegistry := Registry.empty.registerClientStreamingStreamCodec
    collectMethod rawByteCodec rawByteCodec fun input => do
      let messages ← input.collect
      pure (messages.foldl (fun out message => out.append message) ByteArray.empty)
  let firstBody ← expectStatusOk (Message.encode { data := bytes [1, 2] })
  let secondBody ← expectStatusOk (Message.encode { data := bytes [3, 4] })
  let collectHeaders := requestHeadersForPath "/lean.example.proto.NoteService/StreamCollect"
  let collectResponse ← runGrpcM
    (clientStreamingRegistry.dispatchClientStreaming collectHeaders (firstBody.append secondBody))
  expectEq collectResponse.status.code Code.ok "stream-native client-streaming status should be OK"
  expectEq collectResponse.data (bytes [1, 2, 3, 4])
    "stream-native client-streaming should let handlers consume request streams"

  let bidiRegistry := Registry.empty.registerBidirectionalStreamingStreamCodec
    chatMethod rawByteCodec rawByteCodec fun input => do
      let messages ← input.collect
      MessageStream.ofArray (messages.map fun message => message.append (bytes [8]))
  let chatHeaders := requestHeadersForPath "/lean.example.proto.NoteService/StreamChat"
  let chatResponse ← runGrpcM
    (bidiRegistry.dispatchBidirectionalStreaming chatHeaders (firstBody.append secondBody))
  expectEq chatResponse.status.code Code.ok "stream-native bidi status should be OK"
  expectEq chatResponse.messages.size 2 "stream-native bidi should emit response stream messages"
  expectEq chatResponse.messages[0]! (bytes [1, 2, 8])
    "stream-native bidi should transform the first request message"
  expectEq chatResponse.messages[1]! (bytes [3, 4, 8])
    "stream-native bidi should transform the second request message"

  let incrementalSeenFirst ← IO.mkRef false
  let incrementalRegistry := Registry.empty.registerClientStreamingStreamCodec
    incrementalCollectMethod rawByteCodec rawByteCodec fun input => do
      match ← input.recv? with
      | some first =>
          incrementalSeenFirst.set true
          pure first
      | none => throw (Status.invalidArgument "expected streamed request message")
  let incrementalProducer ← runGrpcM (MessageStream.pipe (α := ByteArray) (capacity := some 1))
  let incrementalHeaders :=
    requestHeadersForPath "/lean.example.proto.NoteService/IncrementalStreamCollect"
  let incrementalTask ← IO.asTask do
    runGrpcM (incrementalRegistry.dispatchClientStreamingMessageStream
      incrementalHeaders incrementalProducer.stream)
  runGrpcM (incrementalProducer.send (bytes [6, 7]))
  waitUntil "stream-native client-streaming handler did not observe first message before close" observeTimeoutMs
    incrementalSeenFirst.get
  let incrementalResponse ← awaitIoTask incrementalTask
  expectEq incrementalResponse.data (bytes [6, 7])
    "stream-native client-streaming message-stream dispatch should not wait for request close"
  runGrpcM incrementalProducer.cancel

  let lazyBidiRegistry := Registry.empty.registerBidirectionalStreamingStreamCodec
    lazyChatMethod rawByteCodec rawByteCodec fun input => do
      pure (input.mapM fun message => pure (message.append (bytes [7])))
  let lazyProducer ← runGrpcM (MessageStream.pipe (α := ByteArray) (capacity := some 1))
  let lazyHeaders := requestHeadersForPath "/lean.example.proto.NoteService/LazyStreamChat"
  let lazyResponse ← runGrpcM
    (lazyBidiRegistry.dispatchBidirectionalStreamingMessageStream lazyHeaders lazyProducer.stream)
  let lazyRecvTask ← IO.asTask do
    lazyResponse.messages.recv?.run
  runGrpcM (lazyProducer.send (bytes [8, 8]))
  match ← awaitIoTask lazyRecvTask with
  | .ok (some message) =>
      expectEq message (bytes [8, 8, 7])
        "stream-native bidi response should emit before client request stream closes"
  | .ok none => throw (IO.userError "stream-native bidi response ended before first message")
  | .error status => throw (IO.userError status.messageD)
  runGrpcM lazyProducer.cancel

  let asyncProducerTask ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
  let asyncRegistry := Registry.empty.registerServerStreamingStreamCodec
    asyncListMethod rawByteCodec rawByteCodec fun input => do
      let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
      let task ← IO.asTask do
        runGrpcM do
          producer.send (input.append (bytes [7]))
          IO.sleep 1
          producer.send (bytes [8, 9])
          producer.close
      asyncProducerTask.set (some task)
      pure producer.stream
  let asyncHeaders := requestHeadersForPath "/lean.example.proto.NoteService/AsyncStreamList"
  let asyncResponse ← runGrpcM (asyncRegistry.dispatchServerStreaming asyncHeaders body)
  expectEq asyncResponse.status.code Code.ok "producer-backed server-streaming status should be OK"
  expectEq asyncResponse.messages.size 2 "producer-backed server-streaming should emit two messages"
  expectEq asyncResponse.messages[0]! (bytes [1, 2, 3, 7])
    "producer-backed server-streaming should transform the unary request"
  expectEq asyncResponse.messages[1]! (bytes [8, 9])
    "producer-backed server-streaming should emit asynchronous stream values"
  match ← asyncProducerTask.get with
  | none => throw (IO.userError "expected producer task to start")
  | some task => awaitIoTask task

def testMessageStreamPipe : IO Unit := do
  let producer ← runGrpcM (MessageStream.pipe (α := ByteArray) (capacity := some 1))
  let producerTask ← IO.asTask do
    runGrpcM do
      producer.send (bytes [1])
      producer.send (bytes [2, 3])
      producer.close
  let messages ← runGrpcM producer.stream.collect
  expectEq messages.size 2 "producer-backed streams should collect sent messages"
  expectEq messages[0]! (bytes [1]) "producer-backed streams should preserve first message"
  expectEq messages[1]! (bytes [2, 3]) "producer-backed streams should preserve second message"
  awaitIoTask producerTask

  let failingProducer ← runGrpcM (MessageStream.pipe (α := ByteArray) (capacity := some 1))
  let failTask ← IO.asTask do
    runGrpcM do
      failingProducer.fail (Status.internal "stream failed")
  let status ← expectGrpcMError failingProducer.stream.collect
  expectEq status.code Code.internal "producer-backed streams should propagate explicit status errors"
  expectEq status.message (some "stream failed")
    "producer-backed streams should preserve explicit status messages"
  awaitIoTask failTask

  let cancelledProducer ← runGrpcM (MessageStream.pipe (α := ByteArray) (capacity := some 1))
  let recvTask ← IO.asTask do
    cancelledProducer.stream.recv?.run
  runGrpcM cancelledProducer.cancel
  match ← awaitIoTask recvTask with
  | .ok none => pure ()
  | .ok (some _) => throw (IO.userError "cancelled producer-backed streams should not emit a message")
  | .error status =>
      throw (IO.userError s!"cancelled producer-backed streams should close cleanly, got {status.messageD}")

def testDeadlineExceededDispatch : IO Unit := do
  let echoMethod : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let listMethod : MethodName := { service := "lean.example.proto.NoteService", method := "List" }
  let collectMethod : MethodName := { service := "lean.example.proto.NoteService", method := "Collect" }
  let chatMethod : MethodName := { service := "lean.example.proto.NoteService", method := "Chat" }
  let registry := Registry.empty
    |>.registerUnary echoMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := _root_.Http2.Headers.empty,
        data := request.data,
        status := Status.ok
      })
    |>.registerServerStreaming listMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := _root_.Http2.Headers.empty,
        messages := #[request.data],
        status := Status.ok
      })
    |>.registerClientStreaming collectMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := _root_.Http2.Headers.empty,
        data := request.messages.foldl (fun out message => out.append message) ByteArray.empty,
        status := Status.ok
      })
    |>.registerBidirectionalStreaming chatMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := _root_.Http2.Headers.empty,
        messages := request.messages,
        status := Status.ok
      })

  let requestMessage : Message := { data := bytes [1, 2, 3] }
  let body ← expectStatusOk requestMessage.encode
  let secondBody ← expectStatusOk (Message.encode { data := bytes [4, 5, 6] })

  let echoStatus ← expectGrpcMError <|
    registry.dispatchUnary (requestHeaders.insert "grpc-timeout" "1m") body
  expectEq echoStatus.code Code.deadlineExceeded
    "unary handlers should respect grpc-timeout deadlines"

  let listStatus ← expectGrpcMError <|
    registry.dispatchServerStreaming
      ((requestHeadersForPath "/lean.example.proto.NoteService/List").insert "grpc-timeout" "1m")
      body
  expectEq listStatus.code Code.deadlineExceeded
    "server-streaming handlers should respect grpc-timeout deadlines"

  let streamCancelled ← IO.mkRef false
  let streamDeadlineRegistry := Registry.empty
    |>.registerServerStreamingStream listMethod (fun _request => do
      let stream : MessageStream ByteArray := {
        recv? := do
          IO.sleep 20
          pure none,
        cancel := do
          streamCancelled.set true
      }
      pure {
        metadata := _root_.Http2.Headers.empty,
        messages := stream,
        status := Status.ok
      })
  let streamDeadlineStatus ← expectGrpcMError <|
    streamDeadlineRegistry.dispatchServerStreaming
      ((requestHeadersForPath "/lean.example.proto.NoteService/List").insert "grpc-timeout" "1m")
      body
  expectEq streamDeadlineStatus.code Code.deadlineExceeded
    "server-streaming response streams should respect grpc-timeout deadlines"
  expect (← streamCancelled.get)
    "deadline-expired response streams should be cancelled"

  let cumulativeStreamCancelled ← IO.mkRef false
  let cumulativeStreamDeadlineRegistry := Registry.empty
    |>.registerServerStreamingStream listMethod (fun request => do
      let sent ← IO.mkRef false
      let stream : MessageStream ByteArray := {
        recv? := do
          if ← sent.get then
            IO.sleep 70
            pure none
          else
            sent.set true
            IO.sleep 70
            pure (some request.data),
        cancel := do
          cumulativeStreamCancelled.set true
      }
      pure {
        metadata := _root_.Http2.Headers.empty,
        messages := stream,
        status := Status.ok
      })
  let cumulativeStreamDeadlineStatus ← expectGrpcMError <|
    cumulativeStreamDeadlineRegistry.dispatchServerStreaming
      ((requestHeadersForPath "/lean.example.proto.NoteService/List").insert "grpc-timeout" "100m")
      body
  expectEq cumulativeStreamDeadlineStatus.code Code.deadlineExceeded
    "server-streaming response streams should use one cumulative grpc-timeout deadline"
  expect (← cumulativeStreamCancelled.get)
    "cumulative deadline-expired response streams should be cancelled"

  let collectStatus ← expectGrpcMError <|
    registry.dispatchClientStreaming
      ((requestHeadersForPath "/lean.example.proto.NoteService/Collect").insert "grpc-timeout" "1m")
      (body.append secondBody)
  expectEq collectStatus.code Code.deadlineExceeded
    "client-streaming handlers should respect grpc-timeout deadlines"

  let streamCollectRegistry := Registry.empty
    |>.registerClientStreamingStream collectMethod (fun request => do
      let messages ← request.messages.collect
      pure {
        metadata := _root_.Http2.Headers.empty,
        data := messages.foldl (fun out message => out.append message) ByteArray.empty,
        status := Status.ok
      })
  let slowInputSent ← IO.mkRef false
  let slowInputStream : MessageStream ByteArray := {
    recv? := do
      if ← slowInputSent.get then
        IO.sleep 70
        pure none
      else
        slowInputSent.set true
        IO.sleep 70
        pure (some (bytes [9, 9, 9]))
  }
  let streamCollectStatus ← expectGrpcMError <|
    streamCollectRegistry.dispatchClientStreamingMessageStream
      ((requestHeadersForPath "/lean.example.proto.NoteService/Collect").insert "grpc-timeout" "100m")
      slowInputStream
  expectEq streamCollectStatus.code Code.deadlineExceeded
    "client-streaming request streams should use one cumulative grpc-timeout deadline"

  let chatStatus ← expectGrpcMError <|
    registry.dispatchBidirectionalStreaming
      ((requestHeadersForPath "/lean.example.proto.NoteService/Chat").insert "grpc-timeout" "1m")
      (body.append secondBody)
  expectEq chatStatus.code Code.deadlineExceeded
    "bidirectional-streaming handlers should respect grpc-timeout deadlines"

/-- Timed async dispatch must suspend on its promise instead of occupying the
worker that its handler needs.  A batch larger than the default worker pool
therefore completes under one shared observation budget, far ahead of its wire
deadline. -/
def testConcurrentAsyncDeadlineDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }
  let payload := bytes [1, 2, 3]
  let body ← expectStatusOk (Message.encode { data := payload })
  let metadata := requestHeaders.insert "grpc-timeout" "30S"
  let callCount : Nat := 64
  let mut tasks : Array (Task (Except IO.Error (Except Status UnaryResponse))) := #[]
  for _ in [0:callCount] do
    tasks := tasks.push (← Std.Async.Async.toIO (registry.dispatchUnaryAsync metadata body))

  let allFinished : IO Bool := do
    let mut finished := true
    for task in tasks do
      unless ← IO.hasFinished task do
        finished := false
    pure finished
  try
    waitUntil
      s!"{callCount} immediate timed async dispatches did not complete without worker starvation"
      observeTimeoutMs allFinished
  catch error =>
    for task in tasks do
      IO.cancel task
    throw error

  for task in tasks do
    let response ← expectStatusOk (← awaitIoTask task)
    expectEq response.data payload
      "concurrent timed async dispatch should preserve the unary response"

/-- Scheduler shutdown is a terminal state transition: every registration
already owned by the scheduler is failed exactly once, and no registration
accepted after shutdown can be left waiting for a timer that no longer runs. -/
def testDeadlineSchedulerShutdown : IO Unit := do
  let scheduler ← Grpc.Http2.Connection.DeadlineScheduler.new
  let expiredCount ← IO.mkRef 0
  let liveFailureCount ← IO.mkRef 0
  let futureFailureCount ← IO.mkRef 0
  let deadline := (← IO.monoNanosNow) + 60000000000
  let expire : IO Unit := expiredCount.modify fun count => count + 1
  let failLive : IO Unit := liveFailureCount.modify fun count => count + 1

  let unregisterFirst ← scheduler.register deadline expire failLive
  let unregisterSecond ← scheduler.register (deadline + 1) expire failLive
  Std.Async.Async.block scheduler.shutdown

  expectEq (← liveFailureCount.get) 2
    "scheduler shutdown should fail every live registration exactly once"
  expectEq (← expiredCount.get) 0
    "scheduler shutdown must not report live registrations as expired"

  -- Releases remain safe after shutdown has already removed their entries.
  unregisterFirst
  unregisterFirst
  unregisterSecond
  unregisterSecond
  expectEq (← liveFailureCount.get) 2
    "idempotent unregister should not repeat shutdown failure callbacks"

  let failFuture : IO Unit := futureFailureCount.modify fun count => count + 1
  let unregisterFuture ← scheduler.register (deadline + 2) expire failFuture
  expectEq (← futureFailureCount.get) 1
    "registration after shutdown should fail synchronously"
  expectEq (← expiredCount.get) 0
    "registration after shutdown must not invoke its expiry callback"
  unregisterFuture
  unregisterFuture
  expectEq (← futureFailureCount.get) 1
    "post-shutdown unregister should remain idempotent"

/-- An absolute deadline supplied by the transport is authoritative.  If it
has already elapsed, dispatch rejects the call before scheduling the handler. -/
def testExpiredInjectedDeadlineSkipsHandler : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let invoked ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    invoked.set true
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }
  let body ← expectStatusOk (Message.encode { data := bytes [4, 5, 6] })
  let result ← (registry.dispatchUnaryAsync
    (requestHeaders.insert "grpc-timeout" "30S") body (headerDeadline := some 0)).block
  let status ← expectStatusError result
  expectEq status.code Code.deadlineExceeded
    "an already-expired injected deadline should return DEADLINE_EXCEEDED"
  expect (!(← invoked.get))
    "an already-expired injected deadline must not invoke the handler"

/-- _root_.Http2.Header decoding supplies one absolute instant.  Dispatch must hand that
exact value to the handler rather than restarting the metadata duration. -/
def testInjectedHeaderDeadlinePreserved : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let seenDeadline ← IO.mkRef (none : Option (Option Nat))
  let registry := Registry.empty.registerUnary method fun request => do
    seenDeadline.set (some request.deadline)
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }
  let body ← expectStatusOk (Message.encode { data := bytes [7, 8, 9] })
  let now ← IO.monoNanosNow
  let injectedDeadline := now + 60000000000
  -- Deliberately disagree with the one-hour metadata duration: equality with
  -- this injected instant proves dispatch did not recompute the deadline.
  let result ← (registry.dispatchUnaryAsync
    (requestHeaders.insert "grpc-timeout" "1H") body
    (headerDeadline := some injectedDeadline)).block
  let response ← expectStatusOk result
  expectEq response.data (bytes [7, 8, 9])
    "a live injected deadline should allow an immediate handler to complete"
  expectEq (← seenDeadline.get) (some (some injectedDeadline))
    "the handler should see the exact header-time absolute deadline"

def testHandlerExceptionDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun _request => do
    throwGrpcIo "handler exploded"
  let requestMessage : Message := { data := bytes [1, 2, 3] }
  let body ← expectStatusOk requestMessage.encode
  let status ← expectGrpcMError (registry.dispatchUnary requestHeaders body)
  expectEq status.code Code.unknown "handler IO exceptions should map to UNKNOWN"
  expectEq status.message (some "handler exploded")
    "handler IO exception message should be preserved in gRPC status"

def testResponseMetadataValidationDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let requestMessage : Message := { data := bytes [1, 2, 3] }
  let body ← expectStatusOk requestMessage.encode

  let reservedInitial := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "content-type" "text/plain",
      data := request.data,
      status := Status.ok
    }
  let initialStatus ← expectGrpcMError (reservedInitial.dispatchUnary requestHeaders body)
  expectEq initialStatus.code Code.internal
    "reserved response metadata names should fail as INTERNAL"
  expectEq initialStatus.message (some "reserved gRPC response metadata name content-type")
    "reserved response metadata error should identify the header"

  let reservedInitialDetails := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Grpc.Metadata.insertBinary _root_.Http2.Headers.empty
        "grpc-status-details-bin" (bytes [1, 2]),
      data := request.data,
      status := Status.ok
    }
  let initialDetailsStatus ← expectGrpcMError (reservedInitialDetails.dispatchUnary requestHeaders body)
  expectEq initialDetailsStatus.code Code.internal
    "grpc-status-details-bin should fail in initial response metadata"
  expectEq initialDetailsStatus.message
    (some "reserved gRPC response metadata name grpc-status-details-bin")
    "initial grpc-status-details-bin error should identify the header"

  let reservedTrailer := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty,
      data := request.data,
      status := Status.ok,
      trailers := _root_.Http2.Headers.empty.insert "grpc-status" "0"
    }
  let trailerStatus ← expectGrpcMError (reservedTrailer.dispatchUnary requestHeaders body)
  expectEq trailerStatus.code Code.internal
    "reserved response trailer names should fail as INTERNAL"
  expectEq trailerStatus.message (some "reserved gRPC trailer metadata name grpc-status")
    "reserved response trailer error should identify the header"

  let connectionSpecific := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "connection" "close",
      data := request.data,
      status := Status.ok
    }
  let connectionSpecificStatus ← expectGrpcMError (connectionSpecific.dispatchUnary requestHeaders body)
  expectEq connectionSpecificStatus.code Code.internal
    "HTTP/2 connection-specific response metadata should fail as INTERNAL"
  expectEq connectionSpecificStatus.message
    (some "HTTP/2 connection-specific metadata is forbidden: connection")
    "connection-specific response metadata error should identify the header"

  let statusDetailsTrailer := Registry.empty.registerUnary method fun _request => do
    pure {
      metadata := _root_.Http2.Headers.empty,
      data := ByteArray.empty,
      status := Status.invalidArgument "bad input",
      trailers := Grpc.Metadata.insertBinary _root_.Http2.Headers.empty
        "grpc-status-details-bin" (bytes [1, 2])
    }
  let detailsResponse ← runGrpcM (statusDetailsTrailer.dispatchUnary requestHeaders body)
  expectEq detailsResponse.status.code Code.invalidArgument
    "grpc-status-details-bin should be allowed in response trailers"
  expectEq (detailsResponse.trailers.get? "grpc-status-details-bin") (some "AQI")
    "grpc-status-details-bin trailer should use unpadded base64"

  let okStatusDetailsTrailer := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty,
      data := request.data,
      status := Status.ok,
      trailers := Grpc.Metadata.insertBinary _root_.Http2.Headers.empty
        "grpc-status-details-bin" (bytes [1, 2])
    }
  let okStatusDetailsStatus ← expectGrpcMError
    (okStatusDetailsTrailer.dispatchUnary requestHeaders body)
  expectEq okStatusDetailsStatus.code Code.internal
    "grpc-status-details-bin should reject OK responses"
  expectEq okStatusDetailsStatus.message
    (some "grpc-status-details-bin is only valid for non-OK statuses")
    "OK grpc-status-details-bin rejection should explain the status constraint"

  let invalidAscii := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.push (_root_.Http2.Header.of "x-meta" "bad\nvalue"),
      data := request.data,
      status := Status.ok
    }
  let asciiStatus ← expectGrpcMError (invalidAscii.dispatchUnary requestHeaders body)
  expectEq asciiStatus.code Code.internal
    "invalid response metadata values should fail as INTERNAL"

def testMessageSizeLimits : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty,
      data := request.data,
      status := Status.ok
    }

  let requestMessage : Message := { data := bytes [1, 2, 3] }
  let body ← expectStatusOk requestMessage.encode
  let receiveLimited := registry.withMaxReceiveMessageSize 2
  let receiveStatus ← expectGrpcMError (receiveLimited.dispatchUnary requestHeaders body)
  expectEq receiveStatus.code Code.resourceExhausted
    "oversized inbound unary messages should fail with RESOURCE_EXHAUSTED"

  let sendLimited := Registry.empty
    |>.withMaxSendMessageSize 2
    |>.registerUnary method (fun _request => do
      pure {
        metadata := _root_.Http2.Headers.empty,
        data := bytes [4, 5, 6],
        status := Status.ok
      })
  let smallBody ← expectStatusOk (Message.encode { data := bytes [9] })
  let sendStatus ← expectGrpcMError (sendLimited.dispatchUnary requestHeaders smallBody)
  expectEq sendStatus.code Code.resourceExhausted
    "oversized outbound unary messages should fail with RESOURCE_EXHAUSTED"

  let nonOkSendLimited := Registry.empty
    |>.withMaxSendMessageSize 2
    |>.registerUnary method (fun _request => do
      pure {
        metadata := _root_.Http2.Headers.empty,
        data := bytes [4, 5, 6],
        status := Status.invalidArgument "bad request"
      })
  let nonOkSendResponse ← runGrpcM (nonOkSendLimited.dispatchUnary requestHeaders smallBody)
  expectEq nonOkSendResponse.status.code Code.invalidArgument
    "non-OK unary responses should preserve handler status even if unused response data exceeds send limit"
  expectEq nonOkSendResponse.status.message (some "bad request")
    "non-OK unary responses should preserve handler status messages"

  let streamMethod : MethodName := { service := "lean.example.proto.NoteService", method := "List" }
  let streamSendLimited := Registry.empty
    |>.withMaxSendMessageSize 2
    |>.registerServerStreaming streamMethod (fun request => do
      pure {
        metadata := _root_.Http2.Headers.empty,
        messages := #[request.data],
        status := Status.ok
      })
  let streamHeaders := requestHeadersForPath "/lean.example.proto.NoteService/List"
  let streamSendStatus ← expectGrpcMError
    (streamSendLimited.dispatchServerStreaming streamHeaders body)
  expectEq streamSendStatus.code Code.resourceExhausted
    "oversized outbound server-streaming messages should fail with RESOURCE_EXHAUSTED"

def testHttp2H2CServer : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-server",
      data := request.data,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let teBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} #[_root_.Http2.Header.of "te" "trailers"])
  let requestHeaderBlock := (bytes [
    0x83,
    0x86,
    0x04, 0x9a,
    0x62, 0x82, 0x8e, 0xa5, 0xcb, 0xe4, 0x74, 0xd7,
    0x41, 0x57, 0xae, 0xc3, 0xa4, 0xeb, 0xe9, 0x3a,
    0x4b, 0xb8, 0xb6, 0x77, 0x31, 0x0a, 0xc6, 0x02,
    0x4e, 0x7f,
    0x0f, 0x10, 0x8b,
    0x1d, 0x75, 0xd0, 0x62, 0x0d, 0x26, 0x3d, 0x4c,
    0x4d, 0x65, 0x64
  ]).append teBlock.1
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := requestHeaderBlock.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := requestHeaderBlock
  }
  let requestMessage : Message := { data := bytes [2, 4, 6, 8] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  let requestWire := _root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire
  (client.send requestWire).block

  let responseComplete (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let received ← readHttp2FramesUntilWithTimeout client {} responseComplete observeTimeoutMs
    "h2c server did not complete the unary response"
  let emitted := received.frames
  expectEq emitted.size 6
    "h2c server should emit preface, SETTINGS ACK, connection credit, and unary response frames"
  expectEq emitted[0]!.header.frameType _root_.Http2.FrameType.settings "h2c server should send SETTINGS preface first"
  expect (!_root_.Http2.Settings.isAck emitted[0]!) "h2c server SETTINGS preface should not be ACK"
  expect (_root_.Http2.Settings.isAck emitted[1]!) "h2c server should ACK client SETTINGS"
  expectEq emitted[2]!.header.frameType _root_.Http2.FrameType.windowUpdate "h2c server should update connection window"
  expectEq emitted[2]!.header.streamId 0 "h2c connection WINDOW_UPDATE should use stream 0"
  expect (!emitted.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.windowUpdate && frame.header.streamId == 1)
    "a request stream closed by END_STREAM should not receive redundant stream credit"
  expectEq emitted[3]!.header.frameType _root_.Http2.FrameType.headers "h2c server response should start with HEADERS"
  expectEq emitted[4]!.header.frameType _root_.Http2.FrameType.data "h2c server response should include DATA"
  expectEq emitted[5]!.header.frameType _root_.Http2.FrameType.headers "h2c server response should end with trailers"

  let responseHeaders ← expectStatusOk (_root_.Http2.Hpack.decodeHeaderBlock {} emitted[3]!.payload)
  expectEq (_root_.Http2.Headers.get? responseHeaders.headers "handled-by") (some "h2c-server") "h2c server response metadata should be encoded"
  let responseMessages ← expectStatusOk (Message.decodeAll emitted[4]!.payload)
  expectEq responseMessages.size 1 "h2c server response DATA should contain one message"
  expectEq responseMessages[0]!.data requestMessage.data "h2c server response should echo request payload"
  let responseTrailers ← expectStatusOk (_root_.Http2.Hpack.decodeHeaderBlock responseHeaders.state emitted[5]!.payload)
  expectEq (_root_.Http2.Headers.get? responseTrailers.headers "grpc-status") (some "0") "h2c server trailers should include OK grpc-status"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2ServeManagedLifecycle : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "managed-h2c-server",
      data := request.data,
      status := Status.ok
    }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  expect (!(← Grpc.Server.isShutdown server)) "managed h2c server should start active"

  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Echo"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestData := bytes [5, 8, 13]
  let requestBody ← expectStatusOk (Message.encode { data := requestData })
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  let hasResponseTrailers (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let stateAfterResponse ← readHttp2FramesUntilWithTimeout client {} hasResponseTrailers observeTimeoutMs
    "managed h2c server did not complete unary response"
  expectEq stateAfterResponse.frames[0]!.header.frameType _root_.Http2.FrameType.settings
    "managed h2c server preface should be SETTINGS"
  expect (!_root_.Http2.Settings.isAck stateAfterResponse.frames[0]!)
    "managed h2c server preface should not be SETTINGS ACK"
  expect (stateAfterResponse.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.settings && _root_.Http2.Settings.isAck frame)
    "managed h2c server should ACK client SETTINGS"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stateAfterResponse.frames))
  expect (responseMessages.any fun message => message.data == requestData)
    "managed h2c server should echo the request payload"

  Grpc.Server.shutdown server
  expect (← Grpc.Server.isShutdown server) "managed h2c server should report shutdown"
  let hasGoAway (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway
  let stateAfterGoAway ← readHttp2FramesUntilWithTimeout client stateAfterResponse hasGoAway observeTimeoutMs
    "managed h2c server shutdown did not emit GOAWAY"
  let goAway ← match stateAfterGoAway.frames.find? (fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.goAway) with
    | some frame => pure frame
    | none => throw (IO.userError "expected managed h2c server GOAWAY")
  let decodedGoAway ← expectStatusOk (_root_.Http2.GoAway.decode goAway)
  expectEq decodedGoAway.lastStreamId 1
    "managed h2c server GOAWAY should report the last accepted stream"
  expectEq decodedGoAway.errorCode _root_.Http2.ErrorCode.noError
    "managed h2c server GOAWAY should be graceful"

  let postGoAwayHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Echo"))
  let postGoAwayHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := postGoAwayHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.combine #[_root_.Http2.FrameFlag.endHeaders, _root_.Http2.FrameFlag.endStream],
      streamId := 3
    },
    payload := postGoAwayHeaders.1
  }
  let postGoAwayHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode postGoAwayHeadersFrame)
  (client.send postGoAwayHeadersWire).block
  let hasRefusedStream (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.rstStream && frame.header.streamId == 3
  let stateAfterRefused ← readHttp2FramesUntilWithTimeout client stateAfterGoAway hasRefusedStream observeTimeoutMs
    "managed h2c server did not refuse post-GOAWAY stream"
  match stateAfterRefused.frames.find? (fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.rstStream && frame.header.streamId == 3) with
  | some refused =>
      expectEq (← expectStatusOk (_root_.Http2.RstStream.decode refused))
        _root_.Http2.ErrorCode.refusedStream
        "managed h2c server should refuse a post-GOAWAY stream while it remains connected"
  | none =>
      -- With the sole accepted stream already complete, the shared HTTP/2
      -- state is drained as soon as GOAWAY is sent and may retire the
      -- connection before these forbidden post-GOAWAY bytes arrive.
      pure ()
  expect (!stateAfterRefused.frames.any fun frame =>
      frame.header.streamId == 3 && frame.header.frameType != _root_.Http2.FrameType.rstStream)
    "managed h2c server should not process post-GOAWAY stream as an RPC"

  let stopped ← IO.mkRef false
  let waitTask ← IO.asTask do
    Grpc.Server.wait server
    stopped.set true
  waitUntil "managed h2c server wait did not finish after active RPCs drained" observeTimeoutMs stopped.get
  awaitIoTask waitTask
  expectWriteSideClosed client "managed h2c server did not close its write side after wait"
  (client.shutdown).block

/-- A managed connection owns the deadline from END_HEADERS onward.  A unary
peer that never sends its body must still receive DEADLINE_EXCEEDED, after
which the remote half can drain and the connection can serve another stream. -/
def testHttp2H2CServerExpiresIncompleteUnaryBody : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let handled ← IO.mkRef (none : Option ByteArray)
  let registry := Registry.empty.registerUnary method fun request => do
    handled.set (some request.data)
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let timedHeaders := (requestHeadersForPath "/lean.example.proto.NoteService/Echo")
    |>.insert "grpc-timeout" "100m"
  let timedBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := timedBlock.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := timedBlock.1
  }
  let timedHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode timedHeadersFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append timedHeadersWire)).block

  let hasDeadlineTrailers (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let afterDeadline ← readHttp2FramesUntilWithTimeout client {} hasDeadlineTrailers
    observeTimeoutMs "managed h2c server waited for a unary body after its deadline"
  let stream1Frames := afterDeadline.frames.filter fun frame => frame.header.streamId == 1
  expectEq stream1Frames.size 1
    "an incomplete timed-out unary request should receive one trailers-only frame"
  expectEq stream1Frames[0]!.header.frameType _root_.Http2.FrameType.headers
    "an incomplete timed-out unary request should receive HEADERS"
  expect (_root_.Http2.FrameFlag.has stream1Frames[0]!.header.flags _root_.Http2.FrameFlag.endHeaders)
    "deadline trailers should complete their header block"
  expect (_root_.Http2.FrameFlag.has stream1Frames[0]!.header.flags _root_.Http2.FrameFlag.endStream)
    "deadline trailers should close the server response half"
  expect (!afterDeadline.frames.any fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == _root_.Http2.FrameType.data)
    "an incomplete timed-out unary request must not receive response DATA"
  let deadlineTrailers ← decodeLastServerHeaderBlock afterDeadline.frames
    "expected trailers-only response for incomplete timed-out unary request"
  expectEq (_root_.Http2.Headers.get? deadlineTrailers.headers "grpc-status")
    (some Code.deadlineExceeded.toHeaderValue)
    "an incomplete timed-out unary request should return DEADLINE_EXCEEDED"
  expectEq (← handled.get) none
    "an incomplete timed-out unary request must not invoke its handler"

  -- End the expired request's remote half, then prove the same connection still
  -- accepts and completes a fresh stream using the threaded client HPACK state.
  let drainFrame : _root_.Http2.Frame := {
    header := {
      length := 0,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := ByteArray.empty
  }
  let normalBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock timedBlock.2
    (requestHeadersForPath "/lean.example.proto.NoteService/Echo"))
  let normalHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := normalBlock.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 3
    },
    payload := normalBlock.1
  }
  let requestData := bytes [21, 34, 55]
  let requestBody ← expectStatusOk (Message.encode { data := requestData })
  let normalDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 3
    },
    payload := requestBody
  }
  let drainWire ← expectStatusOk (_root_.Http2.Frame.encode drainFrame)
  let normalHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode normalHeadersFrame)
  let normalDataWire ← expectStatusOk (_root_.Http2.Frame.encode normalDataFrame)
  (client.send (drainWire.append normalHeadersWire |>.append normalDataWire)).block

  let hasStream3Trailers (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 3
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let afterRecovery ← readHttp2FramesUntilWithTimeout client afterDeadline hasStream3Trailers
    observeTimeoutMs "managed h2c connection did not recover after expiring an incomplete unary body"
  let stream3Data := afterRecovery.frames.filter fun frame =>
    frame.header.streamId == 3 && frame.header.frameType == _root_.Http2.FrameType.data
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stream3Data))
  expectEq responseMessages.size 1
    "the recovered managed h2c request should return one message"
  expectEq responseMessages[0]!.data requestData
    "the recovered managed h2c request should echo its payload"
  expectEq (← handled.get) (some requestData)
    "only the post-deadline recovery request should invoke the handler"

  Grpc.Server.shutdown server
  let hasGoAway (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway
  discard <| readHttp2FramesUntilWithTimeout client afterRecovery hasGoAway observeTimeoutMs
    "managed h2c server did not begin graceful shutdown after deadline drain"
  let waitTask ← IO.asTask (Grpc.Server.wait server)
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | some _ => pure ()
  | none =>
      IO.cancel waitTask
      throw (IO.userError "managed h2c server did not drain after incomplete deadline recovery")
  expectWriteSideClosed client
    "managed h2c server did not close after draining the expired request"
  (client.shutdown).block

def testHttp2H2CServerReadsWhileStreamOpen : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "OpenStream" }
  let producerRef ← IO.mkRef (none : Option (MessageStream.Producer ByteArray))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    producerRef.set (some producer)
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-open-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/OpenStream"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c open-stream handler did not start" observeTimeoutMs do
    match ← producerRef.get with
    | none => pure false
    | some _ => pure true
  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected h2c open-stream producer")

  let pingPayload := bytes [9, 8, 7, 6, 5, 4, 3, 2]
  let pingFrame ← expectStatusOk (_root_.Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (_root_.Http2.Frame.encode pingFrame)
  (client.send pingWire).block
  let hasPingAck (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.ping && _root_.Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client {} hasPingAck observeTimeoutMs
    "h2c server did not ACK PING while response stream was open"
  let pingAck ← match stateAfterPing.frames.find? (fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.ping && _root_.Http2.Ping.isAck frame) with
    | some frame => pure frame
    | none => throw (IO.userError "expected h2c PING ACK frame")
  expectEq (← expectStatusOk (_root_.Http2.Ping.decode pingAck)) pingPayload
    "h2c PING ACK should echo payload while stream remains open"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream)
    "h2c open stream should not emit trailers before producer close"

  runGrpcM (producer.send (bytes [4, 4]))
  runGrpcM producer.close
  let done (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let finalState ← readHttp2FramesUntilWithTimeout client stateAfterPing done observeTimeoutMs
    "h2c server did not finish response stream after producer close"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads finalState.frames))
  expectEq responseMessages.size 1 "h2c open stream should emit one produced response message"
  expectEq responseMessages[0]!.data (bytes [4, 4])
    "h2c open stream should preserve produced response payload"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2H2CServerFlushesActiveStreamOnWindowUpdate : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "FlowControlledStream" }
  let producerRef ← IO.mkRef (none : Option (MessageStream.Producer ByteArray))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    producerRef.set (some producer)
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-flow-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[
    { id := _root_.Http2.SettingId.initialWindowSize, value := 0 }
  ])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/FlowControlledStream"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c flow-controlled stream handler did not start" observeTimeoutMs do
    match ← producerRef.get with
    | none => pure false
    | some _ => pure true
  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected h2c flow-controlled producer")

  let hasInitialResponseHeaders (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && !_root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let stateAfterHeaders ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders observeTimeoutMs
    "h2c flow-controlled stream did not emit initial response headers"

  let responseData := bytes [4, 4, 4]
  let responseWire ← expectStatusOk (Message.encode { data := responseData })
  runGrpcM (producer.send responseData)

  let pingPayload := bytes [8, 7, 6, 5, 4, 3, 2, 1]
  let ping ← expectStatusOk (_root_.Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (_root_.Http2.Frame.encode ping)
  (client.send pingWire).block
  let hasPingAck (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.ping && _root_.Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client stateAfterHeaders hasPingAck observeTimeoutMs
    "h2c server did not ACK PING while active response DATA was flow-control blocked"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.data && frame.header.streamId == 1)
    "h2c flow-controlled stream should not emit DATA before WINDOW_UPDATE"

  let streamUpdate ← expectStatusOk (_root_.Http2.WindowUpdate.frame 1 responseWire.size)
  let streamUpdateWire ← expectStatusOk (_root_.Http2.Frame.encode streamUpdate)
  (client.send streamUpdateWire).block
  let hasResponseData (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.data && frame.header.streamId == 1
  let stateAfterWindow ← readHttp2FramesUntilWithTimeout client stateAfterPing hasResponseData observeTimeoutMs
    "h2c WINDOW_UPDATE did not flush active response DATA"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stateAfterWindow.frames))
  expect (responseMessages.any fun message => message.data == responseData)
    "h2c WINDOW_UPDATE should flush the queued response message"

  runGrpcM producer.close
  let hasTrailers (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  discard <| readHttp2FramesUntilWithTimeout client stateAfterWindow hasTrailers observeTimeoutMs
    "h2c flow-controlled stream did not emit trailers after producer close"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2H2CServerBidirectionalRespondsBeforeClientEndStream : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "EarlyChat" }
  let registry := Registry.empty.registerBidirectionalStreamingStream method fun request => do
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-early-bidi",
      messages := request.messages.mapM fun message => pure (message.append (bytes [7])),
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/EarlyChat"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire)).block

  let firstBody ← expectStatusOk (Message.encode { data := bytes [1, 2] })
  let firstDataFrame : _root_.Http2.Frame := {
    header := {
      length := firstBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := 0,
      streamId := 1
    },
    payload := firstBody
  }
  let firstDataWire ← expectStatusOk (_root_.Http2.Frame.encode firstDataFrame)
  (client.send firstDataWire).block

  let hasResponseData (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.data && frame.header.streamId == 1
  let stateAfterFirstData ← readHttp2FramesUntilWithTimeout client {} hasResponseData observeTimeoutMs
    "h2c bidi stream did not emit response DATA before client END_STREAM"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stateAfterFirstData.frames))
  expect (responseMessages.any fun message => message.data == bytes [1, 2, 7])
    "h2c bidi response before client END_STREAM should transform first request message"
  expect (!stateAfterFirstData.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream)
    "h2c bidi stream should not emit trailers before client END_STREAM"

  let secondBody ← expectStatusOk (Message.encode { data := bytes [3, 4] })
  let secondDataFrame : _root_.Http2.Frame := {
    header := {
      length := secondBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := secondBody
  }
  let secondDataWire ← expectStatusOk (_root_.Http2.Frame.encode secondDataFrame)
  (client.send secondDataWire).block
  let hasTrailers (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let finalState ← readHttp2FramesUntilWithTimeout client stateAfterFirstData hasTrailers observeTimeoutMs
    "h2c bidi stream did not emit trailers after client END_STREAM"
  let allMessages ← expectStatusOk (Message.decodeAll (dataPayloads finalState.frames))
  expect (allMessages.any fun message => message.data == bytes [3, 4, 7])
    "h2c bidi stream should transform the final request message"

  (client.shutdown).block
  awaitIoTask serverTask

/-- Completing a bidi response does not mean its terminal frames reached the
wire: DATA and trailers may still sit behind the peer's stream window.  The
dispatch must leave that outbound state owned by the connection until a later
WINDOW_UPDATE flushes END_STREAM. -/
def testHttp2H2CCompletedBidirectionalFlushesPendingTerminalOnWindowUpdate : IO Unit := do
  let method : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "FlowControlledChat"
  }
  let responseData := bytes [9, 8, 7, 6]
  let registry := Registry.empty.registerBidirectionalStreamingStream method fun _request => do
    let messages ← MessageStream.ofArray #[responseData]
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-flow-bidi",
      messages := messages,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[
    { id := _root_.Http2.SettingId.initialWindowSize, value := 0 }
  ])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/FlowControlledChat"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.combine #[
        _root_.Http2.FrameFlag.endHeaders,
        _root_.Http2.FrameFlag.endStream
      ],
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire)).block

  let hasInitialResponseHeaders (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && !_root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let beforeWindow ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders
    observeTimeoutMs "completed h2c bidi response did not emit initial headers"
  expect (!beforeWindow.frames.any fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == _root_.Http2.FrameType.data)
    "zero peer stream window must keep completed bidi response DATA pending"
  expect (!beforeWindow.frames.any fun frame =>
      frame.header.streamId == 1
        && frame.header.frameType == _root_.Http2.FrameType.headers
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream)
    "trailers must remain ordered behind flow-control-blocked bidi DATA"

  let responseWire ← expectStatusOk (Message.encode { data := responseData })
  let streamUpdate ← expectStatusOk (_root_.Http2.WindowUpdate.frame 1 responseWire.size)
  let streamUpdateWire ← expectStatusOk (_root_.Http2.Frame.encode streamUpdate)
  (client.send streamUpdateWire).block
  let hasTrailers (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let afterWindow ← readHttp2FramesUntilWithTimeout client beforeWindow hasTrailers
    observeTimeoutMs
    "WINDOW_UPDATE did not flush a completed bidi response's pending terminal frames"
  let messages ← expectStatusOk (Message.decodeAll (dataPayloads afterWindow.frames))
  expectEq messages.size 1
    "completed flow-controlled bidi response should emit exactly one message"
  expectEq messages[0]!.data responseData
    "completed flow-controlled bidi response should preserve its pending DATA"
  let trailers ← decodeLastServerHeaderBlock afterWindow.frames
    "completed flow-controlled bidi response should emit trailers"
  expectEq (_root_.Http2.Headers.get? trailers.headers "grpc-status") (some "0")
    "completed flow-controlled bidi response should terminate with OK"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2H2CServerCancelsStreamOnRst : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "CancelStream" }
  let startedRef ← IO.mkRef false
  let cancelledRef ← IO.mkRef false
  let cancelCountRef ← IO.mkRef 0
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    startedRef.set true
    let stream : MessageStream ByteArray := {
      recv? := cancelledRecvLoop cancelledRef,
      cancel := cancelCountRef.modify fun count => count + 1
    }
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-cancel-stream",
      messages := stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/CancelStream"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c cancel-stream handler did not start" observeTimeoutMs startedRef.get
  let hasInitialResponseHeaders (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && !_root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let stateAfterHeaders ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders observeTimeoutMs
    "h2c cancel-stream response did not emit initial headers"

  let rst ← expectStatusOk (_root_.Http2.RstStream.frame 1 _root_.Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (_root_.Http2.Frame.encode rst)
  (client.send rstWire).block
  waitUntil "h2c RST_STREAM did not cancel the active response stream" observeTimeoutMs cancelledRef.get
  waitUntil "h2c RST_STREAM did not invoke the response cancel callback" observeTimeoutMs do
    pure ((← cancelCountRef.get) == 1)

  let pingPayload := bytes [1, 2, 3, 4, 5, 6, 7, 8]
  let ping ← expectStatusOk (_root_.Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (_root_.Http2.Frame.encode ping)
  (client.send pingWire).block
  let hasPingAck (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.ping && _root_.Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client stateAfterHeaders hasPingAck observeTimeoutMs
    "h2c server did not continue processing after RST_STREAM cancellation"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream)
    "RST_STREAM cancellation should not emit response trailers for the reset stream"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.rstStream
        && frame.header.streamId == 1)
    "deliberate dispatch cancellation must not emit a second INTERNAL_ERROR reset"
  expectEq (← cancelCountRef.get) 1
    "RST_STREAM and handler cleanup must take the response cancel callback exactly once"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2H2CServerCancelsStreamOnDisconnect : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "DisconnectStream" }
  let startedRef ← IO.mkRef false
  let attemptSendRef ← IO.mkRef false
  let producerTaskRef ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
  let producerSendResultRef ← IO.mkRef (none : Option (Except Status Unit))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    startedRef.set true
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    let producerTask ← IO.asTask do
      waitUntil "h2c disconnect test did not release producer send" observeTimeoutMs attemptSendRef.get
      let result ← (producer.send (bytes [5, 5, 5])).run
      producerSendResultRef.set (some result)
    producerTaskRef.set (some producerTask)
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-disconnect-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/DisconnectStream"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c disconnect handler did not start" observeTimeoutMs startedRef.get
  let hasInitialResponseHeaders (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && !_root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  discard <| readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders observeTimeoutMs
    "h2c disconnect response did not emit initial headers"

  (client.shutdown).block
  awaitIoTask serverTask
  attemptSendRef.set true
  waitUntil "h2c disconnect did not close the producer-backed response stream" observeTimeoutMs do
    match ← producerSendResultRef.get with
    | some _ => pure true
    | none => pure false
  match ← producerSendResultRef.get with
  | some (.error status) =>
      expectEq status.code Code.cancelled
        "producer sends after client disconnect should fail with CANCELLED"
  | some (.ok ()) =>
      throw (IO.userError "producer send after client disconnect should not succeed")
  | none =>
      throw (IO.userError "expected producer send result after client disconnect")
  match ← producerTaskRef.get with
  | none => throw (IO.userError "expected h2c disconnect producer task")
  | some task => awaitIoTask task

def testHttp2H2CServerCancelsPipeStreamOnRst : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "CancelPipeStream" }
  let startedRef ← IO.mkRef false
  let attemptSendRef ← IO.mkRef false
  let producerTaskRef ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
  let producerSendResultRef ← IO.mkRef (none : Option (Except Status Unit))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    startedRef.set true
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    let producerTask ← IO.asTask do
      waitUntil "h2c cancel-pipe test did not release producer send" observeTimeoutMs attemptSendRef.get
      let result ← (producer.send (bytes [9, 9, 9])).run
      producerSendResultRef.set (some result)
    producerTaskRef.set (some producerTask)
    pure {
      metadata := _root_.Http2.Headers.empty.insert "handled-by" "h2c-cancel-pipe-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← Std.Async.Async.toIO (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/CancelPipeStream"))
  let requestHeadersFrame : _root_.Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : _root_.Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := _root_.Http2.FrameType.data,
      flags := _root_.Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (_root_.Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (_root_.Http2.Frame.encode requestDataFrame)
  (client.send (_root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c cancel-pipe handler did not start" observeTimeoutMs startedRef.get
  let hasInitialResponseHeaders (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && !_root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
  let stateAfterHeaders ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders observeTimeoutMs
    "h2c cancel-pipe response did not emit initial headers"

  let rst ← expectStatusOk (_root_.Http2.RstStream.frame 1 _root_.Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (_root_.Http2.Frame.encode rst)
  (client.send rstWire).block
  let pingPayload := bytes [2, 3, 4, 5, 6, 7, 8, 9]
  let ping ← expectStatusOk (_root_.Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (_root_.Http2.Frame.encode ping)
  (client.send pingWire).block
  let hasPingAck (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.ping && _root_.Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client stateAfterHeaders hasPingAck observeTimeoutMs
    "h2c server did not continue processing after pipe-backed RST_STREAM cancellation"
  attemptSendRef.set true
  waitUntil "h2c RST_STREAM did not close the producer-backed response stream" observeTimeoutMs do
    match ← producerSendResultRef.get with
    | some _ => pure true
    | none => pure false
  match ← producerSendResultRef.get with
  | some (.error status) =>
      expectEq status.code Code.cancelled
        "producer sends after RST_STREAM should fail with CANCELLED"
  | some (.ok ()) =>
      throw (IO.userError "producer send after RST_STREAM should not succeed")
  | none =>
      throw (IO.userError "expected producer send result after RST_STREAM")
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == 1
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream)
    "RST_STREAM cancellation should not emit trailers for the reset pipe-backed stream"

  match ← producerTaskRef.get with
  | none => throw (IO.userError "expected h2c cancel-pipe producer task")
  | some task => awaitIoTask task
  (client.shutdown).block
  awaitIoTask serverTask

/-- RFC 9113 §5.4.2 per-stream error containment, end to end over a socket.

A DATA frame arriving on a stream the server has already finished is a *stream*
error (§6.1, STREAM_CLOSED): the server must answer RST_STREAM for that stream
and keep serving.  Before this was contained, the same frame produced
GOAWAY(INTERNAL_ERROR) and killed every other stream on the connection. -/
def testHttp2StreamErrorContainment : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let path := "/lean.example.proto.NoteService/Echo"
  let (block1, encoder1) ← expectStatusOk
    (_root_.Http2.Hpack.encodeHeaderBlock {} (requestHeadersForPath path))
  let (block3, _) ← expectStatusOk
    (_root_.Http2.Hpack.encodeHeaderBlock encoder1 (requestHeadersForPath path))

  let headersFrameFor (streamId : Nat) (block : ByteArray) : _root_.Http2.Frame := {
    header := {
      length := block.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := streamId
    },
    payload := block
  }
  let dataFrameFor (streamId : Nat) (payload : ByteArray) (endStream : Bool) : _root_.Http2.Frame := {
    header := {
      length := payload.size,
      frameType := _root_.Http2.FrameType.data,
      flags := if endStream then _root_.Http2.FrameFlag.endStream else 0,
      streamId := streamId
    },
    payload := payload
  }
  let trailersFor (streamId : Nat) (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == streamId
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let body ← expectStatusOk ({ data := bytes [7, 7, 7] } : Message).encode

  let firstWire := _root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append (← expectStatusOk (_root_.Http2.Frame.encode (headersFrameFor 1 block1)))
    |>.append (← expectStatusOk (_root_.Http2.Frame.encode (dataFrameFor 1 body true)))
  (client.send firstWire).block

  let afterFirst ← readHttp2FramesUntilWithTimeout client {} (trailersFor 1)
    observeTimeoutMs "stream 1 should complete before the stray DATA frame"
  expect (!afterFirst.frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway)
    "a healthy unary call must not produce GOAWAY"

  -- Stream 1 is closed now.  A DATA frame for it is a stream error.
  (client.send (← expectStatusOk
    (_root_.Http2.Frame.encode (dataFrameFor 1 body false)))).block
  let afterStray ← readHttp2FramesUntilWithTimeout client
    { afterFirst with frames := #[] }
    (fun frames => frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.rstStream)
    observeTimeoutMs "DATA on a closed stream should be answered with RST_STREAM"
  let rst? := afterStray.frames.find? fun frame =>
    frame.header.frameType == _root_.Http2.FrameType.rstStream
  match rst? with
  | none => throw (IO.userError "expected an RST_STREAM for the closed stream")
  | some rst =>
      expectEq rst.header.streamId 1 "RST_STREAM must name only the offending stream"
      expectEq (← expectStatusOk (_root_.Http2.RstStream.decode rst)) _root_.Http2.ErrorCode.streamClosed
        "RFC 9113 §6.1 prescribes STREAM_CLOSED for DATA on a closed stream"
  expect (!afterStray.frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway)
    "a stream error must not tear the connection down with GOAWAY"

  -- The connection must keep serving: a fresh stream still completes.
  let secondWire := (← expectStatusOk (_root_.Http2.Frame.encode (headersFrameFor 3 block3)))
    |>.append (← expectStatusOk (_root_.Http2.Frame.encode (dataFrameFor 3 body true)))
  (client.send secondWire).block
  let afterSecond ← readHttp2FramesUntilWithTimeout client
    { afterStray with frames := #[] } (trailersFor 3)
    observeTimeoutMs "the connection must keep serving new streams after a stream error"
  expect (!afterSecond.frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway)
    "serving a later stream must not produce GOAWAY either"
  let responseData := afterSecond.frames.filter fun frame =>
    frame.header.frameType == _root_.Http2.FrameType.data && frame.header.streamId == 3
  expect (responseData.size > 0) "stream 3 should carry a response body"
  let messages ← expectStatusOk (Message.decodeAll (dataPayloads responseData))
  expectEq messages.size 1 "stream 3 response should contain one message"
  expectEq messages[0]!.data (bytes [7, 7, 7]) "stream 3 response should echo the request"

  (client.shutdown).block
  Grpc.Server.shutdown server
  let waitTask ← IO.asTask (Grpc.Server.wait server)
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | some _ => pure ()
  | none =>
      IO.cancel waitTask
      throw (IO.userError "stream-error containment server did not drain")

/-- RFC 9113 §6.3 over a live connection: after HEADERS has opened stream 1, a
PRIORITY frame with a length other than 5 octets answers
RST_STREAM(FRAME_SIZE_ERROR) on that stream — no GOAWAY — and the connection
then serves a fresh request. -/
def testHttp2PriorityFrameSizeContainment : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let path := "/lean.example.proto.NoteService/Echo"
  let (block3, _) ← expectStatusOk
    (_root_.Http2.Hpack.encodeHeaderBlock {} (requestHeadersForPath path))

  let headersFrameFor (streamId : Nat) (block : ByteArray) : _root_.Http2.Frame := {
    header := {
      length := block.size,
      frameType := _root_.Http2.FrameType.headers,
      flags := _root_.Http2.FrameFlag.endHeaders,
      streamId := streamId
    },
    payload := block
  }
  let dataFrameFor (streamId : Nat) (payload : ByteArray) (endStream : Bool) : _root_.Http2.Frame := {
    header := {
      length := payload.size,
      frameType := _root_.Http2.FrameType.data,
      flags := if endStream then _root_.Http2.FrameFlag.endStream else 0,
      streamId := streamId
    },
    payload := payload
  }
  let trailersFor (streamId : Nat) (frames : Array _root_.Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.headers
        && frame.header.streamId == streamId
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream

  let clientSettings ← expectStatusOk (_root_.Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (_root_.Http2.Frame.encode clientSettings)
  let malformedPriority : _root_.Http2.Frame := {
    header := {
      length := 6,
      frameType := _root_.Http2.FrameType.priority,
      flags := 0,
      streamId := 1
    },
    payload := bytes [0, 0, 0, 0, 15, 0]
  }
  let firstWire := _root_.Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append (← expectStatusOk (_root_.Http2.Frame.encode (headersFrameFor 1 block3)))
    |>.append (← expectStatusOk (_root_.Http2.Frame.encode malformedPriority))
  (client.send firstWire).block

  let afterPriority ← readHttp2FramesUntilWithTimeout client {}
    (fun frames => frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.rstStream)
    observeTimeoutMs "malformed-length PRIORITY should be answered with RST_STREAM"
  let rst? := afterPriority.frames.find? fun frame =>
    frame.header.frameType == _root_.Http2.FrameType.rstStream
  match rst? with
  | none => throw (IO.userError "expected an RST_STREAM for the malformed PRIORITY")
  | some rst =>
      expectEq rst.header.streamId 1 "RST_STREAM must name only the PRIORITY frame's stream"
      expectEq (← expectStatusOk (_root_.Http2.RstStream.decode rst)) _root_.Http2.ErrorCode.frameSizeError
        "RFC 9113 §6.3 prescribes FRAME_SIZE_ERROR for a malformed PRIORITY length"
  expect (!afterPriority.frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway)
    "a malformed-length PRIORITY must not tear the connection down with GOAWAY"

  -- The connection must keep serving: a fresh stream still completes.
  let body ← expectStatusOk ({ data := bytes [9, 9, 9] } : Message).encode
  let secondWire := (← expectStatusOk (_root_.Http2.Frame.encode (headersFrameFor 3 block3)))
    |>.append (← expectStatusOk (_root_.Http2.Frame.encode (dataFrameFor 3 body true)))
  (client.send secondWire).block
  let afterSecond ← readHttp2FramesUntilWithTimeout client
    { afterPriority with frames := #[] } (trailersFor 3)
    observeTimeoutMs "the connection must keep serving new streams after a malformed PRIORITY"
  expect (!afterSecond.frames.any fun frame => frame.header.frameType == _root_.Http2.FrameType.goAway)
    "serving a later stream must not produce GOAWAY either"
  let responseData := afterSecond.frames.filter fun frame =>
    frame.header.frameType == _root_.Http2.FrameType.data && frame.header.streamId == 3
  expect (responseData.size > 0) "stream 3 should carry a response body"
  let messages ← expectStatusOk (Message.decodeAll (dataPayloads responseData))
  expectEq messages.size 1 "stream 3 response should contain one message"
  expectEq messages[0]!.data (bytes [9, 9, 9]) "stream 3 response should echo the request"

  (client.shutdown).block
  Grpc.Server.shutdown server
  let waitTask ← IO.asTask (Grpc.Server.wait server)
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | some _ => pure ()
  | none =>
      IO.cancel waitTask
      throw (IO.userError "PRIORITY frame-size containment server did not drain")

/-- Deadline propagation: the remaining time of an inbound request becomes the
`grpc-timeout` of a downstream call, and an exhausted deadline refuses the call
instead of issuing one that cannot succeed. -/
def testDeadlinePropagation : IO Unit := do
  -- Every duration renders to a header value that parses back (the proved law
  -- `Timeout.parse?_render_ofNanoseconds`), including the extremes.
  for nanoseconds in [0, 1, 999, 1000, 250000000, 5000000000, 3600000000000,
      99999999 * 3600000000000 * 2] do
    let timeout := Timeout.ofNanoseconds nanoseconds
    expectEq (Timeout.parse? timeout.render) (some timeout)
      s!"rendered timeout for {nanoseconds}ns should parse back"
    expect (timeout.value != 0) "a propagated timeout must never render as zero"

  -- Rounding is up, so a downstream call never gets less time than remains.
  expectEq (Timeout.ofNanoseconds 1) { value := 1, unit := TimeoutUnit.nanosecond }
    "a sub-unit remainder should round up to the smallest representable timeout"
  expectEq (Timeout.ofNanoseconds 99999999) { value := 99999999, unit := TimeoutUnit.nanosecond }
    "a duration that fits eight digits should use the finest unit"
  expectEq (Timeout.ofNanoseconds 250000000) { value := 250000, unit := TimeoutUnit.microsecond }
    "a duration past eight digits should step up to the next coarser unit"

  -- No deadline on the request: nothing is propagated.
  match ← Deadline.remaining? none with
  | .unbounded => pure ()
  | _ => throw (IO.userError "a request without a deadline should propagate none")

  -- A deadline already in the past refuses the downstream call.
  match ← Deadline.remaining? (some 0) with
  | .exceeded => pure ()
  | _ => throw (IO.userError "an expired deadline should report exceeded")

  -- A live deadline yields a timeout no longer than what remains.
  let now ← IO.monoNanosNow
  match ← Deadline.remaining? (some (now + 5000000000)) with
  | .remaining timeout =>
      expect (timeout.toNanoseconds <= 5000000000 + timeout.unit.nanoseconds)
        "propagated timeout should not exceed the remaining time by more than one unit"
  | _ => throw (IO.userError "a live deadline should report remaining time")

  -- CallOptions.propagating threads it into a downstream call.
  let base : Client.CallOptions := { metadata := _root_.Http2.Headers.empty.insert "x-trace" "downstream" }
  match ← base.propagating none with
  | .ok options =>
      expectEq options.timeout none "no deadline should leave the downstream timeout unset"
      expectEq (options.metadata.get? "x-trace") (some "downstream")
        "propagating must preserve the caller's metadata"
  | .error status => throw (IO.userError s!"unexpected error: {status.messageD}")
  let now ← IO.monoNanosNow
  match ← base.propagating (some (now + 2000000000)) with
  | .ok options =>
      match options.timeout with
      | none => throw (IO.userError "a live deadline should set a downstream grpc-timeout")
      | some raw =>
          match Timeout.parse? raw with
          | none => throw (IO.userError s!"downstream grpc-timeout {raw} should be parseable")
          | some timeout =>
              expect (timeout.toNanoseconds <= 2000000000 + timeout.unit.nanoseconds)
                "downstream grpc-timeout should not exceed the caller's remaining time"
  | .error status => throw (IO.userError s!"unexpected error: {status.messageD}")
  match ← base.propagating (some 0) with
  | .ok _ => throw (IO.userError "an expired deadline should not produce call options")
  | .error status =>
      expectEq status.code Code.deadlineExceeded
        "an expired deadline should refuse the downstream call with DEADLINE_EXCEEDED"

  -- The server hands the absolute deadline to the handler.
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let seenDeadline ← IO.mkRef (none : Option (Option Nat))
  let registry := Registry.empty.registerUnary method fun request => do
    seenDeadline.set (some request.deadline)
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }
  let body ← expectStatusOk (Message.encode { data := bytes [1] })
  discard <| runGrpcM (registry.dispatchUnary (requestHeaders.insert "grpc-timeout" "5S") body)
  match ← seenDeadline.get with
  | some (some _) => pure ()
  | _ => throw (IO.userError "a handler should see the absolute deadline of its request")
  seenDeadline.set none
  discard <| runGrpcM (registry.dispatchUnary requestHeaders body)
  match ← seenDeadline.get with
  | some none => pure ()
  | _ => throw (IO.userError "a request without grpc-timeout should carry no deadline")


def main : IO Unit := do
  testStatus
  testMetadata
  testFraming
  testProtocol
  testDispatch
  testServerStreamingDispatch
  testClientStreamingDispatch
  testBidirectionalStreamingDispatch
  testReflectionService
  testStreamNativeDispatch
  testMessageStreamPipe
  testDeadlineExceededDispatch
  testConcurrentAsyncDeadlineDispatch
  testDeadlineSchedulerShutdown
  testExpiredInjectedDeadlineSkipsHandler
  testInjectedHeaderDeadlinePreserved
  testHandlerExceptionDispatch
  testResponseMetadataValidationDispatch
  testMessageSizeLimits
  testHttp2H2CServer
  testHttp2ServeManagedLifecycle
  testHttp2H2CServerExpiresIncompleteUnaryBody
  testHttp2H2CServerReadsWhileStreamOpen
  testHttp2H2CServerFlushesActiveStreamOnWindowUpdate
  testHttp2H2CServerBidirectionalRespondsBeforeClientEndStream
  testHttp2H2CCompletedBidirectionalFlushesPendingTerminalOnWindowUpdate
  testHttp2H2CServerCancelsStreamOnRst
  testHttp2H2CServerCancelsStreamOnDisconnect
  testHttp2H2CServerCancelsPipeStreamOnRst
  testHttp2StreamErrorContainment
  testHttp2PriorityFrameSizeContainment
  testDeadlinePropagation
