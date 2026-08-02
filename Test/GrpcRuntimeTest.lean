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

def expectStatusOk (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def expectStatusError (result : Except Status α) : IO Status := do
  match result with
  | .ok _ => throw (IO.userError "expected gRPC status error")
  | .error status => pure status

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

def dataPayloads (frames : Array Http2.Frame) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun out frame =>
    if frame.header.frameType == Http2.FrameType.data then
      out.append frame.payload
    else
      out

partial def takeHeaderBlockFramesFrom (frames : Array Http2.Frame) (i : Nat)
    (out : Array Http2.Frame := #[]) : Array Http2.Frame :=
  if i >= frames.size then
    out
  else
    let frame := frames[i]!
    if out.isEmpty then
      if frame.header.frameType != Http2.FrameType.headers then
        out
      else
        let out := out.push frame
        if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
          out
        else
          takeHeaderBlockFramesFrom frames (i + 1) out
    else if frame.header.frameType != Http2.FrameType.continuation then
      out
    else
      let out := out.push frame
      if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
        out
      else
        takeHeaderBlockFramesFrom frames (i + 1) out

def headerBlockPayload (frames : Array Http2.Frame) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun out frame => out.append frame.payload

/-- Decodes every server-emitted header block in emission order with a single
threaded HPACK decoder state, mirroring what a real client does. Returns the
decode result of each block in order. -/
def decodeServerHeaderBlocks (frames : Array Http2.Frame) :
    IO (Array Http2.Hpack.DecodeResult) := do
  let mut state : Http2.Hpack.State := {}
  let mut out := #[]
  let mut block := ByteArray.empty
  let mut inBlock := false
  for frame in frames do
    if inBlock then
      block := block.append frame.payload
      if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
        let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state block)
        state := decoded.state
        out := out.push decoded
        inBlock := false
    else if frame.header.frameType == Http2.FrameType.headers then
      if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
        let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state frame.payload)
        state := decoded.state
        out := out.push decoded
      else
        inBlock := true
        block := frame.payload
  pure out

/-- Decodes all server-emitted header blocks in order and returns the last one
(the trailers of the most recent response). -/
def decodeLastServerHeaderBlock (frames : Array Http2.Frame) (msg : String) :
    IO Http2.Hpack.DecodeResult := do
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

partial def readHttp2FramesFromSocket (client : Std.Async.TCP.Socket.Client)
    (decoder : Http2.Frame.DecodeState) (frames : Array Http2.Frame) (wanted : Nat) :
    IO (Array Http2.Frame) := do
  if frames.size >= wanted then
    pure frames
  else
    let chunk? ← (client.recv? 8192).block
    match chunk? with
    | none => pure frames
    | some chunk =>
        let decoded ← expectStatusOk (Http2.Frame.decodeChunk decoder chunk)
        readHttp2FramesFromSocket client { buffered := decoded.buffered } (frames.append decoded.frames) wanted

structure ReadHttp2FrameState where
  decoder : Http2.Frame.DecodeState := {}
  frames : Array Http2.Frame := #[]

partial def readHttp2FramesUntilFromSocket (client : Std.Async.TCP.Socket.Client)
    (state : ReadHttp2FrameState) (done : Array Http2.Frame -> Bool) :
    IO ReadHttp2FrameState := do
  if done state.frames then
    pure state
  else
    let chunk? ← (client.recv? 8192).block
    match chunk? with
    | none => pure state
    | some chunk =>
        let decoded ← expectStatusOk (Http2.Frame.decodeChunk state.decoder chunk)
        readHttp2FramesUntilFromSocket client
          { decoder := { buffered := decoded.buffered }, frames := state.frames.append decoded.frames }
          done

def readHttp2FramesUntilWithTimeout (client : Std.Async.TCP.Socket.Client)
    (state : ReadHttp2FrameState) (done : Array Http2.Frame -> Bool)
    (timeoutMs : UInt32) (message : String) : IO ReadHttp2FrameState := do
  let readTask ← IO.asTask do
    let state ← readHttp2FramesUntilFromSocket client state done
    pure (some state)
  let timeoutTask ← IO.asTask do
    IO.sleep timeoutMs
    pure (none : Option ReadHttp2FrameState)
  match ← IO.waitAny [readTask, timeoutTask] with
  | .error err => throw err
  | .ok (some state) => pure state
  | .ok none =>
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
  let metadata := Metadata.empty
    |>.insert "Content-Type" "application/grpc+proto"
    |>.insert "te" "trailers"
    |>.insertBinary "trace-bin" (bytes [1, 2, 3, 4])
  expectEq (metadata.get? "content-type") (some "application/grpc+proto") "metadata lookup should be case-normalized"
  expect (metadata.contains "TE" "trailers") "metadata should retain values"
  expectEq (metadata.get? "trace-bin") (some "AQIDBA")
    "binary metadata should be emitted without base64 padding"
  let binary ← expectExceptOk (metadata.getBinary? "trace-bin")
  expectEq binary (some (bytes [1, 2, 3, 4])) "binary metadata should base64 round-trip"
  let mixedCaseBinaryMetadata := Metadata.empty.insertBinary "Trace-Bin" (bytes [5, 6])
  expectEq (mixedCaseBinaryMetadata.get? "trace-bin") (some "BQY")
    "binary metadata insertion should normalize mixed-case -bin suffixes"
  expectEq (mixedCaseBinaryMetadata.get? "trace-bin-bin") none
    "binary metadata insertion should not append a duplicate -bin suffix after normalization"
  let mixedCaseBinary ← expectExceptOk (mixedCaseBinaryMetadata.getBinary? "Trace-Bin")
  expectEq mixedCaseBinary (some (bytes [5, 6]))
    "binary metadata lookup should normalize mixed-case -bin suffixes"
  let singleByteMetadata := Metadata.empty.insertBinary "single-bin" (bytes [255])
  expectEq (singleByteMetadata.get? "single-bin") (some "/w")
    "single-byte binary metadata should omit base64 padding"
  let unpaddedMetadata := Metadata.empty.insert "trace-bin" "AQIDBA"
  let unpaddedBinary ← expectExceptOk (unpaddedMetadata.getBinary? "trace-bin")
  expectEq unpaddedBinary (some (bytes [1, 2, 3, 4]))
    "binary metadata should accept unpadded base64 values"
  let joinedMetadata := Metadata.empty.insert "trace-bin" "AQI,AwQ="
  let joinedBinary ← expectExceptOk (joinedMetadata.getBinaryAll "trace-bin")
  expectEq joinedBinary #[bytes [1, 2], bytes [3, 4]]
    "binary metadata should split comma-joined base64 values"
  let duplicateBinary ← expectExceptOk
    ((Metadata.empty.insert "trace-bin" "AQI" |>.insert "trace-bin" "AwQ=").getBinaryAll "trace-bin")
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

def requestHeadersForPath (path : String) : Metadata :=
  Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

def requestHeaders : Metadata :=
  requestHeadersForPath "/lean.example.proto.NoteService/Echo"

def readyConnectionState : Http2.Connection.State :=
  { prefaceReceived := true, clientSettingsReceived := true }

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
  let missingSchemeHeaders := Metadata.empty
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
  let duplicatePseudoHeaders := Metadata.empty
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
  let responsePseudoHeaders := Metadata.empty
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
  let latePseudoHeaders := Metadata.empty
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
  let protoContentTypeHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc+proto"
    |>.insert "te" "trailers"
  discard <| expectStatusOk (Headers.validateUnaryRequestHeaders protoContentTypeHeaders)
  let jsonContentTypeHeaders := Metadata.empty
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
    (Headers.validateUnaryRequestHeaders (requestHeaders.push (Header.of "trace-bin" "AQIDBA")))
  discard <| expectStatusOk
    (Headers.validateUnaryRequestHeaders (requestHeaders.push (Header.of "trace-bin" "AQI,AwQ=")))
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
    Headers.validateUnaryRequestHeaders (requestHeaders.push (Header.of "x-meta" "bad\nvalue"))
  expectEq badAsciiValueStatus.code Code.invalidArgument
    "ASCII metadata values with control characters should reject"
  let badBinaryValueStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.push (Header.of "trace-bin" "bad!"))
  expectEq badBinaryValueStatus.code Code.invalidArgument
    "binary metadata values with invalid base64 should reject"
  let badBinaryLengthStatus ← expectStatusError <|
    Headers.validateUnaryRequestHeaders (requestHeaders.push (Header.of "trace-bin" "A"))
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
  let missingGrpcStatus ← expectStatusError (Headers.statusFromTrailers Metadata.empty)
  expectEq missingGrpcStatus.code Code.unknown "missing grpc-status trailer should reject"
  let invalidGrpcStatus ← expectStatusError
    (Headers.statusFromTrailers (Metadata.empty.insert "grpc-status" "17"))
  expectEq invalidGrpcStatus.code Code.unknown "invalid grpc-status trailer should reject"
  let invalidGrpcMessage ← expectStatusError
    (Headers.statusFromTrailers (Metadata.empty.insert "grpc-status" "13" |>.insert "grpc-message" "%"))
  expectEq invalidGrpcMessage.code Code.unknown "invalid grpc-message trailer should reject"
  let duplicateGrpcStatus ← expectStatusError
    (Headers.statusFromTrailers (Metadata.empty.insert "grpc-status" "0" |>.insert "grpc-status" "13"))
  expectEq duplicateGrpcStatus.code Code.invalidArgument "duplicate grpc-status trailers should reject"

def testDispatch : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "lean",
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
      metadata := Metadata.empty.insert "handled-by" "server-streaming",
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
      metadata := Metadata.empty.insert "handled-by" "client-streaming",
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
      metadata := Metadata.empty.insert "handled-by" "bidirectional-streaming",
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
  waitUntil "stream-native client-streaming handler did not observe first message before close" 100
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
        metadata := Metadata.empty,
        data := request.data,
        status := Status.ok
      })
    |>.registerServerStreaming listMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := Metadata.empty,
        messages := #[request.data],
        status := Status.ok
      })
    |>.registerClientStreaming collectMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := Metadata.empty,
        data := request.messages.foldl (fun out message => out.append message) ByteArray.empty,
        status := Status.ok
      })
    |>.registerBidirectionalStreaming chatMethod (fun request => do
      IO.sleep 20
      pure {
        metadata := Metadata.empty,
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
        metadata := Metadata.empty,
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
        metadata := Metadata.empty,
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
        metadata := Metadata.empty,
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
      metadata := Metadata.empty.insert "content-type" "text/plain",
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
      metadata := Metadata.empty.insertBinary "grpc-status-details-bin" (bytes [1, 2]),
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
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok,
      trailers := Metadata.empty.insert "grpc-status" "0"
    }
  let trailerStatus ← expectGrpcMError (reservedTrailer.dispatchUnary requestHeaders body)
  expectEq trailerStatus.code Code.internal
    "reserved response trailer names should fail as INTERNAL"
  expectEq trailerStatus.message (some "reserved gRPC trailer metadata name grpc-status")
    "reserved response trailer error should identify the header"

  let connectionSpecific := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "connection" "close",
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
      metadata := Metadata.empty,
      data := ByteArray.empty,
      status := Status.invalidArgument "bad input",
      trailers := Metadata.empty.insertBinary "grpc-status-details-bin" (bytes [1, 2])
    }
  let detailsResponse ← runGrpcM (statusDetailsTrailer.dispatchUnary requestHeaders body)
  expectEq detailsResponse.status.code Code.invalidArgument
    "grpc-status-details-bin should be allowed in response trailers"
  expectEq (detailsResponse.trailers.get? "grpc-status-details-bin") (some "AQI")
    "grpc-status-details-bin trailer should use unpadded base64"

  let okStatusDetailsTrailer := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok,
      trailers := Metadata.empty.insertBinary "grpc-status-details-bin" (bytes [1, 2])
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
      metadata := Metadata.empty.push (Header.of "x-meta" "bad\nvalue"),
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
      metadata := Metadata.empty,
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
        metadata := Metadata.empty,
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
        metadata := Metadata.empty,
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
        metadata := Metadata.empty,
        messages := #[request.data],
        status := Status.ok
      })
  let streamHeaders := requestHeadersForPath "/lean.example.proto.NoteService/List"
  let streamSendStatus ← expectGrpcMError
    (streamSendLimited.dispatchServerStreaming streamHeaders body)
  expectEq streamSendStatus.code Code.resourceExhausted
    "oversized outbound server-streaming messages should fail with RESOURCE_EXHAUSTED"

def testHttp2Frames : IO Unit := do
  expectEq Http2.connectionPreface.size 24 "HTTP/2 connection preface should be 24 bytes"

  let settingsFrame ← expectStatusOk (Http2.Settings.frame #[
    { id := Http2.SettingId.maxFrameSize, value := 16384 },
    { id := Http2.SettingId.initialWindowSize, value := 65535 }
  ])
  let settingsWire ← expectStatusOk (Http2.Frame.encode settingsFrame)
  let decodedFrames ← expectStatusOk (Http2.Frame.decodeAll settingsWire)
  expectEq decodedFrames.size 1 "one HTTP/2 frame should decode"
  expectEq decodedFrames[0]!.header.frameType Http2.FrameType.settings "frame type should be SETTINGS"
  expectEq decodedFrames[0]!.header.streamId 0 "SETTINGS frame should use stream 0"

  let decodedSettings ← expectStatusOk (Http2.Settings.decode decodedFrames[0]!)
  expectEq decodedSettings.size 2 "two settings should decode"
  expectEq decodedSettings[0]!.id Http2.SettingId.maxFrameSize "first setting id should match"
  expectEq decodedSettings[0]!.value 16384 "first setting value should match"
  expectEq decodedSettings[1]!.id Http2.SettingId.initialWindowSize "second setting id should match"
  expectEq decodedSettings[1]!.value 65535 "second setting value should match"

  let dataFrame : Http2.Frame := {
    header := { length := 3, frameType := Http2.FrameType.data, flags := 0, streamId := 1 },
    payload := bytes [10, 11, 12]
  }
  let dataWire ← expectStatusOk (Http2.Frame.encode dataFrame)
  let combined := settingsWire.append dataWire
  let splitAt := settingsWire.size + 4
  let state1 ← expectStatusOk (Http2.Frame.decodeChunk {} (combined.extract 0 splitAt))
  expectEq state1.frames.size 1 "first HTTP/2 chunk should emit complete SETTINGS frame"
  expectEq state1.buffered.size 4 "first HTTP/2 chunk should retain partial DATA header"
  let state2 ← expectStatusOk (Http2.Frame.decodeChunk state1 (combined.extract splitAt combined.size))
  expectEq state2.frames.size 1 "second HTTP/2 chunk should emit DATA frame"
  expectEq state2.frames[0]!.header.streamId 1 "DATA stream id should decode"
  expectEq state2.frames[0]!.payload (bytes [10, 11, 12]) "DATA payload should decode"
  expectEq state2.buffered.size 0 "HTTP/2 frame parser should end with empty buffer"

  let ackFrame ← expectStatusOk (Http2.Settings.frame #[] (ack := true))
  expect (Http2.Settings.isAck ackFrame) "SETTINGS ack flag should be recognized"
  let ackSettings ← expectStatusOk (Http2.Settings.decode ackFrame)
  expectEq ackSettings.size 0 "SETTINGS ack should decode as no settings"
  let ackWithUnknownFlags : Http2.Frame := {
    ackFrame with header := { ackFrame.header with flags := UInt8.ofNat 0x3 }
  }
  expect (Http2.Settings.isAck ackWithUnknownFlags)
    "SETTINGS ack should ignore unknown flag bits"
  let ackWithUnknownSettings ← expectStatusOk (Http2.Settings.decode ackWithUnknownFlags)
  expectEq ackWithUnknownSettings.size 0
    "SETTINGS ack with unknown flags should decode as no settings"

  let serverPrefaceWire ← expectStatusOk Http2.Connection.serverPrefaceBytes
  let serverPrefaceFrames ← expectStatusOk (Http2.Frame.decodeAll serverPrefaceWire)
  expectEq serverPrefaceFrames.size 1 "server preface should contain one SETTINGS frame"
  expectEq serverPrefaceFrames[0]!.header.frameType Http2.FrameType.settings "server preface should be SETTINGS"
  expect (!Http2.Settings.isAck serverPrefaceFrames[0]!) "server preface SETTINGS should not be ACK"
  let serverPrefaceSettings ← expectStatusOk (Http2.Settings.decode serverPrefaceFrames[0]!)
  expectEq serverPrefaceSettings.size 1 "server preface advertises the initial stream window"
  expectEq serverPrefaceSettings[0]!.id Http2.SettingId.initialWindowSize
    "server preface should advertise SETTINGS_INITIAL_WINDOW_SIZE"
  expectEq serverPrefaceSettings[0]!.value Http2.Connection.defaultStreamWindow
    "server preface should advertise the default stream window"

  let limitedPrefaceWire ← expectStatusOk
    (Http2.Connection.serverPrefaceBytes (some 7) (some 4096) Http2.Connection.initialFlowControlWindow)
  let limitedPrefaceFrames ← expectStatusOk (Http2.Frame.decodeAll limitedPrefaceWire)
  expectEq limitedPrefaceFrames.size 1 "limited server preface should contain one SETTINGS frame"
  let limitedSettings ← expectStatusOk (Http2.Settings.decode limitedPrefaceFrames[0]!)
  expectEq limitedSettings.size 2 "limited server preface should advertise two settings"
  expectEq limitedSettings[0]!.id Http2.SettingId.maxConcurrentStreams
    "server preface should advertise SETTINGS_MAX_CONCURRENT_STREAMS when configured"
  expectEq limitedSettings[0]!.value 7
    "server preface should advertise configured max concurrent streams"
  expectEq limitedSettings[1]!.id Http2.SettingId.maxHeaderListSize
    "server preface should advertise SETTINGS_MAX_HEADER_LIST_SIZE when configured"
  expectEq limitedSettings[1]!.value 4096
    "server preface should advertise configured max header list size"
  expectEq (Http2.Connection.initialState (some 7) (some 4096)).inboundMaxConcurrentStreams (some 7)
    "connection initial state should retain configured inbound max concurrent streams"
  expectEq (Http2.Connection.initialState (some 7) (some 4096)).inboundMaxHeaderListSize (some 4096)
    "connection initial state should retain configured inbound max header list size"

  let pingPayload := bytes [1, 2, 3, 4, 5, 6, 7, 8]
  let pingFrame ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode pingFrame)
  let decodedPingFrames ← expectStatusOk (Http2.Frame.decodeAll pingWire)
  expectEq decodedPingFrames.size 1 "one PING frame should decode"
  expectEq decodedPingFrames[0]!.header.frameType Http2.FrameType.ping "frame type should be PING"
  expectEq (← expectStatusOk (Http2.Ping.decode decodedPingFrames[0]!)) pingPayload "PING payload should decode"

  let pingAck ← expectStatusOk (Http2.Ping.frame pingPayload (ack := true))
  expect (Http2.Ping.isAck pingAck) "PING ACK flag should be recognized"

  let goAway ← expectStatusOk (Http2.GoAway.frame 0 Http2.ErrorCode.noError)
  expectEq goAway.header.frameType Http2.FrameType.goAway "GOAWAY frame type should encode"
  expectEq goAway.payload.size 8 "GOAWAY without debug data should have 8-byte payload"
  let decodedGoAway ← expectStatusOk (Http2.GoAway.decode goAway)
  expectEq decodedGoAway.lastStreamId 0 "GOAWAY last stream id should decode"
  expectEq decodedGoAway.errorCode Http2.ErrorCode.noError "GOAWAY error code should decode"
  expect decodedGoAway.debugData.isEmpty "GOAWAY debug data should default to empty"
  let goAwayResult ← Http2.Connection.processFrame Registry.empty readyConnectionState goAway
  let (_goAwayState, emittedGoAway) ← expectStatusOk goAwayResult
  expect emittedGoAway.isEmpty "valid client GOAWAY should not emit response frames"
  let invalidGoAway := { goAway with header := { goAway.header with streamId := 1 } }
  let invalidGoAwayResult ← Http2.Connection.processFrame Registry.empty readyConnectionState invalidGoAway
  let invalidGoAwayStatus ← expectStatusError invalidGoAwayResult
  expectEq invalidGoAwayStatus.code Code.internal "GOAWAY with non-zero stream id should reject"
  let errorGoAwayState := { (Http2.Connection.initialState) with lastClientStreamId := 7 }
  let errorGoAway ← expectStatusOk
    (Http2.Server.errorGoAwayFrame errorGoAwayState (Status.internal "bad frame"))
  let decodedErrorGoAway ← expectStatusOk (Http2.GoAway.decode errorGoAway)
  expectEq decodedErrorGoAway.lastStreamId 7
    "server error GOAWAY should report the last accepted client stream id"
  expectEq decodedErrorGoAway.errorCode Http2.ErrorCode.internalError
    "server error GOAWAY should use INTERNAL_ERROR"
  expectEq decodedErrorGoAway.debugData (Status.internal "bad frame").messageD.toUTF8
    "server error GOAWAY should carry status debug data"

  let windowUpdate ← expectStatusOk (Http2.WindowUpdate.frame 1 1024)
  expectEq windowUpdate.header.frameType Http2.FrameType.windowUpdate "WINDOW_UPDATE frame type should encode"
  expectEq windowUpdate.header.streamId 1 "WINDOW_UPDATE stream id should encode"
  expectEq (← expectStatusOk (Http2.WindowUpdate.decode windowUpdate)) 1024 "WINDOW_UPDATE increment should decode"

  let rstStream ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  expectEq rstStream.header.frameType Http2.FrameType.rstStream "RST_STREAM frame type should encode"
  expectEq rstStream.header.streamId 1 "RST_STREAM stream id should encode"
  expectEq (← expectStatusOk (Http2.RstStream.decode rstStream)) Http2.ErrorCode.cancel
    "RST_STREAM error code should decode"

  let priorityFrame : Http2.Frame := {
    header := {
      length := 5,
      frameType := Http2.FrameType.priority,
      flags := 0,
      streamId := 1
    },
    payload := bytes [0, 0, 0, 0, 15]
  }
  let priority ← expectStatusOk (Http2.Priority.decode priorityFrame)
  expectEq priority.streamDependency 0 "PRIORITY stream dependency should decode"
  expectEq priority.weight 15 "PRIORITY weight should decode"
  let selfDependentPriority : Http2.Frame := {
    priorityFrame with payload := bytes [0, 0, 0, 1, 15]
  }
  let selfDependentPriorityStatus ← expectStatusError (Http2.Priority.decode selfDependentPriority)
  expectEq selfDependentPriorityStatus.code Code.internal
    "PRIORITY self-dependency should reject"
  let selfDependentPriorityResult ← Http2.Connection.processFrame
    Registry.empty readyConnectionState selfDependentPriority
  let selfDependentPriorityConnectionStatus ← expectStatusError selfDependentPriorityResult
  expectEq selfDependentPriorityConnectionStatus.code Code.internal
    "connection should reject PRIORITY self-dependency"

def testHpack : IO Unit := do
  let state : Http2.Hpack.State := {}

  let huffmanString ← expectStatusOk (Http2.Hpack.decodeString (bytes [
    0x8c, 0xf1, 0xe3, 0xc2, 0xe5, 0xf2, 0x3a, 0x6b, 0xa0, 0xab, 0x90, 0xf4, 0xff
  ]) 0)
  expectEq huffmanString.value "www.example.com" "RFC HPACK Huffman string should decode"

  let staticPost ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state (bytes [0x83]))
  expectEq staticPost.headers.size 1 "one static indexed header should decode"
  expectEq staticPost.headers[0]!.name ":method" "static header name should decode"
  expectEq staticPost.headers[0]!.value "POST" "static header value should decode"

  let huffmanContentTypeBlock := bytes [
    0x0f, 0x10, 0x8b,
    0x1d, 0x75, 0xd0, 0x62, 0x0d, 0x26, 0x3d, 0x4c, 0x4d, 0x65, 0x64
  ]
  let huffmanContentType ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state huffmanContentTypeBlock)
  expectEq huffmanContentType.headers.size 1 "one Huffman literal header should decode"
  expectEq huffmanContentType.headers[0]!.name "content-type" "Huffman literal name index should decode"
  expectEq huffmanContentType.headers[0]!.value "application/grpc" "Huffman literal value should decode"

  let headers := #[
    Header.of ":status" "200",
    Header.of "content-type" "application/grpc",
    Header.of "grpc-status" "0"
  ]
  let encoded ← expectStatusOk (Http2.Hpack.encodeHeaderBlock state headers)
  let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state encoded.1)
  expectEq decoded.headers.size headers.size "encoded HPACK header block should decode"
  expectEq decoded.headers[0]!.name ":status" "encoded status header name should decode"
  expectEq decoded.headers[0]!.value "200" "encoded status header value should decode"
  expectEq decoded.headers[1]!.name "content-type" "encoded content-type name should decode"
  expectEq decoded.headers[1]!.value "application/grpc" "encoded content-type value should decode"
  expectEq decoded.headers[2]!.name "grpc-status" "encoded grpc-status name should decode"
  expectEq decoded.headers[2]!.value "0" "encoded grpc-status value should decode"

  let literal := Header.of "grpc-status" "0"
  let indexedLiteral ← expectStatusOk (Http2.Hpack.encodeLiteralWithIndexing state literal)
  let decodedLiteral ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state indexedLiteral.1)
  expectEq decodedLiteral.headers.size 1 "literal with indexing should decode one header"
  expectEq decodedLiteral.headers[0]! literal "literal with indexing should preserve header"
  expectEq decodedLiteral.state.dynamic.size 1 "literal with indexing should update dynamic table"
  expectEq decodedLiteral.state.dynamic[0]! literal "dynamic table should store newest entry first"

  let dynamicIndex ← expectStatusOk (Http2.Hpack.encodeInteger 7 128 (Http2.Hpack.staticTableSize + 1))
  let decodedDynamic ← expectStatusOk (Http2.Hpack.decodeHeaderBlock decodedLiteral.state dynamicIndex)
  expectEq decodedDynamic.headers.size 1 "dynamic indexed header should decode"
  expectEq decodedDynamic.headers[0]! literal "dynamic indexed header should match inserted literal"

  let leadingSizeUpdate ← expectStatusOk (Http2.Hpack.decodeHeaderBlock state (bytes [0x20, 0x83]))
  expectEq leadingSizeUpdate.headers.size 1
    "HPACK dynamic table size update before headers should decode"
  expectEq leadingSizeUpdate.headers[0]!.name ":method"
    "header after HPACK dynamic table size update should decode"
  expectEq leadingSizeUpdate.state.maxSize 0
    "HPACK dynamic table size update should resize the decoder table"

  let restoreSizeUpdate ← expectStatusOk
    (Http2.Hpack.encodeInteger 5 32 Http2.Hpack.defaultDynamicTableSize)
  let shrinkThenRestoreBlock := (bytes [0x20]).append restoreSizeUpdate |>.push 0x83
  let shrinkThenRestore ← expectStatusOk
    (Http2.Hpack.decodeHeaderBlock state shrinkThenRestoreBlock)
  expectEq shrinkThenRestore.state.maxSize Http2.Hpack.defaultDynamicTableSize
    "HPACK dynamic table size update should be able to restore the configured maximum"
  expectEq shrinkThenRestore.headers.size 1
    "HPACK headers after multiple leading dynamic table size updates should decode"

  let oversizedSizeUpdate ← expectStatusOk
    (Http2.Hpack.encodeInteger 5 32 (Http2.Hpack.defaultDynamicTableSize + 1))
  let oversizedSizeUpdateStatus ← expectStatusError
    (Http2.Hpack.decodeHeaderBlock state oversizedSizeUpdate)
  expectEq oversizedSizeUpdateStatus.code Code.internal
    "HPACK dynamic table size update above the configured maximum should reject"

  let lateSizeUpdateStatus ← expectStatusError (Http2.Hpack.decodeHeaderBlock state (bytes [0x83, 0x20]))
  expectEq lateSizeUpdateStatus.code Code.internal
    "HPACK dynamic table size update after a header field should reject"

  let upperName ← expectStatusOk (Http2.Hpack.encodeString "X-Meta")
  let upperValue ← expectStatusOk (Http2.Hpack.encodeString "value")
  let upperBlock := (bytes [0x00]).append upperName |>.append upperValue
  let upperStatus ← expectStatusError (Http2.Hpack.decodeHeaderBlock state upperBlock)
  expectEq upperStatus.code Code.internal
    "HPACK literal header names with uppercase characters should reject"

def testUnaryHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "lean-http2",
      data := request.data,
      status := Status.ok,
      trailers := Metadata.empty.insert "x-trace" "unary-trailer"
    }

  let state : Http2.Hpack.State := {}
  let teBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock state #[Header.of "te" "trailers"])
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
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := requestHeaderBlock.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := requestHeaderBlock
  }

  let requestMessage : Message := { data := bytes [42, 43, 44] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let decodedRequest ← expectStatusOk (Http2.Transport.decodeUnaryRequestFrames state #[requestHeadersFrame, requestDataFrame])
  expectEq decodedRequest.streamId 1 "decoded transport request should preserve stream id"
  expectEq decodedRequest.body requestBody "decoded transport request should preserve DATA bytes"
  expectEq (decodedRequest.metadata.get? ":path") (some "/lean.example.proto.NoteService/Echo") "decoded transport request should preserve path header"

  let splitHeaderAt := 12
  let splitRequestHeadersFrame : Http2.Frame := {
    header := {
      length := splitHeaderAt,
      frameType := Http2.FrameType.headers,
      flags := 0,
      streamId := 1
    },
    payload := requestHeaderBlock.extract 0 splitHeaderAt
  }
  let splitRequestContinuationFrame : Http2.Frame := {
    header := {
      length := requestHeaderBlock.size - splitHeaderAt,
      frameType := Http2.FrameType.continuation,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := requestHeaderBlock.extract splitHeaderAt requestHeaderBlock.size
  }
  let decodedSplitRequest ← expectStatusOk
    (Http2.Transport.decodeUnaryRequestFrames state
      #[splitRequestHeadersFrame, splitRequestContinuationFrame, requestDataFrame])
  expectEq decodedSplitRequest.body requestBody
    "raw transport decoder should collect DATA after request CONTINUATION frames"
  expectEq (decodedSplitRequest.metadata.get? ":path") (some "/lean.example.proto.NoteService/Echo")
    "raw transport decoder should decode request metadata split across CONTINUATION"
  let splitDispatchResult ← Http2.Transport.dispatchUnaryFrames registry state {}
    #[splitRequestHeadersFrame, splitRequestContinuationFrame, requestDataFrame]
  let splitResponseFrames ← expectStatusOk splitDispatchResult
  let splitResponseMessages ← expectStatusOk (Message.decodeAll splitResponseFrames.frames[1]!.payload)
  expectEq splitResponseMessages[0]!.data requestMessage.data
    "raw transport dispatch should handle request HEADERS plus CONTINUATION"
  let incompleteHeaderStatus ← expectStatusError
    (Http2.Transport.decodeUnaryRequestFrames state #[splitRequestHeadersFrame, requestDataFrame])
  expectEq incompleteHeaderStatus.code Code.internal
    "raw transport decoder should require CONTINUATION after incomplete HEADERS"

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry state {} #[requestHeadersFrame, requestDataFrame]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 3 "successful unary response should emit headers, data, trailers"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers "response should start with HEADERS"
  expectEq responseFrames.frames[1]!.header.frameType Http2.FrameType.data "response should include DATA"
  expectEq responseFrames.frames[2]!.header.frameType Http2.FrameType.headers "response should end with trailer HEADERS"
  expect (Http2.FrameFlag.has responseFrames.frames[2]!.header.flags Http2.FrameFlag.endStream) "trailers should end stream"
  expectEq responseFrames.inboundHpack.dynamic decodedRequest.hpack.dynamic "dispatch should preserve inbound HPACK dynamic table"
  expectEq responseFrames.inboundHpack.maxSize decodedRequest.hpack.maxSize "dispatch should preserve inbound HPACK max size"

  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? responseHeaders.headers ":status") (some "200") "response initial headers should include HTTP status"
  expectEq (Metadata.get? responseHeaders.headers "content-type") (some "application/grpc") "response initial headers should include gRPC content-type"
  expectEq (Metadata.get? responseHeaders.headers "grpc-accept-encoding") (some "identity,gzip")
    "response initial headers should advertise identity and gzip compression"
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "lean-http2") "response metadata should be encoded"

  let responseMessages ← expectStatusOk (Message.decodeAll responseFrames.frames[1]!.payload)
  expectEq responseMessages.size 1 "response DATA should contain one gRPC message"
  expectEq responseMessages[0]!.data requestMessage.data "response DATA should echo payload"

  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state responseFrames.frames[2]!.payload)
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0") "response trailers should include OK grpc-status"
  expectEq (Metadata.get? responseTrailers.headers "x-trace") (some "unary-trailer")
    "response trailers should include handler-provided unary trailers"

def testLargeUnaryResponseMetadataContinuationFrames : IO Unit := do
  let largeValue := largeAsciiString (Http2.defaultMaxFramePayloadLength + 200)
  let response : UnaryResponse := {
    metadata := Metadata.empty.insert "x-large" largeValue,
    data := bytes [1, 2, 3],
    status := Status.ok
  }
  let encoded ← expectStatusOk
    (Http2.Transport.encodeUnaryResponseFrames {} 1 response Http2.defaultMaxFramePayloadLength)
  let responseFrames := encoded.1
  let initialBlockFrames := takeHeaderBlockFramesFrom responseFrames 0
  expect (initialBlockFrames.size >= 2)
    "large response metadata should be split across HEADERS and CONTINUATION"
  expectEq initialBlockFrames[0]!.header.frameType Http2.FrameType.headers
    "split response metadata should start with HEADERS"
  expect (!Http2.FrameFlag.has initialBlockFrames[0]!.header.flags Http2.FrameFlag.endStream)
    "initial response metadata HEADERS should not end the stream"
  expect (!Http2.FrameFlag.has initialBlockFrames[0]!.header.flags Http2.FrameFlag.endHeaders)
    "split response metadata HEADERS should not carry END_HEADERS"
  let lastInitial := initialBlockFrames[initialBlockFrames.size - 1]!
  expectEq lastInitial.header.frameType Http2.FrameType.continuation
    "split response metadata should finish with CONTINUATION"
  expect (Http2.FrameFlag.has lastInitial.header.flags Http2.FrameFlag.endHeaders)
    "last response metadata CONTINUATION should carry END_HEADERS"
  for frame in initialBlockFrames do
    expect (frame.payload.size <= Http2.defaultMaxFramePayloadLength)
      "response header block frames should respect the peer max frame size"
  let decodedInitial ← expectStatusOk
    (Http2.Hpack.decodeHeaderBlock {} (headerBlockPayload initialBlockFrames))
  expectEq (Metadata.get? decodedInitial.headers "x-large") (some largeValue)
    "split response metadata should decode after reassembly"
  expectEq responseFrames[initialBlockFrames.size]!.header.frameType Http2.FrameType.data
    "response DATA should follow the complete initial header block"

def testLargeStreamResponseTrailerContinuationFrames : IO Unit := do
  let largeValue := largeAsciiString (Http2.defaultMaxFramePayloadLength + 200)
  let messages ← runGrpcM (MessageStream.ofArray #[bytes [9, 9, 9]])
  let response : ServerStreamingStreamResponse := {
    messages := messages,
    status := Status.ok,
    trailers := Metadata.empty.insert "x-large-trailer" largeValue
  }
  let encoded ← Http2.Transport.encodeServerStreamingStreamResponseFrames
    {} 1 response Http2.defaultMaxFramePayloadLength
  let (responseFrames, _) ← expectStatusOk encoded
  expectEq responseFrames[0]!.header.frameType Http2.FrameType.headers
    "stream response should start with initial HEADERS"
  expectEq responseFrames[1]!.header.frameType Http2.FrameType.data
    "stream response DATA should follow initial HEADERS"
  let initialHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames[0]!.payload)
  let trailerBlockFrames := takeHeaderBlockFramesFrom responseFrames 2
  expect (trailerBlockFrames.size >= 2)
    "large stream trailers should be split across HEADERS and CONTINUATION"
  expectEq trailerBlockFrames[0]!.header.frameType Http2.FrameType.headers
    "split stream trailers should start with HEADERS"
  expect (Http2.FrameFlag.has trailerBlockFrames[0]!.header.flags Http2.FrameFlag.endStream)
    "split stream trailer HEADERS should carry END_STREAM"
  expect (!Http2.FrameFlag.has trailerBlockFrames[0]!.header.flags Http2.FrameFlag.endHeaders)
    "split stream trailer HEADERS should not carry END_HEADERS"
  let lastTrailer := trailerBlockFrames[trailerBlockFrames.size - 1]!
  expectEq lastTrailer.header.frameType Http2.FrameType.continuation
    "split stream trailers should finish with CONTINUATION"
  expect (Http2.FrameFlag.has lastTrailer.header.flags Http2.FrameFlag.endHeaders)
    "last stream trailer CONTINUATION should carry END_HEADERS"
  for frame in trailerBlockFrames do
    expect (frame.payload.size <= Http2.defaultMaxFramePayloadLength)
      "stream trailer block frames should respect the peer max frame size"
  let decodedTrailers ← expectStatusOk
    (Http2.Hpack.decodeHeaderBlock initialHeaders.state (headerBlockPayload trailerBlockFrames))
  expectEq (Metadata.get? decodedTrailers.headers "grpc-status") (some "0")
    "split stream trailers should preserve grpc-status"
  expectEq (Metadata.get? decodedTrailers.headers "x-large-trailer") (some largeValue)
    "split stream trailers should decode after reassembly"

def testServerStreamingHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "List" }
  let registry := Registry.empty.registerServerStreaming method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "stream-http2",
      messages := #[request.data, bytes [8, 8, 8]],
      status := Status.ok,
      trailers := Metadata.empty.insert "x-stream-trace" "server-stream-trailer"
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/List"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestMessage : Message := { data := bytes [7, 7, 7] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[requestHeadersFrame, requestDataFrame]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 4
    "server-streaming response should emit headers, two DATA frames, and trailers"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "server-streaming response should start with HEADERS"
  expectEq responseFrames.frames[1]!.header.frameType Http2.FrameType.data
    "server-streaming response should include first DATA frame"
  expectEq responseFrames.frames[2]!.header.frameType Http2.FrameType.data
    "server-streaming response should include second DATA frame"
  expectEq responseFrames.frames[3]!.header.frameType Http2.FrameType.headers
    "server-streaming response should end with trailers"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state responseFrames.frames[3]!.payload)
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0")
    "server-streaming trailers should include OK grpc-status"
  expectEq (Metadata.get? responseTrailers.headers "x-stream-trace") (some "server-stream-trailer")
    "server-streaming trailers should include handler-provided trailers"
  let streamedMessages ← expectStatusOk (Message.decodeAll (dataPayloads responseFrames.frames))
  expectEq streamedMessages.size 2 "server-streaming DATA should decode two gRPC messages"
  expectEq streamedMessages[0]!.data requestMessage.data
    "first server-streaming DATA should preserve request payload"
  expectEq streamedMessages[1]!.data (bytes [8, 8, 8])
    "second server-streaming DATA should preserve handler payload"

def testStreamNativeServerStreamingHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "StreamList" }
  let producerTaskRef ← IO.mkRef (none : Option (Task (Except IO.Error Unit)))
  let registry := Registry.empty.registerServerStreamingStreamCodec method rawByteCodec rawByteCodec fun input => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    let task ← IO.asTask do
      runGrpcM do
        producer.send (input.append (bytes [1]))
        IO.sleep 1
        producer.send (bytes [2, 3])
        producer.close
    producerTaskRef.set (some task)
    pure producer.stream

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/StreamList"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestMessage : Message := { data := bytes [7, 7, 7] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[requestHeadersFrame, requestDataFrame]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 4
    "stream-native server-streaming response should emit headers, two DATA frames, and trailers"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state responseFrames.frames[3]!.payload)
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0")
    "stream-native server-streaming trailers should include OK grpc-status"
  let streamedMessages ← expectStatusOk (Message.decodeAll (dataPayloads responseFrames.frames))
  expectEq streamedMessages.size 2 "stream-native server-streaming DATA should decode two messages"
  expectEq streamedMessages[0]!.data (bytes [7, 7, 7, 1])
    "stream-native server-streaming should emit the first producer message"
  expectEq streamedMessages[1]!.data (bytes [2, 3])
    "stream-native server-streaming should emit the second producer message"
  match ← producerTaskRef.get with
  | none => throw (IO.userError "expected stream-native producer task to start")
  | some task => awaitIoTask task

def testServerStreamingHttp2SendMessageSizeLimitTransport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "LimitedStreamList" }
  let registry := (Registry.empty.withMaxSendMessageSize 2).registerServerStreaming method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "stream-size-limit",
      messages := #[request.data],
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/LimitedStreamList"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 2
    "oversized streaming response should emit initial headers and error trailers"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "oversized streaming response should still emit initial headers"
  expectEq responseFrames.frames[1]!.header.frameType Http2.FrameType.headers
    "oversized streaming response should end with trailers"
  expect (Http2.FrameFlag.has responseFrames.frames[1]!.header.flags Http2.FrameFlag.endStream)
    "oversized streaming response trailers should end the stream"
  expect (responseFrames.frames.all (fun frame => frame.header.frameType != Http2.FrameType.data))
    "oversized streaming response should not emit DATA"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {}
    responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "stream-size-limit")
    "oversized streaming response should preserve initial metadata"
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state
    responseFrames.frames[1]!.payload)
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "8")
    "oversized streaming response should return RESOURCE_EXHAUSTED trailers"

def testStreamingEncoderEmitsBeforeStreamEnd : IO Unit := do
  let producer ← runGrpcM (MessageStream.pipe (α := ByteArray) (capacity := some 1))
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let closeStartedRef ← IO.mkRef false
  let dataBeforeCloseRef ← IO.mkRef false
  let response : ServerStreamingStreamResponse := {
    metadata := Metadata.empty.insert "handled-by" "callback-stream",
    messages := producer.stream,
    status := Status.ok
  }
  let encodeTask ← IO.asTask do
    Http2.Transport.encodeServerStreamingStreamResponseFramesWith {} 1 response (fun frames => do
      for frame in frames do
        if frame.header.frameType == Http2.FrameType.data then
          if !(← closeStartedRef.get) then
            dataBeforeCloseRef.set true
      emittedRef.modify fun emitted => emitted.append frames)

  runGrpcM (producer.send (bytes [1, 2, 3]))
  waitUntil "streaming encoder did not emit DATA before the stream closed" 100
    dataBeforeCloseRef.get
  let emittedBeforeClose ← emittedRef.get
  expect (emittedBeforeClose.any fun frame => frame.header.frameType == Http2.FrameType.data)
    "streaming encoder should emit DATA before producer close"
  expect (!emittedBeforeClose.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "streaming encoder should not emit trailers before producer close"

  closeStartedRef.set true
  runGrpcM producer.close
  let _finalState ← expectStatusOk (← awaitIoTask encodeTask)
  let emitted ← emittedRef.get
  expectEq emitted.size 3 "streaming encoder should emit headers, DATA, and trailers"
  expectEq emitted[0]!.header.frameType Http2.FrameType.headers
    "streaming encoder should emit initial HEADERS first"
  expectEq emitted[1]!.header.frameType Http2.FrameType.data
    "streaming encoder should emit DATA as soon as stream messages arrive"
  expectEq emitted[2]!.header.frameType Http2.FrameType.headers
    "streaming encoder should emit trailers after producer close"
  expect (Http2.FrameFlag.has emitted[2]!.header.flags Http2.FrameFlag.endStream)
    "streaming encoder trailers should end the stream"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} emitted[0]!.payload)
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state emitted[2]!.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "callback-stream")
    "streaming encoder should preserve initial metadata"
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0")
    "streaming encoder should emit OK trailers after producer close"

def testStreamingDispatchEmitsBeforeStreamEnd : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "StreamDispatch" }
  let producerRef ← IO.mkRef (none : Option (MessageStream.Producer ByteArray))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    producerRef.set (some producer)
    pure {
      metadata := Metadata.empty.insert "handled-by" "dispatch-callback",
      messages := producer.stream,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/StreamDispatch"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [9, 9] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let closeStartedRef ← IO.mkRef false
  let dataBeforeCloseRef ← IO.mkRef false
  let dispatchTask ← IO.asTask do
    Http2.Transport.dispatchUnaryFramesWith registry {} {} #[requestHeadersFrame, requestDataFrame]
      (fun frames => do
        for frame in frames do
          if frame.header.frameType == Http2.FrameType.data then
            if !(← closeStartedRef.get) then
              dataBeforeCloseRef.set true
        emittedRef.modify fun emitted => emitted.append frames)

  waitUntil "streaming dispatch did not start the stream handler" 100 do
    match ← producerRef.get with
    | none => pure false
    | some _ => pure true
  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected dispatch stream producer")
  runGrpcM (producer.send (bytes [4, 4]))
  waitUntil "streaming dispatch did not emit DATA before the stream closed" 100
    dataBeforeCloseRef.get
  let emittedBeforeClose ← emittedRef.get
  expect (emittedBeforeClose.any fun frame => frame.header.frameType == Http2.FrameType.data)
    "streaming dispatch should emit DATA before producer close"
  expect (!emittedBeforeClose.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "streaming dispatch should not emit trailers before producer close"

  closeStartedRef.set true
  runGrpcM producer.close
  let _result ← expectStatusOk (← awaitIoTask dispatchTask)
  let emitted ← emittedRef.get
  expectEq emitted.size 3 "streaming dispatch should emit headers, DATA, and trailers"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads emitted))
  expectEq responseMessages.size 1 "streaming dispatch DATA should decode one message"
  expectEq responseMessages[0]!.data (bytes [4, 4])
    "streaming dispatch should emit producer message data"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} emitted[0]!.payload)
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state emitted[2]!.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "dispatch-callback")
    "streaming dispatch should preserve initial metadata"
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0")
    "streaming dispatch should emit OK trailers after producer close"

def testStreamingConnectionEmitsBeforeStreamEnd : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "StreamConnection" }
  let producerRef ← IO.mkRef (none : Option (MessageStream.Producer ByteArray))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    producerRef.set (some producer)
    pure {
      metadata := Metadata.empty.insert "handled-by" "connection-callback",
      messages := producer.stream,
      status := Status.ok
    }

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/StreamConnection"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [6, 6] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  let emittedRef ← IO.mkRef ByteArray.empty
  let closeStartedRef ← IO.mkRef false
  let dataBeforeCloseRef ← IO.mkRef false
  let processTask ← IO.asTask do
    Http2.Connection.processBytesEncodedWith registry {} (
      Http2.connectionPreface
        |>.append clientSettingsWire
        |>.append requestHeadersWire
        |>.append requestDataWire
    ) fun bytes => do
      emittedRef.modify fun emitted => emitted.append bytes
      match Http2.Frame.decodeAll bytes with
      | .ok frames =>
          for frame in frames do
            if frame.header.frameType == Http2.FrameType.data then
              if !(← closeStartedRef.get) then
                dataBeforeCloseRef.set true
      | .error _ => pure ()

  waitUntil "streaming connection did not start the stream handler" 100 do
    match ← producerRef.get with
    | none => pure false
    | some _ => pure true
  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected connection stream producer")
  runGrpcM (producer.send (bytes [7, 7]))
  waitUntil "streaming connection did not emit DATA before the stream closed" 100
    dataBeforeCloseRef.get
  let emittedBeforeCloseBytes ← emittedRef.get
  let emittedBeforeClose ← expectStatusOk (Http2.Frame.decodeAll emittedBeforeCloseBytes)
  expect (emittedBeforeClose.any fun frame => frame.header.frameType == Http2.FrameType.data)
    "streaming connection should emit DATA before producer close"
  expect (!emittedBeforeClose.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "streaming connection should not emit trailers before producer close"

  closeStartedRef.set true
  runGrpcM producer.close
  let _state ← expectStatusOk (← awaitIoTask processTask)
  let emittedBytes ← emittedRef.get
  let emitted ← expectStatusOk (Http2.Frame.decodeAll emittedBytes)
  let dataFrames := emitted.filter (fun frame => frame.header.frameType == Http2.FrameType.data)
  expectEq dataFrames.size 1 "streaming connection should emit one response DATA frame"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads emitted))
  expectEq responseMessages.size 1 "streaming connection DATA should decode one message"
  expectEq responseMessages[0]!.data (bytes [7, 7])
    "streaming connection should emit producer message data"
  let responseHeaderFrame ← match emitted.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && !Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream) with
    | some frame => pure frame
    | none => throw (IO.userError "expected streaming connection initial response headers")
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseHeaderFrame.payload)
  let trailerFrame ← match emitted.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream) with
    | some frame => pure frame
    | none => throw (IO.userError "expected streaming connection response trailers")
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state trailerFrame.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "connection-callback")
    "streaming connection should preserve initial metadata"
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0")
    "streaming connection should emit OK trailers after producer close"

def testServerStreamingHttp2StreamErrorTransport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "StreamError" }
  let registry := Registry.empty.registerServerStreamingStream method fun request => do
    let sent ← IO.mkRef false
    let stream : MessageStream ByteArray := {
      recv? := do
        if ← sent.get then
          throw (Status.internal "stream failed")
        else
          sent.set true
          pure (some request.data)
    }
    pure {
      metadata := Metadata.empty.insert "handled-by" "stream-error-http2",
      messages := stream,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/StreamError"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestMessage : Message := { data := bytes [4, 5, 6] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[requestHeadersFrame, requestDataFrame]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 3
    "stream errors after data should emit headers, DATA, and error trailers"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "stream-error-http2")
    "stream error response should preserve initial metadata"
  let streamedMessages ← expectStatusOk (Message.decodeAll (dataPayloads responseFrames.frames))
  expectEq streamedMessages.size 1 "stream error response should include data emitted before failure"
  expectEq streamedMessages[0]!.data (bytes [4, 5, 6])
    "stream error response should preserve the message emitted before failure"
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state responseFrames.frames[2]!.payload)
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "13")
    "stream error trailers should carry INTERNAL grpc-status"
  expectEq (Metadata.get? responseTrailers.headers "grpc-message") (some "stream failed")
    "stream error trailers should preserve grpc-message"

def testClientStreamingHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Collect" }
  let registry := Registry.empty.registerClientStreaming method fun request => do
    pure {
      metadata := Metadata.empty,
      data := request.messages.foldl (fun out message => out.append message) ByteArray.empty,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Collect"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let first ← expectStatusOk (Message.encode { data := bytes [1, 2] })
  let second ← expectStatusOk (Message.encode { data := bytes [3, 4] })
  let requestDataFrame1 : Http2.Frame := {
    header := {
      length := first.size,
      frameType := Http2.FrameType.data,
      flags := 0,
      streamId := 1
    },
    payload := first
  }
  let requestDataFrame2 : Http2.Frame := {
    header := {
      length := second.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := second
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame1,
    requestDataFrame2
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 3
    "client-streaming response should emit headers, DATA, and trailers"
  let dataFrames := responseFrames.frames.filter (fun frame => frame.header.frameType == Http2.FrameType.data)
  expectEq dataFrames.size 1 "client-streaming response should include one DATA frame"
  let responseMessages ← expectStatusOk (Message.decodeAll dataFrames[0]!.payload)
  expectEq responseMessages.size 1 "client-streaming response DATA should decode one message"
  expectEq responseMessages[0]!.data (bytes [1, 2, 3, 4])
    "client-streaming response should aggregate request messages"

def testBidirectionalStreamingHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Chat" }
  let registry := Registry.empty.registerBidirectionalStreaming method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "bidi-http2",
      messages := request.messages.map (fun message => message.append (bytes [5])),
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Chat"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let first ← expectStatusOk (Message.encode { data := bytes [1, 2] })
  let second ← expectStatusOk (Message.encode { data := bytes [3, 4] })
  let requestDataFrame1 : Http2.Frame := {
    header := {
      length := first.size,
      frameType := Http2.FrameType.data,
      flags := 0,
      streamId := 1
    },
    payload := first
  }
  let requestDataFrame2 : Http2.Frame := {
    header := {
      length := second.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := second
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame1,
    requestDataFrame2
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 4
    "bidirectional-streaming response should emit headers, two DATA frames, and trailers"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "bidirectional-streaming response should start with HEADERS"
  expectEq responseFrames.frames[1]!.header.frameType Http2.FrameType.data
    "bidirectional-streaming response should include first DATA frame"
  expectEq responseFrames.frames[2]!.header.frameType Http2.FrameType.data
    "bidirectional-streaming response should include second DATA frame"
  expectEq responseFrames.frames[3]!.header.frameType Http2.FrameType.headers
    "bidirectional-streaming response should end with trailers"
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "bidi-http2")
    "bidirectional-streaming response metadata should be encoded"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads responseFrames.frames))
  expectEq responseMessages.size 2 "bidirectional-streaming DATA should decode two gRPC messages"
  expectEq responseMessages[0]!.data (bytes [1, 2, 5])
    "first bidirectional-streaming DATA should transform first request"
  expectEq responseMessages[1]!.data (bytes [3, 4, 5])
    "second bidirectional-streaming DATA should transform second request"

def testPaddedPriorityUnaryHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let headerPadding := bytes [0, 0]
  let priorityFields := bytes [0, 0, 0, 0, 16]
  let paddedHeaderPayload := (bytes [headerPadding.size])
    |>.append priorityFields
    |>.append encodedHeaders.1
    |>.append headerPadding
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := paddedHeaderPayload.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[
        Http2.FrameFlag.endHeaders,
        Http2.FrameFlag.padded,
        Http2.FrameFlag.priority
      ],
      streamId := 1
    },
    payload := paddedHeaderPayload
  }

  let requestMessage : Message := { data := bytes [5, 6, 7] }
  let requestBody ← expectStatusOk requestMessage.encode
  let dataPadding := bytes [0, 0, 0]
  let paddedDataPayload := (bytes [dataPadding.size])
    |>.append requestBody
    |>.append dataPadding
  let requestDataFrame : Http2.Frame := {
    header := {
      length := paddedDataPayload.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endStream, Http2.FrameFlag.padded],
      streamId := 1
    },
    payload := paddedDataPayload
  }

  let decodedRequest ← expectStatusOk (Http2.Transport.decodeUnaryRequestFrames {} #[
    requestHeadersFrame,
    requestDataFrame
  ])
  expectEq decodedRequest.body requestBody
    "padded DATA should decode to the unpadded gRPC request body"
  expectEq (decodedRequest.metadata.get? ":path") (some "/lean.example.proto.NoteService/Echo")
    "priority/padded HEADERS should decode to request metadata"

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame
  ]
  let responseFrames ← expectStatusOk dispatchResult
  let dataFrames := responseFrames.frames.filter (fun frame => frame.header.frameType == Http2.FrameType.data)
  expectEq dataFrames.size 1 "padded unary request should produce one DATA response"
  let responseMessages ← expectStatusOk (Message.decodeAll dataFrames[0]!.payload)
  expectEq responseMessages.size 1 "padded unary response DATA should decode"
  expectEq responseMessages[0]!.data requestMessage.data
    "padded unary request should preserve request payload"

def testHeadersPrioritySelfDependencyRejected : IO Unit := do
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let priorityFields := bytes [0, 0, 0, 1, 16]
  let headersFrame : Http2.Frame := {
    header := {
      length := priorityFields.size + encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[
        Http2.FrameFlag.endHeaders,
        Http2.FrameFlag.endStream,
        Http2.FrameFlag.priority
      ],
      streamId := 1
    },
    payload := priorityFields.append encodedHeaders.1
  }
  let result ← Http2.Connection.processFrame Registry.empty readyConnectionState headersFrame
  let status ← expectStatusError result
  expectEq status.code Code.internal
    "HEADERS priority dependency on the same stream should reject"

def testInboundHeaderListSizeLimit : IO Unit := do
  let headers := requestHeaders.insert "x-large-metadata" "abcdefghijklmnopqrstuvwxyz"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} headers)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let headerListSize := Metadata.headerListSize headers

  let decoded ← expectStatusOk (Http2.Transport.decodeUnaryRequestFrames {}
    #[requestHeadersFrame] (some headerListSize))
  expectEq (decoded.metadata.get? "x-large-metadata") (some "abcdefghijklmnopqrstuvwxyz")
    "header list at the configured limit should decode"

  let tooSmallStatus ← expectStatusError <|
    Http2.Transport.decodeUnaryRequestFrames {} #[requestHeadersFrame] (some (headerListSize - 1))
  expectEq tooSmallStatus.code Code.resourceExhausted
    "oversized decoded header lists should fail with RESOURCE_EXHAUSTED"

def testTrailersOnlyUnaryFailure : IO Unit := do
  let unknownHeaders := requestHeadersForPath "/lean.example.proto.NoteService/Missing"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} unknownHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 1
    },
    payload := encodedHeaders.1
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames Registry.empty {} {} #[requestHeadersFrame]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 1 "early unary failure should emit one trailers-only HEADERS frame"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "trailers-only failure should use HEADERS"
  expect (Http2.FrameFlag.has responseFrames.frames[0]!.header.flags Http2.FrameFlag.endStream)
    "trailers-only failure HEADERS should end the stream"
  expect (responseFrames.frames.all (fun frame => frame.header.frameType != Http2.FrameType.data))
    "trailers-only failure should not emit DATA"

  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers ":status") (some "200")
    "trailers-only failure should include HTTP status"
  expectEq (Metadata.get? trailersOnly.headers "content-type") (some "application/grpc")
    "trailers-only failure should include gRPC content-type"
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "12")
    "unknown method should map to grpc-status UNIMPLEMENTED"

  let nonGrpcHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/json"
    |>.insert "te" "trailers"
  let nonGrpcEncodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} nonGrpcHeaders)
  let nonGrpcHeadersFrame : Http2.Frame := {
    header := {
      length := nonGrpcEncodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 1
    },
    payload := nonGrpcEncodedHeaders.1
  }
  let nonGrpcResult ← Http2.Transport.dispatchUnaryFrames Registry.empty {} {} #[nonGrpcHeadersFrame]
  let nonGrpcResponse ← expectStatusOk nonGrpcResult
  expectEq nonGrpcResponse.frames.size 1
    "unsupported media type should emit one HTTP status HEADERS frame"
  expectEq nonGrpcResponse.frames[0]!.header.frameType Http2.FrameType.headers
    "unsupported media type response should use HEADERS"
  expect (Http2.FrameFlag.has nonGrpcResponse.frames[0]!.header.flags Http2.FrameFlag.endStream)
    "unsupported media type response should end the stream"
  let nonGrpcResponseHeaders ← expectStatusOk
    (Http2.Hpack.decodeHeaderBlock {} nonGrpcResponse.frames[0]!.payload)
  expectEq (Metadata.get? nonGrpcResponseHeaders.headers ":status") (some "415")
    "unsupported media type should map to HTTP 415"
  expectEq (Metadata.get? nonGrpcResponseHeaders.headers "grpc-status") none
    "unsupported media type should not be encoded as a gRPC trailers-only error"
  expectEq (Metadata.get? nonGrpcResponseHeaders.headers "content-type") none
    "unsupported media type should not advertise a gRPC response content-type"

  let grpcJsonHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc+json"
    |>.insert "te" "trailers"
  let grpcJsonEncodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} grpcJsonHeaders)
  let grpcJsonHeadersFrame : Http2.Frame := {
    header := {
      length := grpcJsonEncodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 1
    },
    payload := grpcJsonEncodedHeaders.1
  }
  let grpcJsonResult ← Http2.Transport.dispatchUnaryFrames Registry.empty {} {} #[grpcJsonHeadersFrame]
  let grpcJsonResponse ← expectStatusOk grpcJsonResult
  expectEq grpcJsonResponse.frames.size 1
    "unsupported gRPC subtype should emit one HTTP status HEADERS frame"
  let grpcJsonResponseHeaders ← expectStatusOk
    (Http2.Hpack.decodeHeaderBlock {} grpcJsonResponse.frames[0]!.payload)
  expectEq (Metadata.get? grpcJsonResponseHeaders.headers ":status") (some "415")
    "unsupported gRPC subtype should map to HTTP 415"
  expectEq (Metadata.get? grpcJsonResponseHeaders.headers "grpc-status") none
    "unsupported gRPC subtype should not be encoded as gRPC trailers"

def testDeadlineExceededHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    IO.sleep 20
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let timeoutHeaders := requestHeaders.insert "grpc-timeout" "1m"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} timeoutHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 1
    "deadline-exceeded unary response should emit trailers-only HEADERS"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "deadline-exceeded response should use HEADERS"
  expect (Http2.FrameFlag.has responseFrames.frames[0]!.header.flags Http2.FrameFlag.endStream)
    "deadline-exceeded trailers-only response should end the stream"
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "4")
    "deadline-exceeded transport response should encode grpc-status DEADLINE_EXCEEDED"

def testHandlerExceptionHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun _request => do
    throwGrpcIo "handler exploded"

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 1
    "handler exception response should emit trailers-only HEADERS"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "handler exception response should use HEADERS"
  expect (Http2.FrameFlag.has responseFrames.frames[0]!.header.flags Http2.FrameFlag.endStream)
    "handler exception trailers-only response should end the stream"
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "2")
    "handler exception transport response should encode grpc-status UNKNOWN"
  expectEq (Metadata.get? trailersOnly.headers "grpc-message") (some "handler exploded")
    "handler exception transport response should encode grpc-message"

def testInvalidResponseMetadataHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "content-type" "text/plain",
      data := request.data,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 1
    "invalid response metadata should emit trailers-only HEADERS"
  expectEq responseFrames.frames[0]!.header.frameType Http2.FrameType.headers
    "invalid response metadata response should use HEADERS"
  expect (Http2.FrameFlag.has responseFrames.frames[0]!.header.flags Http2.FrameFlag.endStream)
    "invalid response metadata trailers-only response should end the stream"
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "13")
    "invalid response metadata should encode grpc-status INTERNAL"
  expectEq (Metadata.get? trailersOnly.headers "grpc-message")
    (some "reserved gRPC response metadata name content-type")
    "invalid response metadata should encode grpc-message"

def testNonOkUnaryIgnoresUnusedResponseDataLimitHttp2Transport : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := (Registry.empty.withMaxSendMessageSize 2).registerUnary method fun _request => do
    pure {
      metadata := Metadata.empty,
      data := bytes [9, 9, 9],
      status := Status.invalidArgument "bad request"
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[
    requestHeadersFrame,
    requestDataFrame
  ]
  let responseFrames ← expectStatusOk dispatchResult
  expectEq responseFrames.frames.size 1
    "non-OK unary response with oversized unused data should emit trailers-only"
  expect (responseFrames.frames.all (fun frame => frame.header.frameType != Http2.FrameType.data))
    "non-OK unary response with oversized unused data should not emit DATA"
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} responseFrames.frames[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "3")
    "non-OK unary response should preserve explicit handler status"
  expectEq (Metadata.get? trailersOnly.headers "grpc-message") (some "bad request")
    "non-OK unary response should preserve explicit handler status message"

def testLargeUnaryResponseDataFrames : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let largeData := repeatByte (Http2.defaultMaxFramePayloadLength * 2 + 10) 65
  let registry := Registry.empty.registerUnary method fun _request => do
    pure {
      metadata := Metadata.empty,
      data := largeData,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestMessage : Message := { data := bytes [1] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let dispatchResult ← Http2.Transport.dispatchUnaryFrames registry {} {} #[requestHeadersFrame, requestDataFrame]
  let responseFrames ← expectStatusOk dispatchResult
  let dataFrames := responseFrames.frames.filter (fun frame => frame.header.frameType == Http2.FrameType.data)
  expectEq dataFrames.size 3 "large response should be split across three DATA frames"
  for frame in dataFrames do
    expect (frame.payload.size <= Http2.defaultMaxFramePayloadLength) "DATA frame should respect default max frame size"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads dataFrames))
  expectEq responseMessages.size 1 "split response DATA should decode as one gRPC message"
  expectEq responseMessages[0]!.data largeData "split response DATA should preserve payload"

def testOutboundFlowControl : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let largeData := repeatByte (Http2.Connection.initialFlowControlWindow + Http2.defaultMaxFramePayloadLength + 10) 90
  let registry := Registry.empty.registerUnary method fun _request => do
    pure {
      metadata := Metadata.empty,
      data := largeData,
      status := Status.ok
    }

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestMessage : Message := { data := bytes [1] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  let firstResult ← Http2.Connection.processBytes registry {} (
    Http2.connectionPreface
      |>.append clientSettingsWire
      |>.append requestHeadersWire
      |>.append requestDataWire
  )
  let (state1, emitted1) ← expectStatusOk firstResult
  expect (!state1.pendingOutbound.isEmpty) "large response should leave pending outbound frames"
  expectEq (dataPayloads emitted1).size Http2.Connection.initialFlowControlWindow
    "first outbound flush should stop at initial flow-control window"

  let increment := largeData.size + 5
  let connUpdate ← expectStatusOk (Http2.WindowUpdate.frame 0 increment)
  let streamUpdate ← expectStatusOk (Http2.WindowUpdate.frame 1 increment)
  let connUpdateWire ← expectStatusOk (Http2.Frame.encode connUpdate)
  let streamUpdateWire ← expectStatusOk (Http2.Frame.encode streamUpdate)
  let secondResult ← Http2.Connection.processBytes registry state1 (connUpdateWire.append streamUpdateWire)
  let (state2, emitted2) ← expectStatusOk secondResult
  expect state2.pendingOutbound.isEmpty "WINDOW_UPDATE should flush pending outbound frames"
  expect state2.outboundStreamWindows.isEmpty
    "final WINDOW_UPDATE flush should clear closed stream outbound window state"
  let payload := (dataPayloads emitted1).append (dataPayloads emitted2)
  let responseMessages ← expectStatusOk (Message.decodeAll payload)
  expectEq responseMessages.size 1 "flow-controlled DATA should decode as one gRPC message"
  expectEq responseMessages[0]!.data largeData "flow-controlled DATA should preserve payload"
  expect (emitted2.any (fun frame =>
    frame.header.frameType == Http2.FrameType.headers
      && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream))
    "final flow-control flush should include response trailers"

def testOutboundWindowUpdateOverflowRejected : IO Unit := do
  let connectionOverflow ← expectStatusOk (Http2.WindowUpdate.frame 0 1)
  let connectionResult ← Http2.Connection.processFrame Registry.empty {
    readyConnectionState with
    outboundConnectionWindow := Http2.maxStreamId
  } connectionOverflow
  let connectionStatus ← expectStatusError connectionResult
  expectEq connectionStatus.code Code.internal
    "connection WINDOW_UPDATE overflow should reject"

  let streamOverflow ← expectStatusOk (Http2.WindowUpdate.frame 1 1)
  let streamResult ← Http2.Connection.processFrame Registry.empty {
    readyConnectionState with
    outboundInitialStreamWindow := Http2.maxStreamId
  } streamOverflow
  let streamStatus ← expectStatusError streamResult
  expectEq streamStatus.code Code.internal
    "stream WINDOW_UPDATE overflow should reject"

def testOutboundInitialWindowReductionKeepsNegativeStreamDebt : IO Unit := do
  let pendingData : Http2.Frame := {
    header := {
      length := 2,
      frameType := Http2.FrameType.data,
      flags := 0,
      streamId := 1
    },
    payload := bytes [1, 2]
  }
  let state0 : Http2.Connection.State := {
    readyConnectionState with
    outboundConnectionWindow := 10,
    outboundInitialStreamWindow := 10,
    outboundStreamWindows := #[{ streamId := 1, window := (5 : Int) }],
    pendingOutbound := #[pendingData]
  }
  let reduceInitialWindow ← expectStatusOk (Http2.Settings.frame #[
    { id := Http2.SettingId.initialWindowSize, value := 0 }
  ])
  let reduceResult ← Http2.Connection.processFrame Registry.empty state0 reduceInitialWindow
  let (state1, emitted1) ← expectStatusOk reduceResult
  expectEq emitted1.size 1 "SETTINGS reduction should only emit an ACK"
  expectEq emitted1[0]!.header.frameType Http2.FrameType.settings
    "SETTINGS reduction response should be ACK SETTINGS"
  expect (Http2.Settings.isAck emitted1[0]!)
    "SETTINGS reduction response should mark ACK"
  expectEq state1.outboundStreamWindows[0]!.window (-5 : Int)
    "SETTINGS_INITIAL_WINDOW_SIZE reduction should preserve negative stream-window debt"

  let repayDebt ← expectStatusOk (Http2.WindowUpdate.frame 1 5)
  let repayDebtResult ← Http2.Connection.processFrame Registry.empty state1 repayDebt
  let (state2, emitted2) ← expectStatusOk repayDebtResult
  expect emitted2.isEmpty
    "WINDOW_UPDATE that only repays negative stream-window debt should not flush DATA"
  expectEq state2.outboundStreamWindows[0]!.window (0 : Int)
    "repaid stream-window debt should leave zero send credit"

  let openCredit ← expectStatusOk (Http2.WindowUpdate.frame 1 1)
  let openCreditResult ← Http2.Connection.processFrame Registry.empty state2 openCredit
  let (_state3, emitted3) ← expectStatusOk openCreditResult
  expectEq emitted3.size 1
    "WINDOW_UPDATE beyond stream-window debt should flush pending DATA"
  expectEq emitted3[0]!.header.frameType Http2.FrameType.data
    "positive stream-window credit should emit DATA"
  expectEq emitted3[0]!.payload.size 1
    "positive stream-window credit should cap emitted DATA size"

def testResetStreamClearsPendingOutbound : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let largeData := repeatByte (Http2.Connection.initialFlowControlWindow + Http2.defaultMaxFramePayloadLength + 10) 70
  let registry := Registry.empty.registerUnary method fun _request => do
    pure {
      metadata := Metadata.empty,
      data := largeData,
      status := Status.ok
    }

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  let firstResult ← Http2.Connection.processBytes registry {} (
    Http2.connectionPreface
      |>.append clientSettingsWire
      |>.append requestHeadersWire
      |>.append requestDataWire
  )
  let (state1, emitted1) ← expectStatusOk firstResult
  expect (!state1.pendingOutbound.isEmpty) "large response should leave pending outbound before reset"
  expectEq (dataPayloads emitted1).size Http2.Connection.initialFlowControlWindow
    "first flush should consume the initial stream window"

  let reset ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  let resetWire ← expectStatusOk (Http2.Frame.encode reset)
  let resetResult ← Http2.Connection.processBytes registry state1 resetWire
  let (state2, emitted2) ← expectStatusOk resetResult
  expectEq emitted2.size 0 "RST_STREAM should not emit response frames"
  expect state2.pendingOutbound.isEmpty "RST_STREAM should drop queued outbound frames for the stream"

  let connUpdate ← expectStatusOk (Http2.WindowUpdate.frame 0 (largeData.size + 5))
  let streamUpdate ← expectStatusOk (Http2.WindowUpdate.frame 1 (largeData.size + 5))
  let connUpdateWire ← expectStatusOk (Http2.Frame.encode connUpdate)
  let streamUpdateWire ← expectStatusOk (Http2.Frame.encode streamUpdate)
  let flushedResult ← Http2.Connection.processBytes registry state2 (connUpdateWire.append streamUpdateWire)
  let (state3, emitted3) ← expectStatusOk flushedResult
  expect state3.pendingOutbound.isEmpty "WINDOW_UPDATE after reset should not recreate pending frames"
  expectEq emitted3.size 0 "WINDOW_UPDATE after reset should not flush reset-stream response frames"

def testInboundFrameSizeLimit : IO Unit := do
  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let oversizedPayload := repeatByte (Http2.defaultMaxFramePayloadLength + 1) 7
  let oversizedDataFrame : Http2.Frame := {
    header := {
      length := oversizedPayload.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := oversizedPayload
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let oversizedDataWire ← expectStatusOk (Http2.Frame.encode oversizedDataFrame)
  let result ← Http2.Connection.processBytes Registry.empty {} (
    Http2.connectionPreface
      |>.append clientSettingsWire
      |>.append requestHeadersWire
      |>.append oversizedDataWire
  )
  let status ← expectStatusError result
  expectEq status.code Code.internal "oversized inbound HTTP/2 frames should reject"

def testInboundFlowControlLimit : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let state0 : Http2.Connection.State := {
    readyConnectionState with
    inboundConnectionWindow := 10,
    inboundInitialStreamWindow := 10
  }
  let headersResult ← Http2.Connection.processFrame registry state0 requestHeadersFrame
  let (state1, emitted1) ← expectStatusOk headersResult
  expectEq emitted1.size 0 "incomplete stream HEADERS should not emit frames"

  let payload := repeatByte 11 9
  let dataFrame : Http2.Frame := {
    header := {
      length := payload.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := payload
  }
  let dataResult ← Http2.Connection.processFrame registry state1 dataFrame
  let status ← expectStatusError dataResult
  expectEq status.code Code.internal "DATA exceeding inbound flow-control window should reject"

def testClientStreamIdValidation : IO Unit := do
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let evenHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 2
    },
    payload := encodedHeaders.1
  }
  let headersResult ← Http2.Connection.processFrame Registry.empty readyConnectionState evenHeadersFrame
  let headersStatus ← expectStatusError headersResult
  expectEq headersStatus.code Code.internal "client HEADERS should reject even stream ids"

  let dataFrame : Http2.Frame := {
    header := {
      length := 1,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 2
    },
    payload := bytes [1]
  }
  let dataResult ← Http2.Connection.processFrame Registry.empty readyConnectionState dataFrame
  let dataStatus ← expectStatusError dataResult
  expectEq dataStatus.code Code.internal "client DATA should reject even stream ids"

  let reset ← expectStatusOk (Http2.RstStream.frame 2 Http2.ErrorCode.cancel)
  let resetResult ← Http2.Connection.processFrame Registry.empty readyConnectionState reset
  let resetStatus ← expectStatusError resetResult
  expectEq resetStatus.code Code.internal "client RST_STREAM should reject even stream ids"

  let windowUpdate ← expectStatusOk (Http2.WindowUpdate.frame 2 1)
  let windowResult ← Http2.Connection.processFrame Registry.empty readyConnectionState windowUpdate
  let windowStatus ← expectStatusError windowResult
  expectEq windowStatus.code Code.internal "client stream WINDOW_UPDATE should reject even stream ids"

def testClientStreamIdMonotonicity : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let completedHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let firstResult ← Http2.Connection.processFrame registry readyConnectionState completedHeadersFrame
  let (state1, _emitted1) ← expectStatusOk firstResult
  expectEq state1.lastClientStreamId 1 "completed stream should advance last client stream id"

  let reuseResult ← Http2.Connection.processFrame registry state1 completedHeadersFrame
  let reuseStatus ← expectStatusError reuseResult
  expectEq reuseStatus.code Code.internal "client stream ids should not be reused"

  let activeHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 3
    },
    payload := encodedHeaders.1
  }
  let activeResult ← Http2.Connection.processFrame registry state1 activeHeadersFrame
  let (state2, emitted2) ← expectStatusOk activeResult
  expectEq emitted2.size 0 "active stream HEADERS should not emit before END_STREAM"

  let duplicateResult ← Http2.Connection.processFrame registry state2 activeHeadersFrame
  let duplicateStatus ← expectStatusError duplicateResult
  expectEq duplicateStatus.code Code.internal "active unary stream should reject duplicate HEADERS"

def testMaxConcurrentStreamsEnforced : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let activeHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let state0 := Http2.Connection.initialState (some 1)
  let firstResult ← Http2.Connection.processFrame registry state0 activeHeadersFrame
  let (state1, emitted1) ← expectStatusOk firstResult
  expectEq emitted1.size 0 "incomplete first stream should not emit frames"
  expectEq state1.streams.size 1 "first incomplete stream should occupy one active slot"

  let secondHeadersFrame : Http2.Frame := {
    activeHeadersFrame with header := { activeHeadersFrame.header with streamId := 3 }
  }
  let secondResult ← Http2.Connection.processFrame registry state1 secondHeadersFrame
  let secondStatus ← expectStatusError secondResult
  expectEq secondStatus.code Code.internal
    "second active stream should be rejected when max concurrent streams is one"

  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let dataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let completedResult ← Http2.Connection.processFrame registry state1 dataFrame
  let (state2, _emitted2) ← expectStatusOk completedResult
  expectEq state2.streams.size 0 "completed stream should free its active stream slot"

  let thirdResult ← Http2.Connection.processFrame registry state2 secondHeadersFrame
  let (state3, emitted3) ← expectStatusOk thirdResult
  expectEq emitted3.size 0 "new stream after completion should be admitted"
  expectEq state3.streams.size 1 "new incomplete stream should occupy the freed active slot"

def testMaxConcurrentStreamsCountsEarlyRejectedBodyDrains : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let calledRef ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    calledRef.set true
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let invalidHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
  let encodedInvalidHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} invalidHeaders)
  let invalidHeadersFrame : Http2.Frame := {
    header := {
      length := encodedInvalidHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedInvalidHeaders.1
  }
  let state0 := Http2.Connection.initialState (some 1)
  let firstResult ← Http2.Connection.processFrame registry state0 invalidHeadersFrame
  let (state1, emitted1) ← expectStatusOk firstResult
  expect (!(← calledRef.get))
    "early rejected stream should not invoke the unary handler"
  expectEq emitted1.size 1
    "early rejected stream should emit one trailers-only response"
  expect (state1.ignoredInboundStreams.contains 1)
    "early rejected stream with an open request body should occupy one active slot"

  let validHeaders := requestHeadersForPath "/lean.example.proto.NoteService/Echo"
  let encodedValidHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} validHeaders)
  let secondHeadersFrame : Http2.Frame := {
    header := {
      length := encodedValidHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 3
    },
    payload := encodedValidHeaders.1
  }
  let secondResult ← Http2.Connection.processFrame registry state1 secondHeadersFrame
  let secondStatus ← expectStatusError secondResult
  expectEq secondStatus.code Code.internal
    "early rejected stream should count against max concurrent streams until its body drains"

  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let drainDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let drainResult ← Http2.Connection.processFrame registry state1 drainDataFrame
  let (state2, emitted2) ← expectStatusOk drainResult
  expect (!state2.ignoredInboundStreams.contains 1)
    "END_STREAM on an ignored request body should free the active slot"
  expectEq emitted2.size 2
    "drained ignored body should emit connection and stream WINDOW_UPDATE frames"

  let thirdResult ← Http2.Connection.processFrame registry state2 secondHeadersFrame
  let (state3, emitted3) ← expectStatusOk thirdResult
  expectEq emitted3.size 0
    "new stream after draining an early rejected body should be admitted"
  expectEq state3.streams.size 1
    "admitted stream should occupy the freed active slot"

def testMaxConcurrentStreamsCountsDetachedStreamingDispatch : IO Unit := do
  let streamMethod : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "LimitedStream"
  }
  let producerRef ← IO.mkRef (none : Option (MessageStream.Producer ByteArray))
  let registry := Registry.empty.registerServerStreamingStream streamMethod fun _request => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    producerRef.set (some producer)
    pure {
      metadata := Metadata.empty.insert "handled-by" "max-concurrent-detached",
      messages := producer.stream,
      status := Status.ok
    }

  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/LimitedStream"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState (some 1))
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun emitted => emitted.append frames

  let firstHeadersResult ← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit
  expectStatusOk firstHeadersResult
  let firstDataResult ← Http2.Connection.processFrameSharedWith
    registry stateMutex requestDataFrame emit
  expectStatusOk firstDataResult
  waitUntil "detached stream handler did not start for max-concurrent test" 100 do
    match ← producerRef.get with
    | some _ => pure true
    | none => pure false

  let secondHeadersFrame : Http2.Frame := {
    requestHeadersFrame with header := { requestHeadersFrame.header with streamId := 3 }
  }
  let secondResult ← Http2.Connection.processFrameSharedWith registry stateMutex secondHeadersFrame emit
  let secondStatus ← expectStatusError secondResult
  expectEq secondStatus.code Code.internal
    "detached streaming response should occupy a max-concurrent stream slot"

  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected max-concurrent producer")
  runGrpcM producer.close
  waitUntil "detached stream did not finish for max-concurrent test" 100 do
    let state ← stateMutex.atomically get
    pure state.activeDispatches.isEmpty

  let thirdResult ← Http2.Connection.processFrameSharedWith registry stateMutex secondHeadersFrame emit
  expectStatusOk thirdResult

def testStreamNativeContentLengthEnforced : IO Unit := do
  let method : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "LengthLimitedCollect"
  }
  let registry := Registry.empty.registerClientStreamingStream method fun request => do
    let messages ← request.messages.collect
    pure {
      metadata := Metadata.empty,
      data := messages.foldl (fun out message => out.append message) ByteArray.empty,
      status := Status.ok
    }

  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let headers :=
    (requestHeadersForPath "/lean.example.proto.NoteService/LengthLimitedCollect")
      |>.insert "content-length" (toString (requestBody.size - 1))
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} headers)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }

  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  expectStatusOk (← Http2.Connection.processFrameSharedWith registry stateMutex requestHeadersFrame emit)
  expectStatusOk (← Http2.Connection.processFrameSharedWith registry stateMutex requestDataFrame emit)
  waitUntil "stream-native request DATA exceeding content-length did not emit trailers" 100 do
    let emitted ← emittedRef.get
    pure <| emitted.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let emitted ← emittedRef.get
  let trailerFrame ← match emitted.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream) with
    | some frame => pure frame
    | none => throw (IO.userError "expected stream-native content-length error trailers")
  expect (Http2.FrameFlag.has trailerFrame.header.flags Http2.FrameFlag.endStream)
    "stream-native content-length error trailers should end the stream"
  let trailers ← decodeLastServerHeaderBlock emitted
    "expected stream-native content-length error trailer block"
  expectEq (Metadata.get? trailers.headers "grpc-status") (some "3")
    "stream-native request DATA exceeding content-length should return INVALID_ARGUMENT"
  discard <| Http2.Connection.cancelActiveShared stateMutex

  let shortHeaders :=
    (requestHeadersForPath "/lean.example.proto.NoteService/LengthLimitedCollect")
      |>.insert "content-length" (toString (requestBody.size + 1))
  let shortEncodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} shortHeaders)
  let shortRequestHeadersFrame : Http2.Frame := {
    requestHeadersFrame with
    header := { requestHeadersFrame.header with length := shortEncodedHeaders.1.size },
    payload := shortEncodedHeaders.1
  }
  let shortStateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  let shortEmittedRef ← IO.mkRef #[]
  let shortEmit (frames : Array Http2.Frame) : IO Unit := do
    shortEmittedRef.modify fun emitted => emitted.append frames
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry shortStateMutex shortRequestHeadersFrame shortEmit)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry shortStateMutex requestDataFrame shortEmit)
  waitUntil "stream-native request ending before content-length did not emit trailers" 100 do
    let emitted ← shortEmittedRef.get
    pure <| emitted.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let shortEmitted ← shortEmittedRef.get
  let shortTrailerFrame ← match shortEmitted.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream) with
    | some frame => pure frame
    | none => throw (IO.userError "expected short stream-native content-length error trailers")
  expect (Http2.FrameFlag.has shortTrailerFrame.header.flags Http2.FrameFlag.endStream)
    "short stream-native content-length error trailers should end the stream"
  let shortTrailers ← decodeLastServerHeaderBlock shortEmitted
    "expected short stream-native content-length error trailer block"
  expectEq (Metadata.get? shortTrailers.headers "grpc-status") (some "3")
    "stream-native request ending before content-length should return INVALID_ARGUMENT"
  discard <| Http2.Connection.cancelActiveShared shortStateMutex

  let earlyCalledRef ← IO.mkRef false
  let earlyRegistry := Registry.empty.registerClientStreamingStream method fun request => do
    earlyCalledRef.set true
    let messages ← request.messages.collect
    pure {
      metadata := Metadata.empty,
      data := messages.foldl (fun out message => out.append message) ByteArray.empty,
      status := Status.ok
    }
  let earlyHeaders :=
    (requestHeadersForPath "/lean.example.proto.NoteService/LengthLimitedCollect")
      |>.insert "content-length" "1"
  let earlyEncodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} earlyHeaders)
  let earlyRequestHeadersFrame : Http2.Frame := {
    header := {
      length := earlyEncodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := UInt8.ofNat
        (Http2.FrameFlag.endHeaders.toNat + Http2.FrameFlag.endStream.toNat),
      streamId := 1
    },
    payload := earlyEncodedHeaders.1
  }
  let earlyEmittedRef ← IO.mkRef #[]
  let earlyEmit (frames : Array Http2.Frame) : IO Unit := do
    earlyEmittedRef.modify fun emitted => emitted.append frames
  let earlyStateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    earlyRegistry earlyStateMutex earlyRequestHeadersFrame earlyEmit)
  waitUntil "headers-only content-length mismatch did not emit gRPC trailers" 100 do
    pure (!(← earlyEmittedRef.get).isEmpty)
  expect (!(← earlyCalledRef.get))
    "headers-only content-length mismatch should reject before invoking the handler"
  let earlyEmitted ← earlyEmittedRef.get
  let earlyTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} earlyEmitted[0]!.payload)
  expectEq (Metadata.get? earlyTrailers.headers "grpc-status") (some "3")
    "headers-only stream-native content-length mismatch should return INVALID_ARGUMENT"
  discard <| Http2.Connection.cancelActiveShared earlyStateMutex

def testStreamNativePaddedDataUsesUnpaddedContentLength : IO Unit := do
  let method : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "PaddedCollect"
  }
  let registry := Registry.empty.registerClientStreamingStream method fun request => do
    let messages ← request.messages.collect
    pure {
      metadata := Metadata.empty,
      data := messages.foldl (fun out message => out.append message) ByteArray.empty,
      status := Status.ok
    }

  let requestMessage : Message := { data := bytes [3, 4, 5] }
  let requestBody ← expectStatusOk requestMessage.encode
  let headers :=
    (requestHeadersForPath "/lean.example.proto.NoteService/PaddedCollect")
      |>.insert "content-length" (toString requestBody.size)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} headers)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }

  let padding := bytes [0, 0, 0, 0]
  let paddedPayload := (bytes [padding.size])
    |>.append requestBody
    |>.append padding
  let requestDataFrame : Http2.Frame := {
    header := {
      length := paddedPayload.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endStream, Http2.FrameFlag.padded],
      streamId := 1
    },
    payload := paddedPayload
  }

  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit)
  let emittedCount := (← emittedRef.get).size
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestDataFrame emit)
  waitUntil "padded stream-native request did not emit response trailers" 100 do
    let emitted ← emittedRef.get
    pure <| emitted.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream

  let emitted ← emittedRef.get
  let emittedAfterData := emitted.extract emittedCount emitted.size
  expectEq emittedAfterData[0]!.header.frameType Http2.FrameType.windowUpdate
    "padded stream-native DATA should replenish the connection window"
  expectEq emittedAfterData[1]!.header.frameType Http2.FrameType.windowUpdate
    "padded stream-native DATA should replenish the stream window"
  expectEq (← expectStatusOk (Http2.WindowUpdate.decode emittedAfterData[0]!)) paddedPayload.size
    "connection WINDOW_UPDATE should count raw padded DATA bytes"
  expectEq (← expectStatusOk (Http2.WindowUpdate.decode emittedAfterData[1]!))
    (paddedPayload.size - requestBody.size)
    "stream WINDOW_UPDATE at arrival should credit only padding bytes; payload credit is granted as the handler consumes messages"

  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads emitted))
  expectEq responseMessages.size 1
    "padded stream-native request should produce one response message"
  expectEq responseMessages[0]!.data requestMessage.data
    "padded stream-native request should decode unpadded gRPC message bytes"
  let finalTrailers ← match emitted.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream) with
    | some frame => pure frame
    | none => throw (IO.userError "expected padded stream-native response trailers")
  expect (Http2.FrameFlag.has finalTrailers.header.flags Http2.FrameFlag.endStream)
    "padded stream-native response trailers should end the stream"
  let trailers ← decodeLastServerHeaderBlock emitted
    "expected padded stream-native response trailer block"
  expectEq (Metadata.get? trailers.headers "grpc-status") (some "0")
    "padded stream-native request should complete with OK trailers"
  discard <| Http2.Connection.cancelActiveShared stateMutex

def testEarlyInvalidHeadersIgnoreRequestBodyStateMachine : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let calledRef ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    calledRef.set true
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let invalidHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} invalidHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let headersResult ← Http2.Connection.processFrame registry
    Http2.Connection.initialState requestHeadersFrame
  let (stateAfterHeaders, emittedAfterHeaders) ← expectStatusOk headersResult
  expect (!(← calledRef.get))
    "non-shared invalid request headers should reject before invoking unary handler"
  expect (stateAfterHeaders.ignoredInboundStreams.contains 1)
    "non-shared early rejected request stream should ignore the remaining request body"
  expect stateAfterHeaders.streams.isEmpty
    "non-shared early rejected request stream should not remain in the pending stream table"
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {}
    emittedAfterHeaders[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "3")
    "non-shared missing te header should return INVALID_ARGUMENT"
  expect (Http2.FrameFlag.has emittedAfterHeaders[0]!.header.flags Http2.FrameFlag.endStream)
    "non-shared early invalid header response should end the server side of the stream"

  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let dataResult ← Http2.Connection.processFrame registry stateAfterHeaders requestDataFrame
  let (stateAfterData, dataEmitted) ← expectStatusOk dataResult
  expect (!(← calledRef.get))
    "non-shared ignored request body DATA should not invoke the unary handler"
  expect (!stateAfterData.ignoredInboundStreams.contains 1)
    "non-shared ignored request stream should clear when the client sends END_STREAM"
  expect stateAfterData.streams.isEmpty
    "non-shared ignored request body should leave no pending stream state"
  expectEq dataEmitted.size 2
    "non-shared ignored request DATA should still replenish connection and stream windows"
  expect (dataEmitted.all (fun frame => frame.header.frameType == Http2.FrameType.windowUpdate))
    "non-shared ignored request DATA should only emit WINDOW_UPDATE frames"

def testEarlyInvalidHeadersIgnoreRequestBody : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let calledRef ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    calledRef.set true
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let invalidHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} invalidHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit)
  waitUntil "invalid request headers did not emit early response" 100 do
    pure (!(← emittedRef.get).isEmpty)
  expect (!(← calledRef.get))
    "invalid request headers should reject before invoking unary handler"
  let stateAfterHeaders ← stateMutex.atomically get
  expect (stateAfterHeaders.ignoredInboundStreams.contains 1)
    "early rejected request stream should ignore the remaining request body"
  expect stateAfterHeaders.streams.isEmpty
    "early rejected request stream should not remain in the pending stream table"
  expect (!Http2.Connection.isDrainedAfterOutboundGoAway
      { stateAfterHeaders with outboundGoAwayLastStreamId := some 1 })
    "early rejected request streams should keep graceful shutdown waiting for END_STREAM"
  let emittedAfterHeaders ← emittedRef.get
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {}
    emittedAfterHeaders[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "3")
    "missing te header should return INVALID_ARGUMENT"
  expect (Http2.FrameFlag.has emittedAfterHeaders[0]!.header.flags Http2.FrameFlag.endStream)
    "early invalid header response should end the server side of the stream"

  let requestBody ← expectStatusOk (Message.encode { data := bytes [1, 2, 3] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let emittedCount := emittedAfterHeaders.size
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestDataFrame emit)
  expect (!(← calledRef.get))
    "ignored request body DATA should not invoke the unary handler"
  let stateAfterData ← stateMutex.atomically get
  expect (!stateAfterData.ignoredInboundStreams.contains 1)
    "ignored request stream should clear when the client sends END_STREAM"
  expect stateAfterData.streams.isEmpty
    "ignored request body should leave no pending stream state"
  expect (Http2.Connection.isDrainedAfterOutboundGoAway
      { stateAfterData with outboundGoAwayLastStreamId := some 1 })
    "ignored request stream should allow graceful shutdown to finish after END_STREAM"
  let emittedAfterData ← emittedRef.get
  let dataEmitted := emittedAfterData.extract emittedCount emittedAfterData.size
  expectEq dataEmitted.size 2
    "ignored non-empty request DATA should still replenish connection and stream windows"
  expect (dataEmitted.all (fun frame => frame.header.frameType == Http2.FrameType.windowUpdate))
    "ignored request DATA should only emit WINDOW_UPDATE frames"

def testEarlyHttpStatusOnlyRejectionIgnoreRequestBody : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let calledRef ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    calledRef.set true
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let nonGrpcHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/json"
    |>.insert "te" "trailers"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} nonGrpcHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit)
  waitUntil "non-gRPC request headers did not emit early HTTP status response" 100 do
    pure (!(← emittedRef.get).isEmpty)
  expect (!(← calledRef.get))
    "non-gRPC request headers should reject before invoking unary handler"
  let stateAfterHeaders ← stateMutex.atomically get
  expect (stateAfterHeaders.ignoredInboundStreams.contains 1)
    "HTTP status-only early rejection should ignore the remaining request body"
  let emittedAfterHeaders ← emittedRef.get
  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {}
    emittedAfterHeaders[0]!.payload)
  expectEq (Metadata.get? responseHeaders.headers ":status") (some "415")
    "non-gRPC request headers should return HTTP 415"
  expectEq (Metadata.get? responseHeaders.headers "grpc-status") none
    "non-GRPC early response should not include grpc-status"
  expectEq (Metadata.get? responseHeaders.headers "content-type") none
    "non-GRPC early response should not advertise a gRPC content-type"

  let requestBody ← expectStatusOk (Message.encode { data := bytes [4, 5, 6] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let emittedCount := emittedAfterHeaders.size
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestDataFrame emit)
  expect (!(← calledRef.get))
    "ignored non-gRPC request DATA should not invoke the unary handler"
  let stateAfterData ← stateMutex.atomically get
  expect (!stateAfterData.ignoredInboundStreams.contains 1)
    "ignored non-GRPC request stream should clear when the client sends END_STREAM"
  let emittedAfterData ← emittedRef.get
  let dataEmitted := emittedAfterData.extract emittedCount emittedAfterData.size
  expectEq dataEmitted.size 2
    "ignored non-GRPC request DATA should still replenish connection and stream windows"
  expect (dataEmitted.all (fun frame => frame.header.frameType == Http2.FrameType.windowUpdate))
    "ignored non-GRPC request DATA should only emit WINDOW_UPDATE frames"

def testEarlyUnknownMethodIgnoreRequestBody : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let calledRef ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    calledRef.set true
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let unknownHeaders := requestHeadersForPath "/lean.example.proto.NoteService/Missing"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} unknownHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit)
  waitUntil "unknown method headers did not emit early gRPC status" 100 do
    pure (!(← emittedRef.get).isEmpty)
  expect (!(← calledRef.get))
    "unknown method headers should reject before invoking any registered handler"
  let stateAfterHeaders ← stateMutex.atomically get
  expect (stateAfterHeaders.ignoredInboundStreams.contains 1)
    "early unknown method rejection should ignore the remaining request body"
  let emittedAfterHeaders ← emittedRef.get
  let trailersOnly ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {}
    emittedAfterHeaders[0]!.payload)
  expectEq (Metadata.get? trailersOnly.headers ":status") (some "200")
    "unknown method early response should use gRPC HTTP status"
  expectEq (Metadata.get? trailersOnly.headers "content-type") (some "application/grpc")
    "unknown method early response should advertise gRPC content-type"
  expectEq (Metadata.get? trailersOnly.headers "grpc-status") (some "12")
    "unknown method early response should return UNIMPLEMENTED"
  expect (Http2.FrameFlag.has emittedAfterHeaders[0]!.header.flags Http2.FrameFlag.endStream)
    "unknown method early response should end the server side of the stream"

  let requestBody ← expectStatusOk (Message.encode { data := bytes [7, 8, 9] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let emittedCount := emittedAfterHeaders.size
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestDataFrame emit)
  expect (!(← calledRef.get))
    "ignored unknown-method request DATA should not invoke any registered handler"
  let stateAfterData ← stateMutex.atomically get
  expect (!stateAfterData.ignoredInboundStreams.contains 1)
    "ignored unknown-method request stream should clear when the client sends END_STREAM"
  let emittedAfterData ← emittedRef.get
  let dataEmitted := emittedAfterData.extract emittedCount emittedAfterData.size
  expectEq dataEmitted.size 2
    "ignored unknown-method request DATA should still replenish connection and stream windows"
  expect (dataEmitted.all (fun frame => frame.header.frameType == Http2.FrameType.windowUpdate))
    "ignored unknown-method request DATA should only emit WINDOW_UPDATE frames"

def testEarlyRejectedStreamResetClearsIgnoredBody : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let calledRef ← IO.mkRef false
  let registry := Registry.empty.registerUnary method fun request => do
    calledRef.set true
    pure {
      metadata := Metadata.empty,
      data := request.data,
      status := Status.ok
    }

  let invalidHeaders := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} invalidHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit)
  waitUntil "early rejected stream did not emit response before RST_STREAM" 100 do
    pure (!(← emittedRef.get).isEmpty)
  expect (!(← calledRef.get))
    "early rejected stream should not invoke the unary handler before reset"
  let stateAfterHeaders ← stateMutex.atomically get
  expect (stateAfterHeaders.ignoredInboundStreams.contains 1)
    "early rejected stream should ignore request body before reset"
  expect (!Http2.Connection.isDrainedAfterOutboundGoAway
      { stateAfterHeaders with outboundGoAwayLastStreamId := some 1 })
    "ignored request body should keep graceful shutdown waiting before reset"

  let reset ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  expectStatusOk (← Http2.Connection.processFrameSharedWith registry stateMutex reset emit)
  let stateAfterReset ← stateMutex.atomically get
  expect (!stateAfterReset.ignoredInboundStreams.contains 1)
    "RST_STREAM should clear ignored request body state"
  expect stateAfterReset.streams.isEmpty
    "RST_STREAM should leave no pending stream state for early rejected requests"
  expect (Http2.Connection.isDrainedAfterOutboundGoAway
      { stateAfterReset with outboundGoAwayLastStreamId := some 1 })
    "RST_STREAM should allow graceful shutdown to finish for early rejected requests"
  let emittedAfterReset ← emittedRef.get
  expectEq emittedAfterReset.size 1
    "RST_STREAM for an early rejected stream should not emit additional response frames"

def testStreamNativeMalformedDataReturnsGrpcStatus : IO Unit := do
  let method : MethodName := {
    service := "lean.example.proto.NoteService",
    method := "RejectCompressedCollect"
  }
  let registry := Registry.empty.registerClientStreamingStream method fun request => do
    let messages ← request.messages.collect
    pure {
      metadata := Metadata.empty,
      data := messages.foldl (fun out message => out.append message) ByteArray.empty,
      status := Status.ok
    }

  let headers := requestHeadersForPath "/lean.example.proto.NoteService/RejectCompressedCollect"
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} headers)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let compressedBody ← expectStatusOk (Message.encode {
    compressed := CompressionFlag.compressed,
    data := bytes [1, 2, 3]
  })
  let compressedDataFrame : Http2.Frame := {
    header := {
      length := compressedBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := compressedBody
  }
  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  let stateMutex ← Std.Mutex.new (Http2.Connection.initialState)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex requestHeadersFrame emit)
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex compressedDataFrame emit)
  waitUntil "malformed request DATA did not emit gRPC trailers" 100 do
    let emitted ← emittedRef.get
    pure <| emitted.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let emitted ← emittedRef.get
  let responseFrame ← match emitted.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream) with
    | some frame => pure frame
    | none => throw (IO.userError "expected malformed request gRPC trailer frame")
  expect (Http2.FrameFlag.has responseFrame.header.flags Http2.FrameFlag.endStream)
    "malformed request gRPC trailer frame should end the stream"
  let trailers ← decodeLastServerHeaderBlock emitted
    "expected malformed request gRPC trailer block"
  expectEq (Metadata.get? trailers.headers "grpc-status") (some "13")
    "compressed-flag stream-native request DATA without grpc-encoding should return INTERNAL"
  waitUntil "malformed stream-native request DATA did not finish the active dispatch" 100 do
    let state ← stateMutex.atomically get
    pure state.activeDispatches.isEmpty
  let state ← stateMutex.atomically get
  expect state.activeDispatches.isEmpty
    "malformed stream-native request DATA should finish the active dispatch"
  expect state.activeRequestStreams.isEmpty
    "malformed stream-native request DATA should clear the active request stream"

def testPriorityFrameIgnored : IO Unit := do
  let priorityFrame : Http2.Frame := {
    header := {
      length := 5,
      frameType := Http2.FrameType.priority,
      flags := 0,
      streamId := 1
    },
    payload := bytes [0, 0, 0, 0, 15]
  }
  let result ← Http2.Connection.processFrame Registry.empty readyConnectionState priorityFrame
  let (_state, emitted) ← expectStatusOk result
  expectEq emitted.size 0 "PRIORITY frame should be ignored without emitting frames"

def testUnknownFrameIgnored : IO Unit := do
  let unknownFrame : Http2.Frame := {
    header := {
      length := 3,
      frameType := Http2.FrameType.unknown 0x0b,
      flags := 0,
      streamId := 0
    },
    payload := bytes [1, 2, 3]
  }
  let result ← Http2.Connection.processFrame Registry.empty readyConnectionState unknownFrame
  let (state, emitted) ← expectStatusOk result
  expectEq emitted.size 0 "unknown HTTP/2 frames should be ignored without emitting frames"
  expectEq state.lastClientStreamId readyConnectionState.lastClientStreamId
    "unknown HTTP/2 frames should not mutate connection stream state"

  let emittedRef ← IO.mkRef #[]
  let emit (frames : Array Http2.Frame) : IO Unit := do
    emittedRef.modify fun emitted => emitted.append frames
  let stateMutex ← Std.Mutex.new readyConnectionState
  expectStatusOk (← Http2.Connection.processFrameSharedWith
    Registry.empty stateMutex unknownFrame emit)
  expect (← emittedRef.get).isEmpty
    "shared connection should ignore unknown HTTP/2 frames without emitting"

  let incompleteHeaders : Http2.Frame := {
    header := {
      length := 0,
      frameType := Http2.FrameType.headers,
      flags := 0,
      streamId := 1
    },
    payload := ByteArray.empty
  }
  let firstResult ← Http2.Connection.processFrame Registry.empty readyConnectionState incompleteHeaders
  let (pendingState, emittedFirst) ← expectStatusOk firstResult
  expectEq emittedFirst.size 0 "incomplete HEADERS should wait for CONTINUATION"
  let interruptedResult ← Http2.Connection.processFrame Registry.empty pendingState unknownFrame
  let interruptedStatus ← expectStatusError interruptedResult
  expectEq interruptedStatus.code Code.internal
    "unknown HTTP/2 frames should not interrupt a pending header block"

def testPeerSettingsAffectOutbound : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let peerWindow := 20000
  let peerMaxFrameSize := 20000
  let largeData := repeatByte 45000 81
  let registry := Registry.empty.registerUnary method fun _request => do
    pure {
      metadata := Metadata.empty,
      data := largeData,
      status := Status.ok
    }

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[
    { id := Http2.SettingId.headerTableSize, value := 0 },
    { id := Http2.SettingId.initialWindowSize, value := peerWindow },
    { id := Http2.SettingId.maxFrameSize, value := peerMaxFrameSize }
  ])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestMessage : Message := { data := bytes [1] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  let firstResult ← Http2.Connection.processBytes registry {} (
    Http2.connectionPreface
      |>.append clientSettingsWire
      |>.append requestHeadersWire
      |>.append requestDataWire
  )
  let (state1, emitted1) ← expectStatusOk firstResult
  expectEq state1.outboundInitialStreamWindow peerWindow
    "client SETTINGS_INITIAL_WINDOW_SIZE should update new outbound streams"
  expectEq state1.outboundMaxFramePayloadLength peerMaxFrameSize
    "client SETTINGS_MAX_FRAME_SIZE should update outbound DATA splitting"
  expectEq state1.outboundHpack.maxSize 0
    "client SETTINGS_HEADER_TABLE_SIZE should cap response HPACK table"
  expectEq state1.outboundHpack.maxAllowedSize 0
    "client SETTINGS_HEADER_TABLE_SIZE should update response HPACK dynamic table maximum"
  expect (!state1.pendingOutbound.isEmpty) "peer stream window should leave remaining response frames pending"

  let firstDataFrames := emitted1.filter (fun frame => frame.header.frameType == Http2.FrameType.data)
  expectEq firstDataFrames.size 1 "first outbound flush should emit one peer-sized DATA frame"
  expectEq firstDataFrames[0]!.payload.size peerWindow
    "first outbound DATA flush should stop at peer initial stream window"

  let streamUpdate ← expectStatusOk (Http2.WindowUpdate.frame 1 (largeData.size + 5 - peerWindow))
  let streamUpdateWire ← expectStatusOk (Http2.Frame.encode streamUpdate)
  let secondResult ← Http2.Connection.processBytes registry state1 streamUpdateWire
  let (state2, emitted2) ← expectStatusOk secondResult
  expect state2.pendingOutbound.isEmpty "stream WINDOW_UPDATE should flush response frames pending on peer window"

  let remainingDataFrames := emitted2.filter (fun frame => frame.header.frameType == Http2.FrameType.data)
  expectEq remainingDataFrames.size 2 "remaining response should preserve peer max DATA frame splitting"
  for frame in remainingDataFrames do
    expect (frame.payload.size <= peerMaxFrameSize)
      "flushed DATA frame should respect peer SETTINGS_MAX_FRAME_SIZE"

  let payload := (dataPayloads emitted1).append (dataPayloads emitted2)
  let responseMessages ← expectStatusOk (Message.decodeAll payload)
  expectEq responseMessages.size 1 "peer-settings flow-controlled DATA should decode as one gRPC message"
  expectEq responseMessages[0]!.data largeData "peer-settings flow control should preserve payload"
  expect (emitted2.any (fun frame =>
    frame.header.frameType == Http2.FrameType.headers
      && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream))
    "final peer-settings flush should include response trailers"

def testHttp2Connection : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "connection",
      data := request.data,
      status := Status.ok
    }

  let state0 : Http2.Connection.State := {}
  let prefacePrefix := Http2.connectionPreface.extract 0 8
  let prefaceSuffix := Http2.connectionPreface.extract 8 Http2.connectionPreface.size
  let result1 ← Http2.Connection.processBytes registry state0 prefacePrefix
  let (state1, emitted1) ← expectStatusOk result1
  expectEq emitted1.size 0 "partial preface should not emit frames"
  expect (!state1.prefaceReceived) "partial preface should not mark preface complete"

  let prematurePing ← expectStatusOk (Http2.Ping.frame (bytes [1, 2, 3, 4, 5, 6, 7, 8]))
  let prematurePingWire ← expectStatusOk (Http2.Frame.encode prematurePing)
  let prematurePingResult ← Http2.Connection.processBytes registry state1
    (prefaceSuffix.append prematurePingWire)
  let prematurePingStatus ← expectStatusError prematurePingResult
  expectEq prematurePingStatus.code Code.internal
    "client preface followed by non-SETTINGS should reject"

  let clientSettingsAck ← expectStatusOk (Http2.Settings.frame #[] (ack := true))
  let clientSettingsAckWire ← expectStatusOk (Http2.Frame.encode clientSettingsAck)
  let settingsAckResult ← Http2.Connection.processBytes registry state1
    (prefaceSuffix.append clientSettingsAckWire)
  let settingsAckStatus ← expectStatusError settingsAckResult
  expectEq settingsAckStatus.code Code.internal
    "client preface followed by SETTINGS ACK should reject"

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let result2 ← Http2.Connection.processBytes registry state1 (prefaceSuffix.append clientSettingsWire)
  let (state2, emitted2) ← expectStatusOk result2
  expect state2.prefaceReceived "complete preface should be recorded"
  expect state2.clientSettingsReceived "client SETTINGS should be recorded"
  expectEq emitted2.size 1 "client SETTINGS should emit one ACK"
  expect (Http2.Settings.isAck emitted2[0]!) "emitted frame should be SETTINGS ACK"
  let clientSettingsAckWithUnknownFlags : Http2.Frame := {
    clientSettingsAck with
    header := { clientSettingsAck.header with flags := UInt8.ofNat 0x3 }
  }
  let ackWithUnknownWire ← expectStatusOk (Http2.Frame.encode clientSettingsAckWithUnknownFlags)
  let ackWithUnknownResult ← Http2.Connection.processBytes registry state2 ackWithUnknownWire
  let (_stateAfterAckWithUnknown, emittedAckWithUnknown) ← expectStatusOk ackWithUnknownResult
  expectEq emittedAckWithUnknown.size 0
    "SETTINGS ACK with unknown flags should not be treated as a new SETTINGS frame"

  let pingPayload := bytes [8, 7, 6, 5, 4, 3, 2, 1]
  let pingFrame ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode pingFrame)
  let resultPing ← Http2.Connection.processBytes registry state2 pingWire
  let (statePing, emittedPing) ← expectStatusOk resultPing
  expectEq emittedPing.size 1 "connection should answer PING with one ACK"
  expect (Http2.Ping.isAck emittedPing[0]!) "connection PING response should be ACK"
  expectEq (← expectStatusOk (Http2.Ping.decode emittedPing[0]!)) pingPayload "connection PING ACK should echo payload"

  let teBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} #[Header.of "te" "trailers"])
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
  let splitHeaderAt := 12
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := splitHeaderAt,
      frameType := Http2.FrameType.headers,
      flags := 0,
      streamId := 1
    },
    payload := requestHeaderBlock.extract 0 splitHeaderAt
  }
  let requestContinuationFrame : Http2.Frame := {
    header := {
      length := requestHeaderBlock.size - splitHeaderAt,
      frameType := Http2.FrameType.continuation,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := requestHeaderBlock.extract splitHeaderAt requestHeaderBlock.size
  }
  let requestMessage : Message := { data := bytes [1, 3, 3, 7] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestContinuationWire ← expectStatusOk (Http2.Frame.encode requestContinuationFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  let result3 ← Http2.Connection.processBytes registry statePing (
    requestHeadersWire
      |>.append requestContinuationWire
      |>.append requestDataWire
  )
  let (state3, emitted3) ← expectStatusOk result3
  expectEq state3.streams.size 0 "completed unary stream should be removed"
  expect state3.outboundStreamWindows.isEmpty
    "completed unary stream should clear outbound stream window state"
  expectEq emitted3.size 5 "connection should emit WINDOW_UPDATEs plus unary response frames"
  expectEq emitted3[0]!.header.frameType Http2.FrameType.windowUpdate "connection should update connection window"
  expectEq emitted3[0]!.header.streamId 0 "connection WINDOW_UPDATE should use stream 0"
  expectEq (← expectStatusOk (Http2.WindowUpdate.decode emitted3[0]!)) requestBody.size "connection WINDOW_UPDATE should match DATA bytes"
  expectEq emitted3[1]!.header.frameType Http2.FrameType.windowUpdate "connection should update request stream window"
  expectEq emitted3[1]!.header.streamId 1 "stream WINDOW_UPDATE should use request stream id"
  expectEq (← expectStatusOk (Http2.WindowUpdate.decode emitted3[1]!)) requestBody.size "stream WINDOW_UPDATE should match DATA bytes"
  expectEq emitted3[2]!.header.frameType Http2.FrameType.headers "connection response should start with HEADERS"
  expectEq emitted3[3]!.header.frameType Http2.FrameType.data "connection response should include DATA"
  expectEq emitted3[4]!.header.frameType Http2.FrameType.headers "connection response should include trailers"
  let responseMessages ← expectStatusOk (Message.decodeAll emitted3[3]!.payload)
  expectEq responseMessages.size 1 "connection response DATA should contain one message"
  expectEq responseMessages[0]!.data requestMessage.data "connection response message should echo request payload"

  let unknownHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Missing"))
  let unknownHeadersFrame : Http2.Frame := {
    header := {
      length := unknownHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 3
    },
    payload := unknownHeaders.1
  }
  let unknownHeadersWire ← expectStatusOk (Http2.Frame.encode unknownHeadersFrame)
  let unknownResult ← Http2.Connection.processBytes registry state3 unknownHeadersWire
  let (stateUnknown, emittedUnknown) ← expectStatusOk unknownResult
  expectEq stateUnknown.streams.size 0 "trailers-only failure stream should be removed"
  expectEq emittedUnknown.size 1 "connection trailers-only failure should emit one frame"
  expectEq emittedUnknown[0]!.header.frameType Http2.FrameType.headers
    "connection trailers-only failure should use HEADERS"
  expect (Http2.FrameFlag.has emittedUnknown[0]!.header.flags Http2.FrameFlag.endStream)
    "connection trailers-only failure should end stream"
  let unknownTrailers ← decodeLastServerHeaderBlock (emitted3.append emittedUnknown)
    "expected connection trailers-only failure header block"
  expectEq (Metadata.get? unknownTrailers.headers "grpc-status") (some "12")
    "connection unknown method should map to UNIMPLEMENTED trailers-only status"

def testHttp2H2CServer : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "h2c-server",
      data := request.data,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let teBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} #[Header.of "te" "trailers"])
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
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := requestHeaderBlock.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := requestHeaderBlock
  }
  let requestMessage : Message := { data := bytes [2, 4, 6, 8] }
  let requestBody ← expectStatusOk requestMessage.encode
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  let requestWire := Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire
  (client.send requestWire).block

  let emitted ← readHttp2FramesFromSocket client {} #[] 7
  expectEq emitted.size 7 "h2c server should emit preface, SETTINGS ACK, WINDOW_UPDATEs, and unary response frames"
  expectEq emitted[0]!.header.frameType Http2.FrameType.settings "h2c server should send SETTINGS preface first"
  expect (!Http2.Settings.isAck emitted[0]!) "h2c server SETTINGS preface should not be ACK"
  expect (Http2.Settings.isAck emitted[1]!) "h2c server should ACK client SETTINGS"
  expectEq emitted[2]!.header.frameType Http2.FrameType.windowUpdate "h2c server should update connection window"
  expectEq emitted[2]!.header.streamId 0 "h2c connection WINDOW_UPDATE should use stream 0"
  expectEq emitted[3]!.header.frameType Http2.FrameType.windowUpdate "h2c server should update stream window"
  expectEq emitted[3]!.header.streamId 1 "h2c stream WINDOW_UPDATE should use request stream id"
  expectEq emitted[4]!.header.frameType Http2.FrameType.headers "h2c server response should start with HEADERS"
  expectEq emitted[5]!.header.frameType Http2.FrameType.data "h2c server response should include DATA"
  expectEq emitted[6]!.header.frameType Http2.FrameType.headers "h2c server response should end with trailers"

  let responseHeaders ← expectStatusOk (Http2.Hpack.decodeHeaderBlock {} emitted[4]!.payload)
  expectEq (Metadata.get? responseHeaders.headers "handled-by") (some "h2c-server") "h2c server response metadata should be encoded"
  let responseMessages ← expectStatusOk (Message.decodeAll emitted[5]!.payload)
  expectEq responseMessages.size 1 "h2c server response DATA should contain one message"
  expectEq responseMessages[0]!.data requestMessage.data "h2c server response should echo request payload"
  let responseTrailers ← expectStatusOk (Http2.Hpack.decodeHeaderBlock responseHeaders.state emitted[6]!.payload)
  expectEq (Metadata.get? responseTrailers.headers "grpc-status") (some "0") "h2c server trailers should include OK grpc-status"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2ServeManagedLifecycle : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "Echo" }
  let registry := Registry.empty.registerUnary method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "managed-h2c-server",
      data := request.data,
      status := Status.ok
    }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  expect (!(← Grpc.Server.isShutdown server)) "managed h2c server should start active"

  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Echo"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestData := bytes [5, 8, 13]
  let requestBody ← expectStatusOk (Message.encode { data := requestData })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  let hasResponseTrailers (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let stateAfterResponse ← readHttp2FramesUntilWithTimeout client {} hasResponseTrailers 500
    "managed h2c server did not complete unary response"
  expectEq stateAfterResponse.frames[0]!.header.frameType Http2.FrameType.settings
    "managed h2c server preface should be SETTINGS"
  expect (!Http2.Settings.isAck stateAfterResponse.frames[0]!)
    "managed h2c server preface should not be SETTINGS ACK"
  expect (stateAfterResponse.frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.settings && Http2.Settings.isAck frame)
    "managed h2c server should ACK client SETTINGS"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stateAfterResponse.frames))
  expect (responseMessages.any fun message => message.data == requestData)
    "managed h2c server should echo the request payload"

  Grpc.Server.shutdown server
  expect (← Grpc.Server.isShutdown server) "managed h2c server should report shutdown"
  let hasGoAway (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame => frame.header.frameType == Http2.FrameType.goAway
  let stateAfterGoAway ← readHttp2FramesUntilWithTimeout client stateAfterResponse hasGoAway 500
    "managed h2c server shutdown did not emit GOAWAY"
  let goAway ← match stateAfterGoAway.frames.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.goAway) with
    | some frame => pure frame
    | none => throw (IO.userError "expected managed h2c server GOAWAY")
  let decodedGoAway ← expectStatusOk (Http2.GoAway.decode goAway)
  expectEq decodedGoAway.lastStreamId 1
    "managed h2c server GOAWAY should report the last accepted stream"
  expectEq decodedGoAway.errorCode Http2.ErrorCode.noError
    "managed h2c server GOAWAY should be graceful"

  let postGoAwayHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/Echo"))
  let postGoAwayHeadersFrame : Http2.Frame := {
    header := {
      length := postGoAwayHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.combine #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.endStream],
      streamId := 3
    },
    payload := postGoAwayHeaders.1
  }
  let postGoAwayHeadersWire ← expectStatusOk (Http2.Frame.encode postGoAwayHeadersFrame)
  (client.send postGoAwayHeadersWire).block
  let hasRefusedStream (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.rstStream && frame.header.streamId == 3
  let stateAfterRefused ← readHttp2FramesUntilWithTimeout client stateAfterGoAway hasRefusedStream 500
    "managed h2c server did not refuse post-GOAWAY stream"
  let refused ← match stateAfterRefused.frames.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.rstStream && frame.header.streamId == 3) with
    | some frame => pure frame
    | none => throw (IO.userError "expected post-GOAWAY RST_STREAM")
  expectEq (← expectStatusOk (Http2.RstStream.decode refused)) Http2.ErrorCode.refusedStream
    "managed h2c server should refuse post-GOAWAY streams"
  expect (!stateAfterRefused.frames.any fun frame =>
      frame.header.streamId == 3 && frame.header.frameType != Http2.FrameType.rstStream)
    "managed h2c server should not process post-GOAWAY stream as an RPC"

  let stopped ← IO.mkRef false
  let waitTask ← IO.asTask do
    Grpc.Server.wait server
    stopped.set true
  waitUntil "managed h2c server wait did not finish after active RPCs drained" 500 stopped.get
  awaitIoTask waitTask
  let eofTask ← IO.asTask do
    let chunk? ← (client.recv? 8192).block
    pure (some chunk?)
  let timeoutTask ← IO.asTask do
    IO.sleep 500
    pure (none : Option (Option ByteArray))
  match ← IO.waitAny [eofTask, timeoutTask] with
  | .error err => throw err
  | .ok (some none) => pure ()
  | .ok (some (some _)) =>
      throw (IO.userError "managed h2c server should close its write side after wait")
  | .ok none =>
      throw (IO.userError "managed h2c server did not close its write side after wait")
  (client.shutdown).block

def testHttp2H2CServerReadsWhileStreamOpen : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "OpenStream" }
  let producerRef ← IO.mkRef (none : Option (MessageStream.Producer ByteArray))
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    let producer ← MessageStream.pipe (α := ByteArray) (capacity := some 1)
    producerRef.set (some producer)
    pure {
      metadata := Metadata.empty.insert "handled-by" "h2c-open-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/OpenStream"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c open-stream handler did not start" 100 do
    match ← producerRef.get with
    | none => pure false
    | some _ => pure true
  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected h2c open-stream producer")

  let pingPayload := bytes [9, 8, 7, 6, 5, 4, 3, 2]
  let pingFrame ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode pingFrame)
  (client.send pingWire).block
  let hasPingAck (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.ping && Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client {} hasPingAck 200
    "h2c server did not ACK PING while response stream was open"
  let pingAck ← match stateAfterPing.frames.find? (fun frame =>
      frame.header.frameType == Http2.FrameType.ping && Http2.Ping.isAck frame) with
    | some frame => pure frame
    | none => throw (IO.userError "expected h2c PING ACK frame")
  expectEq (← expectStatusOk (Http2.Ping.decode pingAck)) pingPayload
    "h2c PING ACK should echo payload while stream remains open"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "h2c open stream should not emit trailers before producer close"

  runGrpcM (producer.send (bytes [4, 4]))
  runGrpcM producer.close
  let done (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let finalState ← readHttp2FramesUntilWithTimeout client stateAfterPing done 200
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
      metadata := Metadata.empty.insert "handled-by" "h2c-flow-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[
    { id := Http2.SettingId.initialWindowSize, value := 0 }
  ])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/FlowControlledStream"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c flow-controlled stream handler did not start" 100 do
    match ← producerRef.get with
    | none => pure false
    | some _ => pure true
  let producer ← match ← producerRef.get with
    | some producer => pure producer
    | none => throw (IO.userError "expected h2c flow-controlled producer")

  let hasInitialResponseHeaders (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && !Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let stateAfterHeaders ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders 500
    "h2c flow-controlled stream did not emit initial response headers"

  let responseData := bytes [4, 4, 4]
  let responseWire ← expectStatusOk (Message.encode { data := responseData })
  runGrpcM (producer.send responseData)

  let pingPayload := bytes [8, 7, 6, 5, 4, 3, 2, 1]
  let ping ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode ping)
  (client.send pingWire).block
  let hasPingAck (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.ping && Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client stateAfterHeaders hasPingAck 500
    "h2c server did not ACK PING while active response DATA was flow-control blocked"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.data && frame.header.streamId == 1)
    "h2c flow-controlled stream should not emit DATA before WINDOW_UPDATE"

  let streamUpdate ← expectStatusOk (Http2.WindowUpdate.frame 1 responseWire.size)
  let streamUpdateWire ← expectStatusOk (Http2.Frame.encode streamUpdate)
  (client.send streamUpdateWire).block
  let hasResponseData (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.data && frame.header.streamId == 1
  let stateAfterWindow ← readHttp2FramesUntilWithTimeout client stateAfterPing hasResponseData 500
    "h2c WINDOW_UPDATE did not flush active response DATA"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stateAfterWindow.frames))
  expect (responseMessages.any fun message => message.data == responseData)
    "h2c WINDOW_UPDATE should flush the queued response message"

  runGrpcM producer.close
  let hasTrailers (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  discard <| readHttp2FramesUntilWithTimeout client stateAfterWindow hasTrailers 500
    "h2c flow-controlled stream did not emit trailers after producer close"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2H2CServerBidirectionalRespondsBeforeClientEndStream : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "EarlyChat" }
  let registry := Registry.empty.registerBidirectionalStreamingStream method fun request => do
    pure {
      metadata := Metadata.empty.insert "handled-by" "h2c-early-bidi",
      messages := request.messages.mapM fun message => pure (message.append (bytes [7])),
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/EarlyChat"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire)).block

  let firstBody ← expectStatusOk (Message.encode { data := bytes [1, 2] })
  let firstDataFrame : Http2.Frame := {
    header := {
      length := firstBody.size,
      frameType := Http2.FrameType.data,
      flags := 0,
      streamId := 1
    },
    payload := firstBody
  }
  let firstDataWire ← expectStatusOk (Http2.Frame.encode firstDataFrame)
  (client.send firstDataWire).block

  let hasResponseData (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.data && frame.header.streamId == 1
  let stateAfterFirstData ← readHttp2FramesUntilWithTimeout client {} hasResponseData 500
    "h2c bidi stream did not emit response DATA before client END_STREAM"
  let responseMessages ← expectStatusOk (Message.decodeAll (dataPayloads stateAfterFirstData.frames))
  expect (responseMessages.any fun message => message.data == bytes [1, 2, 7])
    "h2c bidi response before client END_STREAM should transform first request message"
  expect (!stateAfterFirstData.frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "h2c bidi stream should not emit trailers before client END_STREAM"

  let secondBody ← expectStatusOk (Message.encode { data := bytes [3, 4] })
  let secondDataFrame : Http2.Frame := {
    header := {
      length := secondBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := secondBody
  }
  let secondDataWire ← expectStatusOk (Http2.Frame.encode secondDataFrame)
  (client.send secondDataWire).block
  let hasTrailers (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let finalState ← readHttp2FramesUntilWithTimeout client stateAfterFirstData hasTrailers 500
    "h2c bidi stream did not emit trailers after client END_STREAM"
  let allMessages ← expectStatusOk (Message.decodeAll (dataPayloads finalState.frames))
  expect (allMessages.any fun message => message.data == bytes [3, 4, 7])
    "h2c bidi stream should transform the final request message"

  (client.shutdown).block
  awaitIoTask serverTask

def testHttp2H2CServerCancelsStreamOnRst : IO Unit := do
  let method : MethodName := { service := "lean.example.proto.NoteService", method := "CancelStream" }
  let startedRef ← IO.mkRef false
  let cancelledRef ← IO.mkRef false
  let registry := Registry.empty.registerServerStreamingStream method fun _request => do
    startedRef.set true
    let stream : MessageStream ByteArray := {
      recv? := cancelledRecvLoop cancelledRef
    }
    pure {
      metadata := Metadata.empty.insert "handled-by" "h2c-cancel-stream",
      messages := stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/CancelStream"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c cancel-stream handler did not start" 100 startedRef.get
  let hasInitialResponseHeaders (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && !Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let stateAfterHeaders ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders 200
    "h2c cancel-stream response did not emit initial headers"

  let rst ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (Http2.Frame.encode rst)
  (client.send rstWire).block
  waitUntil "h2c RST_STREAM did not cancel the active response stream" 200 cancelledRef.get

  let pingPayload := bytes [1, 2, 3, 4, 5, 6, 7, 8]
  let ping ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode ping)
  (client.send pingWire).block
  let hasPingAck (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.ping && Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client stateAfterHeaders hasPingAck 200
    "h2c server did not continue processing after RST_STREAM cancellation"
  expect (!stateAfterPing.frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "RST_STREAM cancellation should not emit response trailers for the reset stream"

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
      waitUntil "h2c disconnect test did not release producer send" 1000 attemptSendRef.get
      let result ← (producer.send (bytes [5, 5, 5])).run
      producerSendResultRef.set (some result)
    producerTaskRef.set (some producerTask)
    pure {
      metadata := Metadata.empty.insert "handled-by" "h2c-disconnect-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/DisconnectStream"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c disconnect handler did not start" 100 startedRef.get
  let hasInitialResponseHeaders (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && !Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  discard <| readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders 200
    "h2c disconnect response did not emit initial headers"

  (client.shutdown).block
  awaitIoTask serverTask
  attemptSendRef.set true
  waitUntil "h2c disconnect did not close the producer-backed response stream" 500 do
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
      waitUntil "h2c cancel-pipe test did not release producer send" 1000 attemptSendRef.get
      let result ← (producer.send (bytes [9, 9, 9])).run
      producerSendResultRef.set (some result)
    producerTaskRef.set (some producerTask)
    pure {
      metadata := Metadata.empty.insert "handled-by" "h2c-cancel-pipe-stream",
      messages := producer.stream,
      status := Status.ok
    }

  let server ← Grpc.Server.bind { address := Grpc.Server.loopback 0 }
  let serverTask ← IO.asTask (Grpc.Server.acceptOne server registry)
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let clientSettings ← expectStatusOk (Http2.Settings.frame #[])
  let clientSettingsWire ← expectStatusOk (Http2.Frame.encode clientSettings)
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {}
    (requestHeadersForPath "/lean.example.proto.NoteService/CancelPipeStream"))
  let requestHeadersFrame : Http2.Frame := {
    header := {
      length := encodedHeaders.1.size,
      frameType := Http2.FrameType.headers,
      flags := Http2.FrameFlag.endHeaders,
      streamId := 1
    },
    payload := encodedHeaders.1
  }
  let requestBody ← expectStatusOk (Message.encode { data := bytes [1] })
  let requestDataFrame : Http2.Frame := {
    header := {
      length := requestBody.size,
      frameType := Http2.FrameType.data,
      flags := Http2.FrameFlag.endStream,
      streamId := 1
    },
    payload := requestBody
  }
  let requestHeadersWire ← expectStatusOk (Http2.Frame.encode requestHeadersFrame)
  let requestDataWire ← expectStatusOk (Http2.Frame.encode requestDataFrame)
  (client.send (Http2.connectionPreface
    |>.append clientSettingsWire
    |>.append requestHeadersWire
    |>.append requestDataWire)).block

  waitUntil "h2c cancel-pipe handler did not start" 100 startedRef.get
  let hasInitialResponseHeaders (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && !Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  let stateAfterHeaders ← readHttp2FramesUntilWithTimeout client {} hasInitialResponseHeaders 200
    "h2c cancel-pipe response did not emit initial headers"

  let rst ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (Http2.Frame.encode rst)
  (client.send rstWire).block
  let pingPayload := bytes [2, 3, 4, 5, 6, 7, 8, 9]
  let ping ← expectStatusOk (Http2.Ping.frame pingPayload)
  let pingWire ← expectStatusOk (Http2.Frame.encode ping)
  (client.send pingWire).block
  let hasPingAck (frames : Array Http2.Frame) : Bool :=
    frames.any fun frame =>
      frame.header.frameType == Http2.FrameType.ping && Http2.Ping.isAck frame
  let stateAfterPing ← readHttp2FramesUntilWithTimeout client stateAfterHeaders hasPingAck 200
    "h2c server did not continue processing after pipe-backed RST_STREAM cancellation"
  attemptSendRef.set true
  waitUntil "h2c RST_STREAM did not close the producer-backed response stream" 500 do
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
      frame.header.frameType == Http2.FrameType.headers
        && frame.header.streamId == 1
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream)
    "RST_STREAM cancellation should not emit trailers for the reset pipe-backed stream"

  match ← producerTaskRef.get with
  | none => throw (IO.userError "expected h2c cancel-pipe producer task")
  | some task => awaitIoTask task
  (client.shutdown).block
  awaitIoTask serverTask

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
  testHandlerExceptionDispatch
  testResponseMetadataValidationDispatch
  testMessageSizeLimits
  testHttp2Frames
  testHpack
  testUnaryHttp2Transport
  testLargeUnaryResponseMetadataContinuationFrames
  testLargeStreamResponseTrailerContinuationFrames
  testServerStreamingHttp2Transport
  testStreamNativeServerStreamingHttp2Transport
  testServerStreamingHttp2SendMessageSizeLimitTransport
  testStreamingEncoderEmitsBeforeStreamEnd
  testStreamingDispatchEmitsBeforeStreamEnd
  testStreamingConnectionEmitsBeforeStreamEnd
  testServerStreamingHttp2StreamErrorTransport
  testClientStreamingHttp2Transport
  testBidirectionalStreamingHttp2Transport
  testPaddedPriorityUnaryHttp2Transport
  testHeadersPrioritySelfDependencyRejected
  testInboundHeaderListSizeLimit
  testTrailersOnlyUnaryFailure
  testDeadlineExceededHttp2Transport
  testHandlerExceptionHttp2Transport
  testInvalidResponseMetadataHttp2Transport
  testNonOkUnaryIgnoresUnusedResponseDataLimitHttp2Transport
  testLargeUnaryResponseDataFrames
  testOutboundFlowControl
  testOutboundWindowUpdateOverflowRejected
  testOutboundInitialWindowReductionKeepsNegativeStreamDebt
  testResetStreamClearsPendingOutbound
  testInboundFrameSizeLimit
  testInboundFlowControlLimit
  testClientStreamIdValidation
  testClientStreamIdMonotonicity
  testMaxConcurrentStreamsEnforced
  testMaxConcurrentStreamsCountsEarlyRejectedBodyDrains
  testMaxConcurrentStreamsCountsDetachedStreamingDispatch
  testStreamNativeContentLengthEnforced
  testStreamNativePaddedDataUsesUnpaddedContentLength
  testEarlyInvalidHeadersIgnoreRequestBodyStateMachine
  testEarlyInvalidHeadersIgnoreRequestBody
  testEarlyHttpStatusOnlyRejectionIgnoreRequestBody
  testEarlyUnknownMethodIgnoreRequestBody
  testEarlyRejectedStreamResetClearsIgnoredBody
  testStreamNativeMalformedDataReturnsGrpcStatus
  testPriorityFrameIgnored
  testUnknownFrameIgnored
  testPeerSettingsAffectOutbound
  testHttp2Connection
  testHttp2H2CServer
  testHttp2ServeManagedLifecycle
  testHttp2H2CServerReadsWhileStreamOpen
  testHttp2H2CServerFlushesActiveStreamOnWindowUpdate
  testHttp2H2CServerBidirectionalRespondsBeforeClientEndStream
  testHttp2H2CServerCancelsStreamOnRst
  testHttp2H2CServerCancelsStreamOnDisconnect
  testHttp2H2CServerCancelsPipeStreamOnRst
