module

public import Grpc.Framing
public import Grpc.Http2.Frame
public import Grpc.Http2.Hpack
public import Grpc.Protocol
public import Grpc.Server

public section

namespace Grpc
namespace Http2
namespace Transport

structure UnaryRequestFrames where
  streamId : Nat
  metadata : Metadata
  body : ByteArray
  hpack : Hpack.State
  /-- The registry entry authorized when the header block completed, if header
  authorization already ran on the connection.  `none` means dispatch must
  look the method up and run the authorizer itself. -/
  authorizedEntry? : Option MethodEntry := none

structure RequestHeadersFrames where
  streamId : Nat
  metadata : Metadata
  hpack : Hpack.State
  endStream : Bool

structure UnaryDispatchResult where
  frames : Array Frame
  inboundHpack : Hpack.State
  outboundHpack : Hpack.State

structure UnaryDispatchStateResult where
  inboundHpack : Hpack.State
  outboundHpack : Hpack.State

private def clearFlag (flags flag : UInt8) : UInt8 :=
  if FrameFlag.has flags flag then
    UInt8.ofNat (flags.toNat - flag.toNat)
  else
    flags

private def stripPadding (frameName : String) (payload : ByteArray) (offset : Nat)
    (padLength : Nat) : Except Status ByteArray := do
  if offset > payload.size then
    throw (Status.internal s!"HTTP/2 {frameName} frame payload is truncated")
  if padLength > payload.size - offset then
    throw (Status.internal s!"HTTP/2 {frameName} padding exceeds payload size")
  pure (payload.extract offset (payload.size - padLength))

private def readUInt32BE (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 16777216
    + bytes[offset + 1]!.toNat * 65536
    + bytes[offset + 2]!.toNat * 256
    + bytes[offset + 3]!.toNat

def normalizeDataFrame (frame : Frame) : Except Status Frame := do
  if !FrameFlag.has frame.header.flags FrameFlag.padded then
    pure frame
  else if frame.payload.isEmpty then
    throw (Status.internal "HTTP/2 DATA frame missing pad length")
  else
    let payload ← stripPadding "DATA" frame.payload 1 frame.payload[0]!.toNat
    let flags := clearFlag frame.header.flags FrameFlag.padded
    pure {
      frame with
      header := { frame.header with length := payload.size, flags := flags },
      payload := payload
    }

def normalizeHeadersFrame (frame : Frame) : Except Status Frame := do
  let hasPadding := FrameFlag.has frame.header.flags FrameFlag.padded
  let hasPriority := FrameFlag.has frame.header.flags FrameFlag.priority
  let (padLength, offset) ←
    if hasPadding then
      if frame.payload.isEmpty then
        throw (Status.internal "HTTP/2 HEADERS frame missing pad length")
      else
        pure (frame.payload[0]!.toNat, 1)
    else
      pure (0, 0)
  let offset ←
    if hasPriority then
      if frame.payload.size < offset + 5 then
        throw (Status.internal "HTTP/2 HEADERS priority fields are truncated")
      else do
        let rawDependency := readUInt32BE frame.payload offset
        let streamDependency := rawDependency % (maxStreamId + 1)
        if streamDependency == frame.header.streamId then
          throw (Status.internal "HTTP/2 HEADERS priority dependency cannot reference the same stream")
        pure (offset + 5)
    else
      pure offset
  let payload ← stripPadding "HEADERS" frame.payload offset padLength
  let flags := frame.header.flags
  let flags := clearFlag flags FrameFlag.padded
  let flags := clearFlag flags FrameFlag.priority
  pure {
    frame with
    header := { frame.header with length := payload.size, flags := flags },
    payload := payload
  }

def decodeRequestHeadersFrame (state : Hpack.State) (frame : Frame)
    (maxHeaderListSize : Option Nat := none) :
    Except Status RequestHeadersFrames := do
  if frame.header.frameType != FrameType.headers then
    throw (Status.internal "expected HTTP/2 HEADERS frame")
  if frame.header.streamId == 0 then
    throw (Status.internal "gRPC request HEADERS frame must use a client stream")
  let frame ← normalizeHeadersFrame frame
  if !FrameFlag.has frame.header.flags FrameFlag.endHeaders then
    throw (Status.internal "HTTP/2 request header block ended before END_HEADERS")
  let decoded ← Hpack.decodeHeaderBlock state frame.payload
  Metadata.validateHeaderListSize maxHeaderListSize decoded.headers
  pure {
    streamId := frame.header.streamId,
    metadata := decoded.headers,
    hpack := decoded.state,
    endStream := FrameFlag.has frame.header.flags FrameFlag.endStream
  }

structure RequestHeaderBlock where
  frame : Frame
  nextIndex : Nat

private partial def collectContinuationFrames (frames : Array Frame) (i : Nat)
    (headersFrame : Frame) : Except Status RequestHeaderBlock := do
  if FrameFlag.has headersFrame.header.flags FrameFlag.endHeaders then
    pure { frame := headersFrame, nextIndex := i }
  else
    let frame ← match frames[i]? with
      | some frame => pure frame
      | none => throw (Status.internal "HTTP/2 request header block ended before END_HEADERS")
    if frame.header.frameType != FrameType.continuation then
      throw (Status.internal "HTTP/2 header block must be followed by CONTINUATION frames")
    if frame.header.streamId != headersFrame.header.streamId then
      throw (Status.internal "HTTP/2 CONTINUATION frame changed stream id")
    let payload := headersFrame.payload.append frame.payload
    let flags :=
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        UInt8.ofNat (headersFrame.header.flags.toNat + FrameFlag.endHeaders.toNat)
      else
        headersFrame.header.flags
    let headersFrame := {
      headersFrame with
      header := { headersFrame.header with length := payload.size, flags := flags },
      payload := payload
    }
    collectContinuationFrames frames (i + 1) headersFrame

private def collectHeaderBlockFrames (frames : Array Frame) : Except Status RequestHeaderBlock := do
  let headersFrame ← match frames[0]? with
    | some frame => pure frame
    | none => throw (Status.internal "missing HTTP/2 HEADERS frame")
  if headersFrame.header.frameType != FrameType.headers then
    throw (Status.internal "expected HTTP/2 HEADERS frame")
  let headersFrame ← normalizeHeadersFrame headersFrame
  collectContinuationFrames frames 1 headersFrame

private partial def collectData (frames : Array Frame) (i streamId : Nat) (body : ByteArray) :
    Except Status ByteArray := do
  if i >= frames.size then
    throw (Status.internal "HTTP/2 request ended before END_STREAM")
  let frame := frames[i]!
  if frame.header.streamId != streamId then
    throw (Status.internal "HTTP/2 request frames changed stream id")
  if frame.header.frameType != FrameType.data then
    throw (Status.internal "expected HTTP/2 DATA frame")
  let frame ← normalizeDataFrame frame
  let body := body.append frame.payload
  if FrameFlag.has frame.header.flags FrameFlag.endStream then
    pure body
  else
    collectData frames (i + 1) streamId body

def decodeUnaryRequestFrames (state : Hpack.State) (frames : Array Frame)
    (maxHeaderListSize : Option Nat := none) :
    Except Status UnaryRequestFrames := do
  let headerBlock ← collectHeaderBlockFrames frames
  let headers ← decodeRequestHeadersFrame state headerBlock.frame maxHeaderListSize
  let body ←
    if headers.endStream then
      pure ByteArray.empty
    else
      collectData frames headerBlock.nextIndex headers.streamId ByteArray.empty

  pure {
    streamId := headers.streamId,
    metadata := headers.metadata,
    body := body,
    hpack := headers.hpack
  }

private def headerBlockFlags (first last endStream : Bool) : UInt8 :=
  let flags := if first && endStream then FrameFlag.endStream else 0
  if last then
    UInt8.ofNat (flags.toNat + FrameFlag.endHeaders.toNat)
  else
    flags

private def headerBlockFrame (streamId : Nat) (frameType : FrameType)
    (payload : ByteArray) (flags : UInt8) : Frame :=
  {
    header := {
      length := payload.size,
      frameType := frameType,
      flags := flags,
      streamId := streamId
    },
    payload := payload
  }

private partial def headerBlockFramesLoop (streamId maxSize offset : Nat) (block : ByteArray)
    (endStream : Bool) (frames : Array Frame) : Except Status (Array Frame) := do
  if offset >= block.size then
    pure frames
  else
    let next := offset + maxSize
    let stop := if next < block.size then next else block.size
    let payload := block.extract offset stop
    let first := frames.isEmpty
    let last := stop == block.size
    let frameType := if first then FrameType.headers else FrameType.continuation
    let flags := headerBlockFlags first last endStream
    let frame := headerBlockFrame streamId frameType payload flags
    headerBlockFramesLoop streamId maxSize stop block endStream (frames.push frame)

private def headerBlockFrames (streamId : Nat) (block : ByteArray) (endStream : Bool)
    (maxSize : Nat := defaultMaxFramePayloadLength) : Except Status (Array Frame) := do
  if maxSize == 0 then
    throw (Status.internal "HTTP/2 header block frame max size must be positive")
  else if block.isEmpty then
    pure #[headerBlockFrame streamId FrameType.headers ByteArray.empty
      (headerBlockFlags true true endStream)]
  else
    headerBlockFramesLoop streamId maxSize 0 block endStream #[]

private def dataFrame (streamId : Nat) (payload : ByteArray) : Frame :=
  {
    header := {
      length := payload.size,
      frameType := FrameType.data,
      flags := 0,
      streamId := streamId
    },
    payload := payload
  }

private partial def dataFramesLoop (streamId offset maxSize : Nat) (payload : ByteArray)
    (frames : Array Frame) : Except Status (Array Frame) := do
  if maxSize == 0 then
    throw (Status.internal "HTTP/2 DATA frame max size must be positive")
  else if offset >= payload.size then
    pure frames
  else
    let next := offset + maxSize
    let stop := if next < payload.size then next else payload.size
    let chunk := payload.extract offset stop
    dataFramesLoop streamId stop maxSize payload (frames.push (dataFrame streamId chunk))

def dataFrames (streamId : Nat) (payload : ByteArray)
    (maxSize : Nat := defaultMaxFramePayloadLength) : Except Status (Array Frame) :=
  dataFramesLoop streamId 0 maxSize payload #[]

/-- Response headers, with `grpc-encoding: gzip` added when the response body
is gzip-compressed. -/
private def responseHeadersFor (gzip : Bool) : Metadata :=
  if gzip then
    Headers.responseHeaders.insert "grpc-encoding" Headers.gzipEncoding
  else
    Headers.responseHeaders

private def appendMessageDataFrames (streamId maxDataFrameSize : Nat)
    (frames : Array Frame) (data : ByteArray) (gzip : Bool := false) :
    Except Status (Array Frame) := do
  let message ← Message.encode (if gzip then Message.gzipped data else { data := data })
  let data ← dataFrames streamId message maxDataFrameSize
  pure (frames.append data)

def encodeUnaryResponseFrames (state : Hpack.State) (streamId : Nat) (response : UnaryResponse)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false) :
    Except Status (Array Frame × Hpack.State) := do
  if !response.status.isOk then
    let metadata := Metadata.append Headers.responseHeaders response.metadata
    let metadata := Metadata.append metadata (Headers.trailers response.status response.trailers)
    let block ← Hpack.encodeHeaderBlock state metadata
    let state := block.2
    let frames ← headerBlockFrames streamId block.1 true maxDataFrameSize
    pure (frames, state)
  else
    let initialMetadata := Metadata.append (responseHeadersFor gzip) response.metadata
    let initialBlock ← Hpack.encodeHeaderBlock state initialMetadata
    let state := initialBlock.2
    let initial ← headerBlockFrames streamId initialBlock.1 false maxDataFrameSize

    let trailers := Headers.trailers response.status response.trailers
    let trailerBlock ← Hpack.encodeHeaderBlock state trailers
    let state := trailerBlock.2
    let trailerFrames ← headerBlockFrames streamId trailerBlock.1 true maxDataFrameSize

    if response.status.isOk then
      let message ← Message.encode
        (if gzip then Message.gzipped response.data else { data := response.data })
      let data ← dataFrames streamId message maxDataFrameSize
      pure ((initial.append data).append trailerFrames, state)
    else
      pure (initial.append trailerFrames, state)

def encodeServerStreamingResponseFrames (state : Hpack.State) (streamId : Nat)
    (response : ServerStreamingResponse)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false) :
    Except Status (Array Frame × Hpack.State) := do
  if !response.status.isOk && response.messages.isEmpty then
    let metadata := Metadata.append Headers.responseHeaders response.metadata
    let metadata := Metadata.append metadata (Headers.trailers response.status response.trailers)
    let block ← Hpack.encodeHeaderBlock state metadata
    let state := block.2
    let frames ← headerBlockFrames streamId block.1 true maxDataFrameSize
    pure (frames, state)
  else
    let initialMetadata := Metadata.append (responseHeadersFor gzip) response.metadata
    let initialBlock ← Hpack.encodeHeaderBlock state initialMetadata
    let state := initialBlock.2
    let initial ← headerBlockFrames streamId initialBlock.1 false maxDataFrameSize

    let trailers := Headers.trailers response.status response.trailers
    let trailerBlock ← Hpack.encodeHeaderBlock state trailers
    let state := trailerBlock.2
    let trailerFrames ← headerBlockFrames streamId trailerBlock.1 true maxDataFrameSize

    let frames ← response.messages.foldlM
      (init := initial)
      (fun frames message => appendMessageDataFrames streamId maxDataFrameSize frames message gzip)
    pure (frames.append trailerFrames, state)

private def emitFrames (emit : Array Frame -> IO Unit) (frames : Array Frame) :
    IO (Except Status Unit) := do
  if frames.isEmpty then
    pure (.ok ())
  else
    try
      emit frames
      pure (.ok ())
    catch err =>
      pure (.error (Status.ofIOError err))

private partial def emitMessageStreamDataFrames (streamId maxDataFrameSize : Nat)
    (stream : MessageStream ByteArray) (emit : Array Frame -> IO Unit)
    (gzip : Bool := false) :
    IO (Except Status (Option Status)) := do
  match ← stream.recv?.run with
  | .error status => pure (.ok (some status))
  | .ok none => pure (.ok none)
  | .ok (some message) =>
      match appendMessageDataFrames streamId maxDataFrameSize #[] message gzip with
      | .error status => pure (.ok (some status))
      | .ok frames =>
          match ← emitFrames emit frames with
          | .error status => pure (.error status)
          | .ok () => emitMessageStreamDataFrames streamId maxDataFrameSize stream emit gzip

private def encodeTrailersOnlyFrames (state : Hpack.State) (streamId : Nat)
    (metadata : Metadata) (status : Status) (trailers : Metadata)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) :
    Except Status (Array Frame × Hpack.State) := do
  let metadata := Metadata.append Headers.responseHeaders metadata
  let metadata := Metadata.append metadata (Headers.trailers status trailers)
  let block ← Hpack.encodeHeaderBlock state metadata
  let frames ← headerBlockFrames streamId block.1 true maxDataFrameSize
  pure (frames, block.2)

private def encodeHttpStatusOnlyFrames (state : Hpack.State) (streamId : Nat)
    (statusCode : String) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) :
    Except Status (Array Frame × Hpack.State) := do
  let block ← Hpack.encodeHeaderBlock state (Metadata.empty.insert ":status" statusCode)
  let frames ← headerBlockFrames streamId block.1 true maxDataFrameSize
  pure (frames, block.2)

private def unsupportedContentType? (metadata : Metadata) : Option String :=
  match Headers.contentType metadata with
  | some value =>
      if Headers.isGrpcContentType value then none else some value
  | none => none

private def registryContainsMethod (registry : Registry) (method : MethodName) : Bool :=
  (registry.findEntry? method).isSome

inductive EarlyRequestDecision where
  | accept (entry : MethodEntry)
  | reject (frames : Array Frame) (outboundHpack : Hpack.State)

def encodeEarlyRequestRejectionFrames? (registry : Registry) (state : Hpack.State) (streamId : Nat)
    (metadata : Metadata) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) :
    Except Status (Option (Array Frame × Hpack.State)) := do
  let encodeGrpcStatus (status : Status) : Except Status (Array Frame × Hpack.State) :=
    encodeUnaryResponseFrames state streamId { status := status, data := ByteArray.empty }
      maxDataFrameSize
  match Metadata.validate metadata with
  | .error status => some <$> encodeGrpcStatus status
  | .ok () =>
      match unsupportedContentType? metadata with
      | some _ => some <$> encodeHttpStatusOnlyFrames state streamId "415" maxDataFrameSize
      | none =>
          match Headers.validateUnaryRequestHeaders metadata with
          | .error status => some <$> encodeGrpcStatus status
          | .ok method =>
              if registryContainsMethod registry method then
                pure none
              else
                some <$> encodeGrpcStatus
                  (Status.unimplemented s!"unknown gRPC method {method.path}")

/--
Validate and authorize a complete request header block.  This function is
called as soon as END_HEADERS arrives, before the connection accepts DATA for
the stream.  The registry entry for the method is looked up here, so a
successful decision carries the entry (with the authorizer's accepted
handler, which has the entry's exact shape by construction); it is retained
in stream state and used for dispatch without rerunning the authorizer.
-/
def authorizeEarlyRequest (registry : Registry) (state : Hpack.State) (streamId : Nat)
    (metadata : Metadata) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) :
    IO (Except Status EarlyRequestDecision) := do
  match encodeEarlyRequestRejectionFrames?
      registry state streamId metadata maxDataFrameSize with
  | .error status => pure (.error status)
  | .ok (some encoded) => pure (.ok (.reject encoded.1 encoded.2))
  | .ok none =>
    let method ← match Headers.validateUnaryRequestHeaders metadata with
      | .ok method => pure method
      | .error status => return .error status
    let rejectWith (status : Status) : Except Status EarlyRequestDecision :=
      match encodeUnaryResponseFrames state streamId
          { status := status, data := ByteArray.empty } maxDataFrameSize with
      | .ok encoded => .ok (.reject encoded.1 encoded.2)
      | .error encodeStatus => .error encodeStatus
    match registry.findEntry? method with
    | none =>
        pure (rejectWith (Status.unimplemented s!"unknown gRPC method {method.path}"))
    | some entry =>
      let authorizationResult ← try
        registry.authorizeRequestHeaders entry metadata |>.run
      catch error =>
        pure (.error (Status.ofIOError error))
      match authorizationResult with
      | .ok (.accept handler) => pure (.ok (.accept { entry with handler := handler }))
      | .ok (.reject status) => pure (rejectWith status)
      | .error status => pure (rejectWith status)

def encodeServerStreamingStreamResponseFramesWith (state : Hpack.State) (streamId : Nat)
    (response : ServerStreamingStreamResponse)
    (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false) :
    IO (Except Status Hpack.State) := do
  if !response.status.isOk then
    match ← response.messages.recv?.run with
    | .error status =>
        match encodeTrailersOnlyFrames state streamId response.metadata status response.trailers
            maxDataFrameSize with
        | .error status => pure (.error status)
        | .ok encoded =>
            match ← emitFrames emit encoded.1 with
            | .error status => pure (.error status)
            | .ok () => pure (.ok encoded.2)
    | .ok none =>
        match encodeTrailersOnlyFrames state streamId response.metadata response.status response.trailers
            maxDataFrameSize with
        | .error status => pure (.error status)
        | .ok encoded =>
            match ← emitFrames emit encoded.1 with
            | .error status => pure (.error status)
            | .ok () => pure (.ok encoded.2)
    | .ok (some firstMessage) =>
        match Hpack.encodeHeaderBlock state (Metadata.append (responseHeadersFor gzip) response.metadata) with
        | .error status => pure (.error status)
        | .ok initialBlock =>
            let state := initialBlock.2
            match headerBlockFrames streamId initialBlock.1 false maxDataFrameSize with
            | .error status => pure (.error status)
            | .ok initialFrames =>
                match ← emitFrames emit initialFrames with
                | .error status => pure (.error status)
                | .ok () =>
                    match appendMessageDataFrames streamId maxDataFrameSize #[] firstMessage gzip with
                    | .error status => pure (.error status)
                    | .ok firstFrames =>
                        match ← emitFrames emit firstFrames with
                        | .error status => pure (.error status)
                        | .ok () =>
                            match ← emitMessageStreamDataFrames
                                streamId maxDataFrameSize response.messages emit gzip with
                            | .error status => pure (.error status)
                            | .ok streamStatus? =>
                                let finalStatus := streamStatus?.getD response.status
                                match Hpack.encodeHeaderBlock state
                                    (Headers.trailers finalStatus response.trailers) with
                                | .error status => pure (.error status)
                                | .ok trailerBlock =>
                                    match headerBlockFrames streamId trailerBlock.1 true
                                        maxDataFrameSize with
                                    | .error status => pure (.error status)
                                    | .ok trailerFrames =>
                                        match ← emitFrames emit trailerFrames with
                                        | .error status => pure (.error status)
                                        | .ok () => pure (.ok trailerBlock.2)
  else
    match Hpack.encodeHeaderBlock state (Metadata.append (responseHeadersFor gzip) response.metadata) with
    | .error status => pure (.error status)
    | .ok initialBlock =>
        let state := initialBlock.2
        match headerBlockFrames streamId initialBlock.1 false maxDataFrameSize with
        | .error status => pure (.error status)
        | .ok initialFrames =>
            match ← emitFrames emit initialFrames with
            | .error status => pure (.error status)
            | .ok () =>
                match ← emitMessageStreamDataFrames streamId maxDataFrameSize response.messages emit gzip with
                | .error status => pure (.error status)
                | .ok streamStatus? =>
                    let finalStatus := streamStatus?.getD response.status
                    match Hpack.encodeHeaderBlock state
                        (Headers.trailers finalStatus response.trailers) with
                    | .error status => pure (.error status)
                    | .ok trailerBlock =>
                        match headerBlockFrames streamId trailerBlock.1 true maxDataFrameSize with
                        | .error status => pure (.error status)
                        | .ok trailerFrames =>
                            match ← emitFrames emit trailerFrames with
                            | .error status => pure (.error status)
                            | .ok () => pure (.ok trailerBlock.2)

def encodeServerStreamingStreamResponseFrames (state : Hpack.State) (streamId : Nat)
    (response : ServerStreamingStreamResponse)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false) :
    IO (Except Status (Array Frame × Hpack.State)) := do
  let framesRef ← IO.mkRef #[]
  match ← encodeServerStreamingStreamResponseFramesWith state streamId response
      (fun frames => framesRef.modify fun out => out.append frames)
      maxDataFrameSize gzip with
  | .error status => pure (.error status)
  | .ok state => pure (.ok (← framesRef.get, state))

def dispatchDecodedUnaryFramesWith (registry : Registry) (outboundHpack : Hpack.State)
    (request : UnaryRequestFrames) (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (onResponseStream : MessageStream ByteArray -> IO Unit := fun _ => pure ())
    (enableGzip : Bool := true) :
    IO (Except Status UnaryDispatchStateResult) := do
  let gzip := enableGzip && Headers.clientAcceptsGzip request.metadata
  let finish (outboundHpack : Hpack.State) : UnaryDispatchStateResult := {
    inboundHpack := request.hpack,
    outboundHpack := outboundHpack
  }
  let encodeUnary (response : UnaryResponse) : IO (Except Status UnaryDispatchStateResult) := do
    match encodeUnaryResponseFrames outboundHpack request.streamId response maxDataFrameSize gzip with
    | .error status => pure (.error status)
    | .ok encoded =>
        match ← emitFrames emit encoded.1 with
        | .error status => pure (.error status)
        | .ok () => pure (.ok (finish encoded.2))
  let encodeHttpStatus (statusCode : String) : IO (Except Status UnaryDispatchStateResult) := do
    match encodeHttpStatusOnlyFrames outboundHpack request.streamId statusCode maxDataFrameSize with
    | .error status => pure (.error status)
    | .ok encoded =>
        match ← emitFrames emit encoded.1 with
        | .error status => pure (.error status)
        | .ok () => pure (.ok (finish encoded.2))
  let encodeStreaming (response : ServerStreamingStreamResponse) :
      IO (Except Status UnaryDispatchStateResult) := do
    try
      onResponseStream response.messages
    catch err =>
      return .error (Status.ofIOError err)
    match ← encodeServerStreamingStreamResponseFramesWith
        outboundHpack request.streamId response emit maxDataFrameSize gzip with
    | .error status => pure (.error status)
    | .ok outboundHpack => pure (.ok (finish outboundHpack))
  let emptyStreamingResponse (status : Status) : ServerStreamingStreamResponse := {
    messages := { recv? := pure none },
    status := status
  }
  match Metadata.validate request.metadata with
  | .error status =>
      encodeUnary { status := status, data := ByteArray.empty }
  | .ok () =>
    match unsupportedContentType? request.metadata with
    | some _ => encodeHttpStatus "415"
    | none =>
        match Headers.validateUnaryRequestHeaders request.metadata with
        | .error status =>
            encodeUnary { status := status, data := ByteArray.empty }
        | .ok method =>
          let decompressBody : Except Status ByteArray := do
            let usesGzip ← Headers.requestUsesGzip request.metadata
            Message.decompressBody usesGzip registry.maxReceiveMessageSize request.body
          let runEntry (entry : MethodEntry) : IO (Except Status UnaryDispatchStateResult) := do
            match decompressBody with
            | .error status => encodeUnary { status := status, data := ByteArray.empty }
            | .ok body =>
              match entry.dispatchHandler with
              | .unary handler =>
                  match (← (registry.dispatchUnary
                      request.metadata body (some handler)).run) with
                  | .ok response => encodeUnary response
                  | .error status =>
                      encodeUnary { status := status, data := ByteArray.empty }
              | .serverStreaming handler =>
                  match (← (registry.dispatchServerStreamingStream
                      request.metadata body (some handler)).run) with
                  | .ok response => encodeStreaming response
                  | .error status => encodeStreaming (emptyStreamingResponse status)
              | .clientStreaming handler =>
                  match (← (registry.dispatchClientStreaming
                      request.metadata body (some handler)).run) with
                  | .ok response => encodeUnary response
                  | .error status =>
                      encodeUnary { status := status, data := ByteArray.empty }
              | .bidirectionalStreaming handler =>
                  match (← (registry.dispatchBidirectionalStreamingStream
                      request.metadata body (some handler)).run) with
                  | .ok response => encodeStreaming response
                  | .error status => encodeStreaming (emptyStreamingResponse status)
          match request.authorizedEntry? with
          | some entry => runEntry entry
          | none =>
            match registry.findEntry? method with
            | none =>
                match decompressBody with
                | .error status =>
                    encodeUnary { status := status, data := ByteArray.empty }
                | .ok _ =>
                    encodeUnary {
                      status := Status.unimplemented s!"unknown gRPC method {method.path}",
                      data := ByteArray.empty
                    }
            | some entry =>
              match ← (registry.authorizeRequestHeaders entry request.metadata).run with
              | .error status =>
                  encodeUnary { status := status, data := ByteArray.empty }
              | .ok (.reject status) =>
                  encodeUnary { status := status, data := ByteArray.empty }
              | .ok (.accept handler) => runEntry { entry with handler := handler }

def dispatchUnaryFramesWith (registry : Registry) (inboundHpack outboundHpack : Hpack.State)
    (frames : Array Frame) (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (maxHeaderListSize : Option Nat := none) :
    IO (Except Status UnaryDispatchStateResult) := do
  match decodeUnaryRequestFrames inboundHpack frames maxHeaderListSize with
  | .error status => pure (.error status)
  | .ok request =>
      dispatchDecodedUnaryFramesWith registry outboundHpack request emit maxDataFrameSize

def dispatchUnaryFrames (registry : Registry) (inboundHpack outboundHpack : Hpack.State)
    (frames : Array Frame) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (maxHeaderListSize : Option Nat := none) :
    IO (Except Status UnaryDispatchResult) := do
  let emittedRef ← IO.mkRef #[]
  match ← dispatchUnaryFramesWith registry inboundHpack outboundHpack frames
      (fun emitted => emittedRef.modify fun out => out.append emitted)
      maxDataFrameSize maxHeaderListSize with
  | .error status => pure (.error status)
  | .ok result =>
      pure (.ok {
        frames := ← emittedRef.get,
        inboundHpack := result.inboundHpack,
        outboundHpack := result.outboundHpack
      })

end Transport
end Http2
end Grpc
