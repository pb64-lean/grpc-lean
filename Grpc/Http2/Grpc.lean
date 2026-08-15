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
  /-- Absolute deadline captured when END_HEADERS was decoded.  Standalone
  transport callers leave this as `none` and Registry dispatch derives it
  from `grpc-timeout` at dispatch time. -/
  deadline : Option Nat := none
  /-- Parsed header facts retained only by managed connections. Standalone
  callers leave this as `none` and keep the public validation path. -/
  preflight? : Option Headers.RequestPreflight := none

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
      else
        -- RFC 9113 removed the dependency tree. Preserve the legacy five-byte
        -- wire shape for compatibility, but ignore its semantics.
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

private def collectContinuationFrames (frames : Array Frame) (i : Nat)
    (headersFrame : Frame) : Except Status RequestHeaderBlock := do
  let mut headersFrame := headersFrame
  if FrameFlag.has headersFrame.header.flags FrameFlag.endHeaders then
    return { frame := headersFrame, nextIndex := i }
  for j in [i:frames.size] do
    let frame := frames[j]!
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
    headersFrame := {
      headersFrame with
      header := { headersFrame.header with length := payload.size, flags := flags },
      payload := payload
    }
    if FrameFlag.has headersFrame.header.flags FrameFlag.endHeaders then
      return { frame := headersFrame, nextIndex := j + 1 }
  throw (Status.internal "HTTP/2 request header block ended before END_HEADERS")

private def collectHeaderBlockFrames (frames : Array Frame) : Except Status RequestHeaderBlock := do
  let headersFrame ← match frames[0]? with
    | some frame => pure frame
    | none => throw (Status.internal "missing HTTP/2 HEADERS frame")
  if headersFrame.header.frameType != FrameType.headers then
    throw (Status.internal "expected HTTP/2 HEADERS frame")
  let headersFrame ← normalizeHeadersFrame headersFrame
  collectContinuationFrames frames 1 headersFrame

private def collectData (frames : Array Frame) (i streamId : Nat) (body : ByteArray) :
    Except Status ByteArray := do
  let mut body := body
  for j in [i:frames.size] do
    let frame := frames[j]!
    if frame.header.streamId != streamId then
      throw (Status.internal "HTTP/2 request frames changed stream id")
    if frame.header.frameType != FrameType.data then
      throw (Status.internal "expected HTTP/2 DATA frame")
    let frame ← normalizeDataFrame frame
    body := body.append frame.payload
    if FrameFlag.has frame.header.flags FrameFlag.endStream then
      return body
  throw (Status.internal "HTTP/2 request ended before END_STREAM")

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

private def headerBlockFramesLoop (streamId maxSize offset : Nat) (block : ByteArray)
    (endStream : Bool) (frames : Array Frame) : Except Status (Array Frame) := do
  if maxSize == 0 then
    throw (Status.internal "HTTP/2 header block frame max size must be positive")
  else
    pure <| Id.run do
      let mut frames := frames
      let mut offset := offset
      while offset < block.size do
        let stop := Nat.min block.size (offset + maxSize)
        let payload := block.extract offset stop
        let first := frames.isEmpty
        let last := stop == block.size
        let frameType := if first then FrameType.headers else FrameType.continuation
        let flags := headerBlockFlags first last endStream
        frames := frames.push (headerBlockFrame streamId frameType payload flags)
        offset := stop
      return frames

private def headerBlockFrames (streamId : Nat) (block : ByteArray) (endStream : Bool)
    (maxSize : Nat := defaultMaxFramePayloadLength) : Except Status (Array Frame) := do
  if maxSize == 0 then
    throw (Status.internal "HTTP/2 header block frame max size must be positive")
  else if block.isEmpty then
    pure #[headerBlockFrame streamId FrameType.headers ByteArray.empty
      (headerBlockFlags true true endStream)]
  else if block.size <= maxSize then
    -- Keep a reusable complete field-block payload intact.  Besides avoiding a
    -- full-range extract for ordinary blocks, this lets cached immutable HPACK
    -- bytes be shared while the stream-specific frame header remains fresh.
    pure #[headerBlockFrame streamId FrameType.headers block
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

private def dataFramesLoop (streamId offset maxSize : Nat) (payload : ByteArray)
    (frames : Array Frame) : Except Status (Array Frame) := do
  if maxSize == 0 then
    throw (Status.internal "HTTP/2 DATA frame max size must be positive")
  else
    pure <| Id.run do
      let mut frames := frames
      let mut offset := offset
      while offset < payload.size do
        let stop := Nat.min payload.size (offset + maxSize)
        let chunk := payload.extract offset stop
        frames := frames.push (dataFrame streamId chunk)
        offset := stop
      return frames

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

/-- Canonical encoder state used only to build immutable common response
blocks.  A live connection's state is never replaced with this value. -/
private def commonResponseCacheState : Hpack.State :=
  { (Hpack.withoutDynamicTable {}) with pendingSizeUpdate := none }

private def encodeCommonResponseBlock (metadata : Metadata) : Except Status ByteArray := do
  let encoded ← Hpack.encodeHeaderBlock commonResponseCacheState metadata
  pure encoded.1

/- These closed values are initialized once by Lean's compiled runtime.  Keep
the failure in `Except` so a future incompatible HPACK change fails normally
instead of silently substituting an invalid block. -/
private def cachedIdentityResponseHeaders : Except Status ByteArray :=
  encodeCommonResponseBlock (responseHeadersFor false)

private def cachedGzipResponseHeaders : Except Status ByteArray :=
  encodeCommonResponseBlock (responseHeadersFor true)

private def cachedOkResponseTrailers : Except Status ByteArray :=
  encodeCommonResponseBlock (Headers.trailers Status.ok)

private def encodeResponseHeadersBlock (state : Hpack.State) (gzip : Bool)
    (metadata : Metadata) : Except Status (ByteArray × Hpack.State) := do
  if state.canReuseHeaderBlock && metadata.isEmpty then
    let block ← if gzip then cachedGzipResponseHeaders else cachedIdentityResponseHeaders
    pure (block, state)
  else
    Hpack.encodeHeaderBlock state (Metadata.append (responseHeadersFor gzip) metadata)

private def encodeResponseTrailersBlock (state : Hpack.State) (status : Status)
    (trailers : Metadata) : Except Status (ByteArray × Hpack.State) := do
  if state.canReuseHeaderBlock && status == Status.ok && trailers.isEmpty then
    pure (← cachedOkResponseTrailers, state)
  else
    Hpack.encodeHeaderBlock state (Headers.trailers status trailers)

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
    let initialBlock ← encodeResponseHeadersBlock state gzip response.metadata
    let state := initialBlock.2
    let initial ← headerBlockFrames streamId initialBlock.1 false maxDataFrameSize

    let trailerBlock ← encodeResponseTrailersBlock state response.status response.trailers
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
    let initialBlock ← encodeResponseHeadersBlock state gzip response.metadata
    let state := initialBlock.2
    let initial ← headerBlockFrames streamId initialBlock.1 false maxDataFrameSize

    let trailerBlock ← encodeResponseTrailersBlock state response.status response.trailers
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

/-- Run response-stream cleanup after every terminal stream-status frame
attempt.  A managed connection wraps `cancel` in an exactly-once callback
retained by its outer dispatch owner, so awaiting it here cannot orphan
arbitrary user IO.  In particular, a blocking callback may delay dispatch
retirement, but never the trailers that precede it.  Standalone encoders
receive the same best-effort cleanup, including when terminal-frame emission
fails. -/
private def finishStreamAfterTerminalFrames (stream : MessageStream α)
    (streamStatus? : Option Status)
    (finish : Std.Async.Async (Except Status β)) :
    Std.Async.Async (Except Status β) := do
  let result ← finish
  match streamStatus? with
  | some _ =>
      try
        discard <| stream.cancel.run
      catch _ =>
        pure ()
  | none => pure ()
  pure result

private partial def emitMessageStreamDataFramesAsync (streamId maxDataFrameSize : Nat)
    (stream : MessageStream ByteArray) (emit : Array Frame -> IO Unit)
    (gzip : Bool := false) (deadline : Option Nat := none)
    (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status (Option Status)) := do
  match ← Registry.recvWithDeadlineUntilAsync deadline stream runtime? with
  | .error status => pure (.ok (some status))
  | .ok none => pure (.ok none)
  | .ok (some message) =>
      match appendMessageDataFrames streamId maxDataFrameSize #[] message gzip with
      | .error status => pure (.ok (some status))
      | .ok frames =>
          match ← emitFrames emit frames with
          | .error status => pure (.error status)
          | .ok () =>
              emitMessageStreamDataFramesAsync
                streamId maxDataFrameSize stream emit gzip deadline runtime?

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

inductive EarlyRequestDecision where
  | accept (entry : MethodEntry)
  | reject (frames : Array Frame) (outboundHpack : Hpack.State)

inductive EarlyRequestPreflightDecision where
  | accept (entry : MethodEntry) (preflight : Headers.RequestPreflight)
  | reject (frames : Array Frame) (outboundHpack : Hpack.State)

/-- Parse and validate every managed-request header fact once while preserving
the historical wire-error precedence: metadata errors, unsupported
content-type as HTTP 415, then the complete gRPC header/method validation. -/
def preflightEarlyRequest (registry : Registry) (state : Hpack.State) (streamId : Nat)
    (metadata : Metadata) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) :
    Except Status EarlyRequestPreflightDecision := do
  let encodeGrpcStatus (status : Status) : Except Status (Array Frame × Hpack.State) :=
    encodeUnaryResponseFrames state streamId { status := status, data := ByteArray.empty }
      maxDataFrameSize
  match Metadata.validate metadata with
  | .error status =>
      let encoded ← encodeGrpcStatus status
      pure (.reject encoded.1 encoded.2)
  | .ok () =>
      let contentTypes := metadata.getAll "content-type"
      match contentTypes[0]? with
      | some value =>
          if !Headers.isGrpcContentType value then
            let encoded ← encodeHttpStatusOnlyFrames state streamId "415" maxDataFrameSize
            pure (.reject encoded.1 encoded.2)
          else
            match Headers.validateUnaryRequestPreflightAfterMetadata metadata contentTypes with
            | .error status =>
                let encoded ← encodeGrpcStatus status
                pure (.reject encoded.1 encoded.2)
            | .ok preflight =>
                match registry.findEntry? preflight.method with
                | some entry => pure (.accept entry preflight)
                | none =>
                    let encoded ← encodeGrpcStatus
                      (Status.unimplemented s!"unknown gRPC method {preflight.method.path}")
                    pure (.reject encoded.1 encoded.2)
      | none =>
          match Headers.validateUnaryRequestPreflightAfterMetadata metadata contentTypes with
          | .error status =>
              let encoded ← encodeGrpcStatus status
              pure (.reject encoded.1 encoded.2)
          | .ok preflight =>
              match registry.findEntry? preflight.method with
              | some entry => pure (.accept entry preflight)
              | none =>
                  let encoded ← encodeGrpcStatus
                    (Status.unimplemented s!"unknown gRPC method {preflight.method.path}")
                  pure (.reject encoded.1 encoded.2)

def encodeEarlyRequestRejectionFrames? (registry : Registry) (state : Hpack.State) (streamId : Nat)
    (metadata : Metadata) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) :
    Except Status (Option (Array Frame × Hpack.State)) := do
  match ← preflightEarlyRequest registry state streamId metadata maxDataFrameSize with
  | .accept _ _ => pure none
  | .reject frames outboundHpack => pure (some (frames, outboundHpack))

/-- Run bounded pure authorization inline, with the same absolute deadline
checked immediately before and after the callback. -/
private def authorizePureEntryUntilWithClock (now : IO Nat)
    (authorizer : PureRequestHeaderAuthorizer) (entry : MethodEntry)
    (metadata : Metadata) (deadline : Option Nat) :
    IO (Except Status (AuthorizationResult entry)) := do
  match deadline with
  | none => pure (.ok (authorizer entry metadata))
  | some deadline =>
      if deadline <= (← now) then
        pure (.error Deadline.exceededStatus)
      else
        let decision := authorizer entry metadata
        if deadline <= (← now) then
          pure (.error Deadline.exceededStatus)
        else
          pure (.ok decision)

/-- Deadline-race only user-installed authorization IO. Default and bounded
pure acceptors stay inline, while a cancelled effectful callback is joined
here before the header-processing owner proceeds. -/
private def authorizeEntryUntilWithClock (now : IO Nat) (registry : Registry)
    (entry : MethodEntry)
    (metadata : Metadata) (deadline : Option Nat)
    (runtime? : Option DeadlineRuntime := none) :
    IO (Except Status (AuthorizationResult entry)) := do
  match registry.pureRequestHeaderAuthorizer? with
  | some authorizer =>
      authorizePureEntryUntilWithClock now authorizer entry metadata deadline
  | none =>
      if !registry.usesCustomRequestHeaderAuthorizer || deadline.isNone then
        try
          registry.authorizeRequestHeaders entry metadata |>.run
        catch error =>
          pure (.error (Status.ofIOError error))
      else
        let childOwned ←
          IO.mkRef (none : Option (Std.Async.Async Unit × IO Unit))
        let runtime : DeadlineRuntime := {
          externalTimer := runtime?.any (fun runtime => runtime.externalTimer),
          registerTask := fun childDeadline cancel expire join => do
            let release ← match runtime? with
              | none => pure (pure ())
              | some runtime =>
                  runtime.registerTask childDeadline cancel expire join
            childOwned.set (some (join, release))
            pure do
              release
              childOwned.set none
        }
        let result ← try
          Std.Async.Async.block <|
            Registry.runWithDeadlineUntilAsync deadline
              (registry.authorizeRequestHeaders entry metadata) (some runtime)
        catch error =>
          pure (.error (Status.ofIOError error))
        match ← childOwned.modifyGet fun child? => (child?, none) with
        | none => pure ()
        | some (join, release) =>
            try
              Std.Async.Async.block join
            catch _ =>
              pure ()
            release
        pure result

private def authorizeEntryUntil (registry : Registry) (entry : MethodEntry)
    (metadata : Metadata) (deadline : Option Nat)
    (runtime? : Option DeadlineRuntime := none) :
    IO (Except Status (AuthorizationResult entry)) :=
  authorizeEntryUntilWithClock IO.monoNanosNow registry entry metadata deadline runtime?

namespace TestSupport

/-- Focused response-block seam used by deterministic equivalence tests and
the manual cache benchmark.  It deliberately excludes HTTP/2 frame creation
so the measurement isolates HPACK work. -/
structure ResponseHeaderBlocks where
  initial : ByteArray
  trailers : ByteArray
  state : Hpack.State

def encodeCommonResponseHeaderBlocks (state : Hpack.State) (gzip : Bool) :
    Except Status ResponseHeaderBlocks := do
  let initial ← encodeResponseHeadersBlock state gzip Metadata.empty
  let trailers ← encodeResponseTrailersBlock initial.2 Status.ok Metadata.empty
  pure { initial := initial.1, trailers := trailers.1, state := trailers.2 }

/-- Deterministic registry-selection seam. It proves the registered default
does not touch the pure-callback clock while an explicitly installed pure
authorizer receives the required bracket checks. -/
def authorizeRegistryEntryUntilWithClock (now : IO Nat) (registry : Registry)
    (entry : MethodEntry) (metadata : Metadata) (deadline : Option Nat) :
    IO (Except Status (AuthorizationResult entry)) :=
  Transport.authorizeEntryUntilWithClock now registry entry metadata deadline

end TestSupport

/-- Run only authorization for an entry selected by `preflightEarlyRequest`.
The original metadata value is passed through unchanged. -/
def authorizePreflightedEarlyRequest (registry : Registry) (state : Hpack.State)
    (streamId : Nat) (metadata : Metadata) (entry : MethodEntry)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (deadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    IO (Except Status EarlyRequestDecision) := do
  let rejectWith (status : Status) : Except Status EarlyRequestDecision :=
    match encodeUnaryResponseFrames state streamId
        { status := status, data := ByteArray.empty } maxDataFrameSize with
    | .ok encoded => .ok (.reject encoded.1 encoded.2)
    | .error encodeStatus => .error encodeStatus
  let authorizationResult ← authorizeEntryUntil registry entry metadata deadline runtime?
  match authorizationResult with
  | .ok (.accept handler) => pure (.ok (.accept { entry with handler := handler }))
  | .ok (.reject status) => pure (rejectWith status)
  | .error status => pure (rejectWith status)

/--
Validate and authorize a complete request header block.  This function is
called as soon as END_HEADERS arrives, before the connection accepts DATA for
the stream.  The registry entry for the method is looked up here, so a
successful decision carries the entry (with the authorizer's accepted
handler, which has the entry's exact shape by construction); it is retained
in stream state and used for dispatch without rerunning the authorizer.
-/
def authorizeEarlyRequest (registry : Registry) (state : Hpack.State) (streamId : Nat)
    (metadata : Metadata) (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (deadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    IO (Except Status EarlyRequestDecision) := do
  match preflightEarlyRequest registry state streamId metadata maxDataFrameSize with
  | .error status => pure (.error status)
  | .ok (.reject frames outboundHpack) => pure (.ok (.reject frames outboundHpack))
  | .ok (.accept entry _) =>
      authorizePreflightedEarlyRequest registry state streamId metadata entry
        maxDataFrameSize deadline runtime?

private def encodeServerStreamingStreamResponseFramesWithAsyncImpl
    (state : Hpack.State) (streamId : Nat)
    (response : ServerStreamingStreamResponse)
    (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false)
    (deadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status Hpack.State) := do
  if !response.status.isOk then
    match ← Registry.recvWithDeadlineUntilAsync deadline response.messages runtime? with
    | .error status =>
        finishStreamAfterTerminalFrames response.messages (some status) <| do
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
        match encodeResponseHeadersBlock state gzip response.metadata with
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
                            match ← emitMessageStreamDataFramesAsync
                                streamId maxDataFrameSize response.messages emit gzip deadline runtime? with
                            | .error status => pure (.error status)
                            | .ok streamStatus? =>
                                let finalStatus := streamStatus?.getD response.status
                                finishStreamAfterTerminalFrames response.messages streamStatus? <| do
                                  match encodeResponseTrailersBlock state finalStatus
                                      response.trailers with
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
    match encodeResponseHeadersBlock state gzip response.metadata with
    | .error status => pure (.error status)
    | .ok initialBlock =>
        let state := initialBlock.2
        match headerBlockFrames streamId initialBlock.1 false maxDataFrameSize with
        | .error status => pure (.error status)
        | .ok initialFrames =>
            match ← emitFrames emit initialFrames with
            | .error status => pure (.error status)
            | .ok () =>
                match ← emitMessageStreamDataFramesAsync
                    streamId maxDataFrameSize response.messages emit gzip deadline runtime? with
                | .error status => pure (.error status)
                | .ok streamStatus? =>
                    let finalStatus := streamStatus?.getD response.status
                    finishStreamAfterTerminalFrames response.messages streamStatus? <| do
                      match encodeResponseTrailersBlock state finalStatus response.trailers with
                      | .error status => pure (.error status)
                      | .ok trailerBlock =>
                          match headerBlockFrames streamId trailerBlock.1 true maxDataFrameSize with
                          | .error status => pure (.error status)
                          | .ok trailerFrames =>
                              match ← emitFrames emit trailerFrames with
                              | .error status => pure (.error status)
                              | .ok () => pure (.ok trailerBlock.2)

/-- The managed transport already retains each deadline-controlled receive.
For a timed standalone encoder, move that same ownership boundary out around
the whole encode operation: the receive race may report expiry promptly, while
this exact outer task keeps its child until terminal frames and stream cleanup
have run.  Normal receives unregister before the next recursive receive, so a
second registration is an invariant violation rather than an ownership
overwrite. -/
def encodeServerStreamingStreamResponseFramesWithAsync (state : Hpack.State) (streamId : Nat)
    (response : ServerStreamingStreamResponse)
    (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false)
    (deadline : Option Nat := none) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status Hpack.State) := do
  match runtime?, deadline with
  | some runtime, _ =>
      encodeServerStreamingStreamResponseFramesWithAsyncImpl state streamId response emit
        maxDataFrameSize gzip deadline (some runtime)
  | none, none =>
      encodeServerStreamingStreamResponseFramesWithAsyncImpl state streamId response emit
        maxDataFrameSize gzip none none
  | none, some deadline =>
      let childOwned ←
        IO.mkRef (none : Option (Nat × Std.Async.Async Unit × IO Unit))
      let nextChildId ← IO.mkRef 0
      let localRuntime : DeadlineRuntime := {
        externalTimer := false,
        registerTask := fun _childDeadline _cancel _expire join => do
          let id ← nextChildId.modifyGet fun next => (next, next + 1)
          let release : IO Unit := childOwned.modify fun child? =>
            match child? with
            | some (registeredId, _, _) =>
                if registeredId == id then none else child?
            | none => none
          let installed ← childOwned.modifyGet fun child? =>
            match child? with
            | none => (true, some (id, join, release))
            | some _ => (false, child?)
          if installed then
            pure release
          else
            throw (IO.userError
              "standalone streaming encoder registered overlapping deadline children")
      }
      let encoded : Except IO.Error (Except Status Hpack.State) ← try
        pure (Except.ok (← encodeServerStreamingStreamResponseFramesWithAsyncImpl
          state streamId response emit maxDataFrameSize gzip
          (some deadline) (some localRuntime)))
      catch error =>
        -- An unexpected encoder failure still cannot orphan its exact receive.
        -- Give the stream its normal cleanup signal before joining that child.
        try
          discard <| response.messages.cancel.run
        catch _ =>
          pure ()
        pure (Except.error error)
      match ← childOwned.get with
      | none => pure ()
      | some (_, join, release) =>
          try
            join
          catch _ =>
            pure ()
          release
      match encoded with
      | Except.ok result => pure result
      | Except.error error => throw error

def encodeServerStreamingStreamResponseFramesWith (state : Hpack.State) (streamId : Nat)
    (response : ServerStreamingStreamResponse)
    (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength) (gzip : Bool := false) :
    IO (Except Status Hpack.State) :=
  Std.Async.Async.block <|
    encodeServerStreamingStreamResponseFramesWithAsync
      state streamId response emit maxDataFrameSize gzip

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

def dispatchDecodedUnaryFramesWithAsync (registry : Registry) (outboundHpack : Hpack.State)
    (request : UnaryRequestFrames) (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (onResponseStream : MessageStream ByteArray -> IO (MessageStream ByteArray) := pure)
    (enableGzip : Bool := true) (runtime? : Option DeadlineRuntime := none) :
    Std.Async.Async (Except Status UnaryDispatchStateResult) := do
  let managedPreflight? := match request.authorizedEntry?, request.preflight? with
    | some _, some preflight => some preflight
    | _, _ => none
  let clientAcceptsGzip := match managedPreflight? with
    | some preflight => preflight.clientAcceptsGzip
    | none => Headers.clientAcceptsGzip request.metadata
  let gzip := enableGzip && clientAcceptsGzip
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
  let encodeStreaming (response : ServerStreamingStreamResponse) (deadline : Option Nat) :
      Std.Async.Async (Except Status UnaryDispatchStateResult) := do
    let messages ← try
      onResponseStream response.messages
    catch err =>
      return .error (Status.ofIOError err)
    let response := { response with messages := messages }
    match ← encodeServerStreamingStreamResponseFramesWithAsync
        outboundHpack request.streamId response emit maxDataFrameSize gzip deadline runtime? with
    | .error status => pure (.error status)
    | .ok outboundHpack => pure (.ok (finish outboundHpack))
  let emptyStreamingResponse (status : Status) : ServerStreamingStreamResponse := {
    messages := { recv? := pure none },
    status := status
  }
  let decompressBodyWith (usesGzip : Bool) : Except Status ByteArray :=
    Message.decompressBody usesGzip registry.maxReceiveMessageSize request.body
  let decompressBodyFromMetadata : Except Status ByteArray := do
    let usesGzip ← Headers.requestUsesGzip request.metadata
    decompressBodyWith usesGzip
  let runEntry (entry : MethodEntry) :
      Std.Async.Async (Except Status UnaryDispatchStateResult) := do
    match decompressBodyFromMetadata with
    | .error status => encodeUnary { status := status, data := ByteArray.empty }
    | .ok body =>
      match entry.dispatchHandler with
      | .unary handler =>
          match (← registry.dispatchUnaryAsync
              request.metadata body (some handler) request.deadline runtime?) with
          | .ok response => encodeUnary response
          | .error status =>
              encodeUnary { status := status, data := ByteArray.empty }
      | .serverStreaming handler =>
          match (← registry.dispatchServerStreamingStreamAsync
              request.metadata body (some handler) request.deadline runtime?) with
          | .ok (response, deadline) => encodeStreaming response deadline
          | .error status =>
              -- The handler deadline race may still own a cancelled child in
              -- `runtime?`.  This synthetic empty stream only renders the
              -- already-selected terminal status; starting another race at
              -- the expired instant would overwrite the original join handle.
              encodeStreaming (emptyStreamingResponse status) none
      | .clientStreaming handler =>
          match (← registry.dispatchClientStreamingAsync
              request.metadata body (some handler) request.deadline runtime?) with
          | .ok response => encodeUnary response
          | .error status =>
              encodeUnary { status := status, data := ByteArray.empty }
      | .bidirectionalStreaming handler =>
          match (← registry.dispatchBidirectionalStreamingStreamAsync
              request.metadata body (some handler) request.deadline runtime?) with
          | .ok (response, deadline) => encodeStreaming response deadline
          | .error status =>
              encodeStreaming (emptyStreamingResponse status) none
  let runManagedEntry (entry : MethodEntry) (preflight : Headers.RequestPreflight) :
      Std.Async.Async (Except Status UnaryDispatchStateResult) := do
    match decompressBodyWith preflight.requestUsesGzip with
    | .error status => encodeUnary { status := status, data := ByteArray.empty }
    | .ok body =>
      match entry.dispatchHandler with
      | .unary handler =>
          match (← registry.dispatchManagedUnaryAsync request.metadata body preflight
              handler request.deadline runtime?) with
          | .ok response => encodeUnary response
          | .error status =>
              encodeUnary { status := status, data := ByteArray.empty }
      | .serverStreaming handler =>
          match (← registry.dispatchManagedServerStreamingStreamAsync
              request.metadata body preflight handler request.deadline runtime?) with
          | .ok (response, deadline) => encodeStreaming response deadline
          | .error status => encodeStreaming (emptyStreamingResponse status) none
      | .clientStreaming handler =>
          match (← registry.dispatchManagedClientStreamingAsync request.metadata body
              preflight handler request.deadline runtime?) with
          | .ok response => encodeUnary response
          | .error status =>
              encodeUnary { status := status, data := ByteArray.empty }
      | .bidirectionalStreaming handler =>
          match (← registry.dispatchManagedBidirectionalStreamingStreamAsync
              request.metadata body preflight handler request.deadline runtime?) with
          | .ok (response, deadline) => encodeStreaming response deadline
          | .error status => encodeStreaming (emptyStreamingResponse status) none
  -- A retained entry is a capability produced only after the managed
  -- connection validated and authorized END_HEADERS.  Repeating the complete
  -- validation here reparses grpc-timeout on every timed call and cannot
  -- change the decision.  Standalone decoded requests carry `none` and retain
  -- the original validation and HTTP 415 precedence below.
  match request.authorizedEntry?, request.preflight? with
  | some entry, some preflight => runManagedEntry entry preflight
  | _, _ =>
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
            match registry.findEntry? method with
            | none =>
                match decompressBodyFromMetadata with
                | .error status =>
                    encodeUnary { status := status, data := ByteArray.empty }
                | .ok _ =>
                    encodeUnary {
                      status := Status.unimplemented s!"unknown gRPC method {method.path}",
                      data := ByteArray.empty
                    }
            | some entry =>
              match ← authorizeEntryUntil registry entry request.metadata request.deadline with
              | .error status =>
                  encodeUnary { status := status, data := ByteArray.empty }
              | .ok (.reject status) =>
                  encodeUnary { status := status, data := ByteArray.empty }
              | .ok (.accept handler) => runEntry { entry with handler := handler }

def dispatchDecodedUnaryFramesWith (registry : Registry) (outboundHpack : Hpack.State)
    (request : UnaryRequestFrames) (emit : Array Frame -> IO Unit)
    (maxDataFrameSize : Nat := defaultMaxFramePayloadLength)
    (onResponseStream : MessageStream ByteArray -> IO Unit := fun _ => pure ())
    (enableGzip : Bool := true) : IO (Except Status UnaryDispatchStateResult) :=
  Std.Async.Async.block <|
    dispatchDecodedUnaryFramesWithAsync registry outboundHpack request emit
      maxDataFrameSize (fun stream => do onResponseStream stream; pure stream) enableGzip

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
