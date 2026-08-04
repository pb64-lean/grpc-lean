module

public import Std.Sync.Mutex
public import Grpc.Http2.Frame
public import Grpc.Http2.Grpc

public section

namespace Grpc
namespace Http2
namespace Connection

structure StreamState where
  streamId : Nat
  frames : Array Frame := #[]
  requestMetadata : Option Metadata := none
  /-- The registry entry accepted by request-header authorization at
  END_HEADERS.  `none` means the header block has not been authorized, so the
  stream must not dispatch. -/
  authorizedEntry? : Option MethodEntry := none
  deriving Inhabited

structure OutboundStreamWindow where
  streamId : Nat
  window : Int
  deriving Inhabited

structure InboundStreamWindow where
  streamId : Nat
  window : Nat
  deriving Inhabited

structure ActiveRequestStream where
  streamId : Nat
  producer : MessageStream.Producer ByteArray
  decodeState : Message.DecodeState := {}
  contentLength : Option Nat := none
  receivedBodyBytes : Nat := 0
  usesGzip : Bool := false
  /-- Wire size of each decoded-but-unconsumed message; the matching stream
  WINDOW_UPDATE is granted only when the handler consumes the message. -/
  pendingRequestCredits : Array Nat := #[]

structure ActiveDispatch where
  streamId : Nat
  task : Task (Except IO.Error Unit)
  cancelled : IO.Ref Bool
  requestStreamCancel : IO.Ref (Option (IO Unit))
  responseStreamCancel : IO.Ref (Option (IO Unit))

def initialFlowControlWindow : Nat := 65535

/-- Advertised per-stream receive window (`SETTINGS_INITIAL_WINDOW_SIZE`). Set well
above the default gRPC max message size so a single message always fits within one
stream window — required for deadlock-free credit-on-consume flow control, where the
stream window is only replenished as the handler consumes whole messages. -/
def defaultStreamWindow : Nat := 4194304

/-- Upper bound on a reassembled HEADERS + CONTINUATION header block. -/
def maxHeaderBlockSize : Nat := 1048576

/-- Upper bound on buffered outbound frame payload bytes awaiting flow-control window. -/
def maxPendingOutboundBytes : Nat := 4194304

structure State where
  prefaceReceived : Bool := false
  clientSettingsReceived : Bool := false
  prefaceBuffer : ByteArray := ByteArray.empty
  decoder : Frame.DecodeState := {}
  hpack : Hpack.State := {}
  outboundHpack : Hpack.State := {}
  lastClientStreamId : Nat := 0
  outboundGoAwayLastStreamId : Option Nat := none
  outboundConnectionWindow : Nat := initialFlowControlWindow
  outboundInitialStreamWindow : Nat := initialFlowControlWindow
  outboundMaxFramePayloadLength : Nat := defaultMaxFramePayloadLength
  inboundMaxFramePayloadLength : Nat := defaultMaxFramePayloadLength
  inboundConnectionWindow : Nat := initialFlowControlWindow
  inboundInitialStreamWindow : Nat := initialFlowControlWindow
  inboundMaxConcurrentStreams : Option Nat := none
  inboundMaxHeaderListSize : Option Nat := none
  inboundStreamWindows : Array InboundStreamWindow := #[]
  outboundStreamWindows : Array OutboundStreamWindow := #[]
  pendingOutbound : Array Frame := #[]
  streams : Array StreamState := #[]
  ignoredInboundStreams : Array Nat := #[]
  activeRequestStreams : Array ActiveRequestStream := #[]
  activeDispatches : Array ActiveDispatch := #[]
  pendingKeepalivePing : Option ByteArray := none
  deriving Inhabited

def serverSettingsFrame (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : Except Status Frame :=
  let settings := #[]
  let settings := match maxConcurrentStreams with
    | none => settings
    | some value => settings.push { id := SettingId.maxConcurrentStreams, value := value }
  let settings := match maxHeaderListSize with
    | none => settings
    | some value => settings.push { id := SettingId.maxHeaderListSize, value := value }
  let settings :=
    if initialWindowSize == initialFlowControlWindow then
      settings
    else
      settings.push { id := SettingId.initialWindowSize, value := initialWindowSize }
  Settings.frame settings

def initialState (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : State :=
  {
    (default : State) with
    inboundMaxConcurrentStreams := maxConcurrentStreams,
    inboundMaxHeaderListSize := maxHeaderListSize,
    inboundInitialStreamWindow := initialWindowSize
  }

def isDrainedAfterOutboundGoAway (state : State) : Bool :=
  match state.outboundGoAwayLastStreamId with
  | none => false
  | some _ =>
      state.streams.isEmpty
        && state.ignoredInboundStreams.isEmpty
        && state.activeRequestStreams.isEmpty
        && state.activeDispatches.isEmpty
        && state.pendingOutbound.isEmpty

def serverPrefaceBytes (maxConcurrentStreams : Option Nat := none)
    (maxHeaderListSize : Option Nat := none)
    (initialWindowSize : Nat := defaultStreamWindow) : Except Status ByteArray := do
  let frame ← serverSettingsFrame maxConcurrentStreams maxHeaderListSize initialWindowSize
  Frame.encode frame

private def findStream? (streams : Array StreamState) (streamId : Nat) : Option StreamState :=
  streams.find? (fun stream => stream.streamId == streamId)

private def removeStream (streams : Array StreamState) (streamId : Nat) : Array StreamState :=
  streams.filter (fun stream => stream.streamId != streamId)

private def appendStreamFrame (streams : Array StreamState) (frame : Frame) : Array StreamState :=
  let streamId := frame.header.streamId
  let stream := match findStream? streams streamId with
    | some stream => { stream with frames := stream.frames.push frame }
    | none => { streamId := streamId, frames := #[frame] }
  (removeStream streams streamId).push stream

private def replaceStream (streams : Array StreamState) (stream : StreamState) : Array StreamState :=
  (removeStream streams stream.streamId).push stream

private def findOutboundStreamWindow? (windows : Array OutboundStreamWindow) (streamId : Nat) :
    Option OutboundStreamWindow :=
  windows.find? (fun window => window.streamId == streamId)

private def removeOutboundStreamWindow (windows : Array OutboundStreamWindow) (streamId : Nat) :
    Array OutboundStreamWindow :=
  windows.filter (fun window => window.streamId != streamId)

private def findInboundStreamWindow? (windows : Array InboundStreamWindow) (streamId : Nat) :
    Option InboundStreamWindow :=
  windows.find? (fun window => window.streamId == streamId)

private def removeInboundStreamWindow (windows : Array InboundStreamWindow) (streamId : Nat) :
    Array InboundStreamWindow :=
  windows.filter (fun window => window.streamId != streamId)

private def outboundStreamWindow (state : State) (streamId : Nat) : Int :=
  match findOutboundStreamWindow? state.outboundStreamWindows streamId with
  | some window => window.window
  | none => Int.ofNat state.outboundInitialStreamWindow

private def inboundStreamWindow (state : State) (streamId : Nat) : Nat :=
  match findInboundStreamWindow? state.inboundStreamWindows streamId with
  | some window => window.window
  | none => state.inboundInitialStreamWindow

private def setOutboundStreamWindow (state : State) (streamId : Nat) (window : Int) : State :=
  {
    state with
    outboundStreamWindows := (removeOutboundStreamWindow state.outboundStreamWindows streamId).push {
      streamId := streamId,
      window := window
    }
  }

private def setInboundStreamWindow (state : State) (streamId window : Nat) : State :=
  {
    state with
    inboundStreamWindows := (removeInboundStreamWindow state.inboundStreamWindows streamId).push {
      streamId := streamId,
      window := window
    }
  }

private def replaceFirstFrame (frames : Array Frame) (frame : Frame) : Array Frame :=
  #[frame].append (frames.extract 1 frames.size)

private def popFirstFrame (frames : Array Frame) : Array Frame :=
  frames.extract 1 frames.size

private def removePendingOutboundForStream (frames : Array Frame) (streamId : Nat) : Array Frame :=
  frames.filter (fun frame => frame.header.streamId != streamId)

private def activeDispatchesForStream (dispatches : Array ActiveDispatch) (streamId : Nat) :
    Array ActiveDispatch :=
  dispatches.filter (fun dispatch => dispatch.streamId == streamId)

private def removeActiveDispatchesForStream (dispatches : Array ActiveDispatch) (streamId : Nat) :
    Array ActiveDispatch :=
  dispatches.filter (fun dispatch => dispatch.streamId != streamId)

private def containsStreamId (streamIds : Array Nat) (streamId : Nat) : Bool :=
  streamIds.any (· == streamId)

private def removeStreamId (streamIds : Array Nat) (streamId : Nat) : Array Nat :=
  streamIds.filter (· != streamId)

private def pushUniqueStreamId (streamIds : Array Nat) (streamId : Nat) : Array Nat :=
  if containsStreamId streamIds streamId then
    streamIds
  else
    streamIds.push streamId

private def activeInboundStreamIds (state : State) : Array Nat :=
  let streamIds := state.streams.foldl
    (init := #[])
    (fun ids stream => pushUniqueStreamId ids stream.streamId)
  let streamIds := state.ignoredInboundStreams.foldl
    (init := streamIds)
    (fun ids streamId => pushUniqueStreamId ids streamId)
  state.activeDispatches.foldl
    (init := streamIds)
    (fun ids dispatch => pushUniqueStreamId ids dispatch.streamId)

private def activeInboundStreamCount (state : State) : Nat :=
  activeInboundStreamIds state |>.size

private def findActiveRequestStream? (streams : Array ActiveRequestStream) (streamId : Nat) :
    Option ActiveRequestStream :=
  streams.find? (fun stream => stream.streamId == streamId)

private def removeActiveRequestStream (streams : Array ActiveRequestStream) (streamId : Nat) :
    Array ActiveRequestStream :=
  streams.filter (fun stream => stream.streamId != streamId)

private def replaceActiveRequestStream (streams : Array ActiveRequestStream)
    (stream : ActiveRequestStream) : Array ActiveRequestStream :=
  (removeActiveRequestStream streams stream.streamId).push stream

private def removeOutboundStreamState (state : State) (streamId : Nat) : State :=
  {
    state with
    outboundStreamWindows := removeOutboundStreamWindow state.outboundStreamWindows streamId,
    pendingOutbound := removePendingOutboundForStream state.pendingOutbound streamId,
    activeDispatches := removeActiveDispatchesForStream state.activeDispatches streamId
  }

private def removeInboundStreamState (state : State) (streamId : Nat) : State :=
  {
    state with
    inboundStreamWindows := removeInboundStreamWindow state.inboundStreamWindows streamId,
    ignoredInboundStreams := removeStreamId state.ignoredInboundStreams streamId,
    activeRequestStreams := removeActiveRequestStream state.activeRequestStreams streamId
  }

private def ignoreInboundStreamBody (state : State) (streamId : Nat) : State :=
  {
    state with
    streams := removeStream state.streams streamId,
    ignoredInboundStreams := pushUniqueStreamId state.ignoredInboundStreams streamId
  }

private def isClientStreamId (streamId : Nat) : Bool :=
  streamId % 2 == 1

private def requireClientStreamId (streamId : Nat) (frameName : String) : Except Status Unit := do
  if streamId == 0 then
    throw (Status.internal s!"HTTP/2 {frameName} frame must use a stream id")
  if !isClientStreamId streamId then
    throw (Status.internal s!"HTTP/2 {frameName} frame uses a server-initiated stream id")

private def requireNewClientStreamId (state : State) (streamId : Nat) : Except Status Unit := do
  requireClientStreamId streamId "HEADERS"
  if streamId <= state.lastClientStreamId then
    throw (Status.internal "HTTP/2 client stream id must increase monotonically")

private def refusedStreamFrame (streamId : Nat) : Except Status Frame :=
  RstStream.frame streamId ErrorCode.refusedStream

private def rejectNewStreamAfterOutboundGoAway? (state : State) (streamId : Nat) :
    Except Status (Option Frame) := do
  match state.outboundGoAwayLastStreamId with
  | none => pure none
  | some lastStreamId =>
      if streamId > lastStreamId then
        some <$> refusedStreamFrame streamId
      else
        pure none

private def requireInboundStreamCapacity (state : State) : Except Status Unit := do
  match state.inboundMaxConcurrentStreams with
  | none => pure ()
  | some limit =>
      if activeInboundStreamCount state >= limit then
        throw (Status.internal s!"HTTP/2 SETTINGS_MAX_CONCURRENT_STREAMS exceeded: {limit}")
      else
        pure ()

private def headerComplete (frame : Frame) : Bool :=
  frame.header.frameType == FrameType.headers
    && FrameFlag.has frame.header.flags FrameFlag.endHeaders

private def streamHeaderComplete (stream : StreamState) : Bool :=
  match stream.frames[0]? with
  | some frame => headerComplete frame
  | none => false

private def pendingHeaderStream? (streams : Array StreamState) : Option Nat :=
  streams.findSome? fun stream =>
    match stream.frames[0]? with
    | some frame =>
        if frame.header.frameType == FrameType.headers && !headerComplete frame then
          some stream.streamId
        else
          none
    | none => none

private def appendContinuationFrame (streams : Array StreamState) (frame : Frame) :
    Except Status (Array StreamState) := do
  requireClientStreamId frame.header.streamId "CONTINUATION"
  let stream ← match findStream? streams frame.header.streamId with
    | some stream => pure stream
    | none => throw (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS")
  let headersFrame ← match stream.frames[0]? with
    | some headersFrame => pure headersFrame
    | none => throw (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS")
  if headersFrame.header.frameType != FrameType.headers then
    throw (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS")
  if headerComplete headersFrame then
    throw (Status.internal "unexpected HTTP/2 CONTINUATION after END_HEADERS")
  let payload := headersFrame.payload.append frame.payload
  if payload.size > maxHeaderBlockSize then
    throw (Status.internal "HTTP/2 header block exceeds the maximum supported size")
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
  pure <| replaceStream streams {
    stream with frames := replaceFirstFrame stream.frames headersFrame
  }

private def clearFlag (flags flag : UInt8) : UInt8 :=
  if FrameFlag.has flags flag then
    UInt8.ofNat (flags.toNat - flag.toNat)
  else
    flags

private def stripPadding (frame : Frame) (frameName : String) : Except Status Frame := do
  if !FrameFlag.has frame.header.flags FrameFlag.padded then
    pure frame
  else if frame.payload.size < 1 then
    throw (Status.internal s!"HTTP/2 padded {frameName} frame is missing the pad length octet")
  else
    let padLength := frame.payload[0]!.toNat
    let body := frame.payload.extract 1 frame.payload.size
    if padLength > body.size then
      throw (Status.internal s!"HTTP/2 {frameName} frame padding exceeds the payload length")
    else
      let payload := body.extract 0 (body.size - padLength)
      pure {
        frame with
        header := {
          frame.header with
          length := payload.size,
          flags := clearFlag frame.header.flags FrameFlag.padded
        },
        payload := payload
      }

private def stripHeadersPriority (frame : Frame) : Except Status Frame := do
  if !FrameFlag.has frame.header.flags FrameFlag.priority then
    pure frame
  else if frame.payload.size < 5 then
    throw (Status.internal "HTTP/2 HEADERS frame priority section is truncated")
  else
    let rawDependency :=
      frame.payload[0]!.toNat * 16777216
        + frame.payload[1]!.toNat * 65536
        + frame.payload[2]!.toNat * 256
        + frame.payload[3]!.toNat
    if rawDependency % (maxStreamId + 1) == frame.header.streamId then
      throw (Status.internal "HTTP/2 PRIORITY dependency cannot reference the same stream")
    let payload := frame.payload.extract 5 frame.payload.size
    pure {
      frame with
      header := {
        frame.header with
        length := payload.size,
        flags := clearFlag frame.header.flags FrameFlag.priority
      },
      payload := payload
    }

/-- Strip the optional padding and priority sections from an inbound HEADERS frame so
downstream header-block handling sees only the header block fragment. Flow control does
not apply to HEADERS, so this can run before any window accounting. -/
private def normalizeHeadersFrame (frame : Frame) : Except Status Frame := do
  stripHeadersPriority (← stripPadding frame "HEADERS")

private def dataWindowUpdates (frame : Frame) : Except Status (Array Frame) := do
  if frame.payload.isEmpty then
    pure #[]
  else
    let connectionUpdate ← WindowUpdate.frame 0 frame.payload.size
    let streamUpdate ← WindowUpdate.frame frame.header.streamId frame.payload.size
    pure #[connectionUpdate, streamUpdate]

private def dataFrameWithPayload (frame : Frame) (payload : ByteArray) : Frame :=
  { frame with header := { frame.header with length := payload.size }, payload := payload }

private def consumeInboundDataWindow (state : State) (frame : Frame) : Except Status State := do
  let size := frame.payload.size
  if size == 0 then
    pure state
  else if size > state.inboundConnectionWindow then
    throw (Status.internal "HTTP/2 DATA frame exceeds connection flow-control window")
  else
    let streamWindow := inboundStreamWindow state frame.header.streamId
    if size > streamWindow then
      throw (Status.internal "HTTP/2 DATA frame exceeds stream flow-control window")
    else
      let state := {
        state with inboundConnectionWindow := state.inboundConnectionWindow - size
      }
      pure (setInboundStreamWindow state frame.header.streamId (streamWindow - size))

private def replenishInboundConnectionWindow (state : State) (size : Nat) : State :=
  if size == 0 then
    state
  else
    { state with inboundConnectionWindow := state.inboundConnectionWindow + size }

private def replenishInboundStreamWindowBy (state : State) (streamId size : Nat) : State :=
  if size == 0 then
    state
  else
    setInboundStreamWindow state streamId (inboundStreamWindow state streamId + size)

/-- Window updates for DATA on a streaming request: the connection window is
credited for the whole frame immediately (so one stalled stream cannot starve
the connection), while the stream window is only credited for padding — the
payload's stream credit is granted when the handler consumes each message. -/
private def activeDataWindowUpdates (streamId originalSize paddingBytes : Nat) :
    Except Status (Array Frame) := do
  let updates := #[]
  let updates ←
    if originalSize == 0 then
      pure updates
    else do
      let connectionUpdate ← WindowUpdate.frame 0 originalSize
      pure (updates.push connectionUpdate)
  if paddingBytes == 0 then
    pure updates
  else do
    let streamUpdate ← WindowUpdate.frame streamId paddingBytes
    pure (updates.push streamUpdate)

private def replenishInboundDataWindow (state : State) (frame : Frame) : State :=
  let size := frame.payload.size
  if size == 0 then
    state
  else
    let streamWindow := inboundStreamWindow state frame.header.streamId
    let state := { state with inboundConnectionWindow := state.inboundConnectionWindow + size }
    setInboundStreamWindow state frame.header.streamId (streamWindow + size)

private def cleanupOutboundIfEndStream (state : State) (frame : Frame) : State :=
  if FrameFlag.has frame.header.flags FrameFlag.endStream then
    { state with outboundStreamWindows := removeOutboundStreamWindow state.outboundStreamWindows frame.header.streamId }
  else
    state

private theorem cleanupOutboundIfEndStream_pendingOutbound (state : State) (frame : Frame) :
    (cleanupOutboundIfEndStream state frame).pendingOutbound = state.pendingOutbound := by
  unfold cleanupOutboundIfEndStream
  split <;> rfl

private theorem popFirstFrame_size_lt {frames : Array Frame} {frame : Frame}
    (h : frames[0]? = some frame) : (popFirstFrame frames).size < frames.size := by
  have hpos : 0 < frames.size := (Array.getElem?_eq_some_iff.mp h).1
  simp only [popFirstFrame, Array.size_extract]
  omega

private def flushOutbound (state : State) (emitted : Array Frame := #[]) :
    State × Array Frame :=
  match h : state.pendingOutbound[0]? with
  | none => (state, emitted)
  | some frame =>
      if frame.header.frameType != FrameType.data then
        let state := { state with pendingOutbound := popFirstFrame state.pendingOutbound }
        let state := cleanupOutboundIfEndStream state frame
        flushOutbound state (emitted.push frame)
      else
        let streamWindow := outboundStreamWindow state frame.header.streamId
        let streamWindowAvailable := streamWindow.toNat
        let available := Nat.min state.outboundConnectionWindow streamWindowAvailable
        if available == 0 then
          (state, emitted)
        else
          let sendSize := Nat.min available frame.payload.size
          let sendPayload := frame.payload.extract 0 sendSize
          let sentFrame := dataFrameWithPayload frame sendPayload
          let state := {
            state with
            outboundConnectionWindow := state.outboundConnectionWindow - sendSize
          }
          let state := setOutboundStreamWindow state frame.header.streamId
            (streamWindow - Int.ofNat sendSize)
          if sendSize == frame.payload.size then
            let state := { state with pendingOutbound := popFirstFrame state.pendingOutbound }
            let state := cleanupOutboundIfEndStream state sentFrame
            flushOutbound state (emitted.push sentFrame)
          else
            let remaining := frame.payload.extract sendSize frame.payload.size
            let remainingFrame := dataFrameWithPayload frame remaining
            let state := {
              state with pendingOutbound := replaceFirstFrame state.pendingOutbound remainingFrame
            }
            (state, emitted.push sentFrame)
  termination_by state.pendingOutbound.size
  decreasing_by
    all_goals
      simp only [cleanupOutboundIfEndStream_pendingOutbound, setOutboundStreamWindow]
      exact popFirstFrame_size_lt h

private def queueOutbound (state : State) (frames : Array Frame) : State × Array Frame :=
  flushOutbound { state with pendingOutbound := state.pendingOutbound.append frames }

private def addOutboundConnectionWindow (kind : String) (current increment : Nat) :
    Except Status Nat := do
  let updated := current + increment
  if updated > maxStreamId then
    throw (Status.internal s!"HTTP/2 {kind} flow-control window exceeds 31-bit length")
  else
    pure updated

private def addOutboundStreamWindow (kind : String) (current : Int) (increment : Nat) :
    Except Status Int := do
  let updated := current + Int.ofNat increment
  if updated > Int.ofNat maxStreamId then
    throw (Status.internal s!"HTTP/2 {kind} flow-control window exceeds 31-bit length")
  else
    pure updated

private def applyWindowUpdate (state : State) (frame : Frame) : Except Status State := do
  let increment ← WindowUpdate.decode frame
  if frame.header.streamId == 0 then
    let window ← addOutboundConnectionWindow "connection" state.outboundConnectionWindow increment
    pure { state with outboundConnectionWindow := window }
  else
    let window := outboundStreamWindow state frame.header.streamId
    let window ← addOutboundStreamWindow "stream" window increment
    pure (setOutboundStreamWindow state frame.header.streamId window)

private def processWindowUpdate (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  if frame.header.streamId != 0 then
    requireClientStreamId frame.header.streamId "WINDOW_UPDATE"
  let state ← applyWindowUpdate state frame
  pure (flushOutbound state)

private def adjustWindow (oldInitial newInitial : Nat) (current : Int) : Int :=
  current + Int.ofNat newInitial - Int.ofNat oldInitial

private def applyInitialWindowSize (state : State) (value : Nat) : Except Status State := do
  if value > maxStreamId then
    throw (Status.internal "HTTP/2 SETTINGS_INITIAL_WINDOW_SIZE exceeds 31-bit length")
  let oldInitial := state.outboundInitialStreamWindow
  let windows ← state.outboundStreamWindows.mapM fun window => do
    let adjusted := adjustWindow oldInitial value window.window
    if adjusted > Int.ofNat maxStreamId then
      throw (Status.internal "HTTP/2 stream flow-control window exceeds 31-bit length")
    else
      pure { window with window := adjusted }
  pure {
    state with
    outboundInitialStreamWindow := value,
    outboundStreamWindows := windows
  }

private def applyMaxFrameSize (state : State) (value : Nat) : Except Status State := do
  if value < defaultMaxFramePayloadLength || value > maxFramePayloadLength then
    throw (Status.internal "HTTP/2 SETTINGS_MAX_FRAME_SIZE is outside the allowed range")
  pure { state with outboundMaxFramePayloadLength := value }

private def applyPeerSetting (state : State) (setting : Setting) : Except Status State := do
  match setting.id with
  | .headerTableSize =>
      pure { state with outboundHpack := Hpack.setMaxAllowedSize state.outboundHpack setting.value }
  | .enablePush =>
      if setting.value == 0 || setting.value == 1 then
        pure state
      else
        throw (Status.internal "HTTP/2 SETTINGS_ENABLE_PUSH must be 0 or 1")
  | .initialWindowSize =>
      applyInitialWindowSize state setting.value
  | .maxFrameSize =>
      applyMaxFrameSize state setting.value
  | .maxConcurrentStreams =>
      pure state
  | .maxHeaderListSize =>
      pure state
  | .unknown _ =>
      pure state

private def applyPeerSettings (state : State) (settings : Array Setting) : Except Status State :=
  settings.foldlM (init := state) applyPeerSetting

private def consumePreface (state : State) (chunk : ByteArray) : Except Status (State × ByteArray) := do
  if state.prefaceReceived then
    pure (state, chunk)
  else
    let buffered := state.prefaceBuffer.append chunk
    if buffered.size < connectionPreface.size then
      pure ({ state with prefaceBuffer := buffered }, ByteArray.empty)
    else
      let seenPreface := buffered.extract 0 connectionPreface.size
      if seenPreface != connectionPreface then
        throw (Status.internal "invalid HTTP/2 client connection preface")
      else
        pure (
          { state with prefaceReceived := true, prefaceBuffer := ByteArray.empty },
          buffered.extract connectionPreface.size buffered.size
        )

private def emitFrameBatch (emit : Array Frame -> IO Unit) (frames : Array Frame) :
    IO (Except Status Unit) := do
  if frames.isEmpty then
    pure (.ok ())
  else
    try
      emit frames
      pure (.ok ())
    catch err =>
      pure (.error (Status.ofIOError err))

private def emitResultFrames (emit : Array Frame -> IO Unit)
    (result : Except Status (State × Array Frame)) : IO (Except Status State) := do
  match result with
  | .error status => pure (.error status)
  | .ok (state, frames) =>
      match ← emitFrameBatch emit frames with
      | .error status => pure (.error status)
      | .ok () => pure (.ok state)

private structure DetachedDispatch where
  request : Transport.UnaryRequestFrames
  outboundHpack : Hpack.State
  maxDataFrameSize : Nat

/-- The dispatch family for a request whose body is fed to the handler
incrementally, carrying the authorized handler at its exact shape. -/
private inductive RequestStreamingKind where
  | clientStreaming (handler : ClientStreamingStreamHandler)
  | bidirectionalStreaming (handler : BidirectionalStreamingStreamHandler)

private structure RequestStreamingDispatch where
  streamId : Nat
  metadata : Metadata
  outboundHpack : Hpack.State
  maxDataFrameSize : Nat
  kind : RequestStreamingKind
  contentLength : Option Nat := none
  requestError : Option Status := none
  closeImmediately : Bool := false
  usesGzip : Bool := false

private structure RequestStreamFeed where
  producer : MessageStream.Producer ByteArray
  messages : Array ByteArray := #[]
  error : Option Status := none
  close : Bool := false

private structure SharedFrameResult where
  emitted : Array Frame := #[]
  detached : Option DetachedDispatch := none
  requestStreaming : Option RequestStreamingDispatch := none
  requestFeeds : Array RequestStreamFeed := #[]
  cancelDispatches : Array ActiveDispatch := #[]

/-- Incremental request-body dispatch applies exactly to entries whose shape
consumes a `MessageStream`; aggregate shapes buffer the body instead. -/
private def requestStreamingKind? (entry : MethodEntry) : Option RequestStreamingKind :=
  match entry with
  | { shape := .clientStreamingStream, handler, .. } => some (.clientStreaming handler)
  | { shape := .bidirectionalStreamingStream, handler, .. } =>
      some (.bidirectionalStreaming handler)
  | _ => none

private def requestStreamingDispatchForStream? (state : State)
    (streamId : Nat) : Except Status (State × Option RequestStreamingDispatch) := do
  let stream ← match findStream? state.streams streamId with
    | some stream => pure stream
    | none => throw (Status.internal s!"unknown HTTP/2 stream {streamId}")
  let headersFrame ← match stream.frames[0]? with
    | some frame => pure frame
    | none => throw (Status.internal "missing HTTP/2 HEADERS frame")
  if !headerComplete headersFrame then
    pure (state, none)
  else
    let entry ← match stream.authorizedEntry? with
      | some entry => pure entry
      | none =>
          throw (Status.internal "request body dispatch attempted before header authorization")
    let metadata ← match stream.requestMetadata with
      | some metadata => pure metadata
      | none => throw (Status.internal "authorized request metadata was not retained")
    match requestStreamingKind? entry with
    | none => pure (state, none)
    | some kind =>
        let contentLength ← Headers.contentLength? metadata
        let usesGzip ← Headers.requestUsesGzip metadata
        let closeImmediately := FrameFlag.has headersFrame.header.flags FrameFlag.endStream
        let requestError :=
          if closeImmediately then
            match Headers.validateContentLength metadata 0 with
            | .ok () => none
            | .error status => some status
          else
            none
        let state := {
          state with
          streams :=
            if closeImmediately then
              removeStream state.streams streamId
            else
              state.streams
        }
        let state :=
          if closeImmediately then
            removeInboundStreamState state streamId
          else
            state
        pure (state, some {
          streamId := streamId,
          metadata := metadata,
          outboundHpack := state.outboundHpack,
          maxDataFrameSize := state.outboundMaxFramePayloadLength,
          kind := kind,
          contentLength := contentLength,
          requestError := requestError,
          closeImmediately := closeImmediately,
          usesGzip := usesGzip
        })

/-- Pure state transition for a request rejected at completed request
headers: the buffered stream is dropped and the stream id is either forgotten
entirely (the request already carried END_STREAM) or put in drain-only mode
so later DATA is consumed without dispatch.  See the authorization-before-body
groundwork section at the end of this file for the properties proved about
this transition. -/
def rejectStreamAtHeaders (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) (endStream : Bool) : State :=
  let state := {
    state with
    hpack := inboundHpack,
    outboundHpack := outboundHpack,
    streams := removeStream state.streams streamId
  }
  if endStream then
    removeInboundStreamState state streamId
  else
    ignoreInboundStreamBody state streamId

private def authorizeRequestHeadersForStream (registry : Registry) (state : State)
    (streamId : Nat) : IO (Except Status (State × Option (Array Frame))) := do
  let decoded : Except Status (StreamState × Frame × Transport.RequestHeadersFrames) := do
    let stream ← match findStream? state.streams streamId with
      | some stream => pure stream
      | none => throw (Status.internal s!"unknown HTTP/2 stream {streamId}")
    let headersFrame ← match stream.frames[0]? with
      | some frame => pure frame
      | none => throw (Status.internal "missing HTTP/2 HEADERS frame")
    if !headerComplete headersFrame then
      throw (Status.internal "request header authorization ran before END_HEADERS")
    let headers ← Transport.decodeRequestHeadersFrame
      state.hpack headersFrame state.inboundMaxHeaderListSize
    pure (stream, headersFrame, headers)
  match decoded with
  | .error status => pure (.error status)
  | .ok (stream, _headersFrame, headers) =>
    match ← Transport.authorizeEarlyRequest registry state.outboundHpack streamId
        headers.metadata state.outboundMaxFramePayloadLength with
    | .error status => pure (.error status)
    | .ok (.accept entry) =>
        let stream := {
          stream with
          requestMetadata := some headers.metadata,
          authorizedEntry? := some entry
        }
        pure (.ok ({
          state with
          hpack := headers.hpack,
          streams := replaceStream state.streams stream
        }, none))
    | .ok (.reject frames outboundHpack) =>
        pure (.ok (rejectStreamAtHeaders state streamId
          headers.hpack outboundHpack headers.endStream, some frames))

private def earlyRequestRejectionForStream? (registry : Registry) (state : State) (streamId : Nat) :
    IO (Except Status (State × Option SharedFrameResult)) := do
  match ← authorizeRequestHeadersForStream registry state streamId with
  | .error status => pure (.error status)
  | .ok (state, none) => pure (.ok (state, none))
  | .ok (state, some frames) => pure (.ok (state, some { emitted := frames }))

private def processIgnoredInboundData (state : State) (frame : Frame) :
    Except Status (State × Array Frame) := do
  let state ← consumeInboundDataWindow state frame
  let updates ← dataWindowUpdates frame
  let state := replenishInboundDataWindow state frame
  let frame ← stripPadding frame "DATA"
  discard <| Transport.normalizeDataFrame frame
  let state :=
    if FrameFlag.has frame.header.flags FrameFlag.endStream then
      removeInboundStreamState state frame.header.streamId
    else
      state
  pure (state, updates)

private def decodeActiveRequestData (registry : Registry) (active : ActiveRequestStream)
    (frame : Frame) : Except Status (ActiveRequestStream × Array ByteArray × Bool) := do
  let receivedBodyBytes := active.receivedBodyBytes + frame.payload.size
  match active.contentLength with
  | none => pure ()
  | some expected =>
      if receivedBodyBytes > expected then
        throw (Status.invalidArgument s!"content-length {expected} is smaller than received request body size {receivedBodyBytes}")
      else
        pure ()
  let decoded ← Message.decodeChunkWithLimit registry.maxReceiveMessageSize
    active.decodeState frame.payload
  let credits := decoded.messages.map fun message => Message.prefixLength + message.data.size
  let maxDecompressedSize := registry.maxReceiveMessageSize.getD Message.defaultMaxDecompressedSize
  let messages ← decoded.messages.mapM fun message => do
    let message ← Message.decompress active.usesGzip maxDecompressedSize message
    pure message.data
  let endStream := FrameFlag.has frame.header.flags FrameFlag.endStream
  if endStream && !decoded.buffered.isEmpty then
    throw (Status.internal "incomplete gRPC message")
  match active.contentLength with
  | none => pure ()
  | some expected =>
      if endStream && receivedBodyBytes != expected then
        throw (Status.invalidArgument s!"content-length {expected} does not match request body size {receivedBodyBytes}")
      else
        pure ()
  pure ({
      active with
      decodeState := { buffered := decoded.buffered },
      receivedBodyBytes := receivedBodyBytes,
      pendingRequestCredits := active.pendingRequestCredits.append credits
    },
    messages,
    endStream)

private def authorizedUnaryRequestForStream (state : State) (stream : StreamState) :
    Except Status Transport.UnaryRequestFrames := do
  let entry ← match stream.authorizedEntry? with
    | some entry => pure entry
    | none =>
        throw (Status.internal "request body dispatch attempted before header authorization")
  let metadata ← match stream.requestMetadata with
    | some metadata => pure metadata
    | none => throw (Status.internal "authorized request metadata was not retained")
  let body ← (stream.frames.extract 1 stream.frames.size).foldlM
    (init := ByteArray.empty) fun body frame => do
      if frame.header.streamId != stream.streamId then
        throw (Status.internal "HTTP/2 request frames changed stream id")
      if frame.header.frameType != FrameType.data then
        throw (Status.internal "expected HTTP/2 DATA frame")
      let frame ← Transport.normalizeDataFrame frame
      pure (body.append frame.payload)
  pure {
    streamId := stream.streamId,
    metadata := metadata,
    body := body,
    hpack := state.hpack,
    authorizedEntry? := some entry
  }

private def detachStreamForDispatch (state : State) (streamId : Nat) :
    Except Status (State × DetachedDispatch) := do
  let stream ← match findStream? state.streams streamId with
    | some stream => pure stream
    | none => throw (Status.internal s!"unknown HTTP/2 stream {streamId}")
  let request ← authorizedUnaryRequestForStream state stream
  let state := {
    state with
    streams := removeStream state.streams streamId
  }
  let state := removeInboundStreamState state streamId
  pure (state, {
    request := request,
    outboundHpack := state.outboundHpack,
    maxDataFrameSize := state.outboundMaxFramePayloadLength
  })

private def framePayloadBytes (frames : Array Frame) : Nat :=
  frames.foldl (fun total frame => total + frame.payload.size) 0

private def queueOutboundShared (stateMutex : Std.Mutex State) (emit : Array Frame -> IO Unit)
    (frames : Array Frame) : IO (Except Status Unit) := do
  let emitted? ← stateMutex.atomically do
    let state ← get
    if framePayloadBytes state.pendingOutbound + framePayloadBytes frames
        > maxPendingOutboundBytes then
      pure (Except.error
        (Status.resourceExhausted "HTTP/2 outbound buffer limit exceeded: peer is not consuming flow-controlled data"))
    else
      let (state, emitted) := queueOutbound state frames
      set state
      pure (Except.ok emitted)
  match emitted? with
  | .error status => pure (.error status)
  | .ok emitted => emitFrameBatch emit emitted

private def cancelResponseStreamRef (responseStreamCancel : IO.Ref (Option (IO Unit))) : IO Unit := do
  match ← responseStreamCancel.get with
  | none => pure ()
  | some cancel =>
      try
        cancel
      catch _ =>
        pure ()

private def cancelRequestStreamRef (requestStreamCancel : IO.Ref (Option (IO Unit))) : IO Unit := do
  match ← requestStreamCancel.get with
  | none => pure ()
  | some cancel =>
      try
        cancel
      catch _ =>
        pure ()

private def cancelResponseStream (dispatch : ActiveDispatch) : IO Unit :=
  cancelResponseStreamRef dispatch.responseStreamCancel

private def cancelRequestStream (dispatch : ActiveDispatch) : IO Unit :=
  cancelRequestStreamRef dispatch.requestStreamCancel

/-- Unbounded so that feeding inbound messages from the connection loop never
blocks on a slow handler (one stalled stream must not stall the connection).
Memory stays bounded by HTTP/2 stream flow control: the peer can have at most
one stream window of unconsumed payload in flight per stream, because the
stream window is only credited back as the handler consumes messages. -/
private def runGrpcPipe : IO (Except Status (MessageStream.Producer ByteArray)) :=
  (MessageStream.pipe (α := ByteArray) (capacity := none)).run

private def feedRequestStream (feed : RequestStreamFeed) : IO (Except Status Unit) := do
  for message in feed.messages do
    match ← (feed.producer.send message).run with
    | .ok () => pure ()
    | .error status => return .error status
  match feed.error with
  | some status => feed.producer.fail status
  | none =>
      if feed.close then
        feed.producer.close.run
      else
        pure (.ok ())

/-- Wait for the dispatch to be registered in connection state before running the
handler. Resolved immediately after the spawn site's registration, so the wait is
momentary; a promise (instead of a poll loop) avoids adding latency to every RPC. -/
private def waitUntilDispatchRegistered (registered : IO.Promise Unit) : IO Unit := do
  discard <| IO.wait registered.result?

/-- Drop all connection-level state for a stream and send RST_STREAM so the peer learns
the stream is dead instead of waiting on a response that will never arrive. -/
private def abortStreamShared (stateMutex : Std.Mutex State) (emit : Array Frame -> IO Unit)
    (streamId : Nat) (code : ErrorCode) : IO Unit := do
  stateMutex.atomically do
    let state ← get
    let state := { state with streams := removeStream state.streams streamId }
    let state := removeInboundStreamState state streamId
    set (removeOutboundStreamState state streamId)
  match RstStream.frame streamId code with
  | .error _ => pure ()
  | .ok rst =>
      try
        emit #[rst]
      catch _ =>
        pure ()

private def spawnDetachedDispatch (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (detached : DetachedDispatch) : IO Unit := do
  let cancelled ← IO.mkRef false
  let registered ← IO.Promise.new
  let requestStreamCancel ← IO.mkRef (none : Option (IO Unit))
  let responseStreamCancel ← IO.mkRef (none : Option (IO Unit))
  let registerResponseStream (stream : MessageStream ByteArray) : IO Unit := do
    let cancel : IO Unit := do
      discard <| stream.cancel.run
    responseStreamCancel.set (some cancel)
    if ← cancelled.get then
      cancel
  let emitOutbound (frames : Array Frame) : IO Unit := do
    if ← IO.checkCanceled then
      throw (IO.userError Status.dispatchCancelledMessage)
    else if ← cancelled.get then
      throw (IO.userError Status.dispatchCancelledMessage)
    else
      match ← queueOutboundShared stateMutex emit frames with
      | .ok () => pure ()
      | .error status => throw (IO.userError status.messageD)
  let task ← IO.asTask do
    waitUntilDispatchRegistered registered
    try
      match ← Transport.dispatchDecodedUnaryFramesWith
          registry detached.outboundHpack detached.request emitOutbound detached.maxDataFrameSize
          registerResponseStream with
      | .ok result =>
          stateMutex.atomically do
            let state ← get
            let activeDispatches := removeActiveDispatchesForStream
              state.activeDispatches detached.request.streamId
            set {
              state with
              outboundHpack := result.outboundHpack,
              activeDispatches := activeDispatches
            }
      | .error _status =>
          cancelResponseStreamRef responseStreamCancel
          stateMutex.atomically do
            let state ← get
            set {
              state with
              activeDispatches := removeActiveDispatchesForStream
                state.activeDispatches detached.request.streamId
            }
          abortStreamShared stateMutex emit detached.request.streamId ErrorCode.internalError
    catch _ =>
      cancelResponseStreamRef responseStreamCancel
      stateMutex.atomically do
        let state ← get
        set {
          state with
          activeDispatches := removeActiveDispatchesForStream
            state.activeDispatches detached.request.streamId
        }
      abortStreamShared stateMutex emit detached.request.streamId ErrorCode.internalError
  stateMutex.atomically do
    let state ← get
    set {
      state with
      activeDispatches := state.activeDispatches.push {
        streamId := detached.request.streamId,
        task := task,
        cancelled := cancelled,
        requestStreamCancel := requestStreamCancel,
        responseStreamCancel := responseStreamCancel
      }
    }
  registered.resolve ()
  if ← IO.hasFinished task then
    stateMutex.atomically do
      let state ← get
      set {
        state with
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches detached.request.streamId
      }

/-- Pop the wire size of the next consumed message and send the deferred
stream WINDOW_UPDATE for it, keeping our inbound window accounting in sync. -/
private def grantRequestStreamCredit (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (streamId : Nat) : IO (Except Status Unit) := do
  let credit ← stateMutex.atomically do
    let state ← get
    match findActiveRequestStream? state.activeRequestStreams streamId with
    | none => pure 0
    | some active =>
        match active.pendingRequestCredits[0]? with
        | none => pure 0
        | some credit =>
            let active := {
              active with
              pendingRequestCredits :=
                active.pendingRequestCredits.extract 1 active.pendingRequestCredits.size
            }
            let state := replenishInboundStreamWindowBy state streamId credit
            set {
              state with
              activeRequestStreams := replaceActiveRequestStream state.activeRequestStreams active
            }
            pure credit
  if credit == 0 then
    pure (.ok ())
  else
    match WindowUpdate.frame streamId credit with
    | .error status => pure (.error status)
    | .ok frame => queueOutboundShared stateMutex emit #[frame]

/-- Wrap a streaming request body so each consumed message grants its deferred
stream flow-control credit back to the peer. -/
private def creditingRequestStream (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (streamId : Nat)
    (inner : MessageStream ByteArray) : MessageStream ByteArray :=
  {
    recv? := ExceptT.mk do
      match ← inner.recv?.run with
      | .error status => pure (.error status)
      | .ok none => pure (.ok none)
      | .ok (some item) =>
          match ← grantRequestStreamCredit stateMutex emit streamId with
          | .ok () => pure (.ok (some item))
          | .error status => pure (.error status)
    cancel := inner.cancel
  }

private def spawnRequestStreamingDispatch (registry : Registry) (stateMutex : Std.Mutex State)
    (emit : Array Frame -> IO Unit) (dispatch : RequestStreamingDispatch) :
    IO (Except Status Unit) := do
  let producer ← match ← runGrpcPipe with
    | .ok producer => pure producer
    | .error status => return .error status
  let requestStream := creditingRequestStream stateMutex emit dispatch.streamId producer.stream
  let acceptsGzip := Headers.clientAcceptsGzip dispatch.metadata
  let cancelled ← IO.mkRef false
  let registered ← IO.Promise.new
  let requestStreamCancel ← IO.mkRef (some (discard <| producer.cancel.run) : Option (IO Unit))
  let responseStreamCancel ← IO.mkRef (none : Option (IO Unit))
  let registerResponseStream (stream : MessageStream ByteArray) : IO Unit := do
    let cancel : IO Unit := do
      discard <| stream.cancel.run
    responseStreamCancel.set (some cancel)
    if ← cancelled.get then
      cancel
  let emitOutbound (frames : Array Frame) : IO Unit := do
    if ← IO.checkCanceled then
      throw (IO.userError Status.dispatchCancelledMessage)
    else if ← cancelled.get then
      throw (IO.userError Status.dispatchCancelledMessage)
    else
      match ← queueOutboundShared stateMutex emit frames with
      | .ok () => pure ()
      | .error status => throw (IO.userError status.messageD)
  let finish (outboundHpack : Option Hpack.State) : IO Unit := do
    cancelRequestStreamRef requestStreamCancel
    stateMutex.atomically do
      let state ← get
      let state := {
        state with
        streams := removeStream state.streams dispatch.streamId,
        activeRequestStreams := removeActiveRequestStream state.activeRequestStreams dispatch.streamId,
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches dispatch.streamId
      }
      let state := match outboundHpack with
        | none => state
        | some outboundHpack => { state with outboundHpack := outboundHpack }
      set state
  let encodeUnary (response : UnaryResponse) : IO (Except Status Hpack.State) := do
    match Transport.encodeUnaryResponseFrames
        dispatch.outboundHpack dispatch.streamId response dispatch.maxDataFrameSize acceptsGzip with
    | .error status => pure (.error status)
    | .ok encoded =>
        match ← queueOutboundShared stateMutex emit encoded.1 with
        | .error status => pure (.error status)
        | .ok () => pure (.ok encoded.2)
  let encodeStreaming (response : ServerStreamingStreamResponse) :
      IO (Except Status Hpack.State) := do
    try
      registerResponseStream response.messages
    catch err =>
      return .error (Status.ofIOError err)
    Transport.encodeServerStreamingStreamResponseFramesWith
      dispatch.outboundHpack dispatch.streamId response emitOutbound dispatch.maxDataFrameSize
      acceptsGzip
  let emptyStreamingResponse (status : Status) : ServerStreamingStreamResponse := {
    messages := { recv? := pure none },
    status := status
  }
  let task ← IO.asTask do
    waitUntilDispatchRegistered registered
    try
      match dispatch.requestError with
      | some status =>
          let encoded ← match dispatch.kind with
            | .clientStreaming _ =>
                encodeUnary { status := status, data := ByteArray.empty }
            | .bidirectionalStreaming _ =>
                encodeStreaming (emptyStreamingResponse status)
          match encoded with
          | .ok outboundHpack => finish (some outboundHpack)
          | .error _status =>
              cancelResponseStreamRef responseStreamCancel
              finish none
              abortStreamShared stateMutex emit dispatch.streamId ErrorCode.internalError
      | none =>
          match dispatch.kind with
          | .clientStreaming handler =>
              let result ← (registry.dispatchClientStreamingMessageStream
                dispatch.metadata requestStream (some handler)).run
              let encoded ← match result with
                | .ok response => encodeUnary response
                | .error status => encodeUnary { status := status, data := ByteArray.empty }
              match encoded with
              | .ok outboundHpack => finish (some outboundHpack)
              | .error _status =>
                  cancelResponseStreamRef responseStreamCancel
                  finish none
                  abortStreamShared stateMutex emit dispatch.streamId ErrorCode.internalError
          | .bidirectionalStreaming handler =>
              let result ← (registry.dispatchBidirectionalStreamingMessageStream
                dispatch.metadata requestStream (some handler)).run
              let encoded ← match result with
                | .ok response => encodeStreaming response
                | .error status => encodeStreaming (emptyStreamingResponse status)
              match encoded with
              | .ok outboundHpack => finish (some outboundHpack)
              | .error _status =>
                  cancelResponseStreamRef responseStreamCancel
                  finish none
                  abortStreamShared stateMutex emit dispatch.streamId ErrorCode.internalError
    catch _ =>
      cancelResponseStreamRef responseStreamCancel
      finish none
      abortStreamShared stateMutex emit dispatch.streamId ErrorCode.internalError
  stateMutex.atomically do
    let state ← get
    let activeDispatch : ActiveDispatch := {
      streamId := dispatch.streamId,
      task := task,
      cancelled := cancelled,
      requestStreamCancel := requestStreamCancel,
      responseStreamCancel := responseStreamCancel
    }
    let activeRequestStreams :=
      if dispatch.closeImmediately then
        state.activeRequestStreams
      else
        state.activeRequestStreams.push {
          streamId := dispatch.streamId,
          producer := producer,
          contentLength := dispatch.contentLength,
          usesGzip := dispatch.usesGzip
        }
    set {
      state with
      activeDispatches := state.activeDispatches.push activeDispatch,
      activeRequestStreams := activeRequestStreams
    }
  registered.resolve ()
  if dispatch.closeImmediately then
    match ← producer.close.run with
    | .ok () => pure ()
    | .error status => return .error status
  if ← IO.hasFinished task then
    stateMutex.atomically do
      let state ← get
      set {
        state with
        streams := removeStream state.streams dispatch.streamId,
        activeRequestStreams := removeActiveRequestStream
          state.activeRequestStreams dispatch.streamId,
        activeDispatches := removeActiveDispatchesForStream
          state.activeDispatches dispatch.streamId
      }
  pure (.ok ())

def cancelActiveShared (stateMutex : Std.Mutex State) : IO State := do
  let (state, dispatches, requestStreams) ← stateMutex.atomically do
    let state ← get
    let dispatches := state.activeDispatches
    let requestStreams := state.activeRequestStreams
    let state := {
      state with
      streams := #[],
      ignoredInboundStreams := #[],
      activeRequestStreams := #[],
      activeDispatches := #[],
      pendingOutbound := #[],
      inboundStreamWindows := #[],
      outboundStreamWindows := #[]
    }
    set state
    pure (state, dispatches, requestStreams)
  for dispatch in dispatches do
    dispatch.cancelled.set true
    cancelRequestStream dispatch
    cancelResponseStream dispatch
    IO.cancel dispatch.task
  for requestStream in requestStreams do
    discard <| requestStream.producer.cancel.run
  pure state

private def finalizeStreamWith (registry : Registry) (state : State) (streamId : Nat)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match findStream? state.streams streamId with
  | none => pure (.error (Status.internal s!"unknown HTTP/2 stream {streamId}"))
  | some stream =>
      let request ← match authorizedUnaryRequestForStream state stream with
        | .ok request => pure request
        | .error status => return .error status
      let streams := removeStream state.streams streamId
      let stateRef ← IO.mkRef { state with streams := streams }
      let emitOutbound (frames : Array Frame) : IO Unit := do
        let state ← stateRef.get
        let (state, emitted) := queueOutbound state frames
        stateRef.set state
        emit emitted
      match (← Transport.dispatchDecodedUnaryFramesWith
          registry state.outboundHpack request emitOutbound
          state.outboundMaxFramePayloadLength) with
      | .ok result =>
          let state ← stateRef.get
          let state := {
            state with
            hpack := result.inboundHpack,
            outboundHpack := result.outboundHpack
          }
          pure (.ok (removeInboundStreamState state streamId))
      | .error status => pure (.error status)

private def finalizeStream (registry : Registry) (state : State) (streamId : Nat) :
    IO (Except Status (State × Array Frame)) := do
  let emittedRef ← IO.mkRef #[]
  match ← finalizeStreamWith registry state streamId
      (fun frames => emittedRef.modify fun emitted => emitted.append frames) with
  | .ok state => pure (.ok (state, ← emittedRef.get))
  | .error status => pure (.error status)

private def processSettings (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  let settings ← Settings.decode frame
  if Settings.isAck frame then
    if state.prefaceReceived && !state.clientSettingsReceived then
      throw (Status.internal "HTTP/2 client preface must be followed by a non-ACK SETTINGS frame")
    else
      pure (state, #[])
  else
    let state ← applyPeerSettings state settings
    let state := { state with clientSettingsReceived := true }
    let ack ← Settings.frame #[] (ack := true)
    let (state, flushed) := flushOutbound state
    pure (state, #[ack].append flushed)

private def processPing (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  let payload ← Ping.decode frame
  if Ping.isAck frame then
    let state :=
      match state.pendingKeepalivePing with
      | some pending =>
          if pending == payload then
            { state with pendingKeepalivePing := none }
          else
            state
      | none => state
    pure (state, #[])
  else
    let ack ← Ping.frame payload (ack := true)
    pure (state, #[ack])

private def processGoAway (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  discard <| GoAway.decode frame
  pure (state, #[])

private def processPriority (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  discard <| Priority.decode frame
  requireClientStreamId frame.header.streamId "PRIORITY"
  pure (state, #[])

private def processRstStream (state : State) (frame : Frame) : Except Status (State × Array Frame) := do
  discard <| RstStream.decode frame
  requireClientStreamId frame.header.streamId "RST_STREAM"
  let state := { state with streams := removeStream state.streams frame.header.streamId }
  let state := removeInboundStreamState state frame.header.streamId
  pure (removeOutboundStreamState state frame.header.streamId, #[])

private def processRstStreamShared (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  discard <| RstStream.decode frame
  requireClientStreamId frame.header.streamId "RST_STREAM"
  let cancelDispatches := activeDispatchesForStream state.activeDispatches frame.header.streamId
  let state := { state with streams := removeStream state.streams frame.header.streamId }
  let state := removeInboundStreamState state frame.header.streamId
  pure (removeOutboundStreamState state frame.header.streamId, { cancelDispatches := cancelDispatches })

private def processHeaders (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match requireClientStreamId frame.header.streamId "HEADERS" with
  | .error status => pure (.error status)
  | .ok () =>
    if (findStream? state.streams frame.header.streamId).isSome then
      pure (.error (Status.internal "HTTP/2 duplicate HEADERS for active unary stream"))
    else
      match requireNewClientStreamId state frame.header.streamId with
      | .error status => pure (.error status)
      | .ok () =>
        match rejectNewStreamAfterOutboundGoAway? state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (some rst) => pure (.ok (state, #[rst]))
        | .ok none =>
          match requireInboundStreamCapacity state with
          | .error status => pure (.error status)
          | .ok () =>
            let state := {
              state with
              lastClientStreamId := frame.header.streamId,
              streams := appendStreamFrame state.streams frame
            }
            if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
              match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
              | .error status => pure (.error status)
              | .ok (state, some frames) => pure (.ok (state, frames))
              | .ok (state, none) =>
                  if FrameFlag.has frame.header.flags FrameFlag.endStream then
                    finalizeStream registry state frame.header.streamId
                  else
                    pure (.ok (state, #[]))
            else
              pure (.ok (state, #[]))

private def processHeadersWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match requireClientStreamId frame.header.streamId "HEADERS" with
  | .error status => pure (.error status)
  | .ok () =>
    if (findStream? state.streams frame.header.streamId).isSome then
      pure (.error (Status.internal "HTTP/2 duplicate HEADERS for active unary stream"))
    else
      match requireNewClientStreamId state frame.header.streamId with
      | .error status => pure (.error status)
      | .ok () =>
        match rejectNewStreamAfterOutboundGoAway? state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (some rst) =>
            match ← emitFrameBatch emit #[rst] with
            | .error status => pure (.error status)
            | .ok () => pure (.ok state)
        | .ok none =>
          match requireInboundStreamCapacity state with
          | .error status => pure (.error status)
          | .ok () =>
            let state := {
              state with
              lastClientStreamId := frame.header.streamId,
              streams := appendStreamFrame state.streams frame
            }
            if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
              match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
              | .error status => pure (.error status)
              | .ok (state, some frames) =>
                  match ← emitFrameBatch emit frames with
                  | .error status => pure (.error status)
                  | .ok () => pure (.ok state)
              | .ok (state, none) =>
                  if FrameFlag.has frame.header.flags FrameFlag.endStream then
                    finalizeStreamWith registry state frame.header.streamId emit
                  else
                    pure (.ok state)
            else
              pure (.ok state)

private def processContinuation (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match appendContinuationFrame state.streams frame with
  | .error status => pure (.error status)
  | .ok streams =>
      let state := { state with streams := streams }
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        match findStream? streams frame.header.streamId with
        | some stream =>
            match stream.frames[0]? with
            | some headersFrame =>
                match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
                | .error status => pure (.error status)
                | .ok (state, some frames) => pure (.ok (state, frames))
                | .ok (state, none) =>
                    if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
                      finalizeStream registry state frame.header.streamId
                    else
                      pure (.ok (state, #[]))
            | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
        | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
      else
        pure (.ok (state, #[]))

private def processContinuationWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match appendContinuationFrame state.streams frame with
  | .error status => pure (.error status)
  | .ok streams =>
      let state := { state with streams := streams }
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        match findStream? streams frame.header.streamId with
        | some stream =>
            match stream.frames[0]? with
            | some headersFrame =>
                match ← authorizeRequestHeadersForStream registry state frame.header.streamId with
                | .error status => pure (.error status)
                | .ok (state, some frames) =>
                    match ← emitFrameBatch emit frames with
                    | .error status => pure (.error status)
                    | .ok () => pure (.ok state)
                | .ok (state, none) =>
                    if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
                      finalizeStreamWith registry state frame.header.streamId emit
                    else
                      pure (.ok state)
            | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
        | none => pure (.error (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
      else
        pure (.ok state)

private def processData (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match requireClientStreamId frame.header.streamId "DATA" with
  | .error status => pure (.error status)
  | .ok () =>
    if containsStreamId state.ignoredInboundStreams frame.header.streamId then
      match processIgnoredInboundData state frame with
      | .error status => pure (.error status)
      | .ok result => pure (.ok result)
    else match findStream? state.streams frame.header.streamId with
    | none =>
        pure (.error (Status.internal "HTTP/2 DATA frame arrived before request HEADERS"))
    | some stream =>
        if !streamHeaderComplete stream then
          pure (.error (Status.internal "HTTP/2 DATA frame arrived before END_HEADERS"))
        else
          match consumeInboundDataWindow state frame with
          | .error status => pure (.error status)
          | .ok state =>
            match dataWindowUpdates frame with
            | .error status => pure (.error status)
            | .ok updates =>
              let state := replenishInboundDataWindow state frame
              match stripPadding frame "DATA" with
              | .error status => pure (.error status)
              | .ok frame =>
                let state := { state with streams := appendStreamFrame state.streams frame }
                if FrameFlag.has frame.header.flags FrameFlag.endStream then
                  match (← finalizeStream registry state frame.header.streamId) with
                  | .ok (state, frames) => pure (.ok (state, updates.append frames))
                  | .error status => pure (.error status)
                else
                  pure (.ok (state, updates))

private def processDataWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match requireClientStreamId frame.header.streamId "DATA" with
  | .error status => pure (.error status)
  | .ok () =>
    if containsStreamId state.ignoredInboundStreams frame.header.streamId then
      match processIgnoredInboundData state frame with
      | .error status => pure (.error status)
      | .ok (state, updates) =>
          match ← emitFrameBatch emit updates with
          | .error status => pure (.error status)
          | .ok () => pure (.ok state)
    else match findStream? state.streams frame.header.streamId with
    | none =>
        pure (.error (Status.internal "HTTP/2 DATA frame arrived before request HEADERS"))
    | some stream =>
        if !streamHeaderComplete stream then
          pure (.error (Status.internal "HTTP/2 DATA frame arrived before END_HEADERS"))
        else
          match consumeInboundDataWindow state frame with
          | .error status => pure (.error status)
          | .ok state =>
            match dataWindowUpdates frame with
            | .error status => pure (.error status)
            | .ok updates =>
              let state := replenishInboundDataWindow state frame
              match stripPadding frame "DATA" with
              | .error status => pure (.error status)
              | .ok frame =>
                let state := { state with streams := appendStreamFrame state.streams frame }
                match ← emitFrameBatch emit updates with
                | .error status => pure (.error status)
                | .ok () =>
                    if FrameFlag.has frame.header.flags FrameFlag.endStream then
                      finalizeStreamWith registry state frame.header.streamId emit
                    else
                      pure (.ok state)

private def requireHeaderBlockContinuation (state : State) (frame : Frame) : Except Status Unit := do
  match pendingHeaderStream? state.streams with
  | none => pure ()
  | some streamId =>
      if frame.header.frameType == FrameType.continuation && frame.header.streamId == streamId then
        pure ()
      else
        throw (Status.internal "HTTP/2 header block must be followed by CONTINUATION frames")

private def requireInboundFrameSize (state : State) (frame : Frame) : Except Status Unit := do
  if frame.header.length != frame.payload.size then
    throw (Status.internal "HTTP/2 frame header length does not match payload size")
  if frame.payload.size > state.inboundMaxFramePayloadLength then
    throw (Status.internal "HTTP/2 inbound frame exceeds advertised max frame size")

private def withNormalizedHeaders (frame : Frame)
    (k : Frame -> IO (Except Status α)) : IO (Except Status α) := do
  match normalizeHeadersFrame frame with
  | .error status => pure (.error status)
  | .ok frame => k frame

private def requireClientSettingsFrame (state : State) (frame : Frame) : Except Status Unit := do
  if state.prefaceReceived
      && !state.clientSettingsReceived
      && frame.header.frameType != FrameType.settings then
    throw (Status.internal "HTTP/2 client preface must be followed by a non-ACK SETTINGS frame")

def processFrame (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × Array Frame)) := do
  match requireInboundFrameSize state frame with
  | .error status => pure (.error status)
  | .ok () =>
      match requireClientSettingsFrame state frame with
      | .error status => pure (.error status)
      | .ok () =>
          match requireHeaderBlockContinuation state frame with
          | .error status => pure (.error status)
          | .ok () =>
              match frame.header.frameType with
              | .settings => pure (processSettings state frame)
              | .headers => withNormalizedHeaders frame (processHeaders registry state)
              | .data => processData registry state frame
              | .rstStream => pure (processRstStream state frame)
              | .windowUpdate => pure (processWindowUpdate state frame)
              | .ping => pure (processPing state frame)
              | .continuation => processContinuation registry state frame
              | .priority => pure (processPriority state frame)
              | .goAway => pure (processGoAway state frame)
              | .pushPromise => pure (.error (Status.unimplemented "HTTP/2 PUSH_PROMISE frames are not supported"))
              | .unknown _ => pure (.ok (state, #[]))

def processFrameWith (registry : Registry) (state : State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match requireInboundFrameSize state frame with
  | .error status => pure (.error status)
  | .ok () =>
      match requireClientSettingsFrame state frame with
      | .error status => pure (.error status)
      | .ok () =>
          match requireHeaderBlockContinuation state frame with
          | .error status => pure (.error status)
          | .ok () =>
              match frame.header.frameType with
              | .settings => emitResultFrames emit (processSettings state frame)
              | .headers => withNormalizedHeaders frame (processHeadersWith registry state · emit)
              | .data => processDataWith registry state frame emit
              | .rstStream => emitResultFrames emit (processRstStream state frame)
              | .windowUpdate => emitResultFrames emit (processWindowUpdate state frame)
              | .ping => emitResultFrames emit (processPing state frame)
              | .continuation => processContinuationWith registry state frame emit
              | .priority => emitResultFrames emit (processPriority state frame)
              | .goAway => emitResultFrames emit (processGoAway state frame)
              | .pushPromise => pure (.error (Status.unimplemented "HTTP/2 PUSH_PROMISE frames are not supported"))
              | .unknown _ => pure (.ok state)

/-- The pure bookkeeping `processHeadersShared` performs before the `IO`
authorizer call: stream-id validation, buffering the header frame, and
claiming the stream id.  Factored out so the authorization-before-body
groundwork (end of file) can reason about HEADERS steps without touching
`IO`. -/
private def prepareHeadersShared (state : State) (frame : Frame) :
    Except Status (State × Option Frame) := do
  requireClientStreamId frame.header.streamId "HEADERS"
  if (findStream? state.streams frame.header.streamId).isSome then
    throw (Status.internal "HTTP/2 duplicate HEADERS for active unary stream")
  requireNewClientStreamId state frame.header.streamId
  match ← rejectNewStreamAfterOutboundGoAway? state frame.header.streamId with
  | some rst => pure (state, some rst)
  | none =>
      requireInboundStreamCapacity state
      pure ({
        state with
        lastClientStreamId := frame.header.streamId,
        streams := appendStreamFrame state.streams frame
      }, none)

private def processHeadersShared (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × SharedFrameResult)) := do
  match prepareHeadersShared state frame with
  | .error status => pure (.error status)
  | .ok (state, some rst) => pure (.ok (state, { emitted := #[rst] }))
  | .ok (state, none) =>
      if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
        match ← earlyRequestRejectionForStream? registry state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (state, some result) => pure (.ok (state, result))
        | .ok (state, none) =>
            match requestStreamingDispatchForStream? state frame.header.streamId with
            | .error status => pure (.error status)
            | .ok (state, some requestStreaming) =>
                pure (.ok (state, { requestStreaming := some requestStreaming }))
            | .ok (state, none) =>
                if FrameFlag.has frame.header.flags FrameFlag.endStream then
                  match detachStreamForDispatch state frame.header.streamId with
                  | .error status => pure (.error status)
                  | .ok (state, detached) => pure (.ok (state, { detached := some detached }))
                else
                  pure (.ok (state, {}))
      else
        pure (.ok (state, {}))

private def processContinuationShared (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × SharedFrameResult)) := do
  match appendContinuationFrame state.streams frame with
  | .error status => pure (.error status)
  | .ok streams =>
    let state := { state with streams := streams }
    if FrameFlag.has frame.header.flags FrameFlag.endHeaders then
      let headersFrame? := (findStream? streams frame.header.streamId).bind fun stream =>
        stream.frames[0]?
      match headersFrame? with
      | none => pure (.error
          (Status.internal "HTTP/2 CONTINUATION frame arrived before request HEADERS"))
      | some headersFrame =>
        match ← earlyRequestRejectionForStream? registry state frame.header.streamId with
        | .error status => pure (.error status)
        | .ok (state, some result) => pure (.ok (state, result))
        | .ok (state, none) =>
          match requestStreamingDispatchForStream? state frame.header.streamId with
          | .error status => pure (.error status)
          | .ok (state, some requestStreaming) =>
              pure (.ok (state, { requestStreaming := some requestStreaming }))
          | .ok (state, none) =>
            if FrameFlag.has headersFrame.header.flags FrameFlag.endStream then
              match detachStreamForDispatch state frame.header.streamId with
              | .error status => pure (.error status)
              | .ok (state, detached) => pure (.ok (state, { detached := some detached }))
            else
              pure (.ok (state, {}))
    else
      pure (.ok (state, {}))

private def processDataShared (registry : Registry) (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  requireClientStreamId frame.header.streamId "DATA"
  if containsStreamId state.ignoredInboundStreams frame.header.streamId then
    let (state, updates) ← processIgnoredInboundData state frame
    pure (state, { emitted := updates })
  else match findActiveRequestStream? state.activeRequestStreams frame.header.streamId with
  | some active =>
      let originalSize := frame.payload.size
      let state ← consumeInboundDataWindow state frame
      let frame ← stripPadding frame "DATA"
      let paddingBytes := originalSize - frame.payload.size
      let updates ← activeDataWindowUpdates frame.header.streamId originalSize paddingBytes
      let state := replenishInboundConnectionWindow state originalSize
      let state := replenishInboundStreamWindowBy state frame.header.streamId paddingBytes
      let frame ← Transport.normalizeDataFrame frame
      match decodeActiveRequestData registry active frame with
      | .ok (active, messages, close) =>
          let state :=
            if close then
              {
                state with
                streams := removeStream state.streams frame.header.streamId,
                activeRequestStreams := removeActiveRequestStream
                  state.activeRequestStreams frame.header.streamId
              }
            else
              {
                state with
                activeRequestStreams := replaceActiveRequestStream state.activeRequestStreams active
              }
          let state :=
            if close then
              removeInboundStreamState state frame.header.streamId
            else
              state
          pure (state, {
            emitted := updates,
            requestFeeds := #[{
              producer := active.producer,
              messages := messages,
              close := close
            }]
          })
      | .error status =>
          let state := {
            state with
            streams := removeStream state.streams frame.header.streamId,
            activeRequestStreams := removeActiveRequestStream
              state.activeRequestStreams frame.header.streamId
          }
          let state := removeInboundStreamState state frame.header.streamId
          pure (state, {
            emitted := updates,
            requestFeeds := #[{
              producer := active.producer,
              error := some status
            }]
          })
  | none =>
      let stream ← match findStream? state.streams frame.header.streamId with
        | some stream => pure stream
        | none => throw (Status.internal "HTTP/2 DATA frame arrived before request HEADERS")
      if !streamHeaderComplete stream then
        throw (Status.internal "HTTP/2 DATA frame arrived before END_HEADERS")
      let state ← consumeInboundDataWindow state frame
      let updates ← dataWindowUpdates frame
      let state := replenishInboundDataWindow state frame
      let frame ← stripPadding frame "DATA"
      let state := { state with streams := appendStreamFrame state.streams frame }
      if FrameFlag.has frame.header.flags FrameFlag.endStream then
        let (state, detached) ← detachStreamForDispatch state frame.header.streamId
        pure (state, { emitted := updates, detached := some detached })
      else
        pure (state, { emitted := updates })

/-- The pure shared-kernel step for every frame type that does not require the
`IO` authorizer (i.e. everything except HEADERS/CONTINUATION).  Factored out of
`processFrameShared` so the authorization-before-body groundwork (end of file)
can state trace theorems over arbitrary non-header frame steps. -/
private def processNonHeaderFrameShared (registry : Registry) (state : State) (frame : Frame) :
    Except Status (State × SharedFrameResult) := do
  match frame.header.frameType with
  | .settings =>
      let (state, emitted) ← processSettings state frame
      pure (state, { emitted := emitted })
  | .data => processDataShared registry state frame
  | .rstStream => processRstStreamShared state frame
  | .windowUpdate =>
      let (state, emitted) ← processWindowUpdate state frame
      pure (state, { emitted := emitted })
  | .ping =>
      let (state, emitted) ← processPing state frame
      pure (state, { emitted := emitted })
  | .priority =>
      let (state, emitted) ← processPriority state frame
      pure (state, { emitted := emitted })
  | .goAway =>
      let (state, emitted) ← processGoAway state frame
      pure (state, { emitted := emitted })
  | .pushPromise =>
      throw (Status.unimplemented "HTTP/2 PUSH_PROMISE frames are not supported")
  | .unknown _ => pure (state, {})
  | .headers | .continuation =>
      throw (Status.internal "unreachable HTTP/2 header dispatch")

private def processFrameShared (registry : Registry) (state : State) (frame : Frame) :
    IO (Except Status (State × SharedFrameResult)) := do
  let validated : Except Status Unit := do
    requireInboundFrameSize state frame
    requireClientSettingsFrame state frame
    requireHeaderBlockContinuation state frame
  match validated with
  | .error status => pure (.error status)
  | .ok () =>
    match frame.header.frameType with
    | .headers =>
        match normalizeHeadersFrame frame with
        | .error status => pure (.error status)
        | .ok frame => processHeadersShared registry state frame
    | .continuation => processContinuationShared registry state frame
    | _ => pure (processNonHeaderFrameShared registry state frame)

def processFrameSharedWith (registry : Registry) (stateMutex : Std.Mutex State) (frame : Frame)
    (emit : Array Frame -> IO Unit) : IO (Except Status Unit) := do
  match ← stateMutex.atomically (do
    let state ← get
    match ← processFrameShared registry state frame with
    | .error status => pure (Except.error status)
    | .ok (state, result) =>
        set state
        pure (Except.ok result)) with
  | .error status => pure (Except.error status)
  | .ok result =>
      for dispatch in result.cancelDispatches do
        dispatch.cancelled.set true
        cancelRequestStream dispatch
        cancelResponseStream dispatch
        IO.cancel dispatch.task
      match ← emitFrameBatch emit result.emitted with
      | .error status => pure (.error status)
      | .ok () =>
          for feed in result.requestFeeds do
            match ← feedRequestStream feed with
            | .ok () => pure ()
            | .error status => return .error status
          match result.requestStreaming with
          | some dispatch =>
              match ← spawnRequestStreamingDispatch registry stateMutex emit dispatch with
              | .error status => return .error status
              | .ok () => pure ()
          | none => pure ()
          match result.detached with
          | none => pure (.ok ())
          | some detached =>
              spawnDetachedDispatch registry stateMutex emit detached
              pure (.ok ())

private partial def processFrames (registry : Registry) (frames : Array Frame) (i : Nat)
    (state : State) (out : Array Frame) : IO (Except Status (State × Array Frame)) := do
  if i >= frames.size then
    pure (.ok (state, out))
  else
    match (← processFrame registry state frames[i]!) with
    | .error status => pure (Except.error status)
    | .ok (state, emitted) => processFrames registry frames (i + 1) state (out.append emitted)

private partial def processFramesWith (registry : Registry) (frames : Array Frame) (i : Nat)
    (state : State) (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  if i >= frames.size then
    pure (.ok state)
  else
    match (← processFrameWith registry state frames[i]! emit) with
    | .error status => pure (.error status)
    | .ok state => processFramesWith registry frames (i + 1) state emit

private partial def processFramesSharedWith (registry : Registry) (stateMutex : Std.Mutex State)
    (frames : Array Frame) (i : Nat) (emit : Array Frame -> IO Unit) :
    IO (Except Status Unit) := do
  if i >= frames.size then
    pure (.ok ())
  else
    match ← processFrameSharedWith registry stateMutex frames[i]! emit with
    | .error status => pure (.error status)
    | .ok () => processFramesSharedWith registry stateMutex frames (i + 1) emit

def processBytes (registry : Registry) (state : State) (chunk : ByteArray) :
    IO (Except Status (State × Array Frame)) := do
  match consumePreface state chunk with
  | .error status => pure (.error status)
  | .ok (state, remaining) =>
      if remaining.isEmpty then
        pure (.ok (state, #[]))
      else
        match Frame.decodeChunk state.decoder remaining with
        | .error status => pure (.error status)
        | .ok decoded =>
            let state := { state with decoder := { buffered := decoded.buffered } }
            processFrames registry decoded.frames 0 state #[]

def processBytesWith (registry : Registry) (state : State) (chunk : ByteArray)
    (emit : Array Frame -> IO Unit) : IO (Except Status State) := do
  match consumePreface state chunk with
  | .error status => pure (.error status)
  | .ok (state, remaining) =>
      if remaining.isEmpty then
        pure (.ok state)
      else
        match Frame.decodeChunk state.decoder remaining with
        | .error status => pure (.error status)
        | .ok decoded =>
            let state := { state with decoder := { buffered := decoded.buffered } }
            processFramesWith registry decoded.frames 0 state emit

def processBytesSharedWith (registry : Registry) (stateMutex : Std.Mutex State) (chunk : ByteArray)
    (emit : Array Frame -> IO Unit) : IO (Except Status Unit) := do
  match ← stateMutex.atomically (do
    let state ← get
    match consumePreface state chunk with
    | .error status => pure (.error status)
    | .ok (state, remaining) =>
        if remaining.isEmpty then
          set state
          pure (Except.ok #[])
        else
          match Frame.decodeChunk state.decoder remaining with
          | .error status => pure (Except.error status)
          | .ok decoded =>
              set { state with decoder := { buffered := decoded.buffered } }
              pure (Except.ok decoded.frames)) with
  | .error status => pure (Except.error status)
  | .ok frames => processFramesSharedWith registry stateMutex frames 0 emit

def encodeFrames (frames : Array Frame) : Except Status ByteArray :=
  frames.foldlM (init := ByteArray.empty) fun out frame => do
    let bytes ← Frame.encode frame
    pure (out.append bytes)

def processBytesEncodedWith (registry : Registry) (state : State) (chunk : ByteArray)
    (emit : ByteArray -> IO Unit) : IO (Except Status State) := do
  processBytesWith registry state chunk fun frames => do
    match encodeFrames frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

def processBytesEncodedSharedWith (registry : Registry) (stateMutex : Std.Mutex State)
    (chunk : ByteArray) (emit : ByteArray -> IO Unit) : IO (Except Status Unit) := do
  processBytesSharedWith registry stateMutex chunk fun frames => do
    match encodeFrames frames with
    | .ok bytes =>
        if bytes.isEmpty then pure () else emit bytes
    | .error status => throw (IO.userError status.messageD)

def processBytesEncoded (registry : Registry) (state : State) (chunk : ByteArray) :
    IO (Except Status (State × ByteArray)) := do
  let bytesRef ← IO.mkRef ByteArray.empty
  match (← processBytesEncodedWith registry state chunk
      (fun bytes => bytesRef.modify fun out => out.append bytes)) with
  | .ok state => pure (.ok (state, ← bytesRef.get))
  | .error status => pure (.error status)

/-!
## Authorization-before-body groundwork

Target trace property: over any frame sequence processed by a connection, a
stream whose request headers were rejected (authorization failure, invalid
headers, or unknown method) never feeds body bytes to a handler and never
dispatches one.

The rejection transition itself is the pure `rejectStreamAtHeaders` (used by
`authorizeRequestHeadersForStream`), and the pure kernel of body processing
is `processDataShared`.  Proved below, entirely against those real
implementations:

* `rejectStreamAtHeaders_rejected` / `rejectStreamAtHeaders_inert` — a
  rejection puts the stream in drain-only mode and makes it *inert*: no
  buffered frames, no incremental request feed, id already claimed.
* `processDataShared_rejected` — DATA for a drain-mode stream produces no
  request feed, no detached dispatch, no request-streaming dispatch and no
  cancellations, and cannot make the stream dispatchable again.
* `processDataShared_inert_error` — DATA for an inert stream that is not in
  drain mode (e.g. after END_STREAM finished the drain) is a protocol error;
  the connection tears down instead of dispatching.
* `DataTrace.inert_no_dispatch` / `rejectStreamAtHeaders_dataTrace_no_dispatch`
  — the trace-level statement: over any pure DATA trace for a rejected
  stream, every step is dispatch-free and the stream ends inert.

Remaining obligations for the full connection-level property (identified,
not yet proved):

* HEADERS/CONTINUATION steps: an inert stream id can never be reopened
  because `requireNewClientStreamId` enforces id monotonicity and rejection
  only happens for ids at or below `lastClientStreamId`; proving preservation
  through `processHeadersShared` requires factoring its pure bookkeeping out
  of the surrounding `IO` (the authorizer call), of which
  `rejectStreamAtHeaders` is the first piece.
* Non-DATA pure steps (SETTINGS, WINDOW_UPDATE, RST_STREAM, PING, PRIORITY,
  GOAWAY) preserve inertness; SETTINGS routes through the `partial`
  `flushOutbound`, which must be totalized (its recursion is structural in
  `pendingOutbound.size`) before that lemma is provable.
* The `IO` layer (`processFrameSharedWith`) only spawns dispatch tasks for
  the `detached`/`requestStreaming`/`requestFeeds` artifacts shown empty
  above, so the pure results extend to the task layer by inspection; making
  that formal needs an `IO`-free event-trace refactor of the spawn sites.
-/

/-- `true` when the connection rejected the stream at request headers and is
draining its remaining body without dispatch. -/
def State.rejectedAtHeaders (state : State) (streamId : Nat) : Bool :=
  containsStreamId state.ignoredInboundStreams streamId

/-- A stream id that can never reach a handler in this connection state: no
buffered header/body frames, no incremental request feed, and the id is
already claimed, so HTTP/2 stream-id monotonicity forbids reopening it. -/
structure State.StreamInert (state : State) (streamId : Nat) : Prop where
  notBuffered : ∀ stream ∈ state.streams, stream.streamId ≠ streamId
  notActive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId
  claimed : streamId ≤ state.lastClientStreamId

private theorem containsStreamId_pushUniqueStreamId (l : Array Nat) (id : Nat) :
    containsStreamId (pushUniqueStreamId l id) id = true := by
  unfold pushUniqueStreamId
  split
  next h => exact h
  next h => simp [containsStreamId]

private theorem removeStream_not_mem (streams : Array StreamState) (id : Nat) :
    ∀ s ∈ removeStream streams id, s.streamId ≠ id := by
  intro s hs
  have := (Array.mem_filter.mp hs).2
  simpa [bne_iff_ne] using this

private theorem removeActiveRequestStream_not_mem (streams : Array ActiveRequestStream)
    (id : Nat) : ∀ s ∈ removeActiveRequestStream streams id, s.streamId ≠ id := by
  intro s hs
  have := (Array.mem_filter.mp hs).2
  simpa [bne_iff_ne] using this

/-- A rejection whose request body is still open leaves the stream in
drain-only mode. -/
theorem rejectStreamAtHeaders_rejected (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) :
    (rejectStreamAtHeaders state streamId inboundHpack outboundHpack false).rejectedAtHeaders
      streamId = true := by
  unfold rejectStreamAtHeaders ignoreInboundStreamBody State.rejectedAtHeaders
  simp only [Bool.false_eq_true]
  exact containsStreamId_pushUniqueStreamId _ _

/-- Rejecting a stream at headers makes it inert: its buffered frames are
gone, it never entered the incremental request path, and its id cannot be
reopened. -/
theorem rejectStreamAtHeaders_inert (state : State) (streamId : Nat)
    (inboundHpack outboundHpack : Hpack.State) (endStream : Bool)
    (hclaimed : streamId ≤ state.lastClientStreamId)
    (hactive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId) :
    (rejectStreamAtHeaders state streamId inboundHpack outboundHpack
      endStream).StreamInert streamId := by
  unfold rejectStreamAtHeaders
  split
  · exact {
      notBuffered := by
        intro s hs
        exact removeStream_not_mem _ _ s (by simpa [removeInboundStreamState] using hs)
      notActive := by
        intro s hs
        exact removeActiveRequestStream_not_mem _ _ s
          (by simpa [removeInboundStreamState] using hs)
      claimed := hclaimed
    }
  · exact {
      notBuffered := by
        intro s hs
        have hs' : s ∈ removeStream (removeStream state.streams streamId) streamId := by
          simpa [ignoreInboundStreamBody] using hs
        exact removeStream_not_mem _ _ s hs'
      notActive := by
        intro s hs
        exact hactive s (by simpa [ignoreInboundStreamBody] using hs)
      claimed := hclaimed
    }


private theorem consumeInboundDataWindow_ok {state state' : State} {frame : Frame}
    (h : consumeInboundDataWindow state frame = .ok state') :
    state'.streams = state.streams
      ∧ state'.activeRequestStreams = state.activeRequestStreams
      ∧ state'.ignoredInboundStreams = state.ignoredInboundStreams
      ∧ state'.lastClientStreamId = state.lastClientStreamId := by
  unfold consumeInboundDataWindow at h
  simp only [] at h
  split at h
  next =>
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  next =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next =>
        cases h
        simp [setInboundStreamWindow]

private theorem replenishInboundDataWindow_fields (state : State) (frame : Frame) :
    (replenishInboundDataWindow state frame).streams = state.streams
      ∧ (replenishInboundDataWindow state frame).activeRequestStreams
          = state.activeRequestStreams
      ∧ (replenishInboundDataWindow state frame).ignoredInboundStreams
          = state.ignoredInboundStreams
      ∧ (replenishInboundDataWindow state frame).lastClientStreamId
          = state.lastClientStreamId := by
  unfold replenishInboundDataWindow
  grind [setInboundStreamWindow]

private theorem removeInboundStreamState_fields (state : State) (streamId : Nat) :
    (removeInboundStreamState state streamId).streams = state.streams
      ∧ (removeInboundStreamState state streamId).lastClientStreamId
          = state.lastClientStreamId
      ∧ (∀ active ∈ (removeInboundStreamState state streamId).activeRequestStreams,
          active ∈ state.activeRequestStreams) := by
  refine ⟨rfl, rfl, ?_⟩
  intro active hactive
  exact (Array.mem_filter.mp hactive).1

private theorem processIgnoredInboundData_ok {state state' : State} {frame : Frame}
    {updates : Array Frame}
    (h : processIgnoredInboundData state frame = .ok (state', updates)) :
    state'.streams = state.streams
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams) := by
  unfold processIgnoredInboundData at h
  simp only [bind, Except.bind, discard, Functor.discard, Functor.mapConst,
    pure, Except.pure] at h
  split at h
  next => cases h
  next s1 hcons =>
    split at h
    next => cases h
    next updates1 hupd =>
      split at h
      next => cases h
      next frame1 hstrip =>
        split at h
        next => cases h
        next _u hnorm =>
          cases h
          obtain ⟨hs1, ha1, -, hl1⟩ := consumeInboundDataWindow_ok hcons
          obtain ⟨hs2, ha2, -, hl2⟩ := replenishInboundDataWindow_fields s1 frame
          split
          · obtain ⟨hs3, hl3, ha3⟩ := removeInboundStreamState_fields
              (replenishInboundDataWindow s1 frame) frame1.header.streamId
            refine ⟨hs3.trans (hs2.trans hs1), hl3.trans (hl2.trans hl1), ?_⟩
            intro active hmem
            have hmem' := ha3 active hmem
            rw [ha2, ha1] at hmem'
            exact hmem'
          · refine ⟨hs2.trans hs1, hl2.trans hl1, ?_⟩
            intro active hmem
            rw [ha2, ha1] at hmem
            exact hmem


/-- A DATA frame for a stream rejected at headers is drained: the step
produces no request feed, no detached dispatch, no request-streaming
dispatch, and no cancellations, and the stream cannot re-enter the
dispatchable state. -/
private theorem processDataShared_rejected {registry : Registry} {state state' : State}
    {frame : Frame} {result : SharedFrameResult}
    (hrej : state.rejectedAtHeaders frame.header.streamId = true)
    (h : processDataShared registry state frame = .ok (state', result)) :
    result.requestFeeds = #[] ∧ result.detached = none ∧ result.requestStreaming = none
      ∧ result.cancelDispatches = #[]
      ∧ state'.streams = state.streams
      ∧ state'.lastClientStreamId = state.lastClientStreamId
      ∧ (∀ active ∈ state'.activeRequestStreams, active ∈ state.activeRequestStreams) := by
  unfold processDataShared at h
  simp only [bind, Except.bind] at h
  split at h
  next => cases h
  next _u _hreq =>
    rw [show containsStreamId state.ignoredInboundStreams frame.header.streamId = true
      from hrej] at h
    simp only [if_true] at h
    split at h
    next => cases h
    next pair hproc =>
      obtain ⟨s2, updates⟩ := pair
      cases h
      obtain ⟨hs, hl, ha⟩ := processIgnoredInboundData_ok hproc
      exact ⟨rfl, rfl, rfl, rfl, hs, hl, ha⟩

/-- A DATA frame for an inert stream that is not in drain mode is a protocol
error: the connection refuses it instead of dispatching. -/
private theorem processDataShared_inert_error {registry : Registry} {state : State}
    {frame : Frame} (hinert : state.StreamInert frame.header.streamId)
    (hnotrej : state.rejectedAtHeaders frame.header.streamId = false)
    {state' : State} {result : SharedFrameResult} :
    processDataShared registry state frame ≠ .ok (state', result) := by
  intro h
  unfold processDataShared at h
  simp only [bind, Except.bind] at h
  split at h
  next => cases h
  next _u _hreq =>
    rw [show containsStreamId state.ignoredInboundStreams frame.header.streamId = false
      from hnotrej] at h
    simp only [Bool.false_eq_true, if_false] at h
    have hactive : findActiveRequestStream? state.activeRequestStreams
        frame.header.streamId = none := by
      unfold findActiveRequestStream?
      rw [Array.find?_eq_none]
      intro x hx
      simp [hinert.notActive x hx]
    have hstream : findStream? state.streams frame.header.streamId = none := by
      unfold findStream?
      rw [Array.find?_eq_none]
      intro x hx
      simp [hinert.notBuffered x hx]
    rw [hactive, hstream] at h
    simp at h


/-- A pure trace of the shared kernel's DATA-frame steps: each listed frame
is processed by `processDataShared` from the previous state and produces the
recorded `SharedFrameResult`. -/
private inductive DataTrace (registry : Registry) :
    State -> List (Frame × SharedFrameResult) -> State -> Prop
  | nil (state : State) : DataTrace registry state [] state
  | step {state mid final : State} {frame : Frame} {result : SharedFrameResult}
      {rest : List (Frame × SharedFrameResult)}
      (h : processDataShared registry state frame = .ok (mid, result))
      (htail : DataTrace registry mid rest final) :
      DataTrace registry state ((frame, result) :: rest) final

private theorem DataTrace.inert_no_dispatch {registry : Registry}
    {state final : State} {steps : List (Frame × SharedFrameResult)}
    (trace : DataTrace registry state steps final) (streamId : Nat)
    (htarget : ∀ step ∈ steps, (step.1 : Frame).header.streamId = streamId)
    (hinert : state.StreamInert streamId) :
    final.StreamInert streamId
      ∧ ∀ step ∈ steps,
          (step.2 : SharedFrameResult).requestFeeds = #[] ∧ (step.2).detached = none
            ∧ (step.2).requestStreaming = none ∧ (step.2).cancelDispatches = #[] := by
  induction steps generalizing state with
  | nil =>
      cases trace
      exact ⟨hinert, by simp⟩
  | cons head rest ih =>
      cases trace with
      | step h htail =>
        rename_i mid frame result
        have htargetHead : frame.header.streamId = streamId :=
          htarget (frame, result) List.mem_cons_self
        cases hrej : state.rejectedAtHeaders frame.header.streamId with
        | false =>
            exact absurd h (processDataShared_inert_error (htargetHead.symm ▸ hinert) hrej)
        | true =>
            obtain ⟨hfeeds, hdet, hstreaming, hcancel, hs, hl, ha⟩ :=
              processDataShared_rejected hrej h
            have hmid : mid.StreamInert streamId := {
              notBuffered := fun s hs' => hinert.notBuffered s (hs ▸ hs'),
              notActive := fun a ha' => hinert.notActive a (ha a ha'),
              claimed := by rw [hl]; exact hinert.claimed
            }
            have ihres := ih htail
              (fun step hstep => htarget step (List.mem_cons_of_mem _ hstep)) hmid
            refine ⟨ihres.1, ?_⟩
            intro step hstep
            cases hstep with
            | head => exact ⟨hfeeds, hdet, hstreaming, hcancel⟩
            | tail _ hstep => exact ihres.2 step hstep

/-- Groundwork headline: when request-header authorization rejects a stream
whose body is still open, any pure DATA trace for that stream drains without
producing any dispatch work, and the stream ends (and stays) inert. -/
private theorem rejectStreamAtHeaders_dataTrace_no_dispatch
    {registry : Registry} {state final : State}
    {steps : List (Frame × SharedFrameResult)}
    (streamId : Nat) (inboundHpack outboundHpack : Hpack.State) (endStream : Bool)
    (hclaimed : streamId ≤ state.lastClientStreamId)
    (hactive : ∀ active ∈ state.activeRequestStreams, active.streamId ≠ streamId)
    (trace : DataTrace registry
      (rejectStreamAtHeaders state streamId inboundHpack outboundHpack endStream)
      steps final)
    (htarget : ∀ step ∈ steps, (step.1 : Frame).header.streamId = streamId) :
    final.StreamInert streamId
      ∧ ∀ step ∈ steps,
          (step.2 : SharedFrameResult).requestFeeds = #[] ∧ (step.2).detached = none
            ∧ (step.2).requestStreaming = none ∧ (step.2).cancelDispatches = #[] :=
  trace.inert_no_dispatch streamId htarget
    (rejectStreamAtHeaders_inert state streamId inboundHpack outboundHpack endStream
      hclaimed hactive)

end Connection
end Http2
end Grpc
