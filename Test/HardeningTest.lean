import Std.Async.TCP

import Grpc

open Grpc

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectStatusOk [Repr ε] (result : Except ε α) : IO α := do
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (repr error).pretty)

def expectStatusError (result : Except Status α) : IO Status := do
  match result with
  | .ok _ => throw (IO.userError "expected gRPC status error")
  | .error status => pure status

def u32be (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (UInt8.ofNat ((n / 16777216) % 256))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

def grpcMessageBytes (data : ByteArray) : ByteArray :=
  (ByteArray.empty.push 0).append ((u32be data.size).append data)

def repeatByte (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

def echoMethod : MethodName :=
  { service := "lean.example.proto.NoteService", method := "Echo" }

def echoRegistry : Registry :=
  Registry.empty.registerUnary echoMethod fun request => do
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }

def requestHeaders : _root_.Http2.Headers :=
  _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

def clientSettingsWire : IO ByteArray := do
  let frame ← expectStatusOk (_root_.Http2.Settings.frame #[])
  expectStatusOk (_root_.Http2.Frame.encode frame)

def encodedRequestHeaderBlock : IO ByteArray := do
  let encoded ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  pure encoded.1

def frameWire (frameType : _root_.Http2.FrameType) (flags : UInt8) (streamId : Nat)
    (payload : ByteArray) : IO ByteArray := do
  expectStatusOk (_root_.Http2.Frame.encode {
    header := {
      length := payload.size,
      frameType := frameType,
      flags := flags,
      streamId := streamId
    },
    payload := payload
  })

partial def awaitFrame (emittedRef : IO.Ref (Array _root_.Http2.Frame))
    (want : _root_.Http2.FrameType) (attempts : Nat) : IO Bool := do
  let emitted ← emittedRef.get
  let found := emitted.any fun frame =>
    frame.header.frameType == want && frame.header.streamId == 1
  if found then
    pure true
  else if attempts == 0 then
    pure false
  else do
    IO.sleep 10
    awaitFrame emittedRef want (attempts - 1)

def sharedConnection : IO (Std.Mutex Grpc.Http2.Connection.State × IO.Ref (Array _root_.Http2.Frame)) := do
  let initial := Grpc.Http2.Connection.initialState
  let stateMutex ← Std.Mutex.new {
    initial with
    protocol := {
      initial.protocol with
      prefaceReceived := true
      receivedSettings := true
    }
  }
  let emittedRef ← IO.mkRef (#[] : Array _root_.Http2.Frame)
  pure (stateMutex, emittedRef)

/-- A handler that dies with an IO error still produces a gRPC status response. -/
def testHandlerCrashReturnsStatus : IO Unit := do
  let registry := Registry.empty.registerUnary echoMethod fun _ =>
    ExceptT.mk (throw (IO.userError "handler crashed") : IO (Except Status UnaryResponse))
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders 1 headerBlock
  let body := grpcMessageBytes (repeatByte 3 5)
  let dataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream 1 body
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let wire := ((← clientSettingsWire).append headersWire).append dataWire
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex wire emit with
  | .error status => throw (IO.userError status.message)
  | .ok () => pure ()
  let sawResponse ← awaitFrame emittedRef _root_.Http2.FrameType.headers 100
  expect sawResponse "crashed handler should still produce a response with a gRPC status"

partial def cancellableHandlerLoop : IO (Except Status UnaryResponse) := do
  if ← IO.checkCanceled then
    throw (IO.userError "handler cancelled")
  else do
    IO.sleep 5
    cancellableHandlerLoop

partial def observedCancellableHandlerLoop (sawCancellation : IO.Ref Bool) :
    IO (Except Status UnaryResponse) := do
  if ← IO.checkCanceled then
    sawCancellation.set true
    throw (IO.userError "handler cancelled")
  else do
    IO.sleep 5
    observedCancellableHandlerLoop sawCancellation

partial def awaitTaskFinished (task : Task α) (remainingMilliseconds : Nat) : IO Bool := do
  if ← IO.hasFinished task then
    pure true
  else if remainingMilliseconds == 0 then
    pure false
  else
    IO.sleep 1
    awaitTaskFinished task (remainingMilliseconds - 1)

partial def awaitNoActiveDispatches (stateMutex : Std.Mutex Grpc.Http2.Connection.State)
    (remainingMilliseconds : Nat) : IO Bool := do
  if (← stateMutex.atomically get).activeDispatches.isEmpty then
    pure true
  else if remainingMilliseconds == 0 then
    pure false
  else
    IO.sleep 1
    awaitNoActiveDispatches stateMutex (remainingMilliseconds - 1)

partial def awaitFlag (flag : IO.Ref Bool) (remainingMilliseconds : Nat) : IO Bool := do
  if ← flag.get then
    pure true
  else if remainingMilliseconds == 0 then
    pure false
  else
    IO.sleep 1
    awaitFlag flag (remainingMilliseconds - 1)

structure SocketFrameState where
  decoder : _root_.Http2.Frame.DecodeState := {}
  frames : Array _root_.Http2.Frame := #[]

partial def readSocketFramesUntil (client : Std.Async.TCP.Socket.Client)
    (state : SocketFrameState) (done : Array _root_.Http2.Frame -> Bool) : IO SocketFrameState := do
  if done state.frames then
    pure state
  else
    match ← (client.recv? 8192).block with
    | none => pure state
    | some chunk =>
        let decoded ← expectStatusOk (_root_.Http2.Frame.decodeChunk state.decoder chunk)
        readSocketFramesUntil client {
          decoder := { buffered := decoded.buffered },
          frames := state.frames.append decoded.frames
        } done

def readSocketFramesUntilWithin (client : Std.Async.TCP.Socket.Client)
    (state : SocketFrameState) (done : Array _root_.Http2.Frame -> Bool)
    (remainingMilliseconds : Nat) (message : String) : IO SocketFrameState := do
  let task ← IO.asTask (readSocketFramesUntil client state done)
  unless ← awaitTaskFinished task remainingMilliseconds do
    IO.cancel task
    throw (IO.userError message)
  match ← IO.wait task with
  | .error error => throw error
  | .ok state => pure state

structure DecodedServerHeaderBlock where
  streamId : Nat
  headers : _root_.Http2.Headers

/-- Decode server header blocks in wire order with one HPACK state, as a real
client must.  Keeping the stream id lets tests inspect trailers independently
after several calls reuse a connection. -/
def decodeServerHeaderBlocks (frames : Array _root_.Http2.Frame) :
    IO (Array DecodedServerHeaderBlock) := do
  let mut hpack : _root_.Http2.Hpack.State := {}
  let mut blocks := #[]
  let mut payload := ByteArray.empty
  let mut streamId? : Option Nat := none
  for frame in frames do
    match streamId? with
    | some streamId =>
        payload := payload.append frame.payload
        if _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endHeaders then
          let decoded ← expectStatusOk (_root_.Http2.Hpack.decodeHeaderBlock hpack payload)
          hpack := decoded.state
          blocks := blocks.push { streamId := streamId, headers := decoded.headers }
          payload := ByteArray.empty
          streamId? := none
    | none =>
        if frame.header.frameType == _root_.Http2.FrameType.headers then
          if _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endHeaders then
            let decoded ← expectStatusOk (_root_.Http2.Hpack.decodeHeaderBlock hpack frame.payload)
            hpack := decoded.state
            blocks := blocks.push {
              streamId := frame.header.streamId,
              headers := decoded.headers
            }
          else
            payload := frame.payload
            streamId? := some frame.header.streamId
  expect streamId?.isNone "server left an incomplete HPACK response header block"
  pure blocks

def grpcStatusForStream? (blocks : Array DecodedServerHeaderBlock) (streamId : Nat) :
    Option String :=
  blocks.findSome? fun block =>
    if block.streamId == streamId then _root_.Http2.Headers.get? block.headers "grpc-status" else none

/-- Aggregate request limits are enforced incrementally. An oversized framed
message is rejected as soon as its DATA arrives, without waiting for
END_STREAM, retaining the request, invoking the handler, or returning stream
receive credit that could let the peer continue an unbounded upload. -/
def testAggregateRequestLimitBeforeEndStream : IO Unit := do
  let handlerInvoked ← IO.mkRef false
  let registry := Registry.empty
    |>.withMaxReceiveMessageSize 8
    |>.registerUnary echoMethod (fun request => do
      handlerInvoked.set true
      pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok })
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire _root_.Http2.FrameType.headers
    _root_.Http2.FrameFlag.endHeaders 1 headerBlock
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex headersWire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  emittedRef.set #[]

  let oversizedBody := grpcMessageBytes (repeatByte 9 0xa5)
  let dataWire ← frameWire _root_.Http2.FrameType.data 0 1 oversizedBody
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex dataWire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()

  let emitted ← emittedRef.get
  let blocks ← decodeServerHeaderBlocks emitted
  expectEq (grpcStatusForStream? blocks 1) (some "8")
    "oversized aggregate DATA should return RESOURCE_EXHAUSTED before END_STREAM"
  let reset ← match emitted.find? fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == .rstStream with
    | some frame => pure frame
    | none => throw (IO.userError "oversized aggregate DATA should reset its stream")
  expectEq (← expectStatusOk (_root_.Http2.RstStream.decode reset))
    _root_.Http2.ErrorCode.enhanceYourCalm
    "oversized aggregate DATA should use ENHANCE_YOUR_CALM"
  expect (!emitted.any fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == .windowUpdate)
    "rejected aggregate DATA must not replenish stream receive credit"
  expect (!(← handlerInvoked.get))
    "oversized aggregate DATA must not invoke the unary handler"
  let state ← stateMutex.atomically get
  expect (!state.streams.any fun stream => stream.streamId == 1)
    "oversized aggregate DATA must release its retained request body"

def gzipRequestHeadersForPath (path : String) : _root_.Http2.Headers :=
  _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
    |>.insert "grpc-encoding" "gzip"

def compressedMessageWire (size : Nat) : IO ByteArray := do
  let message := Message.gzipped (repeatByte size 0x41)
  expect (message.compressed == .compressed)
    "compressed-memory regression payload must actually use gzip"
  expectStatusOk message.encode

def expectResourceExhaustedReset (frames : Array _root_.Http2.Frame)
    (label : String) : IO Unit := do
  let blocks ← decodeServerHeaderBlocks frames
  expectEq (grpcStatusForStream? blocks 1) (some "8")
    s!"{label}: expected RESOURCE_EXHAUSTED"
  let reset ← match frames.find? fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == .rstStream with
    | some frame => pure frame
    | none => throw (IO.userError s!"{label}: expected RST_STREAM")
  expectEq (← expectStatusOk (_root_.Http2.RstStream.decode reset))
    _root_.Http2.ErrorCode.enhanceYourCalm
    s!"{label}: expected ENHANCE_YOUR_CALM"

/-- The retained decoded bound admits one exact-limit message, but rejects a
small compressed aggregate whose normalized messages cumulatively exceed it. -/
def testAggregateDecodedRetentionBound : IO Unit := do
  let decodedLimit := 2048
  let exactWire ← compressedMessageWire decodedLimit
  let exact ← expectStatusOk (Message.decompressBody true (some decodedLimit) exactWire)
  expectEq exact.size (Message.prefixLength + decodedLimit)
    "exact decoded aggregate limit should be admitted"

  let handlerInvoked ← IO.mkRef false
  let registry := Registry.empty
    |>.withMaxReceiveMessageSize decodedLimit
    |>.registerUnary echoMethod (fun request => do
      handlerInvoked.set true
      pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok })
  let encodedHeaders ← expectStatusOk <| _root_.Http2.Hpack.encodeHeaderBlock {}
    (gzipRequestHeadersForPath "/lean.example.proto.NoteService/Echo")
  let headersWire ← frameWire _root_.Http2.FrameType.headers
    _root_.Http2.FrameFlag.endHeaders 1 encodedHeaders.1
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex headersWire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  emittedRef.set #[]
  let first ← compressedMessageWire 1200
  let second ← compressedMessageWire 1200
  let dataWire ← frameWire _root_.Http2.FrameType.data 0 1 (first.append second)
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex dataWire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  expectResourceExhaustedReset (← emittedRef.get) "aggregate gzip expansion"
  expect (!(← handlerInvoked.get))
    "aggregate gzip expansion must be rejected before handler invocation"

/-- A batch of individually valid gzip messages cannot multiply the memory
retained in a live request-stream producer beyond the configured total. -/
def testStreamingDecodedRetentionBound : IO Unit := do
  let decodedLimit := 2048
  let method : MethodName := {
    service := "lean.example.proto.NoteService"
    method := "Collect"
  }
  let registry := Registry.empty
    |>.withMaxReceiveMessageSize decodedLimit
    |>.registerClientStreamingStream method (fun request => do
      let messages ← request.messages.collect
      pure {
        metadata := _root_.Http2.Headers.empty
        data := (toString messages.size).toUTF8
        status := Status.ok
      })
  let encodedHeaders ← expectStatusOk <| _root_.Http2.Hpack.encodeHeaderBlock {}
    (gzipRequestHeadersForPath method.path)
  let headersWire ← frameWire _root_.Http2.FrameType.headers
    _root_.Http2.FrameFlag.endHeaders 1 encodedHeaders.1
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex headersWire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  emittedRef.set #[]
  let first ← compressedMessageWire 1200
  let second ← compressedMessageWire 1200
  let dataWire ← frameWire _root_.Http2.FrameType.data 0 1 (first.append second)
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex dataWire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  expectResourceExhaustedReset (← emittedRef.get) "streaming gzip expansion"
  let state ← stateMutex.atomically get
  expect state.activeRequestStreams.isEmpty
    "streaming gzip expansion must release its producer accounting"
  expect state.activeDispatches.isEmpty
    "streaming gzip expansion must cancel and join its handler"

/-- Concurrent handlers may enqueue their already-encoded response blocks in
either order. Keeping the encoder table at zero makes every block independently
decodable even after a peer advertises a nonzero table capacity. -/
def testResponseHpackOrderIndependence : IO Unit := do
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let settings ← expectStatusOk <| _root_.Http2.Settings.frame #[{
    id := .headerTableSize
    value := 8192
  }]
  let wire ← expectStatusOk (_root_.Http2.Frame.encode settings)
  match ← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned Registry.empty stateMutex wire emit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  let state ← stateMutex.atomically get
  expect (state.protocol.hpackEncode.maxSize == 0 &&
      state.protocol.hpackEncode.dynamic.isEmpty)
    "peer SETTINGS must not re-enable the concurrent response encoder table"
  let firstHeaders := _root_.Http2.Headers.empty
    |>.insert ":status" "200"
    |>.insert "content-type" "application/grpc"
    |>.insert "x-response" "first"
  let secondHeaders := _root_.Http2.Headers.empty
    |>.insert ":status" "200"
    |>.insert "content-type" "application/grpc"
    |>.insert "x-response" "second"
  let (firstBlock, afterFirst) ← expectStatusOk <|
    _root_.Http2.Hpack.encodeHeaderBlock state.protocol.hpackEncode firstHeaders
  expect afterFirst.canReuseHeaderBlock
    "the first post-SETTINGS block must settle the zero-table size update"
  let (secondBlock, _) ← expectStatusOk <|
    _root_.Http2.Hpack.encodeHeaderBlock afterFirst secondHeaders
  let decodedSecond ← expectStatusOk <| _root_.Http2.Hpack.decodeHeaderBlock {} secondBlock
  let decodedFirst ← expectStatusOk <| _root_.Http2.Hpack.decodeHeaderBlock {} firstBlock
  expectEq (_root_.Http2.Headers.get? decodedSecond.headers "x-response") (some "second")
    "later concurrent HPACK block must decode before the earlier block"
  expectEq (_root_.Http2.Headers.get? decodedFirst.headers "x-response") (some "first")
    "earlier concurrent HPACK block must remain independently decodable"

  -- Exercise the actual response path with the first encoded response parked
  -- in its emitter while a second handler encodes and emits behind it.
  emittedRef.set #[]
  let firstParked ← IO.mkRef false
  let releaseFirst ← IO.mkRef false
  let secondEmitted ← IO.mkRef false
  let reorderedRef ← IO.mkRef (#[] : Array _root_.Http2.Frame)
  let reorderedEmit (frames : Array _root_.Http2.Frame) : IO Unit := do
    if frames.any fun frame =>
        frame.header.streamId == 1 && frame.header.frameType == .headers then
      firstParked.set true
      while !(← releaseFirst.get) do
        IO.sleep 1
    if frames.any fun frame =>
        frame.header.streamId == 3 && frame.header.frameType == .headers then
      secondEmitted.set true
    reorderedRef.modify fun out => out.append frames
  let registry := Registry.empty.registerUnary echoMethod fun request => do
    let label := if request.data[0]? == some 1 then "first" else "second"
    pure {
      metadata := _root_.Http2.Headers.empty.insert "x-response" label
      data := request.data
      status := Status.ok
    }
  let (requestBlock1, requestEncoder) ← expectStatusOk <|
    _root_.Http2.Hpack.encodeHeaderBlock {} requestHeaders
  let (requestBlock3, _) ← expectStatusOk <|
    _root_.Http2.Hpack.encodeHeaderBlock requestEncoder requestHeaders
  let requestWire (streamId : Nat) (block : ByteArray) (value : UInt8) : IO ByteArray := do
    let headers ← frameWire _root_.Http2.FrameType.headers
      _root_.Http2.FrameFlag.endHeaders streamId block
    let data ← frameWire _root_.Http2.FrameType.data
      _root_.Http2.FrameFlag.endStream streamId (grpcMessageBytes (ByteArray.empty.push value))
    pure (headers.append data)
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned
      registry stateMutex (← requestWire 1 requestBlock1 1) reorderedEmit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  expect (← awaitFlag firstParked 1000)
    "first response did not reach the parked concurrent emitter"
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned
      registry stateMutex (← requestWire 3 requestBlock3 2) reorderedEmit with
  | .error error => throw (IO.userError error.message)
  | .ok () => pure ()
  expect (← awaitFlag secondEmitted 1000)
    "second response did not overtake the parked first response"
  releaseFirst.set true
  expect (← awaitNoActiveDispatches stateMutex 1000)
    "reordered response handlers did not retire"
  let reordered ← reorderedRef.get
  let blocks ← decodeServerHeaderBlocks reordered
  let firstResponse := blocks.findSome? fun block =>
    if block.streamId == 1 then
      (_root_.Http2.Headers.get? block.headers "x-response").map fun value =>
        (block.streamId, value)
    else none
  let secondResponse := blocks.findSome? fun block =>
    if block.streamId == 3 then
      (_root_.Http2.Headers.get? block.headers "x-response").map fun value =>
        (block.streamId, value)
    else none
  expectEq firstResponse (some (1, "first"))
    "parked first response must decode after reordered emission"
  expectEq secondResponse (some (3, "second"))
    "overtaking second response must decode without the first block"
  let firstNamedBlock := blocks.findIdx? fun block =>
    block.streamId == 1 && _root_.Http2.Headers.get? block.headers "x-response" == some "first"
  let secondNamedBlock := blocks.findIdx? fun block =>
    block.streamId == 3 && _root_.Http2.Headers.get? block.headers "x-response" == some "second"
  expect (secondNamedBlock.isSome && firstNamedBlock.isSome &&
      secondNamedBlock.getD 0 < firstNamedBlock.getD 0)
    "test did not actually reverse the concurrently encoded response blocks"

def streamEnded (streamId : Nat) (frames : Array _root_.Http2.Frame) : Bool :=
  frames.any fun frame =>
    frame.header.streamId == streamId
      && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream

def responseBodyForStream (frames : Array _root_.Http2.Frame) (streamId : Nat) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun body frame =>
    if frame.header.streamId == streamId && frame.header.frameType == _root_.Http2.FrameType.data then
      body.append frame.payload
    else
      body

/-- A complete, authorized header block with an incomplete body must not rely
on the socket event loop for deadline delivery.  In particular, arbitrary
authorization IO on another stream may occupy that loop indefinitely. -/
def testPendingBodyDeadlineIndependentOfBlockedAuthorization : IO Unit := do
  let authorizationBlocked ← IO.mkRef false
  let releaseAuthorization ← IO.mkRef false
  let registry := (Registry.empty.registerUnary echoMethod fun request => do
      pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer (fun entry metadata => do
      if _root_.Http2.Headers.get? metadata "authorization" == some "block" then
        authorizationBlocked.set true
        while !(← releaseAuthorization.get) do
          IO.sleep 1
      pure (.accept entry.handler))

  let scheduler ← Grpc.Http2.Connection.DeadlineScheduler.new
  let initial := Grpc.Http2.Connection.initialState
  let stateMutex ← Std.Mutex.new {
    initial with
    protocol := {
      initial.protocol with
      prefaceReceived := true
      receivedSettings := true
    }
    deadlineScheduler := some scheduler
  }
  let emittedRef ← IO.mkRef (#[] : Array _root_.Http2.Frame)
  let deadlineEmitted ← IO.mkRef false
  let emit (frames : Array _root_.Http2.Frame) : IO Unit := do
    if frames.any fun frame =>
        frame.header.streamId == 1
          && frame.header.frameType == _root_.Http2.FrameType.headers
          && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream then
      deadlineEmitted.set true
    emittedRef.modify fun emitted => emitted.append frames

  let timedHeaders := requestHeaders
    |>.insert "authorization" "allow"
    |>.insert "grpc-timeout" "250m"
  let timedBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders
    1 timedBlock.1
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex timedWire emit with
  | .error status =>
      discard <| Std.Async.Async.block <| Grpc.Http2.Connection.cancelActiveSharedOwned stateMutex
      throw (IO.userError status.message)
  | .ok () => pure ()
  let pendingState ← stateMutex.atomically get
  expect (Grpc.Http2.Connection.nextPendingDeadline? pendingState).isSome
    "timed request should be waiting for its incomplete body"
  expect (Grpc.Http2.Connection.nextPendingDeadlineFallback? pendingState).isNone
    "independent scheduler should suppress the duplicate connection-loop timer"
  let fallbackState := { pendingState with deadlineScheduler := none }
  expect (Grpc.Http2.Connection.nextPendingDeadlineFallback? fallbackState).isSome
    "state owners without an independent scheduler should retain the fallback timer"

  let blockedHeaders := requestHeaders.insert "authorization" "block"
  let blockedBlock ← expectStatusOk
    (_root_.Http2.Hpack.encodeHeaderBlock timedBlock.2 blockedHeaders)
  let blockedWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders
    3 blockedBlock.1
  let processing ← IO.asTask <|
    Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex blockedWire emit
  try
    unless ← awaitFlag authorizationBlocked 1000 do
      throw (IO.userError "second stream did not enter its blocking authorizer")
    unless ← awaitFlag deadlineEmitted 2000 do
      throw (IO.userError
        "pending-body deadline was delayed by another stream's blocking authorizer")
    expect (!(← IO.hasFinished processing))
      "deadline test requires the other stream's authorizer to remain blocked"
    let blocks ← decodeServerHeaderBlocks (← emittedRef.get)
    expectEq (grpcStatusForStream? blocks 1) (some "4")
      "pending-body timer should emit DEADLINE_EXCEEDED"
    releaseAuthorization.set true
    unless ← awaitTaskFinished processing 1000 do
      throw (IO.userError "blocked authorizer did not finish after release")
    match processing.get with
    | .error error => throw error
    | .ok (.error status) => throw (IO.userError status.message)
    | .ok (.ok ()) => pure ()
  catch error =>
    releaseAuthorization.set true
    IO.cancel processing
    discard <| Std.Async.Async.block <| Grpc.Http2.Connection.cancelActiveSharedOwned stateMutex
    throw error
  discard <| Std.Async.Async.block <| Grpc.Http2.Connection.cancelActiveSharedOwned stateMutex

/-- The active-handler deadline path must terminate only the expired RPC, not
its managed h2c connection.  The first complete request enters a sleeping
handler and returns status 4; the same socket then completes an untimed call. -/
def testManagedH2CDeadlineThenConnectionReuse : IO Unit := do
  let slowPayload := ByteArray.mk #[1, 1, 2, 3, 5]
  let fastPayload := ByteArray.mk #[8, 13, 21]
  let slowStarted ← IO.mkRef false
  let slowFinishedNaturally ← IO.mkRef false
  let fastHandled ← IO.mkRef false
  let registry := Registry.empty.registerUnary echoMethod fun request => do
    if request.data == slowPayload then
      slowStarted.set true
      IO.sleep 2000
      slowFinishedNaturally.set true
    else if request.data == fastPayload then
      fastHandled.set true
    pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let settings ← clientSettingsWire
  let timedHeaders := requestHeaders.insert "grpc-timeout" "250m"
  let timedBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedHeadersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders
    1 timedBlock.1
  let timedDataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream
    1 (grpcMessageBytes slowPayload)
  (client.send (_root_.Http2.connectionPreface
    |>.append settings
    |>.append timedHeadersWire
    |>.append timedDataWire)).block

  let afterDeadline ← readSocketFramesUntilWithin client {} (streamEnded 1) 5000
    "managed h2c handler did not return its deadline status"
  expect (← slowStarted.get)
    "timed managed h2c handler should start before its deadline"
  expect (!(← slowFinishedNaturally.get))
    "managed deadline response must arrive before the sleeping handler finishes naturally"
  let deadlineBlocks ← decodeServerHeaderBlocks afterDeadline.frames
  expectEq (grpcStatusForStream? deadlineBlocks 1) (some "4")
    "sleeping managed h2c handler should return DEADLINE_EXCEEDED"
  expect (!afterDeadline.frames.any fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == _root_.Http2.FrameType.data)
    "expired unary handler must not emit its late response DATA"

  let fastBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock timedBlock.2 requestHeaders)
  let fastHeadersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders
    3 fastBlock.1
  let fastDataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream
    3 (grpcMessageBytes fastPayload)
  (client.send (fastHeadersWire.append fastDataWire)).block

  let afterReuse ← readSocketFramesUntilWithin client afterDeadline (streamEnded 3) 5000
    "managed h2c connection did not serve a request after handler deadline"
  let allBlocks ← decodeServerHeaderBlocks afterReuse.frames
  expectEq (grpcStatusForStream? allBlocks 3) (some "0")
    "post-deadline request on the same connection should succeed"
  let responseBody := responseBodyForStream afterReuse.frames 3
  let responseMessages ← expectStatusOk (Message.decodeAll responseBody)
  expectEq responseMessages.size 1
    "post-deadline request should return exactly one response message"
  expectEq responseMessages[0]!.data fastPayload
    "post-deadline request should echo its payload"
  expect (← fastHandled.get)
    "post-deadline request should invoke its handler"

  Grpc.Server.shutdown server
  Grpc.Server.wait server
  (client.shutdown).block

/-- _root_.Http2.Header authorization consumes the same absolute budget as body and handler
work.  Expiring a custom authorizer must reject only that RPC, suppress its
handler, and leave the managed h2c connection usable by an untimed call. -/
def testManagedH2CAuthorizerDeadlineThenConnectionReuse : IO Unit := do
  let slowPayload := ByteArray.mk #[34, 55, 89]
  let fastPayload := ByteArray.mk #[144, 233]
  let authorizerStarted ← IO.mkRef false
  let authorizerFinishedNaturally ← IO.mkRef false
  let fastAuthorized ← IO.mkRef false
  let slowHandlerInvoked ← IO.mkRef false
  let fastHandlerInvoked ← IO.mkRef false
  let registry := (Registry.empty.registerUnary echoMethod fun request => do
      if request.data == slowPayload then
        slowHandlerInvoked.set true
      else if request.data == fastPayload then
        fastHandlerInvoked.set true
      pure { metadata := _root_.Http2.Headers.empty, data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer (fun entry metadata => do
      match _root_.Http2.Headers.get? metadata "authorization" with
      | some "slow-deadline" =>
          authorizerStarted.set true
          IO.sleep 2000
          authorizerFinishedNaturally.set true
          pure (.accept entry.handler)
      | _ =>
          fastAuthorized.set true
          pure (.accept entry.handler))

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let settings ← clientSettingsWire
  let timedHeaders := requestHeaders
    |>.insert "authorization" "slow-deadline"
    |>.insert "grpc-timeout" "250m"
  let timedBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedHeadersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders
    1 timedBlock.1
  let timedDataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream
    1 (grpcMessageBytes slowPayload)
  (client.send (_root_.Http2.connectionPreface
    |>.append settings
    |>.append timedHeadersWire
    |>.append timedDataWire)).block

  let afterDeadline ← readSocketFramesUntilWithin client {} (streamEnded 1) 5000
    "managed h2c authorizer did not return its deadline status"
  expect (← authorizerStarted.get)
    "custom authorizer should start before its request deadline"
  expect (!(← authorizerFinishedNaturally.get))
    "authorizer deadline response must arrive before the slow callback finishes naturally"
  expect (!(← slowHandlerInvoked.get))
    "an expired custom authorizer must not invoke the RPC handler"
  let deadlineBlocks ← decodeServerHeaderBlocks afterDeadline.frames
  expectEq (grpcStatusForStream? deadlineBlocks 1) (some "4")
    "expired custom authorizer should return DEADLINE_EXCEEDED"
  expect (!afterDeadline.frames.any fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == _root_.Http2.FrameType.data)
    "expired custom authorizer must not emit response DATA"

  let fastHeaders := requestHeaders.insert "authorization" "allow"
  let fastBlock ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock timedBlock.2 fastHeaders)
  let fastHeadersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders
    3 fastBlock.1
  let fastDataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream
    3 (grpcMessageBytes fastPayload)
  (client.send (fastHeadersWire.append fastDataWire)).block

  let afterReuse ← readSocketFramesUntilWithin client afterDeadline (streamEnded 3) 5000
    "managed h2c connection did not recover after authorizer deadline"
  let allBlocks ← decodeServerHeaderBlocks afterReuse.frames
  expectEq (grpcStatusForStream? allBlocks 3) (some "0")
    "untimed request after authorizer deadline should succeed"
  let responseMessages ← expectStatusOk
    (Message.decodeAll (responseBodyForStream afterReuse.frames 3))
  expectEq responseMessages.size 1
    "post-authorizer-deadline request should return one response message"
  expectEq responseMessages[0]!.data fastPayload
    "post-authorizer-deadline request should echo its payload"
  expect (← fastAuthorized.get)
    "custom authorizer should promptly allow the untimed recovery request"
  expect (← fastHandlerInvoked.get)
    "untimed recovery request should invoke its handler"

  Grpc.Server.shutdown server
  Grpc.Server.wait server
  (client.shutdown).block

/-- A peer RST is already the terminal stream signal. It cancels the in-flight
dispatch and removes stream state without echoing a second RST_STREAM after the
cancelled handler unwinds. -/
def testPeerRstCancelsDispatchWithoutEchoReset : IO Unit := do
  let registry := Registry.empty.registerUnary echoMethod fun _ =>
    ExceptT.mk cancellableHandlerLoop
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders 1 headerBlock
  let body := grpcMessageBytes (repeatByte 3 5)
  let dataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream 1 body
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let wire := ((← clientSettingsWire).append headersWire).append dataWire
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex wire emit with
  | .error status => throw (IO.userError status.message)
  | .ok () => pure ()
  let rstFrame ← expectStatusOk (_root_.Http2.RstStream.frame 1 _root_.Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (_root_.Http2.Frame.encode rstFrame)
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex rstWire emit with
  | .error status => throw (IO.userError status.message)
  | .ok () => pure ()
  let state ← stateMutex.atomically get
  expect state.activeDispatches.isEmpty
    "peer RST should remove the cancelled dispatch from connection state"
  let sawRst ← awaitFrame emittedRef _root_.Http2.FrameType.rstStream 200
  expect (!sawRst) "peer RST should not provoke a second server RST_STREAM"

/-- A deadline wraps the user handler in a child task.  Peer cancellation must
reach that exact child rather than merely marking its suspended dispatch owner:
the polling handler observes cancellation, the dispatch retires without waiting
for its long deadline, and the peer's terminal RST is not echoed. -/
def testPeerRstCancelsDeadlineHandlerWithoutEchoReset : IO Unit := do
  let sawCancellation ← IO.mkRef false
  let registry := Registry.empty.registerUnary echoMethod fun _ =>
    ExceptT.mk (observedCancellableHandlerLoop sawCancellation)
  let timedHeaders := requestHeaders.insert "grpc-timeout" "1H"
  let encodedHeaders ← expectStatusOk (_root_.Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let headersWire ← frameWire _root_.Http2.FrameType.headers _root_.Http2.FrameFlag.endHeaders 1 encodedHeaders.1
  let body := grpcMessageBytes (repeatByte 3 5)
  let dataWire ← frameWire _root_.Http2.FrameType.data _root_.Http2.FrameFlag.endStream 1 body
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array _root_.Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let wire := ((← clientSettingsWire).append headersWire).append dataWire
  match ← Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex wire emit with
  | .error status => throw (IO.userError status.message)
  | .ok () => pure ()
  let rstFrame ← expectStatusOk (_root_.Http2.RstStream.frame 1 _root_.Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (_root_.Http2.Frame.encode rstFrame)
  let rstTask ← IO.asTask
    (Std.Async.Async.block <| Grpc.Http2.Connection.processBytesSharedWithOwned registry stateMutex rstWire emit)
  unless ← awaitTaskFinished rstTask 1000 do
    IO.cancel rstTask
    throw (IO.userError "peer RST did not promptly retire a deadline-wrapped handler")
  match ← IO.wait rstTask with
  | .error error => throw error
  | .ok (.error status) => throw (IO.userError status.message)
  | .ok (.ok ()) => pure ()
  expect (← sawCancellation.get)
    "deadline-wrapped handler did not observe peer cancellation"
  let state ← stateMutex.atomically get
  expect state.activeDispatches.isEmpty
    "peer RST should promptly remove the deadline-wrapped dispatch"
  let sawRst ← awaitFrame emittedRef _root_.Http2.FrameType.rstStream 200
  expect (!sawRst)
    "peer RST should not provoke a second RST_STREAM from a deadline-wrapped dispatch"

def main : IO Unit := do
  testHandlerCrashReturnsStatus
  IO.println "handler crash returns status ok"
  testAggregateRequestLimitBeforeEndStream
  IO.println "aggregate request limit rejects DATA before END_STREAM"
  testAggregateDecodedRetentionBound
  IO.println "aggregate decoded retention bound rejects gzip expansion"
  testStreamingDecodedRetentionBound
  IO.println "streaming decoded retention bound rejects gzip expansion"
  testResponseHpackOrderIndependence
  IO.println "concurrent response HPACK blocks are order independent"
  testPendingBodyDeadlineIndependentOfBlockedAuthorization
  IO.println "pending-body deadline is independent of blocked cross-stream authorization"
  testPeerRstCancelsDispatchWithoutEchoReset
  IO.println "peer RST cancels dispatch without an echo reset"
  testPeerRstCancelsDeadlineHandlerWithoutEchoReset
  IO.println "peer RST cancels a deadline-wrapped handler without an echo reset"
  testManagedH2CDeadlineThenConnectionReuse
  IO.println "managed h2c handler deadline preserves connection reuse"
  testManagedH2CAuthorizerDeadlineThenConnectionReuse
  IO.println "managed h2c authorizer deadline preserves connection reuse"
  IO.println "all hardening assertions passed"
