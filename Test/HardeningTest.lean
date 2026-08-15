import Std.Async.TCP

import Grpc

open Grpc

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def expectStatusOk (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

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
    pure { metadata := Metadata.empty, data := request.data, status := Status.ok }

def requestHeaders : Metadata :=
  Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

def clientSettingsWire : IO ByteArray := do
  let frame ← expectStatusOk (Http2.Settings.frame #[])
  expectStatusOk (Http2.Frame.encode frame)

def encodedRequestHeaderBlock : IO ByteArray := do
  let encoded ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} requestHeaders)
  pure encoded.1

def frameWire (frameType : Http2.FrameType) (flags : UInt8) (streamId : Nat)
    (payload : ByteArray) : IO ByteArray := do
  expectStatusOk (Http2.Frame.encode {
    header := {
      length := payload.size,
      frameType := frameType,
      flags := flags,
      streamId := streamId
    },
    payload := payload
  })

def dataPayloads (frames : Array Http2.Frame) : Array ByteArray :=
  frames.filterMap fun frame =>
    if frame.header.frameType == Http2.FrameType.data then some frame.payload else none

/-- A padded DATA frame must be de-padded before gRPC message decoding. -/
def testPaddedDataFrame : IO Unit := do
  let body := grpcMessageBytes (repeatByte 5 42)
  let padding := repeatByte 7 0
  let paddedPayload := ((ByteArray.empty.push 7).append body).append padding
  let settings ← clientSettingsWire
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders 1 headerBlock
  let dataWire ← frameWire Http2.FrameType.data
    (Http2.FrameFlag.combine #[Http2.FrameFlag.endStream, Http2.FrameFlag.padded]) 1 paddedPayload
  let result ← Http2.Connection.processBytes echoRegistry {} (
    Http2.connectionPreface
      |>.append settings
      |>.append headersWire
      |>.append dataWire
  )
  let (_, emitted) ← expectStatusOk result
  let responses := dataPayloads emitted
  expect (responses.size >= 1) "padded DATA request should produce a response DATA frame"
  expectEq responses[0]! (grpcMessageBytes (repeatByte 5 42))
    "echo response should contain the de-padded request message"

/-- Padding length >= remaining payload is a protocol violation. -/
def testInvalidPadding : IO Unit := do
  let body := grpcMessageBytes (repeatByte 3 1)
  let paddedPayload := (ByteArray.empty.push 255).append body
  let settings ← clientSettingsWire
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders 1 headerBlock
  let dataWire ← frameWire Http2.FrameType.data
    (Http2.FrameFlag.combine #[Http2.FrameFlag.endStream, Http2.FrameFlag.padded]) 1 paddedPayload
  let result ← Http2.Connection.processBytes echoRegistry {} (
    Http2.connectionPreface
      |>.append settings
      |>.append headersWire
      |>.append dataWire
  )
  discard <| expectStatusError result

/-- HEADERS carrying padding and a priority section must still decode the header block. -/
def testPaddedPriorityHeaders : IO Unit := do
  let headerBlock ← encodedRequestHeaderBlock
  let prioritySection := ByteArray.mk #[0x80, 0x00, 0x00, 0x03, 0x10]
  let padding := repeatByte 4 0
  let payload := ((ByteArray.empty.push 4).append prioritySection)
    |>.append headerBlock
    |>.append padding
  let flags := Http2.FrameFlag.combine
    #[Http2.FrameFlag.endHeaders, Http2.FrameFlag.padded, Http2.FrameFlag.priority]
  let settings ← clientSettingsWire
  let headersWire ← frameWire Http2.FrameType.headers flags 1 payload
  let body := grpcMessageBytes (repeatByte 2 9)
  let dataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream 1 body
  let result ← Http2.Connection.processBytes echoRegistry {} (
    Http2.connectionPreface
      |>.append settings
      |>.append headersWire
      |>.append dataWire
  )
  let (_, emitted) ← expectStatusOk result
  let responses := dataPayloads emitted
  expect (responses.size >= 1) "padded+priority HEADERS request should still be served"
  expectEq responses[0]! body "echo response should match request body"

/-- A header block reassembled from CONTINUATION frames is capped. -/
def testContinuationSizeCap : IO Unit := do
  let settings ← clientSettingsWire
  let headersWire ← frameWire Http2.FrameType.headers 0 1 (repeatByte 16000 0x1f)
  let mut wire := (Http2.connectionPreface.append settings).append headersWire
  let chunk := repeatByte 16000 0x1f
  for _ in [0:70] do
    let continuationWire ← frameWire Http2.FrameType.continuation 0 1 chunk
    wire := wire.append continuationWire
  let result ← Http2.Connection.processBytes echoRegistry {} wire
  let status ← expectStatusError result
  expect (status.messageD.startsWith "HTTP/2 header block exceeds")
    s!"oversized header block should be rejected, got: {status.messageD}"

/-- A keepalive PING ack clears the pending-keepalive marker. -/
def testKeepalivePingAck : IO Unit := do
  let payload := ByteArray.mk #[1, 2, 3, 4, 5, 6, 7, 8]
  let state : Http2.Connection.State := {
    prefaceReceived := true,
    clientSettingsReceived := true,
    pendingKeepalivePing := some payload
  }
  let ack ← expectStatusOk (Http2.Ping.frame payload (ack := true))
  let result ← Http2.Connection.processFrame Registry.empty state ack
  let (state1, emitted) ← expectStatusOk result
  expectEq emitted.size 0 "PING ack should not emit frames"
  expectEq state1.pendingKeepalivePing none "matching PING ack should clear keepalive marker"
  let otherAck ← expectStatusOk
    (Http2.Ping.frame (ByteArray.mk #[9, 9, 9, 9, 9, 9, 9, 9]) (ack := true))
  let result2 ← Http2.Connection.processFrame Registry.empty state otherAck
  let (state2, _) ← expectStatusOk result2
  expectEq state2.pendingKeepalivePing (some payload)
    "non-matching PING ack should leave keepalive marker in place"

partial def awaitFrame (emittedRef : IO.Ref (Array Http2.Frame))
    (want : Http2.FrameType) (attempts : Nat) : IO Bool := do
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

def sharedConnection : IO (Std.Mutex Http2.Connection.State × IO.Ref (Array Http2.Frame)) := do
  let stateMutex ← Std.Mutex.new ({
    prefaceReceived := true,
    clientSettingsReceived := true
  } : Http2.Connection.State)
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  pure (stateMutex, emittedRef)

/-- A handler that dies with an IO error still produces a gRPC status response. -/
def testHandlerCrashReturnsStatus : IO Unit := do
  let registry := Registry.empty.registerUnary echoMethod fun _ =>
    ExceptT.mk (throw (IO.userError "handler crashed") : IO (Except Status UnaryResponse))
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders 1 headerBlock
  let body := grpcMessageBytes (repeatByte 3 5)
  let dataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream 1 body
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let wire := ((← clientSettingsWire).append headersWire).append dataWire
  match ← Http2.Connection.processBytesSharedWith registry stateMutex wire emit with
  | .error status => throw (IO.userError status.messageD)
  | .ok () => pure ()
  let sawResponse ← awaitFrame emittedRef Http2.FrameType.headers 100
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

partial def awaitNoActiveDispatches (stateMutex : Std.Mutex Http2.Connection.State)
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

/-- Detaching a complete request and publishing its gated handler are separate
mutex transitions.  Once GOAWAY is active, the state between them must remain
non-drained; otherwise the server can elect connection shutdown in the gap and
cancel a request whose stream id it promised to finish. -/
def testPendingDispatchPublicationPreventsFalseDrain : IO Unit := do
  let handlerStarted ← IO.mkRef false
  let registry := Registry.empty.registerUnary echoMethod fun request => do
    handlerStarted.set true
    pure { metadata := Metadata.empty, data := request.data, status := Status.ok }
  let headerBlock ← encodedRequestHeaderBlock
  let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders 1 headerBlock
  let dataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream 1
    (grpcMessageBytes (repeatByte 3 7))
  let stateMutex ← Std.Mutex.new ({
    prefaceReceived := true,
    clientSettingsReceived := true,
    outboundGoAwayLastStreamId := some 1
  } : Http2.Connection.State)
  let emissionEntered ← IO.mkRef false
  let releaseEmission ← IO.mkRef false
  let emit (_frames : Array Http2.Frame) : IO Unit := do
    unless ← emissionEntered.get do
      emissionEntered.set true
      while !(← releaseEmission.get) do
        IO.sleep 1
  let processing ← IO.asTask <|
    Http2.Connection.processBytesSharedWith registry stateMutex
      (headersWire.append dataWire) emit
  try
    unless ← awaitFlag emissionEntered 1000 do
      throw (IO.userError "request did not reach the pre-publication emission gate")
    let gapState ← stateMutex.atomically get
    expect gapState.activeDispatches.isEmpty
      "handler dispatch should still be unpublished while emission is gated"
    expect (gapState.pendingDispatchPublications.contains 1)
      "detached request should retain a pending-publication ownership token"
    expect (Http2.Connection.isDrainedAfterOutboundGoAway
      { gapState with pendingDispatchPublications := #[] })
      "test fixture should otherwise be drained during the publication gap"
    expect (!(Http2.Connection.isDrainedAfterOutboundGoAway gapState))
      "pending dispatch publication must prevent graceful drain election"
    releaseEmission.set true
  catch error =>
    releaseEmission.set true
    IO.cancel processing
    throw error
  unless ← awaitTaskFinished processing 1000 do
    IO.cancel processing
    throw (IO.userError "request did not finish after releasing publication")
  match processing.get with
  | .error error => throw error
  | .ok (.error status) => throw (IO.userError status.messageD)
  | .ok (.ok ()) => pure ()
  unless ← awaitFlag handlerStarted 1000 do
    throw (IO.userError "published request handler did not start")
  let state ← stateMutex.atomically get
  expect state.pendingDispatchPublications.isEmpty
    "successful publication should retire its ownership token"

structure SocketFrameState where
  decoder : Http2.Frame.DecodeState := {}
  frames : Array Http2.Frame := #[]

partial def readSocketFramesUntil (client : Std.Async.TCP.Socket.Client)
    (state : SocketFrameState) (done : Array Http2.Frame -> Bool) : IO SocketFrameState := do
  if done state.frames then
    pure state
  else
    match ← (client.recv? 8192).block with
    | none => pure state
    | some chunk =>
        let decoded ← expectStatusOk (Http2.Frame.decodeChunk state.decoder chunk)
        readSocketFramesUntil client {
          decoder := { buffered := decoded.buffered },
          frames := state.frames.append decoded.frames
        } done

def readSocketFramesUntilWithin (client : Std.Async.TCP.Socket.Client)
    (state : SocketFrameState) (done : Array Http2.Frame -> Bool)
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
  headers : Metadata

/-- Decode server header blocks in wire order with one HPACK state, as a real
client must.  Keeping the stream id lets tests inspect trailers independently
after several calls reuse a connection. -/
def decodeServerHeaderBlocks (frames : Array Http2.Frame) :
    IO (Array DecodedServerHeaderBlock) := do
  let mut hpack : Http2.Hpack.State := {}
  let mut blocks := #[]
  let mut payload := ByteArray.empty
  let mut streamId? : Option Nat := none
  for frame in frames do
    match streamId? with
    | some streamId =>
        payload := payload.append frame.payload
        if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
          let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock hpack payload)
          hpack := decoded.state
          blocks := blocks.push { streamId := streamId, headers := decoded.headers }
          payload := ByteArray.empty
          streamId? := none
    | none =>
        if frame.header.frameType == Http2.FrameType.headers then
          if Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endHeaders then
            let decoded ← expectStatusOk (Http2.Hpack.decodeHeaderBlock hpack frame.payload)
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
    if block.streamId == streamId then Metadata.get? block.headers "grpc-status" else none

def streamEnded (streamId : Nat) (frames : Array Http2.Frame) : Bool :=
  frames.any fun frame =>
    frame.header.streamId == streamId
      && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream

def responseBodyForStream (frames : Array Http2.Frame) (streamId : Nat) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun body frame =>
    if frame.header.streamId == streamId && frame.header.frameType == Http2.FrameType.data then
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
      pure { metadata := Metadata.empty, data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer (fun entry metadata => do
      if Metadata.get? metadata "authorization" == some "block" then
        authorizationBlocked.set true
        while !(← releaseAuthorization.get) do
          IO.sleep 1
      pure (.accept entry.handler))

  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let stateMutex ← Std.Mutex.new ({
    prefaceReceived := true,
    clientSettingsReceived := true,
    deadlineScheduler := some scheduler
  } : Http2.Connection.State)
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let deadlineEmitted ← IO.mkRef false
  let emit (frames : Array Http2.Frame) : IO Unit := do
    if frames.any fun frame =>
        frame.header.streamId == 1
          && frame.header.frameType == Http2.FrameType.headers
          && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream then
      deadlineEmitted.set true
    emittedRef.modify fun emitted => emitted.append frames

  let timedHeaders := requestHeaders
    |>.insert "authorization" "allow"
    |>.insert "grpc-timeout" "250m"
  let timedBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
    1 timedBlock.1
  match ← Http2.Connection.processBytesSharedWith registry stateMutex timedWire emit with
  | .error status =>
      discard <| Http2.Connection.cancelActiveShared stateMutex
      throw (IO.userError status.messageD)
  | .ok () => pure ()
  let pendingState ← stateMutex.atomically get
  expect (Http2.Connection.nextPendingDeadline? pendingState).isSome
    "timed request should be waiting for its incomplete body"
  expect (Http2.Connection.nextPendingDeadlineFallback? pendingState).isNone
    "independent scheduler should suppress the duplicate connection-loop timer"
  let compatibilityState := { pendingState with deadlineScheduler := none }
  expect (Http2.Connection.nextPendingDeadlineFallback? compatibilityState).isSome
    "state owners without an independent scheduler should retain the fallback timer"

  let blockedHeaders := requestHeaders.insert "authorization" "block"
  let blockedBlock ← expectStatusOk
    (Http2.Hpack.encodeHeaderBlock timedBlock.2 blockedHeaders)
  let blockedWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
    3 blockedBlock.1
  let processing ← IO.asTask <|
    Http2.Connection.processBytesSharedWith registry stateMutex blockedWire emit
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
    | .ok (.error status) => throw (IO.userError status.messageD)
    | .ok (.ok ()) => pure ()
  catch error =>
    releaseAuthorization.set true
    IO.cancel processing
    discard <| Http2.Connection.cancelActiveShared stateMutex
    throw error
  discard <| Http2.Connection.cancelActiveShared stateMutex

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
    pure { metadata := Metadata.empty, data := request.data, status := Status.ok }

  let server ← Grpc.Server.serve registry { address := Grpc.Server.loopback 0 }
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay

  let settings ← clientSettingsWire
  let timedHeaders := requestHeaders.insert "grpc-timeout" "250m"
  let timedBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedHeadersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
    1 timedBlock.1
  let timedDataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream
    1 (grpcMessageBytes slowPayload)
  (client.send (Http2.connectionPreface
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
      frame.header.streamId == 1 && frame.header.frameType == Http2.FrameType.data)
    "expired unary handler must not emit its late response DATA"

  let fastBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock timedBlock.2 requestHeaders)
  let fastHeadersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
    3 fastBlock.1
  let fastDataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream
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

/-- Header authorization consumes the same absolute budget as body and handler
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
      pure { metadata := Metadata.empty, data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer (fun entry metadata => do
      match Metadata.get? metadata "authorization" with
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
  let timedBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let timedHeadersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
    1 timedBlock.1
  let timedDataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream
    1 (grpcMessageBytes slowPayload)
  (client.send (Http2.connectionPreface
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
      frame.header.streamId == 1 && frame.header.frameType == Http2.FrameType.data)
    "expired custom authorizer must not emit response DATA"

  let fastHeaders := requestHeaders.insert "authorization" "allow"
  let fastBlock ← expectStatusOk (Http2.Hpack.encodeHeaderBlock timedBlock.2 fastHeaders)
  let fastHeadersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
    3 fastBlock.1
  let fastDataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream
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
  let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders 1 headerBlock
  let body := grpcMessageBytes (repeatByte 3 5)
  let dataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream 1 body
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let wire := ((← clientSettingsWire).append headersWire).append dataWire
  match ← Http2.Connection.processBytesSharedWith registry stateMutex wire emit with
  | .error status => throw (IO.userError status.messageD)
  | .ok () => pure ()
  let rstFrame ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (Http2.Frame.encode rstFrame)
  match ← Http2.Connection.processBytesSharedWith registry stateMutex rstWire emit with
  | .error status => throw (IO.userError status.messageD)
  | .ok () => pure ()
  let state ← stateMutex.atomically get
  expect state.activeDispatches.isEmpty
    "peer RST should remove the cancelled dispatch from connection state"
  let sawRst ← awaitFrame emittedRef Http2.FrameType.rstStream 200
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
  let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} timedHeaders)
  let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders 1 encodedHeaders.1
  let body := grpcMessageBytes (repeatByte 3 5)
  let dataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream 1 body
  let (stateMutex, emittedRef) ← sharedConnection
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun out => out.append frames
  let wire := ((← clientSettingsWire).append headersWire).append dataWire
  match ← Http2.Connection.processBytesSharedWith registry stateMutex wire emit with
  | .error status => throw (IO.userError status.messageD)
  | .ok () => pure ()
  let rstFrame ← expectStatusOk (Http2.RstStream.frame 1 Http2.ErrorCode.cancel)
  let rstWire ← expectStatusOk (Http2.Frame.encode rstFrame)
  let rstTask ← IO.asTask
    (Http2.Connection.processBytesSharedWith registry stateMutex rstWire emit)
  unless ← awaitTaskFinished rstTask 1000 do
    IO.cancel rstTask
    throw (IO.userError "peer RST did not promptly retire a deadline-wrapped handler")
  match ← IO.wait rstTask with
  | .error error => throw error
  | .ok (.error status) => throw (IO.userError status.messageD)
  | .ok (.ok ()) => pure ()
  expect (← sawCancellation.get)
    "deadline-wrapped handler did not observe peer cancellation"
  let state ← stateMutex.atomically get
  expect state.activeDispatches.isEmpty
    "peer RST should promptly remove the deadline-wrapped dispatch"
  let sawRst ← awaitFrame emittedRef Http2.FrameType.rstStream 200
  expect (!sawRst)
    "peer RST should not provoke a second RST_STREAM from a deadline-wrapped dispatch"

/-- A terminal response that cannot enter the bounded outbound queue closes
the stream exactly once while retaining the outer task until it has unwound. -/
def testManagedDeadlineTerminalQueueFailureOwnsOneReset : IO Unit := do
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let handlerStarted ← IO.mkRef false
  let releaseHandler ← IO.mkRef false
  let registry := Registry.empty.registerUnary echoMethod fun request => do
    handlerStarted.set true
    -- Deliberately ignore cooperative cancellation until the test releases
    -- the gate, proving the connection keeps the exact outer task discoverable.
    while !(← releaseHandler.get) do
      try IO.sleep 1 catch _ => pure ()
    pure { metadata := Metadata.empty, data := request.data, status := Status.ok }
  let saturatedPayload := repeatByte Http2.Connection.maxPendingOutboundBytes 0
  let saturatedFrame : Http2.Frame := {
    header := {
      length := saturatedPayload.size,
      frameType := Http2.FrameType.data,
      flags := 0,
      streamId := 99
    },
    payload := saturatedPayload
  }
  let stateMutex ← Std.Mutex.new ({
    prefaceReceived := true,
    clientSettingsReceived := true,
    outboundConnectionWindow := 0,
    pendingOutbound := #[saturatedFrame],
    deadlineScheduler := some scheduler
  } : Http2.Connection.State)
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun emitted => emitted.append frames
  try
    let timedHeaders := requestHeaders.insert "grpc-timeout" "1H"
    let encodedHeaders ← expectStatusOk (Http2.Hpack.encodeHeaderBlock {} timedHeaders)
    let headersWire ← frameWire Http2.FrameType.headers Http2.FrameFlag.endHeaders
      1 encodedHeaders.1
    let dataWire ← frameWire Http2.FrameType.data Http2.FrameFlag.endStream
      1 (grpcMessageBytes (repeatByte 3 7))
    match ← Http2.Connection.processBytesSharedWith registry stateMutex
        (headersWire.append dataWire) emit with
    | .error status => throw (IO.userError status.messageD)
    | .ok () => pure ()

    unless ← awaitFlag handlerStarted 1000 do
      throw (IO.userError "outbound-cap handler did not enter its retained task")
    expectEq
      (← Http2.Connection.TestSupport.deadlineSchedulerRegistrationCountForBenchmark scheduler)
      1 "outbound-cap handler did not own one deadline registration"
    Std.Async.Async.block scheduler.shutdown
    unless ← awaitFrame emittedRef Http2.FrameType.rstStream 200 do
      throw (IO.userError "outbound-cap terminal failure did not reset its stream")
    let retained ← stateMutex.atomically get
    expect (!retained.activeDispatches.isEmpty)
      "scheduler terminal failure dropped an uncooperative handler task"
    expectEq
      (← Http2.Connection.TestSupport.deadlineSchedulerRegistrationCountForBenchmark scheduler)
      0 "scheduler terminal failure retained a deadline registration"
    releaseHandler.set true
    unless ← awaitNoActiveDispatches stateMutex 1000 do
      throw (IO.userError "outbound-cap terminal failure lost its retained dispatch owner")
    let resets := (← emittedRef.get).filter fun frame =>
      frame.header.streamId == 1 && frame.header.frameType == Http2.FrameType.rstStream
    expectEq resets.size 1
      "outbound-cap terminal failure must emit exactly one RST_STREAM"
  finally
    releaseHandler.set true
    discard <| Http2.Connection.cancelActiveShared stateMutex

def main : IO Unit := do
  testPaddedDataFrame
  IO.println "padded DATA ok"
  testInvalidPadding
  IO.println "invalid padding rejected"
  testPaddedPriorityHeaders
  IO.println "padded+priority HEADERS ok"
  testContinuationSizeCap
  IO.println "continuation size cap ok"
  testKeepalivePingAck
  IO.println "keepalive PING ack ok"
  testHandlerCrashReturnsStatus
  IO.println "handler crash returns status ok"
  testPendingDispatchPublicationPreventsFalseDrain
  IO.println "pending dispatch publication blocks false graceful drain"
  testPendingBodyDeadlineIndependentOfBlockedAuthorization
  IO.println "pending-body deadline is independent of blocked cross-stream authorization"
  testPeerRstCancelsDispatchWithoutEchoReset
  IO.println "peer RST cancels dispatch without an echo reset"
  testPeerRstCancelsDeadlineHandlerWithoutEchoReset
  IO.println "peer RST cancels a deadline-wrapped handler without an echo reset"
  testManagedDeadlineTerminalQueueFailureOwnsOneReset
  IO.println "managed deadline terminal queue failure owns one reset"
  testManagedH2CDeadlineThenConnectionReuse
  IO.println "managed h2c handler deadline preserves connection reuse"
  testManagedH2CAuthorizerDeadlineThenConnectionReuse
  IO.println "managed h2c authorizer deadline preserves connection reuse"
  IO.println "all hardening assertions passed"
