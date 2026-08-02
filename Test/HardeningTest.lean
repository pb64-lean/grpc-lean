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

/-- Cancelling a dispatch mid-handler (client RST) resets connection stream state and
sends RST_STREAM rather than leaving the stream in limbo. -/
def testRstStreamOnCancelledDispatch : IO Unit := do
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
  let sawRst ← awaitFrame emittedRef Http2.FrameType.rstStream 200
  expect sawRst "cancelled dispatch should emit RST_STREAM for its stream"

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
  testRstStreamOnCancelledDispatch
  IO.println "RST_STREAM on cancelled dispatch ok"
  IO.println "all hardening assertions passed"
