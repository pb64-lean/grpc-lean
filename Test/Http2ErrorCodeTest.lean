import Std.Async.TCP

import Grpc

open Grpc

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectEq [BEq α] (actual expected : α) (message : String) : IO Unit :=
  expect (actual == expected) message

private def requireOk [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (repr error).pretty)

private partial def awaitTaskWithin (task : Task (Except IO.Error α)) (remainingMs : Nat) :
    IO (Option α) := do
  if ← IO.hasFinished task then
    match task.get with
    | .ok value => pure (some value)
    | .error error => throw error
  else if remainingMs == 0 then
    pure none
  else
    IO.sleep 1
    awaitTaskWithin task (remainingMs - 1)

private structure ReadState where
  decoder : _root_.Http2.Frame.DecodeState := {}
  frames : Array _root_.Http2.Frame := #[]

private def hasGoAway (frames : Array _root_.Http2.Frame) : Bool :=
  frames.any (·.header.frameType == _root_.Http2.FrameType.goAway)

private def goAwayCount (frames : Array _root_.Http2.Frame) : Nat :=
  frames.foldl (fun count frame =>
    if frame.header.frameType == _root_.Http2.FrameType.goAway then count + 1 else count) 0

private partial def readUntilGoAwayCount (client : Std.Async.TCP.Socket.Client)
    (wanted : Nat) (state : ReadState := {}) : IO ReadState := do
  if goAwayCount state.frames >= wanted then
    pure state
  else
    match ← (client.recv? 8192).block with
    | none => pure state
    | some chunk =>
        let decoded ← requireOk (_root_.Http2.Frame.decodeChunk state.decoder chunk)
        readUntilGoAwayCount client wanted {
          decoder := { buffered := decoded.buffered }
          frames := state.frames.append decoded.frames
        }

private partial def readUntilSettingsAck (client : Std.Async.TCP.Socket.Client)
    (state : ReadState := {}) : IO ReadState := do
  if state.frames.any fun frame =>
      frame.header.frameType == _root_.Http2.FrameType.settings &&
        _root_.Http2.Settings.isAck frame then
    pure state
  else
    match ← (client.recv? 8192).block with
    | none => pure state
    | some chunk =>
        let decoded ← requireOk (_root_.Http2.Frame.decodeChunk state.decoder chunk)
        readUntilSettingsAck client {
          decoder := { buffered := decoded.buffered }
          frames := state.frames.append decoded.frames
        }

private def readUntilGoAway (client : Std.Async.TCP.Socket.Client)
    (state : ReadState := {}) : IO ReadState :=
  readUntilGoAwayCount client 1 state

private def firstGoAway (name : String) (frames : Array _root_.Http2.Frame) :
    IO _root_.Http2.GoAway.Decoded := do
  let some frame := frames.find? (·.header.frameType == _root_.Http2.FrameType.goAway)
    | throw (IO.userError s!"{name}: server closed without GOAWAY")
  requireOk (_root_.Http2.GoAway.decode frame)

private def settingsWire (ack : Bool := false) : IO ByteArray := do
  let frame ← requireOk (_root_.Http2.Settings.frame #[] ack)
  requireOk (_root_.Http2.Frame.encode frame)

private def encodedFrame (frame : _root_.Http2.Frame) : IO ByteArray :=
  requireOk (_root_.Http2.Frame.encode frame)

private def protocolErrorWire : IO ByteArray := do
  pure (_root_.Http2.connectionPreface.append (← settingsWire true))

private def frameSizeErrorWire : IO ByteArray := do
  let oversized ← requireOk <| _root_.Http2.Frame.encodeHeader {
    length := _root_.Http2.defaultMaxFramePayloadLength + 1
    frameType := .data
    streamId := 1
  }
  pure ((_root_.Http2.connectionPreface.append (← settingsWire)).append oversized)

private def flowControlErrorWire : IO ByteArray := do
  let update ← requireOk <|
    _root_.Http2.WindowUpdate.frame 0 _root_.Http2.maxStreamId
  pure ((_root_.Http2.connectionPreface.append (← settingsWire)).append
    (← encodedFrame update))

private def compressionErrorWire : IO ByteArray := do
  let malformed : _root_.Http2.Frame := {
    header := {
      length := 1
      frameType := .headers
      flags := _root_.Http2.FrameFlag.endHeaders
      streamId := 1
    }
    payload := ByteArray.mk #[0xff]
  }
  pure ((_root_.Http2.connectionPreface.append (← settingsWire)).append
    (← encodedFrame malformed))

private def openRequestWire : IO ByteArray := do
  let headers := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/test.Service/Open"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let (block, _) ← requireOk (_root_.Http2.Hpack.encodeHeaderBlock {} headers)
  let frame : _root_.Http2.Frame := {
    header := {
      length := block.size
      frameType := .headers
      flags := _root_.Http2.FrameFlag.endHeaders
      streamId := 1
    }
    payload := block
  }
  pure (((_root_.Http2.connectionPreface.append (← settingsWire)).append
    (← encodedFrame frame)))

private def semanticFailureThenFrameSizeErrorWire : IO ByteArray := do
  let settings ← requireOk <| _root_.Http2.Settings.frame #[{
    id := .maxHeaderListSize
    value := 0
  }]
  let headers := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/missing.Service/Method"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let (block, _) ← requireOk (_root_.Http2.Hpack.encodeHeaderBlock {} headers)
  let request : _root_.Http2.Frame := {
    header := {
      length := block.size
      frameType := .headers
      flags := _root_.Http2.FrameFlag.endHeaders
      streamId := 1
    }
    payload := block
  }
  let oversized ← requireOk <| _root_.Http2.Frame.encodeHeader {
    length := _root_.Http2.defaultMaxFramePayloadLength + 1
    frameType := .data
    streamId := 1
  }
  pure (((_root_.Http2.connectionPreface.append (← encodedFrame settings)).append
    (← encodedFrame request)).append oversized)

private def checkWireErrorCode (name : String) (wire : ByteArray)
    (expected : _root_.Http2.ErrorCode) : IO Unit := do
  let server ← Grpc.Server.serve Registry.empty {
    address := Grpc.Server.loopback 0
  }
  let client ← Std.Async.TCP.Socket.Client.mk
  try
    (client.connect server.localAddress).block
    client.noDelay
    (client.send wire).block
    let task ← IO.asTask (readUntilGoAway client)
    let state ← match ← awaitTaskWithin task 5000 with
      | some state => pure state
      | none =>
          IO.cancel task
          throw (IO.userError s!"{name}: timed out waiting for GOAWAY")
    let goAway ← firstGoAway name state.frames
    expectEq goAway.errorCode expected
      s!"{name}: GOAWAY erased the HTTP/2 error code"
  finally
    try (client.shutdown).block catch _ => pure ()
    Grpc.Server.shutdown server
    Grpc.Server.wait server

private def checkFatalGoAwayAfterGraceful : IO Unit := do
  let server ← Grpc.Server.serve Registry.empty {
    address := Grpc.Server.loopback 0
  }
  let client ← Std.Async.TCP.Socket.Client.mk
  try
    (client.connect server.localAddress).block
    client.noDelay
    (client.send (← openRequestWire)).block
    let readyTask ← IO.asTask (readUntilSettingsAck client)
    let ready ← match ← awaitTaskWithin readyTask 5000 with
      | some state => pure state
      | none =>
          IO.cancel readyTask
          throw (IO.userError "graceful escalation: timed out waiting for SETTINGS ACK")
    expect (ready.frames.any fun frame =>
        frame.header.frameType == _root_.Http2.FrameType.settings &&
          _root_.Http2.Settings.isAck frame)
      "graceful escalation: server closed before processing the open request"
    Grpc.Server.shutdown server
    let firstTask ← IO.asTask (readUntilGoAwayCount client 1 ready)
    let first ← match ← awaitTaskWithin firstTask 5000 with
      | some state => pure state
      | none =>
          IO.cancel firstTask
          throw (IO.userError "graceful escalation: timed out waiting for graceful GOAWAY")
    let graceful ← firstGoAway "graceful escalation" first.frames
    expectEq graceful.errorCode .noError
      "graceful escalation: first GOAWAY was not NO_ERROR"
    let oversized ← requireOk <| _root_.Http2.Frame.encodeHeader {
      length := _root_.Http2.defaultMaxFramePayloadLength + 1
      frameType := .data
      streamId := 1
    }
    (client.send oversized).block
    let secondTask ← IO.asTask (readUntilGoAwayCount client 2 first)
    let second ← match ← awaitTaskWithin secondTask 5000 with
      | some state => pure state
      | none =>
          IO.cancel secondTask
          throw (IO.userError "graceful escalation: timed out waiting for fatal GOAWAY")
    let mut goAways : Array _root_.Http2.GoAway.Decoded := #[]
    for frame in second.frames do
      if frame.header.frameType == _root_.Http2.FrameType.goAway then
        goAways := goAways.push (← requireOk (_root_.Http2.GoAway.decode frame))
    expectEq goAways.size 2
      "graceful escalation: expected exactly two GOAWAY frames"
    expectEq goAways[1]!.errorCode .frameSizeError
      "graceful escalation: fatal GOAWAY lost the exact frame-size code"
    expect (goAways[1]!.lastStreamId <= goAways[0]!.lastStreamId)
      "graceful escalation: second GOAWAY increased last-stream-id"
  finally
    try (client.shutdown).block catch _ => pure ()
    Grpc.Server.shutdown server
    Grpc.Server.wait server

def main : IO Unit := do
  checkWireErrorCode "protocol error" (← protocolErrorWire) .protocolError
  checkWireErrorCode "frame-size error" (← frameSizeErrorWire) .frameSizeError
  checkWireErrorCode "flow-control error" (← flowControlErrorWire) .flowControlError
  checkWireErrorCode "compression error" (← compressionErrorWire) .compressionError
  checkWireErrorCode "terminal frame-size error after semantic failure"
    (← semanticFailureThenFrameSizeErrorWire) .frameSizeError
  checkFatalGoAwayAfterGraceful
