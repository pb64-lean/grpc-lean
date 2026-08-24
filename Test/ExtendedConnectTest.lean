import Grpc

open Grpc
open Std.Async

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def expectEq [BEq α] (actual expected : α) (message : String) : IO Unit :=
  expect (actual == expected) message

def requireOk (result : Except Status α) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def expectError (result : Except Status α) (message : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

def expectOkEq [BEq α] (result : Except Status α) (expected : α)
    (message : String) : IO Unit :=
  match result with
  | .ok actual => expectEq actual expected message
  | .error status => throw (IO.userError s!"{message}: {status.messageD}")

def repeatByte (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

def awaitPromiseWithin (promise : IO.Promise Unit) (milliseconds : Nat) : IO Bool :=
  Async.block <| Async.race
    (do pure (← Async.ofTask promise.result?).isSome)
    (do
      Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat milliseconds)
      pure false)

def settingFrame (value : Nat) : IO Http2.Frame :=
  requireOk <| Http2.Settings.frame #[{
    id := Http2.SettingId.enableConnectProtocol,
    value := value
  }]

def testSettings : IO Unit := do
  let disabled ← requireOk <| Http2.Connection.serverSettingsFrame
  let disabledSettings ← requireOk <| Http2.Settings.decode disabled
  expect (!disabledSettings.any fun setting =>
      setting.id == Http2.SettingId.enableConnectProtocol)
    "disabled server preface must not advertise extended CONNECT"

  let enabled ← requireOk <| Http2.Connection.serverSettingsFrame
    (enableExtendedConnect := true)
  let enabledSettings ← requireOk <| Http2.Settings.decode enabled
  expect (enabledSettings.any fun setting =>
      setting.id == Http2.SettingId.enableConnectProtocol && setting.value == 1)
    "enabled server preface must advertise SETTINGS_ENABLE_CONNECT_PROTOCOL=1"

  let invalid ← settingFrame 2
  expectError (Http2.Connection.processNonHeaderFrameShared
      Registry.empty {} invalid)
    "SETTINGS_ENABLE_CONNECT_PROTOCOL=2 must be a connection error"

  let enabledByPeer ← settingFrame 1
  let state ← match Http2.Connection.processNonHeaderFrameShared
      Registry.empty {} enabledByPeer with
    | .ok (state, _) => pure state
    | .error status => throw (IO.userError status.messageD)
  expect state.peerExtendedConnectEnabled
    "peer SETTINGS_ENABLE_CONNECT_PROTOCOL=1 should be tracked"
  let retracted ← settingFrame 0
  expectError (Http2.Connection.processNonHeaderFrameShared
      Registry.empty state retracted)
    "SETTINGS_ENABLE_CONNECT_PROTOCOL must not retract 1 to 0"

def validRequest : Http2.ExtendedConnect.Request := {
  protocol := "websocket",
  scheme := "http",
  authority := "localhost",
  path := "/echo",
  headers := Metadata.singleton "origin" "https://example.test"
}

def testFields : IO Unit := do
  expect (Http2.ExtendedConnect.validProtocolToken "websocket")
    "websocket must be a valid protocol token"
  expect (!Http2.ExtendedConnect.validProtocolToken "wébsocket")
    "non-ASCII protocol tokens must be rejected"
  let encoded ← requireOk <| Http2.ExtendedConnect.encodeRequest validRequest
  let decoded ← requireOk <| Http2.ExtendedConnect.decodeRequest encoded
  expectEq decoded validRequest "extended CONNECT request must round-trip"

  let genericRequest : Http2.ExtendedConnect.Request := {
    validRequest with
    headers := #[
      { name := "x!trace", value := "left\tright" },
      { name := "x-bin", value := "literal-not-base64" },
      { name := "te", value := "trailers" }
    ]
  }
  let genericEncoded ← requireOk <| Http2.ExtendedConnect.encodeRequest genericRequest
  let genericDecoded ← requireOk <| Http2.ExtendedConnect.decodeRequest genericEncoded
  expectEq genericDecoded genericRequest
    "extended CONNECT must use generic HTTP field syntax, not gRPC metadata syntax"
  expectError (Http2.ExtendedConnect.encodeRequest {
      validRequest with headers := Metadata.singleton "te" "gzip"
    }) "HTTP/2 TE values other than trailers must be rejected"

  expectError (Http2.ExtendedConnect.decodeRequest
      (encoded.insert ":protocol" "duplicate"))
    "duplicate :protocol must be rejected"
  expectError (Http2.ExtendedConnect.decodeRequest
      (encoded.push { name := "X-Upper", value := "bad" }))
    "uppercase HTTP/2 field names must be rejected"
  expectError (Http2.ExtendedConnect.encodeResponse { status := 600 })
    "HTTP status 600 must not be encoded"
  expectError (Http2.ExtendedConnect.decodeResponse
      (Metadata.singleton ":status" "600"))
    "HTTP status 600 must not be decoded"
  expectError (Http2.ExtendedConnect.decodeResponse
      (Metadata.singleton ":status" "101"))
    "HTTP/2 status 101 must be rejected"

def requestInput (metadata : Metadata) : IO ByteArray := do
  let settings ← requireOk <| Http2.Settings.frame #[]
  let encoded ← requireOk <| Http2.Hpack.encodeHeaderBlock {} metadata
  let headers ← requireOk <| Http2.Transport.headerBlockFrames 1 encoded.1 false
  let wire ← requireOk <| Http2.Frame.encodeBatch (#[settings].append headers)
  pure (Http2.connectionPreface.append wire)

def emittedFramesFor (enabled : Bool) (metadata : Metadata)
    (handlerCalled : IO.Ref Bool) : IO (Array Http2.Frame) := do
  let stateMutex ← Std.Mutex.new <|
    Http2.Connection.initialState none none Http2.Connection.defaultStreamWindow
      (enableExtendedConnect := enabled)
  let emitted ← IO.mkRef ByteArray.empty
  let handler : Http2.ExtendedConnect.Handler := fun _ => do
    handlerCalled.set true
    pure (.reject { status := 403 })
  let result ← Async.block <| Http2.Connection.processBytesEncodedSharedWithOwned
    Registry.empty stateMutex (← requestInput metadata)
    (fun bytes => emitted.modify fun current => current.append bytes) (some handler)
  discard <| requireOk result
  let decoded ← requireOk <| Http2.Frame.decodeChunk {} (← emitted.get)
  pure decoded.frames

def hasProtocolReset (frames : Array Http2.Frame) : Bool :=
  frames.any fun frame =>
    frame.header.frameType == Http2.FrameType.rstStream &&
      (match Http2.RstStream.decode frame with
      | .ok code => code == Http2.ErrorCode.protocolError
      | .error _ => false)

def testStreamProtocolErrors : IO Unit := do
  let metadata ← requireOk <| Http2.ExtendedConnect.encodeRequest validRequest
  let called ← IO.mkRef false
  let frames ← emittedFramesFor false metadata called
  expect (hasProtocolReset frames)
    "extended CONNECT before server advertisement must get RST_STREAM(PROTOCOL_ERROR)"
  expect (!(← called.get)) "use-before-advertisement must not invoke the handler"

  let malformed := metadata.insert ":protocol" "duplicate"
  let called ← IO.mkRef false
  let frames ← emittedFramesFor true malformed called
  expect (hasProtocolReset frames)
    "malformed extended CONNECT fields must get RST_STREAM(PROTOCOL_ERROR)"
  expect (!(← called.get)) "malformed fields must not invoke the handler"

def testPendingDecisionData : IO Unit := do
  let stateMutex ← Std.Mutex.new <|
    Http2.Connection.initialState none none Http2.Connection.defaultStreamWindow
      (enableExtendedConnect := true)
  let emitted ← IO.mkRef ByteArray.empty
  let entered ← IO.Promise.new
  let release ← IO.Promise.new
  let received ← IO.Promise.new
  let secondReceiveStarted ← IO.Promise.new
  let secondReceived ← IO.Promise.new
  let observed ← IO.mkRef (none : Option ByteArray)
  let secondObserved ← IO.mkRef (none : Option ByteArray)
  let handler : Http2.ExtendedConnect.Handler := fun _ => do
    entered.resolve ()
    discard <| Async.ofTask release.result?
    pure (.accept {
      run := fun tunnel => do
        match ← tunnel.recv? with
        | .ok (some bytes) => observed.set (some bytes)
        | _ => pure ()
        received.resolve ()
        let secondReceive ← Async.toIO tunnel.recv?
        secondReceiveStarted.resolve ()
        match ← Async.ofAsyncTask secondReceive with
        | .ok (some bytes) => secondObserved.set (some bytes)
        | _ => pure ()
        secondReceived.resolve ()
        tunnel.cancel
    })
  let emit := fun bytes => emitted.modify fun current => current.append bytes
  let headers ← requireOk <| Http2.ExtendedConnect.encodeRequest validRequest
  discard <| requireOk (← Async.block <|
    Http2.Connection.processBytesEncodedSharedWithOwned Registry.empty stateMutex
      (← requestInput headers) emit (some handler))
  expect (← awaitPromiseWithin entered 2000)
    "extended CONNECT policy callback did not start"

  let earlyPayload := "arrived-before-policy".toUTF8
  let earlyFrame : Http2.Frame := {
    header := {
      length := earlyPayload.size,
      frameType := Http2.FrameType.data,
      streamId := 1
    },
    payload := earlyPayload
  }
  let earlyWire ← requireOk <| Http2.Frame.encode earlyFrame
  discard <| requireOk (← Async.block <|
    Http2.Connection.processBytesEncodedSharedWithOwned Registry.empty stateMutex
      earlyWire emit (some handler))
  release.resolve ()
  expect (← awaitPromiseWithin received 2000)
    "DATA buffered during an extended CONNECT policy decision was not delivered"
  expectEq (← observed.get) (some earlyPayload)
    "pre-decision DATA changed before tunnel delivery"
  expect (← awaitPromiseWithin secondReceiveStarted 2000)
    "starting an asynchronous tunnel receive blocked the application owner"
  let secondPayload := "arrived-after-receive-started".toUTF8
  let secondFrame : Http2.Frame := {
    header := {
      length := secondPayload.size,
      frameType := Http2.FrameType.data,
      streamId := 1
    },
    payload := secondPayload
  }
  let secondWire ← requireOk <| Http2.Frame.encode secondFrame
  discard <| requireOk (← Async.block <|
    Http2.Connection.processBytesEncodedSharedWithOwned Registry.empty stateMutex
      secondWire emit (some handler))
  expect (← awaitPromiseWithin secondReceived 2000)
    "task-backed extended CONNECT receive did not observe later DATA"
  expectEq (← secondObserved.get) (some secondPayload)
    "task-backed extended CONNECT receive changed the payload"
  discard <| Async.block (Http2.Connection.cancelActiveSharedOwned stateMutex)

partial def echoTunnel (tunnel : Http2.ExtendedConnect.Tunnel) : Async Unit := do
  match ← tunnel.recv? with
  | .error _ => pure ()
  | .ok none => discard <| tunnel.closeSend
  | .ok (some bytes) =>
      match ← tunnel.send bytes with
      | .error _ => pure ()
      | .ok () => echoTunnel tunnel

partial def receiveBytes (tunnel : Http2.ExtendedConnect.Tunnel) (size : Nat)
    (acc : ByteArray := ByteArray.empty) : Async (Except Status ByteArray) := do
  if acc.size >= size then
    pure (.ok acc)
  else
    match ← tunnel.recv? with
    | .error status => pure (.error status)
    | .ok none => pure (.error (Status.internal "tunnel ended before the expected bytes arrived"))
    | .ok (some bytes) => receiveBytes tunnel size (acc.append bytes)

def tunnelHandler : Http2.ExtendedConnect.Handler := fun request => do
  if request.path == "/reject" then
    pure (.reject {
      status := 403,
      headers := Metadata.singleton "x-rejected" "true"
    })
  else
    pure (.accept {
      headers := Metadata.singleton "x-tunnel" "ready",
      run := fun tunnel => do
        -- Immediate DATA proves the final response HEADERS are queued first.
        match ← tunnel.send "ready".toUTF8 with
        | .error _ => pure ()
        | .ok () => echoTunnel tunnel
    })

def echoMethod : MethodName := { service := "test.Echo", method := "Echo" }

def registry : Registry :=
  Registry.empty.registerUnary echoMethod fun request => do
    pure { data := request.data }

def testDisabledClientCapability : IO Unit := do
  let server ← Http2.Server.serveApplications { grpc := Registry.empty } {
    address := Http2.Server.loopback 0
  }
  let port := match server.localAddress with
    | .v4 address => address.port
    | .v6 address => address.port
  let client ← Client.connect {
    address := Http2.Server.loopback port,
    authority := "localhost"
  }
  expectOkEq (← Async.block client.peerExtendedConnectEnabled) false
    "client must distinguish a valid SETTINGS block without RFC 8441 capability"
  Async.block (Client.close client)
  Http2.Server.shutdown server
  Http2.Server.wait server (some 3000)

def openTunnel (client : Client.Connection) (path : String := "/echo") :
    IO (Http2.ExtendedConnect.Response × Http2.ExtendedConnect.Tunnel) := do
  let opened ← Async.block <| client.openExtendedConnect { validRequest with path := path }
  match opened with
  | .error status => throw (IO.userError status.messageD)
  | .ok (.rejected response) =>
      throw (IO.userError s!"tunnel unexpectedly rejected with {response.status}")
  | .ok (.accepted response tunnel) => pure (response, tunnel)

def testRuntime : IO Unit := do
  let slowEntered ← IO.Promise.new
  let slowRelease ← IO.Promise.new
  let cancelledOpenEntered ← IO.Promise.new
  let cancelledOpenRelease ← IO.Promise.new
  let cancelledOpenExited ← IO.Promise.new
  let applicationsHandler : Http2.ExtendedConnect.Handler := fun request => do
    if request.path == "/slow-policy" then
      slowEntered.resolve ()
      discard <| Async.ofTask slowRelease.result?
      tunnelHandler request
    else if request.path == "/cancel-open" then
      cancelledOpenEntered.resolve ()
      try
        discard <| Async.ofTask cancelledOpenRelease.result?
        tunnelHandler request
      finally
        cancelledOpenExited.resolve ()
    else
      tunnelHandler request
  let server ← Http2.Server.serveApplications {
    grpc := registry,
    extendedConnect := some applicationsHandler
  } {
    address := Http2.Server.loopback 0,
    maxConcurrentStreams := some 2
  }
  let port := match server.localAddress with
    | .v4 address => address.port
    | .v6 address => address.port
  let client ← Client.connect {
    address := Http2.Server.loopback port,
    authority := "localhost"
  }
  expectOkEq (← Async.block client.peerExtendedConnectEnabled) true
    "client must observe the server's RFC 8441 SETTINGS capability"

  -- A slow policy callback is connection-owned work, not work for the sole
  -- frame reader: a normal stream must continue to make progress meanwhile.
  let slowOpen ← Async.toIO <| client.openExtendedConnect
    { validRequest with path := "/slow-policy" }
  expect (← awaitPromiseWithin slowEntered 2000)
    "slow extended CONNECT policy callback did not start"
  let concurrentGrpc ← Async.block <| Async.race
    (Client.call client "/test.Echo/Echo" "while-policy-waits".toUTF8)
    (do
      Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 2000)
      pure (.error (Status.error .deadlineExceeded
        "gRPC stream stalled behind an extended CONNECT policy callback")))
  match concurrentGrpc with
  | .error status => throw (IO.userError status.messageD)
  | .ok (_, body) =>
      expectEq body "while-policy-waits".toUTF8
        "slow tunnel policy must not stall multiplexed gRPC"
  slowRelease.resolve ()
  match ← Async.block (Async.ofAsyncTask slowOpen) with
  | .error status => throw (IO.userError status.messageD)
  | .ok (.rejected response) =>
      throw (IO.userError s!"slow tunnel unexpectedly rejected with {response.status}")
  | .ok (.accepted _ slowTunnel) =>
      Async.block slowTunnel.cancel
      expectError (← Async.block slowTunnel.wait)
        "cancelled slow-policy tunnel must fail"

  -- Cancelling the cooperative opening token before a final response transfers
  -- no public handle. The operation emits RST_STREAM and lets the server retire
  -- the exact policy task instead of leaking a stream owner.
  let openingCancellation ← Std.CancellationToken.new
  let cancelledOpen ← Async.toIO <| client.openExtendedConnect
    { validRequest with path := "/cancel-open" } (some openingCancellation)
  expect (← awaitPromiseWithin cancelledOpenEntered 2000)
    "cancellable extended CONNECT policy callback did not start"
  discard <| Grpc.CancellationToken.cancel openingCancellation
  expectError (← Async.block (Async.ofAsyncTask cancelledOpen))
    "cooperatively cancelled openExtendedConnect unexpectedly succeeded"
  expectEq (← Client.TestSupport.activeTunnelCount client) 0
    "cancelling openExtendedConnect retained its untransferred stream record"
  cancelledOpenRelease.resolve ()
  expect (← awaitPromiseWithin cancelledOpenExited 2000)
    "cancelled open policy callback did not retire"

  let (response, tunnel) ← openTunnel client
  expectEq response.status 200 "accepted tunnel response status"
  expectEq (response.headers.get? "x-tunnel") (some "ready")
    "accepted tunnel response headers"
  expectOkEq (← Async.block tunnel.recv?) (some "ready".toUTF8)
    "response HEADERS must precede immediate tunnel DATA"

  -- A normal gRPC stream and an extended CONNECT stream share one connection.
  let grpcResult ← Async.block <| Client.call client "/test.Echo/Echo" "rpc".toUTF8
  match grpcResult with
  | .error status => throw (IO.userError status.messageD)
  | .ok (_, body) => expectEq body "rpc".toUTF8 "multiplexed gRPC response"

  let payload := repeatByte 70000 0x5a
  let receiveTask ← Async.toIO (receiveBytes tunnel payload.size)
  discard <| requireOk (← Async.block (tunnel.send payload))
  expectOkEq (← Async.block (Async.ofAsyncTask receiveTask)) payload
    "tunnel DATA must round-trip across multiple HTTP/2 frames and windows"
  discard <| requireOk (← Async.block tunnel.closeSend)
  expectOkEq (← Async.block tunnel.recv?) none
    "peer END_STREAM must surface as end-of-input"
  discard <| requireOk (← Async.block tunnel.wait)

  let rejected ← Async.block <| client.openExtendedConnect
    { validRequest with path := "/reject" }
  match rejected with
  | .ok (.rejected response) =>
      expectEq response.status 403 "rejection response status"
  | .ok (.accepted _ _) => throw (IO.userError "rejected path was accepted")
  | .error status => throw (IO.userError status.messageD)

  let (_, cancelled) ← openTunnel client "/cancel"
  Async.block cancelled.cancel
  expectError (← Async.block cancelled.wait)
    "locally cancelled tunnel wait must fail promptly"

  -- Fault injection verifies admission is not reported as transport success.
  expectError (← Async.block
      (Client.TestSupport.acknowledgedWriteAfterSocketShutdown client))
    "acknowledged writer failure must reach the waiting sender"
  Async.block (Client.close client)
  Http2.Server.shutdown server
  Http2.Server.wait server (some 3000)

def main : IO Unit := do
  testSettings
  testFields
  testStreamProtocolErrors
  testPendingDecisionData
  testDisabledClientCapability
  testRuntime
  IO.println "extended CONNECT assertions passed"
