import Grpc

open Grpc

namespace Test.EarlyAuthentication

def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

def fail (failure : String) : IO α :=
  throw (IO.userError failure)

def expectOk (result : Except Status α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => fail s!"{description}: {status.code}: {status.messageD}"

def method : MethodName := {
  service := "test.authentication.v1.AuthenticationService"
  method := "Check"
}

def metadata (authorization? : Option String) : Metadata :=
  let value := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  match authorization? with
  | none => value
  | some authorization => value.insert "authorization" authorization

def headersFrame (authorization? : Option String) (streamId : Nat := 1) : IO Http2.Frame := do
  let encoded ← expectOk (Http2.Hpack.encodeHeaderBlock {} (metadata authorization?))
    "encode request headers"
  pure {
    header := {
      length := encoded.1.size
      frameType := .headers
      flags := Http2.FrameFlag.endHeaders
      streamId
    }
    payload := encoded.1
  }

def dataFrame (payload : ByteArray) (streamId : Nat := 1) : Http2.Frame := {
  header := {
    length := payload.size
    frameType := .data
    flags := Http2.FrameFlag.endStream
    streamId
  }
  payload
}

def readyState : Http2.Connection.State := {
  (Http2.Connection.initialState) with
  prefaceReceived := true
  clientSettingsReceived := true
}

def rejectedStatus (frames : Array Http2.Frame) : IO Status := do
  let some frame := frames.find? fun frame =>
      frame.header.frameType == .headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
    | fail "authorization rejection did not emit trailers"
  let decoded ← expectOk (Http2.Hpack.decodeHeaderBlock {} frame.payload)
    "decode authorization rejection"
  expectOk (Headers.statusFromTrailers decoded.headers)
    "decode authorization rejection status"

def authenticatedRegistry (authorizerCalls handlerCalls : IO.Ref Nat) : Registry :=
  let registry := Registry.empty
    |>.withMaxReceiveMessageSize 1
    |>.registerUnary method (fun _ => do
      handlerCalls.modify (fun calls => calls + 1000)
      throw (Status.internal "registry fallback handler must not run"))
  registry.withRequestHeaderAuthorizer fun requested metadata => do
    authorizerCalls.modify (fun calls => calls + 1)
    if requested != method then
      throw (Status.internal "authorizer received the wrong method")
    match (metadata.getAll "authorization").back? with
    | some "TestScheme local-test-token" =>
        let resolvedSession := 23
        pure (.unary fun request => do
          handlerCalls.modify (fun calls => calls + 1)
          pure {
            data := request.data.push (UInt8.ofNat resolvedSession)
            status := Status.ok
          })
    | _ => throw (Status.error .unauthenticated "invalid local access token")

partial def waitUntil (description : String) (remaining : Nat)
    (condition : IO Bool) : IO Unit := do
  if ← condition then
    pure ()
  else if remaining == 0 then
    fail description
  else
    IO.sleep 1
    waitUntil description (remaining - 1) condition

def testMissingAndWrongRejectAtHeaders : IO Unit := do
  for presented in [none, some "TestScheme wrong"] do
    let authorizerCalls ← IO.mkRef 0
    let handlerCalls ← IO.mkRef 0
    let registry := authenticatedRegistry authorizerCalls handlerCalls
    let headers ← headersFrame presented
    let (state, emitted) ← expectOk
      (← Http2.Connection.processFrame registry readyState headers)
      "process unauthenticated headers"
    expect ((← authorizerCalls.get) == 1)
      "request-header authorizer did not run exactly once at END_HEADERS"
    expect ((← handlerCalls.get) == 0)
      "unauthenticated headers entered the RPC handler"
    expect (state.ignoredInboundStreams.contains 1)
      "unauthenticated request body was not put in drain-only state"
    let status ← rejectedStatus emitted
    expect (status.code == .unauthenticated)
      s!"wrong early authentication status: {status.code}"
    expect (status.message == some "invalid local access token")
      s!"wrong early authentication detail: {status.message}"

def testAuthorizerResourceFailureIsEarlyStatus : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let registry := Registry.empty
    |>.registerUnary method (fun request => do
      handlerCalls.modify (fun calls => calls + 1)
      pure { data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer (fun _ _ =>
      ExceptT.mk (throw (IO.userError "session manager unavailable")))
  let headers ← headersFrame (some "TestScheme local-test-token")
  let (state, emitted) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers)
    "process authorizer resource failure"
  let status ← rejectedStatus emitted
  expect (status.code == .unknown)
    s!"authorizer IO failure returned the wrong status: {status.code}"
  expect (state.ignoredInboundStreams.contains 1)
    "authorizer IO failure did not reject before request DATA"
  expect ((← handlerCalls.get) == 0)
    "authorizer IO failure entered the handler"

def testMalformedUnauthenticatedBodyCannotOverrideStatus : IO Unit := do
  let authorizerCalls ← IO.mkRef 0
  let handlerCalls ← IO.mkRef 0
  let registry := authenticatedRegistry authorizerCalls handlerCalls
  let headers ← headersFrame none
  let (state, emitted) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers)
    "process missing-auth headers"
  let originalStatus ← rejectedStatus emitted
  let malformedGrpcBody := ByteArray.mk #[0xff, 0x00, 0x01]
  let (state, bodyFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (dataFrame malformedGrpcBody))
    "drain malformed unauthenticated body"
  expect (originalStatus.code == .unauthenticated)
    "malformed body displaced the UNAUTHENTICATED response"
  expect (!state.ignoredInboundStreams.contains 1)
    "END_STREAM did not finish draining the malformed unauthenticated body"
  expect ((← authorizerCalls.get) == 1)
    "malformed body caused request reauthorization"
  expect ((← handlerCalls.get) == 0)
    "malformed unauthenticated body entered the handler"
  expect (bodyFrames.all fun frame => frame.header.frameType == .windowUpdate)
    "drained malformed body emitted a second application response"

def testOversizedUnauthenticatedBodyCannotOverrideStatus : IO Unit := do
  let authorizerCalls ← IO.mkRef 0
  let handlerCalls ← IO.mkRef 0
  let registry := authenticatedRegistry authorizerCalls handlerCalls
  let headers ← headersFrame (some "TestScheme wrong")
  let (state, emitted) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers)
    "process wrong-auth headers"
  let originalStatus ← rejectedStatus emitted
  let oversizedMessage ← expectOk
    (Message.encode { data := ByteArray.mk (Array.replicate 128 0x41) })
    "encode oversized request message"
  let (_state, bodyFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (dataFrame oversizedMessage))
    "drain oversized unauthenticated body"
  expect (originalStatus.code == .unauthenticated)
    "oversized body displaced the UNAUTHENTICATED response"
  expect ((← authorizerCalls.get) == 1)
    "oversized body caused request reauthorization"
  expect ((← handlerCalls.get) == 0)
    "oversized unauthenticated body entered the handler"
  expect (bodyFrames.all fun frame => frame.header.frameType == .windowUpdate)
    "drained oversized body emitted a second application response"

def testSharedServerPathAuthenticatesBeforeBody : IO Unit := do
  let authorizerCalls ← IO.mkRef 0
  let handlerCalls ← IO.mkRef 0
  let registry := authenticatedRegistry authorizerCalls handlerCalls
  let stateMutex ← Std.Mutex.new readyState
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun emitted => emitted.append frames
  let headers ← headersFrame none
  expectOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex headers emit) "shared server header authorization"
  let state ← stateMutex.atomically get
  expect (state.ignoredInboundStreams.contains 1)
    "shared server path did not reject the stream before DATA"
  expect ((← authorizerCalls.get) == 1)
    "shared server path did not authorize exactly once at END_HEADERS"
  let status ← rejectedStatus (← emittedRef.get)
  expect (status.code == .unauthenticated)
    "shared server path did not emit UNAUTHENTICATED before DATA"

  let malformedGrpcBody := ByteArray.mk #[0xff, 0x00, 0x01]
  expectOk (← Http2.Connection.processFrameSharedWith registry stateMutex
    (dataFrame malformedGrpcBody) emit) "shared server malformed-body drain"
  let state ← stateMutex.atomically get
  expect (!state.ignoredInboundStreams.contains 1)
    "shared server did not finish draining malformed request DATA"
  expect ((← authorizerCalls.get) == 1)
    "shared server reauthorized while draining rejected DATA"
  expect ((← handlerCalls.get) == 0)
    "shared server delivered malformed unauthenticated DATA to the handler"

def testSharedServerPathReusesAcceptedCapability : IO Unit := do
  let authorizerCalls ← IO.mkRef 0
  let handlerCalls ← IO.mkRef 0
  let registry := authenticatedRegistry authorizerCalls handlerCalls
  let stateMutex ← Std.Mutex.new readyState
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun emitted => emitted.append frames
  let headers ← headersFrame (some "TestScheme local-test-token")
  expectOk (← Http2.Connection.processFrameSharedWith
    registry stateMutex headers emit) "shared accepted header authorization"
  let requestMessage ← expectOk (Message.encode { data := ByteArray.mk #[1] })
    "encode shared authorized request"
  expectOk (← Http2.Connection.processFrameSharedWith registry stateMutex
    (dataFrame requestMessage) emit) "shared authorized dispatch"
  waitUntil "shared authorized response did not finish" 200 do
    pure <| (← emittedRef.get).any fun frame =>
      frame.header.frameType == .headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
  expect ((← authorizerCalls.get) == 1)
    "shared accepted dispatch repeated header authorization"
  expect ((← handlerCalls.get) == 1)
    "shared accepted dispatch used the fallback instead of the captured capability"
  let data := (← emittedRef.get).foldl (init := ByteArray.empty) fun body frame =>
    if frame.header.frameType == .data then body.append frame.payload else body
  let messages ← expectOk (Message.decodeAll data)
    "decode shared authorized response"
  expect (messages.size == 1 && messages[0]!.data == ByteArray.mk #[1, 23])
    "shared dispatch did not use the capability resolved at END_HEADERS"

def testAuthorizationAdvancesHpackBeforeBody : IO Unit := do
  let authorizerCalls ← IO.mkRef 0
  let handlerCalls ← IO.mkRef 0
  let registry := authenticatedRegistry authorizerCalls handlerCalls
  let requestMetadata := metadata (some "TestScheme local-test-token")
  let firstBlock ← expectOk (Http2.Hpack.encodeHeaderBlock {} requestMetadata)
    "encode first interleaved header block"
  let secondBlock ← expectOk
    (Http2.Hpack.encodeHeaderBlock firstBlock.2 requestMetadata)
    "encode dynamic-table-dependent interleaved header block"
  let frame (streamId : Nat) (payload : ByteArray) : Http2.Frame := {
    header := {
      length := payload.size
      frameType := .headers
      flags := Http2.FrameFlag.endHeaders
      streamId
    }
    payload
  }
  let (state, firstFrames) ← expectOk
    (← Http2.Connection.processFrame registry readyState (frame 1 firstBlock.1))
    "authorize first open request"
  expect firstFrames.isEmpty "first authorized open request emitted a response"
  let (state, secondFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (frame 3 secondBlock.1))
    "authorize interleaved dynamic-table-dependent request"
  expect secondFrames.isEmpty "second authorized open request emitted a response"
  expect (state.streams.size == 2)
    "interleaved authorized requests were not both retained"
  expect ((← authorizerCalls.get) == 2)
    "interleaved request headers were not each authorized exactly once"
  expect ((← handlerCalls.get) == 0)
    "open interleaved requests entered the handler before DATA"

def testAcceptedCapabilityCarriesResolvedStateOnce : IO Unit := do
  let authorizerCalls ← IO.mkRef 0
  let handlerCalls ← IO.mkRef 0
  let registry := authenticatedRegistry authorizerCalls handlerCalls
  let headers ← headersFrame (some "TestScheme local-test-token")
  let (state, headerFrames) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers)
    "process authenticated headers"
  expect headerFrames.isEmpty "authenticated headers emitted an early response"
  expect ((← authorizerCalls.get) == 1)
    "authenticated header capability was not resolved exactly once"
  let requestMessage ← expectOk (Message.encode { data := ByteArray.mk #[1] })
    "encode valid request message"
  let (_state, responseFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (dataFrame requestMessage))
    "dispatch authenticated request"
  expect ((← authorizerCalls.get) == 1)
    "dispatch repeated the live authorization lookup"
  expect ((← handlerCalls.get) == 1)
    "dispatch did not use the captured authorized handler exactly once"
  let data := responseFrames.foldl (init := ByteArray.empty) fun body frame =>
    if frame.header.frameType == .data then body.append frame.payload else body
  let messages ← expectOk (Message.decodeAll data) "decode authenticated response"
  expect (messages.size == 1) "authenticated response did not contain one message"
  expect (messages[0]!.data == ByteArray.mk #[1, 23])
    "authorized dispatch did not receive the state captured at header authorization"

end Test.EarlyAuthentication

def main : IO Unit := do
  Test.EarlyAuthentication.testMissingAndWrongRejectAtHeaders
  Test.EarlyAuthentication.testAuthorizerResourceFailureIsEarlyStatus
  Test.EarlyAuthentication.testMalformedUnauthenticatedBodyCannotOverrideStatus
  Test.EarlyAuthentication.testOversizedUnauthenticatedBodyCannotOverrideStatus
  Test.EarlyAuthentication.testSharedServerPathAuthenticatesBeforeBody
  Test.EarlyAuthentication.testSharedServerPathReusesAcceptedCapability
  Test.EarlyAuthentication.testAuthorizationAdvancesHpackBeforeBody
  Test.EarlyAuthentication.testAcceptedCapabilityCarriesResolvedStateOnce
  IO.println "gRPC early request authentication tests passed"
