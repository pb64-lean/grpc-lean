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

def headersFrameFor (requestMetadata : Metadata) (streamId : Nat := 1) : IO Http2.Frame := do
  let encoded ← expectOk (Http2.Hpack.encodeHeaderBlock {} requestMetadata)
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

def replaceHeaderValue (source : Metadata) (name value : String) : Metadata :=
  let normalized := Header.normalizeName name
  source.map fun header =>
    if header.name == normalized then { header with value := value } else header

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

def responseHttpStatus (frames : Array Http2.Frame) : IO String := do
  let some frame := frames.find? fun frame => frame.header.frameType == .headers
    | fail "request rejection did not emit HTTP headers"
  let decoded ← expectOk (Http2.Hpack.decodeHeaderBlock {} frame.payload)
    "decode request rejection headers"
  match Metadata.get? decoded.headers ":status" with
  | some status => pure status
  | none => fail "request rejection omitted :status"

def preflightRejectionFrames (registry : Registry) (requestMetadata : Metadata) :
    IO (Array Http2.Frame) := do
  match ← expectOk
      (Http2.Transport.preflightEarlyRequest registry {} 1 requestMetadata)
      "preflight request headers" with
  | .reject frames _ => pure frames
  | .accept _ _ => fail "invalid request headers passed managed preflight"

def frameData (frames : Array Http2.Frame) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun body frame =>
    if frame.header.frameType == .data then body.append frame.payload else body

def authenticatedRegistry (authorizerCalls handlerCalls : IO.Ref Nat) : Registry :=
  let registry := Registry.empty
    |>.withMaxReceiveMessageSize 1
    |>.registerUnary method (fun _ => do
      handlerCalls.modify (fun calls => calls + 1000)
      throw (Status.internal "registry fallback handler must not run"))
  registry.withRequestHeaderAuthorizer fun entry metadata => do
    authorizerCalls.modify (fun calls => calls + 1)
    if entry.name != method then
      throw (Status.internal "authorizer received the wrong method")
    match (metadata.getAll "authorization").back? with
    | some "TestScheme local-test-token" =>
        let resolvedSession := 23
        match entry with
        | { shape := .unary, .. } =>
            pure (.accept fun request => do
              handlerCalls.modify (fun calls => calls + 1)
              pure {
                data := request.data.push (UInt8.ofNat resolvedSession)
                status := Status.ok
              })
        | _ => throw (Status.internal "authorizer expected a unary method entry")
    | _ => throw (Status.error .unauthenticated "invalid local access token")

def pureAuthenticatedRegistry (handlerCalls : IO.Ref Nat) : Registry :=
  let registry := Registry.empty
    |>.withMaxReceiveMessageSize 1
    |>.registerUnary method (fun _ => do
      handlerCalls.modify (fun calls => calls + 1000)
      throw (Status.internal "registry fallback handler must not run"))
  registry.withPureRequestHeaderAuthorizer fun entry requestMetadata =>
    if entry.name != method then
      .reject (Status.internal "pure authorizer received the wrong method")
    else
      match (requestMetadata.getAll "authorization").back? with
      | some "TestScheme local-test-token" =>
          let resolvedSession := 23
          match entry with
          | { shape := .unary, .. } =>
              .accept fun request => do
                handlerCalls.modify (fun calls => calls + 1)
                pure {
                  data := request.data.push (UInt8.ofNat resolvedSession)
                  status := Status.ok
                }
          | _ => .reject (Status.internal "pure authorizer expected a unary method entry")
      | _ => .reject (Status.error .unauthenticated "invalid local access token")

partial def waitUntil (description : String) (remaining : Nat)
    (condition : IO Bool) : IO Unit := do
  if ← condition then
    pure ()
  else if remaining == 0 then
    fail description
  else
    IO.sleep 1
    waitUntil description (remaining - 1) condition

def testPureAuthorizerDeadlineBracketsAndDefaultFastPath : IO Unit := do
  let registry := Registry.empty.registerUnary method fun request =>
    pure { data := request.data, status := Status.ok }
  let some entry := registry.findEntry? method
    | fail "registered unary entry was not found"

  let defaultClockReads ← IO.mkRef 0
  let defaultNow := do
    defaultClockReads.modify (fun reads => reads + 1)
    pure 100
  let defaultDecision ← Http2.Transport.TestSupport.authorizeRegistryEntryUntilWithClock
    defaultNow registry entry (metadata none) (some 100)
  match defaultDecision with
  | .ok (.accept _) => pure ()
  | _ => fail "registered default authorizer did not accept inline"
  expect ((← defaultClockReads.get) == 0)
    "registered default authorizer entered the pure-callback clock path"

  let pureRegistry := registry.withPureRequestHeaderAuthorizer fun _ _ =>
    .reject (Status.error .permissionDenied "bounded policy rejection")
  let untimedClockReads ← IO.mkRef 0
  let untimedNow := do
    untimedClockReads.modify (fun reads => reads + 1)
    pure 100
  let untimedDecision ← Http2.Transport.TestSupport.authorizeRegistryEntryUntilWithClock
    untimedNow pureRegistry entry (metadata none) none
  match untimedDecision with
  | .ok (.reject status) =>
      expect (status.code == .permissionDenied)
        "untimed pure authorizer changed its policy decision"
  | _ => fail "untimed pure authorizer returned the wrong result"
  expect ((← untimedClockReads.get) == 0)
    "untimed pure authorizer read a deadline clock"

  let expiredBeforeReads ← IO.mkRef 0
  let expiredBeforeNow := do
    expiredBeforeReads.modify (fun reads => reads + 1)
    pure 100
  let expiredBefore ← Http2.Transport.TestSupport.authorizeRegistryEntryUntilWithClock
    expiredBeforeNow pureRegistry entry (metadata none) (some 100)
  match expiredBefore with
  | .error status =>
      expect (status.code == .deadlineExceeded)
        "pre-authorization deadline check returned the wrong status"
  | .ok _ => fail "expired request entered the pure authorizer"
  expect ((← expiredBeforeReads.get) == 1)
    "expired request did not stop after the pre-authorization clock check"

  let bracketReads ← IO.mkRef 0
  let bracketNow := do
    let read ← bracketReads.modifyGet fun reads => (reads, reads + 1)
    pure (if read == 0 then 99 else 100)
  let expiredAfter ← Http2.Transport.TestSupport.authorizeRegistryEntryUntilWithClock
    bracketNow pureRegistry entry (metadata none) (some 100)
  match expiredAfter with
  | .error status =>
      expect (status.code == .deadlineExceeded)
        "post-authorization deadline check did not override the policy result"
  | .ok _ => fail "deadline reached during pure authorization was ignored"
  expect ((← bracketReads.get) == 2)
    "pure authorization was not bracketed by exactly two clock checks"

def testAuthorizerInstallersAreLastWins : IO Unit := do
  let base := Registry.empty.registerUnary method fun request =>
    pure { data := request.data, status := Status.ok }
  let some entry := base.findEntry? method
    | fail "registered unary entry was not found"
  let effectful : RequestHeaderAuthorizer := fun _ _ =>
    pure (.reject (Status.error .unauthenticated "effectful"))
  let bounded : PureRequestHeaderAuthorizer := fun _ _ =>
    .reject (Status.error .permissionDenied "pure")

  let pureLast := (base.withRequestHeaderAuthorizer effectful)
    |>.withPureRequestHeaderAuthorizer bounded
  let pureDecision ← expectOk
    (← pureLast.authorizeRequestHeaders entry (metadata none) |>.run)
    "run last-installed pure authorizer"
  match pureDecision with
  | .reject status =>
      expect (status.code == .permissionDenied)
        "effectful authorizer remained active after pure installation"
  | .accept _ => fail "last-installed pure rejection was ignored"

  let effectfulLast := (base.withPureRequestHeaderAuthorizer bounded)
    |>.withRequestHeaderAuthorizer effectful
  let effectfulDecision ← expectOk
    (← effectfulLast.authorizeRequestHeaders entry (metadata none) |>.run)
    "run last-installed effectful authorizer"
  match effectfulDecision with
  | .reject status =>
      expect (status.code == .unauthenticated)
        "pure authorizer remained active after effectful installation"
  | .accept _ => fail "last-installed effectful rejection was ignored"

def testPureAuthorizerRejectsBeforeBody : IO Unit := do
  for presented in [none, some "TestScheme wrong"] do
    let handlerCalls ← IO.mkRef 0
    let registry := pureAuthenticatedRegistry handlerCalls
    let headers ← headersFrame presented
    let (state, emitted) ← expectOk
      (← Http2.Connection.processFrame registry readyState headers)
      "process pure-authorizer rejection"
    expect (state.ignoredInboundStreams.contains 1)
      "pure-authorizer rejection did not enter drain-only state at END_HEADERS"
    expect ((← handlerCalls.get) == 0)
      "pure-authorizer rejection entered the RPC handler"
    let status ← rejectedStatus emitted
    expect (status.code == .unauthenticated)
      "pure-authorizer rejection returned the wrong status"

def testPureAuthorizerRunsInlineAndCarriesCapability : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let registry := pureAuthenticatedRegistry handlerCalls
  let scheduler ← Http2.Connection.DeadlineScheduler.new
  let stateMutex ← Std.Mutex.new {
    readyState with deadlineScheduler := some scheduler
  }
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let emit (frames : Array Http2.Frame) : IO Unit :=
    emittedRef.modify fun emitted => emitted.append frames
  try
    let requestMetadata := metadata (some "TestScheme local-test-token")
      |>.insert "grpc-timeout" "1H"
    let headers ← headersFrameFor requestMetadata
    let anchor ← IO.monoNanosNow
    discard <| expectOk (← Std.Async.Async.block <|
      Http2.Connection.processFrameSharedWithOwned registry stateMutex headers emit
        (some anchor)) "process bounded pure authorization"
    let state ← stateMutex.atomically get
    expect state.activeAuthorizations.isEmpty
      "bounded pure authorization entered the effectful authorization lifecycle"
    let some stream := state.streams.find? (fun stream => stream.streamId == 1)
      | fail "pure-authorized open request was not retained"
    expect stream.authorizedEntry?.isSome
      "pure-authorized handler capability was not cached at END_HEADERS"

    let requestMessage ← expectOk (Message.encode { data := ByteArray.mk #[1] })
      "encode pure-authorized request"
    expectOk (← Http2.Connection.processFrameSharedWith registry stateMutex
      (dataFrame requestMessage) emit) "dispatch pure-authorized request"
    waitUntil "pure-authorized response did not finish" 200 do
      pure <| (← emittedRef.get).any fun frame =>
        frame.header.frameType == .headers
          && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
    expect ((← handlerCalls.get) == 1)
      "dispatch did not use the handler capability selected by pure authorization"
    let messages ← expectOk (Message.decodeAll (frameData (← emittedRef.get)))
      "decode pure-authorized response"
    expect (messages.size == 1 && messages[0]!.data == ByteArray.mk #[1, 23])
      "pure-authorized capability did not carry resolved state into dispatch"
  finally
    discard <| Std.Async.Async.block <|
      Http2.Connection.cancelActiveSharedOwned stateMutex

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

def testRejectResultIsEarlyStatus : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let registry := Registry.empty
    |>.registerUnary method (fun request => do
      handlerCalls.modify (fun calls => calls + 1)
      pure { data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer (fun _ _ =>
      pure (.reject (Status.error .permissionDenied "token lacks scope")))
  let headers ← headersFrame (some "TestScheme local-test-token")
  let (state, emitted) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers)
    "process authorizer reject result"
  let status ← rejectedStatus emitted
  expect (status.code == .permissionDenied)
    s!"reject result returned the wrong status: {status.code}"
  expect (status.message == some "token lacks scope")
    s!"reject result returned the wrong detail: {status.message}"
  expect (state.ignoredInboundStreams.contains 1)
    "reject result did not put the request body in drain-only state"
  expect ((← handlerCalls.get) == 0)
    "reject result entered the handler"

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

def testManagedPreflightRejectionPrecedence : IO Unit := do
  let registry := Registry.empty

  let invalidMetadata :=
    replaceHeaderValue
      (replaceHeaderValue (metadata none) ":method" "GET")
      "content-type" "application/json"
    |>.push { name := "bad header", value := "x" }
  let invalidMetadataFrames ← preflightRejectionFrames registry invalidMetadata
  let invalidMetadataStatus ← rejectedStatus invalidMetadataFrames
  expect (invalidMetadataStatus.code == .invalidArgument)
    "metadata validation did not win managed preflight precedence"
  expect (invalidMetadataStatus.message == some "invalid gRPC metadata name bad header")
    s!"wrong metadata-precedence detail: {invalidMetadataStatus.message}"

  let unsupportedContentType :=
    replaceHeaderValue
      (replaceHeaderValue (metadata none) ":method" "GET")
      "content-type" "application/json"
  let unsupportedFrames ← preflightRejectionFrames registry unsupportedContentType
  expect ((← responseHttpStatus unsupportedFrames) == "415")
    "unsupported content-type did not win over full method validation"

  let invalidMethod :=
    replaceHeaderValue (metadata none) ":method" "GET"
    |>.insert "grpc-timeout" "not-a-timeout"
  let invalidMethodFrames ← preflightRejectionFrames registry invalidMethod
  let invalidMethodStatus ← rejectedStatus invalidMethodFrames
  expect (invalidMethodStatus.code == .invalidArgument)
    "invalid method did not produce INVALID_ARGUMENT"
  expect (invalidMethodStatus.message == some "gRPC requests must use POST")
    "grpc-timeout validation displaced the earlier method error"

  let duplicateContentType :=
    metadata none |>.insert "content-type" "application/json"
  let duplicateFrames ← preflightRejectionFrames registry duplicateContentType
  let duplicateStatus ← rejectedStatus duplicateFrames
  expect (duplicateStatus.code == .invalidArgument)
    "duplicate content-type did not produce INVALID_ARGUMENT"
  expect (duplicateStatus.message == some "duplicate content-type header")
    "a later unsupported content-type displaced the duplicate-header error"

def testPreflightPreservesMetadataAndEndHeadersDeadline : IO Unit := do
  let capturedMetadata ← IO.mkRef (none : Option Metadata)
  let registry :=
    (Registry.empty.registerUnary method fun request =>
      pure { data := request.data, status := Status.ok })
    |>.withRequestHeaderAuthorizer fun entry requestMetadata => do
      capturedMetadata.set (some requestMetadata)
      pure (AuthorizationResult.acceptRegistered entry)
  let requestMetadata := metadata none
    |>.insert "grpc-timeout" "1H"
    |>.insert "x-order" "first"
    |>.insert "x-order" "second"
  let headers ← headersFrameFor requestMetadata
  let stateMutex ← Std.Mutex.new readyState
  let anchor ← IO.monoNanosNow
  let result ← Std.Async.Async.block <|
    Http2.Connection.processFrameSharedWithOwned registry stateMutex headers
      (fun _ => pure ()) (some anchor)
  discard <| expectOk result "process anchored request headers"
  expect ((← capturedMetadata.get) == some requestMetadata)
    "request-header authorization did not receive the original metadata unchanged"
  let state ← stateMutex.atomically get
  let some stream := state.streams.find? (fun stream => stream.streamId == 1)
    | fail "accepted open request was not retained"
  expect (stream.requestMetadata == some requestMetadata)
    "stream state did not retain the original metadata"
  let expectedPreflight ← expectOk
    (Headers.validateUnaryRequestPreflight requestMetadata) "validate expected preflight"
  expect (stream.requestPreflight == some expectedPreflight)
    "stream state did not retain the parsed request preflight"
  expect (stream.endHeadersReceivedAt == some anchor)
    "stream state lost the END_HEADERS receive time"
  expect (stream.deadline == some (anchor + 3600000000000))
    "managed deadline was not anchored exactly once at END_HEADERS"

def testManagedDispatchUsesCachedCompressionFacts : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let requestPayload := ByteArray.mk (Array.replicate 4096 0x61)
  let responsePayload := ByteArray.mk (Array.replicate 4096 0x62)
  let registry := Registry.empty.registerUnary method fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    if request.data != requestPayload then
      throw (Status.internal "cached gzip request was not decompressed")
    pure { data := responsePayload, status := Status.ok }
  let some entry := registry.findEntry? method
    | fail "registered unary entry was not found"
  let requestBody ← expectOk (Message.encode (Message.gzipped requestPayload))
    "encode cached gzip request"
  let contradictoryMetadata := metadata none
    |>.insert "content-length" "not-a-number"
    |>.insert "grpc-encoding" "deflate"
    |>.insert "grpc-accept-encoding" "identity"
  let preflight : Headers.RequestPreflight := {
    method := method
    timeout := none
    contentLength := none
    requestUsesGzip := true
    clientAcceptsGzip := true
  }
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let dispatchResult ← Http2.Transport.dispatchDecodedUnaryFramesWith registry {} {
    streamId := 1
    metadata := contradictoryMetadata
    body := requestBody
    hpack := {}
    authorizedEntry? := some entry
    preflight? := some preflight
  } (fun frames => emittedRef.modify fun emitted => emitted.append frames)
  discard <| expectOk dispatchResult "dispatch cached gzip request"
  expect ((← handlerCalls.get) == 1)
    "cached gzip request did not invoke its authorized handler exactly once"
  let emitted ← emittedRef.get
  let some initialHeaders := emitted.find? fun frame =>
      frame.header.frameType == .headers
        && !Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
    | fail "cached gzip response omitted initial headers"
  let decodedHeaders ← expectOk (Http2.Hpack.decodeHeaderBlock {} initialHeaders.payload)
    "decode cached gzip response headers"
  expect (Metadata.get? decodedHeaders.headers "grpc-encoding" == some "gzip")
    "cached client gzip acceptance did not select gzip response encoding"
  let messages ← expectOk (Message.decodeAll (frameData emitted))
    "decode cached gzip response body"
  expect (messages.size == 1 && messages[0]!.compressed == .compressed)
    "cached client gzip acceptance did not compress the response message"
  let restored ← expectOk
    (Message.decompress true (responsePayload.size + 16) messages[0]!)
    "decompress cached gzip response"
  expect (restored.data == responsePayload)
    "cached gzip response did not preserve the handler payload"

def testManagedDispatchUsesCachedContentLength : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let registry := Registry.empty.registerUnary method fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    pure { data := request.data, status := Status.ok }
  let some entry := registry.findEntry? method
    | fail "registered unary entry was not found"
  let requestBody ← expectOk (Message.encode { data := ByteArray.mk #[1, 2, 3] })
    "encode cached-length request"
  let requestMetadata := metadata none |>.insert "content-length" "not-a-number"
  let preflight : Headers.RequestPreflight := {
    method := method
    timeout := none
    contentLength := some requestBody.size
    requestUsesGzip := false
    clientAcceptsGzip := false
  }
  let emittedRef ← IO.mkRef (#[] : Array Http2.Frame)
  let dispatchResult ← Http2.Transport.dispatchDecodedUnaryFramesWith registry {} {
    streamId := 1
    metadata := requestMetadata
    body := requestBody
    hpack := {}
    authorizedEntry? := some entry
    preflight? := some preflight
  } (fun frames => emittedRef.modify fun emitted => emitted.append frames)
  discard <| expectOk dispatchResult "dispatch cached-length request"
  expect ((← handlerCalls.get) == 1)
    "managed dispatch reparsed invalid content-length metadata"

  let mismatchedPreflight := {
    preflight with contentLength := some (requestBody.size + 1)
  }
  let mismatchFrames ← IO.mkRef (#[] : Array Http2.Frame)
  let mismatchResult ← Http2.Transport.dispatchDecodedUnaryFramesWith registry {} {
    streamId := 3
    metadata := requestMetadata
    body := requestBody
    hpack := {}
    authorizedEntry? := some entry
    preflight? := some mismatchedPreflight
  } (fun frames => mismatchFrames.modify fun emitted => emitted.append frames)
  discard <| expectOk mismatchResult "dispatch cached content-length mismatch"
  expect ((← handlerCalls.get) == 1)
    "cached content-length mismatch entered the handler"
  let mismatchStatus ← rejectedStatus (← mismatchFrames.get)
  expect (mismatchStatus.code == .invalidArgument)
    "cached content-length mismatch did not produce INVALID_ARGUMENT"
  expect (mismatchStatus.message == some
      s!"content-length {requestBody.size + 1} does not match request body size {requestBody.size}")
    "cached content-length mismatch changed its rejection detail"

def testStandaloneDispatchStillValidatesAndDerivesDeadline : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let seenDeadline ← IO.mkRef (none : Option (Option Nat))
  let registry := Registry.empty.registerUnary method fun request => do
    handlerCalls.modify (fun calls => calls + 1)
    seenDeadline.set (some request.deadline)
    pure { data := request.data, status := Status.ok }
  let some entry := registry.findEntry? method
    | fail "registered unary entry was not found"
  let requestBody ← expectOk (Message.encode { data := ByteArray.mk #[4, 5, 6] })
    "encode standalone request"

  let invalidFrames ← IO.mkRef (#[] : Array Http2.Frame)
  let invalidResult ← Http2.Transport.dispatchDecodedUnaryFramesWith registry {} {
    streamId := 1
    metadata := metadata none |>.insert "content-length" "not-a-number"
    body := requestBody
    hpack := {}
    authorizedEntry? := some entry
    preflight? := none
  } (fun frames => invalidFrames.modify fun emitted => emitted.append frames)
  discard <| expectOk invalidResult "dispatch preflight-absent invalid request"
  let invalidStatus ← rejectedStatus (← invalidFrames.get)
  expect (invalidStatus.code == .invalidArgument)
    "preflight-absent request bypassed ordinary validation"
  expect (invalidStatus.message == some "invalid content-length header not-a-number")
    "preflight-absent request changed ordinary validation detail"
  expect ((← handlerCalls.get) == 0)
    "preflight-absent invalid request entered the retained handler"

  let before ← IO.monoNanosNow
  let liveFrames ← IO.mkRef (#[] : Array Http2.Frame)
  let liveResult ← Http2.Transport.dispatchDecodedUnaryFramesWith registry {} {
    streamId := 3
    metadata := metadata none |>.insert "grpc-timeout" "1H"
    body := requestBody
    hpack := {}
  } (fun frames => liveFrames.modify fun emitted => emitted.append frames)
  discard <| expectOk liveResult "dispatch ordinary timed request"
  let after ← IO.monoNanosNow
  expect ((← handlerCalls.get) == 1)
    "ordinary timed request did not invoke its handler"
  match ← seenDeadline.get with
  | some (some deadline) =>
      expect (before + 3600000000000 <= deadline
          && deadline <= after + 3600000000000)
        "standalone dispatch did not derive grpc-timeout at dispatch time"
  | _ => fail "standalone timed request handler did not receive a deadline"

end Test.EarlyAuthentication

def main : IO Unit := do
  Test.EarlyAuthentication.testPureAuthorizerDeadlineBracketsAndDefaultFastPath
  Test.EarlyAuthentication.testAuthorizerInstallersAreLastWins
  Test.EarlyAuthentication.testPureAuthorizerRejectsBeforeBody
  Test.EarlyAuthentication.testPureAuthorizerRunsInlineAndCarriesCapability
  Test.EarlyAuthentication.testMissingAndWrongRejectAtHeaders
  Test.EarlyAuthentication.testRejectResultIsEarlyStatus
  Test.EarlyAuthentication.testAuthorizerResourceFailureIsEarlyStatus
  Test.EarlyAuthentication.testMalformedUnauthenticatedBodyCannotOverrideStatus
  Test.EarlyAuthentication.testOversizedUnauthenticatedBodyCannotOverrideStatus
  Test.EarlyAuthentication.testSharedServerPathAuthenticatesBeforeBody
  Test.EarlyAuthentication.testSharedServerPathReusesAcceptedCapability
  Test.EarlyAuthentication.testAuthorizationAdvancesHpackBeforeBody
  Test.EarlyAuthentication.testAcceptedCapabilityCarriesResolvedStateOnce
  Test.EarlyAuthentication.testManagedPreflightRejectionPrecedence
  Test.EarlyAuthentication.testPreflightPreservesMetadataAndEndHeadersDeadline
  Test.EarlyAuthentication.testManagedDispatchUsesCachedCompressionFacts
  Test.EarlyAuthentication.testManagedDispatchUsesCachedContentLength
  Test.EarlyAuthentication.testStandaloneDispatchStillValidatesAndDerivesDeadline
  IO.println "gRPC early request authentication tests passed"
