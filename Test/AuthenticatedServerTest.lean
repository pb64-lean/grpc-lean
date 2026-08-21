import Grpc

open Grpc

namespace Test.AuthenticatedServer

def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

def fail (failure : String) : IO α :=
  throw (IO.userError failure)

def expectOk (result : Except Status α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => fail s!"{description}: {status.code}: {status.messageD}"

def protectedMethod : MethodName := {
  service := "test.authenticated.v1.Service"
  method := "Protected"
}

def publicMethod : MethodName := {
  service := "test.authenticated.v1.Service"
  method := "Public"
}

def identityDecode (data : ByteArray) : Except String ByteArray := .ok data
def identityEncode (data : ByteArray) : Except String ByteArray := .ok data

def tokenMetadata (token : String) : Metadata :=
  Metadata.empty.insert "authorization" token

def requestMetadata (method : MethodName) (token? : Option String := none) : Metadata :=
  let metadata := Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  match token? with
  | none => metadata
  | some token => metadata.insert "authorization" token

def headersFrame (state : Http2.Hpack.State) (method : MethodName)
    (token? : Option String := none) (streamId : Nat := 1) :
    IO (Http2.Frame × Http2.Hpack.State) := do
  let encoded ← expectOk (Http2.Hpack.encodeHeaderBlock state (requestMetadata method token?))
    "encode authenticated request headers"
  pure ({
    header := {
      length := encoded.1.size
      frameType := .headers
      flags := Http2.FrameFlag.endHeaders
      streamId
    }
    payload := encoded.1
  }, encoded.2)

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
  Http2.Connection.initialState with
  prefaceReceived := true
  clientSettingsReceived := true
}

def rejectedStatus (frames : Array Http2.Frame) : IO Status := do
  let some frame := frames.find? fun frame =>
      frame.header.frameType == .headers
        && Http2.FrameFlag.has frame.header.flags Http2.FrameFlag.endStream
    | fail "authentication rejection did not emit trailers"
  let decoded ← expectOk (Http2.Hpack.decodeHeaderBlock {} frame.payload)
    "decode authentication rejection"
  expectOk (Headers.statusFromTrailers decoded.headers)
    "decode authentication rejection status"

def frameData (frames : Array Http2.Frame) : ByteArray :=
  frames.foldl (init := ByteArray.empty) fun data frame =>
    if frame.header.frameType == .data then data.append frame.payload else data

def pureAuthenticator : RequestAuthenticator Nat := .pure fun metadata =>
  match metadata.getLast? "authorization" with
  | some "Bearer good" => .ok 23
  | _ => .error (Status.error .unauthenticated "invalid bearer token")

def pureRegistry (interceptorCalls : IO.Ref Nat) : Registry :=
  let registry := Registry.empty
    |>.registerAuthenticatedUnaryCodec protectedMethod pureAuthenticator
      identityDecode identityEncode (fun principal input =>
        pure (input.push (UInt8.ofNat principal.value)))
    |>.registerUnary publicMethod (fun request =>
      pure { data := request.data, status := Status.ok })
    |>.withPureRequestHeaderAuthorizer (fun entry metadata =>
      if metadata.getLast? "x-global-deny" == some "true" then
        .reject (Status.error .permissionDenied "global policy rejected request")
      else
        AuthorizationResult.acceptRegistered entry)
  registry.withHandlerInterceptor fun entry handler =>
    match entry with
    | { shape := .unary, .. } => fun request => do
        interceptorCalls.modify (fun calls => calls + 1)
        let response ← handler request
        pure { response with data := response.data.push 99 }
    | _ => handler

private def methodEntryNameViaLegacyCases (entry : MethodEntry) : MethodName := by
  cases entry with
  | mk name _ _ => exact name

def testMethodEntryConstructionCompatibility : IO Unit := do
  let handler : UnaryHandler := fun request =>
    pure { data := request.data, status := Status.ok }
  let constructed : MethodEntry := MethodEntry.mk publicMethod .unary handler
  expect (methodEntryNameViaLegacyCases constructed == publicMethod)
    "three-argument MethodEntry.mk or legacy cases construction changed"
  match constructed.requestHeaderHandlerResolver with
  | .registered => pure ()
  | _ => fail "three-argument MethodEntry.mk did not install the default resolver"

  let recorded : MethodEntry := {
    name := publicMethod
    shape := .unary
    handler := handler
  }
  let updated : MethodEntry := { recorded with name := protectedMethod }
  expect (updated.name == protectedMethod)
    "MethodEntry record omission or update changed"

  let explicit : MethodEntry := {
    name := protectedMethod
    shape := .unary
    handler := handler
    requestHeaderHandlerResolver := .pure fun _ => .ok handler
  }
  match explicit.requestHeaderHandlerResolver with
  | .pure resolve =>
      match resolve Metadata.empty with
      | .ok _ => pure ()
      | .error status => fail s!"explicit method resolver failed: {status.messageD}"
  | _ => fail "explicit MethodEntry resolver initialization changed"

def expectUnaryHandler (entry : MethodEntry) (decision : AuthorizationResult entry)
    (description : String) : IO UnaryHandler := do
  match decision with
  | .reject status => fail s!"{description}: {status.code}: {status.messageD}"
  | .accept handler =>
      let resolved := { entry with handler := handler }
      match resolved.handlerFor? .unary with
      | some unary => pure unary
      | none => fail s!"{description}: resolved entry was not unary"

def testPureAuthenticationAndComposition : IO Unit := do
  let interceptorCalls ← IO.mkRef 0
  let registry := pureRegistry interceptorCalls
  let some entry := registry.findEntry? protectedMethod
    | fail "protected entry was not registered"
  expect (!registry.usesEffectfulRequestHeaderResolution entry)
    "pure method authentication was classified as effectful"

  let some resolve := registry.pureRequestHeaderAuthorizerFor? entry
    | fail "pure authenticated entry did not expose an inline resolver"
  let handler ← expectUnaryHandler entry (resolve (tokenMetadata "Bearer good"))
    "resolve valid pure authentication"
  let response ← expectOk (← handler {
      method := protectedMethod
      metadata := tokenMetadata "Bearer good"
      data := ByteArray.mk #[1, 2]
    } |>.run) "run resolved authenticated handler"
  expect (response.data == ByteArray.mk #[1, 2, 23, 99])
    "local authentication, global authorization, or interception ran out of order"
  expect ((← interceptorCalls.get) == 1)
    "effective-handler interceptor did not wrap the resolved handler"

  match resolve (tokenMetadata "Bearer bad") with
  | .reject status =>
      expect (status.code == .unauthenticated)
        "pure authentication failure returned the wrong status"
  | .accept _ => fail "invalid token resolved an authenticated handler"

  match resolve (tokenMetadata "Bearer good" |>.insert "x-global-deny" "true") with
  | .reject status =>
      expect (status.code == .permissionDenied)
        "global authorizer did not compose after local authentication"
  | .accept _ => fail "global policy rejection was bypassed"

  let some fallback := entry.handlerFor? .unary
    | fail "protected fallback entry was not unary"
  let fallbackResult ← fallback {
    method := protectedMethod
    metadata := tokenMetadata "Bearer good"
    data := ByteArray.mk #[7]
  } |>.run
  match fallbackResult with
  | .error status =>
      expect (status.code == .unauthenticated)
        "authenticated entry fallback did not fail closed"
  | .ok _ => fail "authenticated entry fallback was callable without authentication"

def testMethodLocalIsolation : IO Unit := do
  let interceptorCalls ← IO.mkRef 0
  let registry := pureRegistry interceptorCalls
  let some publicEntry := registry.findEntry? publicMethod
    | fail "public entry was not registered"
  expect (!registry.usesEffectfulRequestHeaderResolution publicEntry)
    "public entry inherited unrelated authentication scheduling"
  let some resolve := registry.pureRequestHeaderAuthorizerFor? publicEntry
    | fail "public entry lost the registered-handler fast path"
  let handler ← expectUnaryHandler publicEntry (resolve Metadata.empty)
    "resolve public entry"
  let response ← expectOk (← handler {
      method := publicMethod
      metadata := Metadata.empty
      data := ByteArray.mk #[4]
    } |>.run) "run public handler"
  expect (response.data == ByteArray.mk #[4, 99])
    "public handler did not retain effective-handler interception"

def testEffectfulAuthenticationAndDeadline : IO Unit := do
  let calls ← IO.mkRef 0
  let authenticator : RequestAuthenticator Nat := .effectful fun _ => do
    calls.modify (fun count => count + 1)
    pure 31
  let registry := Registry.empty.registerAuthenticatedUnaryCodec protectedMethod authenticator
    identityDecode identityEncode (fun principal input =>
      pure (input.push (UInt8.ofNat principal.value)))
  let some entry := registry.findEntry? protectedMethod
    | fail "effectful protected entry was not registered"
  expect (registry.usesEffectfulRequestHeaderResolution entry)
    "effectful method authentication was not classified per entry"
  expect (registry.pureRequestHeaderAuthorizerFor? entry).isNone
    "effectful method exposed a pure header resolver"

  let decision ← expectOk
    (← registry.authorizeRequestHeaders entry Metadata.empty |>.run)
    "run effectful method authentication"
  let handler ← expectUnaryHandler entry decision "resolve effectful authentication"
  let response ← expectOk (← handler {
      method := protectedMethod
      metadata := Metadata.empty
      data := ByteArray.mk #[5]
    } |>.run) "run effectfully authenticated handler"
  expect (response.data == ByteArray.mk #[5, 31])
    "effectfully authenticated principal was not delivered"
  expect ((← calls.get) == 1)
    "effectful authenticator did not run exactly once"

  let expired ← Http2.Transport.TestSupport.authorizeRegistryEntryUntilWithClock
    (pure 0) registry entry Metadata.empty (some 0)
  match expired with
  | .error status =>
      expect (status.code == .deadlineExceeded)
        "expired effectful authentication returned the wrong status"
  | .ok _ => fail "expired effectful authentication was allowed"

def testCheckedRegistrationRejectsShadowing : IO Unit := do
  let base := Registry.empty.registerUnary protectedMethod fun request =>
    pure { data := request.data.push 88, status := Status.ok }
  let checked := base.registerAuthenticatedUnaryCodecChecked protectedMethod pureAuthenticator
    identityDecode identityEncode (fun principal input =>
      pure (input.push (UInt8.ofNat principal.value)))
  match checked with
  | .error duplicate =>
      expect (duplicate.name == protectedMethod)
        "checked authenticated registration reported the wrong collision"
  | .ok _ => fail "checked authenticated registration appended a shadowed method"
  expect (base.entries.size == 1)
    "failed checked registration changed the source registry"
  let some original := base.findUnary? protectedMethod
    | fail "original handler disappeared after duplicate rejection"
  let response ← expectOk (← original {
      method := protectedMethod
      metadata := Metadata.empty
      data := ByteArray.mk #[1]
    } |>.run) "run original handler after duplicate rejection"
  expect (response.data == ByteArray.mk #[1, 88])
    "duplicate authenticated registration shadowed the original handler"

  match base.ensureMethodsAvailable #[publicMethod, protectedMethod] with
  | .error duplicate =>
      expect (duplicate.name == protectedMethod)
        "batch preflight reported the wrong existing collision"
  | .ok _ => fail "batch preflight accepted an existing method collision"
  match Registry.empty.ensureMethodsAvailable
      #[protectedMethod, publicMethod, protectedMethod] with
  | .error duplicate =>
      expect (duplicate.name == protectedMethod)
        "batch preflight reported the wrong within-batch duplicate"
  | .ok _ => fail "batch preflight accepted an internal duplicate"
  let preflighted ← match Registry.empty.ensureMethodsAvailable
      #[protectedMethod, publicMethod] with
    | .ok registry => pure registry
    | .error _ => fail "batch preflight rejected distinct available methods"
  expect (preflighted.entries.isEmpty)
    "successful registration preflight mutated the registry"

def testPureFrameRejectionBeforeData : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let registry := Registry.empty.registerAuthenticatedUnaryCodec protectedMethod pureAuthenticator
    identityDecode identityEncode (fun _ input => do
      handlerCalls.modify (fun calls => calls + 1)
      pure input)
  let headers ← headersFrame {} protectedMethod none
  let (state, emitted) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers.1)
    "process method-local pure authentication rejection"
  expect (state.ignoredInboundStreams.contains 1)
    "method-local pure rejection did not enter drain-only state at END_HEADERS"
  expect ((← handlerCalls.get) == 0)
    "method-local pure rejection entered the handler before DATA"
  let status ← rejectedStatus emitted
  expect (status.code == .unauthenticated)
    "method-local pure rejection emitted the wrong status"
  let malformed := dataFrame (ByteArray.mk #[0xff, 0x00, 0x01])
  let (_state, bodyFrames) ← expectOk
    (← Http2.Connection.processFrame registry state malformed)
    "drain rejected method-local request body"
  expect ((← handlerCalls.get) == 0)
    "rejected method-local request DATA reached the handler"
  expect (bodyFrames.all fun frame => frame.header.frameType == .windowUpdate)
    "rejected request body emitted a second application response"

def testFramePrincipalExactlyOnceAndPublicIsolation : IO Unit := do
  let authenticatorCalls ← IO.mkRef 0
  let protectedHandlerCalls ← IO.mkRef 0
  let publicHandlerCalls ← IO.mkRef 0
  let authenticator : RequestAuthenticator Nat := .effectful fun metadata => do
    authenticatorCalls.modify (fun calls => calls + 1)
    if metadata.getLast? "authorization" == some "Bearer good" then
      pure 41
    else
      throw (Status.error .unauthenticated "invalid bearer token")
  let registry := Registry.empty
    |>.registerAuthenticatedUnaryCodec protectedMethod authenticator
      identityDecode identityEncode (fun principal input => do
        protectedHandlerCalls.modify (fun calls => calls + 1)
        pure (input.push (UInt8.ofNat principal.value)))
    |>.registerUnary publicMethod (fun request => do
      publicHandlerCalls.modify (fun calls => calls + 1)
      pure { data := request.data.push 7, status := Status.ok })

  let protectedHeaders ← headersFrame {} protectedMethod (some "Bearer good") 1
  let (state, headerFrames) ← expectOk
    (← Http2.Connection.processFrame registry readyState protectedHeaders.1)
    "authenticate protected method headers"
  expect headerFrames.isEmpty "accepted protected headers emitted an early response"
  expect ((← authenticatorCalls.get) == 1)
    "method-local authenticator did not run exactly once at END_HEADERS"
  expect ((← protectedHandlerCalls.get) == 0)
    "protected handler ran before request DATA"
  let protectedBody ← expectOk
    (Message.encode { data := ByteArray.mk #[1] }) "encode protected request"
  let (state, protectedFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (dataFrame protectedBody 1))
    "dispatch protected authenticated request"
  expect ((← authenticatorCalls.get) == 1)
    "protected dispatch repeated method-local authentication"
  expect ((← protectedHandlerCalls.get) == 1)
    "protected handler did not run exactly once"
  let protectedMessages ← expectOk (Message.decodeAll (frameData protectedFrames))
    "decode protected response"
  expect (protectedMessages.size == 1
      && protectedMessages[0]!.data == ByteArray.mk #[1, 41])
    "accepted handler did not receive the authenticated principal"

  let publicHeaders ← headersFrame protectedHeaders.2 publicMethod none 3
  let (state, publicHeaderFrames) ← expectOk
    (← Http2.Connection.processFrame registry state publicHeaders.1)
    "process public method headers beside protected method"
  expect publicHeaderFrames.isEmpty "public headers emitted an early response"
  expect ((← authenticatorCalls.get) == 1)
    "public method invoked an unrelated method-local authenticator"
  let publicBody ← expectOk
    (Message.encode { data := ByteArray.mk #[2] }) "encode public request"
  let (_state, publicFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (dataFrame publicBody 3))
    "dispatch public request"
  expect ((← authenticatorCalls.get) == 1)
    "public dispatch inherited protected authentication"
  expect ((← publicHandlerCalls.get) == 1)
    "public method did not dispatch exactly once"
  let publicMessages ← expectOk (Message.decodeAll (frameData publicFrames))
    "decode public response"
  expect (publicMessages.size == 1
      && publicMessages[0]!.data == ByteArray.mk #[2, 7])
    "public method response was changed by protected authentication"

def serverStreamingMethod : MethodName := {
  service := "test.authenticated.v1.Service"
  method := "ProtectedStream"
}

def testAuthenticatedServerStreamingFrames : IO Unit := do
  let handlerCalls ← IO.mkRef 0
  let registry := Registry.empty.registerAuthenticatedServerStreamingStreamCodec
    serverStreamingMethod pureAuthenticator identityDecode identityEncode
    (fun principal input => do
      handlerCalls.modify (fun calls => calls + 1)
      MessageStream.ofArray #[
        input.push (UInt8.ofNat principal.value),
        ByteArray.mk #[9]
      ])
  let headers ← headersFrame {} serverStreamingMethod (some "Bearer good")
  let (state, headerFrames) ← expectOk
    (← Http2.Connection.processFrame registry readyState headers.1)
    "authenticate server-streaming headers"
  expect headerFrames.isEmpty "accepted server-streaming headers emitted early output"
  let body ← expectOk (Message.encode { data := ByteArray.mk #[3] })
    "encode server-streaming request"
  let (_state, responseFrames) ← expectOk
    (← Http2.Connection.processFrame registry state (dataFrame body))
    "dispatch authenticated server-streaming request"
  expect ((← handlerCalls.get) == 1)
    "authenticated server-streaming handler did not run exactly once"
  let messages ← expectOk (Message.decodeAll (frameData responseFrames))
    "decode authenticated server-streaming response"
  expect (messages.size == 2
      && messages[0]!.data == ByteArray.mk #[3, 23]
      && messages[1]!.data == ByteArray.mk #[9])
    "server-streaming handler lost its authenticated principal or stream shape"

def testDirectDispatchAuthenticatedFallbackIsClosed : IO Unit := do
  let registry := Registry.empty.registerAuthenticatedUnaryCodec
    protectedMethod pureAuthenticator identityDecode identityEncode
    (fun principal input => pure (input.push (UInt8.ofNat principal.value)))
  let body ← expectOk (Message.encode { data := ByteArray.mk #[6] })
    "encode direct-dispatch request"
  let result ← registry.dispatchUnary
    (requestMetadata protectedMethod (some "Bearer good")) body |>.run
  match result with
  | .error status =>
      expect (status.code == .unauthenticated)
        "direct dispatch of an unresolved authenticated entry did not fail closed"
  | .ok _ => fail "direct dispatch bypassed END_HEADERS authentication"

end Test.AuthenticatedServer

def main : IO Unit := do
  Test.AuthenticatedServer.testMethodEntryConstructionCompatibility
  Test.AuthenticatedServer.testPureAuthenticationAndComposition
  Test.AuthenticatedServer.testMethodLocalIsolation
  Test.AuthenticatedServer.testEffectfulAuthenticationAndDeadline
  Test.AuthenticatedServer.testCheckedRegistrationRejectsShadowing
  Test.AuthenticatedServer.testPureFrameRejectionBeforeData
  Test.AuthenticatedServer.testFramePrincipalExactlyOnceAndPublicIsolation
  Test.AuthenticatedServer.testAuthenticatedServerStreamingFrames
  Test.AuthenticatedServer.testDirectDispatchAuthenticatedFallbackIsClosed
  IO.println "gRPC authenticated server registration tests passed"
