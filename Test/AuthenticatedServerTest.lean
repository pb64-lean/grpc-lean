import Grpc

open Grpc

namespace Test.AuthenticatedServer

def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

def fail (failure : String) : IO α :=
  throw (IO.userError failure)

def expectOk [Repr ε] (result : Except ε α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => fail s!"{description}: {(repr error).pretty}"

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

def tokenMetadata (token : String) : _root_.Http2.Headers :=
  _root_.Http2.Headers.empty.insert "authorization" token

def requestMetadata (method : MethodName) (token? : Option String := none) : _root_.Http2.Headers :=
  let metadata := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  match token? with
  | none => metadata
  | some token => metadata.insert "authorization" token

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
      match resolve _root_.Http2.Headers.empty with
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
  let handler ← expectUnaryHandler publicEntry (resolve _root_.Http2.Headers.empty)
    "resolve public entry"
  let response ← expectOk (← handler {
      method := publicMethod
      metadata := _root_.Http2.Headers.empty
      data := ByteArray.mk #[4]
    } |>.run) "run public handler"
  expect (response.data == ByteArray.mk #[4, 99])
    "public handler did not retain effective-handler interception"

def testEffectfulAuthentication : IO Unit := do
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
    (← registry.authorizeRequestHeaders entry _root_.Http2.Headers.empty |>.run)
    "run effectful method authentication"
  let handler ← expectUnaryHandler entry decision "resolve effectful authentication"
  let response ← expectOk (← handler {
      method := protectedMethod
      metadata := _root_.Http2.Headers.empty
      data := ByteArray.mk #[5]
    } |>.run) "run effectfully authenticated handler"
  expect (response.data == ByteArray.mk #[5, 31])
    "effectfully authenticated principal was not delivered"
  expect ((← calls.get) == 1)
    "effectful authenticator did not run exactly once"

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
      metadata := _root_.Http2.Headers.empty
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
  Test.AuthenticatedServer.testEffectfulAuthentication
  Test.AuthenticatedServer.testCheckedRegistrationRejectsShadowing
  Test.AuthenticatedServer.testDirectDispatchAuthenticatedFallbackIsClosed
  IO.println "gRPC authenticated server registration tests passed"
