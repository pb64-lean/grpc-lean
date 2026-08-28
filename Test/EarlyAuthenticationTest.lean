import Grpc

open Grpc

namespace Test.EarlyAuthentication

def expect (condition : Bool) (failure : String) : IO Unit := do
  unless condition do throw (IO.userError failure)

def fail (failure : String) : IO α :=
  throw (IO.userError failure)

def expectOk [Repr ε] (result : Except ε α) (description : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => fail s!"{description}: {(repr error).pretty}"

def method : MethodName := {
  service := "test.authentication.v1.AuthenticationService"
  method := "Check"
}

def metadata (authorization? : Option String) : _root_.Http2.Headers :=
  let value := _root_.Http2.Headers.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "127.0.0.1"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  match authorization? with
  | none => value
  | some authorization => value.insert "authorization" authorization

def headersFrame (authorization? : Option String) (streamId : Nat := 1) : IO _root_.Http2.Frame := do
  let encoded ← expectOk (_root_.Http2.Hpack.encodeHeaderBlock {} (metadata authorization?))
    "encode request headers"
  pure {
    header := {
      length := encoded.1.size
      frameType := .headers
      flags := _root_.Http2.FrameFlag.endHeaders
      streamId
    }
    payload := encoded.1
  }

def headersFrameFor (requestMetadata : _root_.Http2.Headers) (streamId : Nat := 1) : IO _root_.Http2.Frame := do
  let encoded ← expectOk (_root_.Http2.Hpack.encodeHeaderBlock {} requestMetadata)
    "encode request headers"
  pure {
    header := {
      length := encoded.1.size
      frameType := .headers
      flags := _root_.Http2.FrameFlag.endHeaders
      streamId
    }
    payload := encoded.1
  }

def replaceHeaderValue (source : _root_.Http2.Headers) (name value : String) : _root_.Http2.Headers :=
  let normalized := _root_.Http2.Header.normalizeName name
  source.map fun header =>
    if header.name == normalized then { header with value := value } else header

def dataFrame (payload : ByteArray) (streamId : Nat := 1) : _root_.Http2.Frame := {
  header := {
    length := payload.size
    frameType := .data
    flags := _root_.Http2.FrameFlag.endStream
    streamId
  }
  payload
}

def rejectedStatus (frames : Array _root_.Http2.Frame) : IO Status := do
  let some frame := frames.find? fun frame =>
      frame.header.frameType == .headers
        && _root_.Http2.FrameFlag.has frame.header.flags _root_.Http2.FrameFlag.endStream
    | fail "authorization rejection did not emit trailers"
  let decoded ← expectOk (_root_.Http2.Hpack.decodeHeaderBlock {} frame.payload)
    "decode authorization rejection"
  expectOk (Headers.statusFromTrailers decoded.headers)
    "decode authorization rejection status"
def frameData (frames : Array _root_.Http2.Frame) : ByteArray :=
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


def readyState : Grpc.Http2.Connection.State :=
  let initial := Grpc.Http2.Connection.initialState
  {
    initial with
    protocol := {
      initial.protocol with
      prefaceReceived := true
      receivedSettings := true
    }
  }

def testOwnedConnectionAuthenticatesAtHeaders : IO Unit := do
  let rejectedAuthorizerCalls ← IO.mkRef 0
  let rejectedHandlerCalls ← IO.mkRef 0
  let rejectedRegistry :=
    authenticatedRegistry rejectedAuthorizerCalls rejectedHandlerCalls
  let rejectedState ← Std.Mutex.new readyState
  let rejectedFrames ← IO.mkRef (#[] : Array _root_.Http2.Frame)
  let emitRejected (frames : Array _root_.Http2.Frame) : IO Unit :=
    rejectedFrames.modify fun emitted => emitted.append frames
  try
    let headers ← headersFrame none
    let headerWire ← expectOk (_root_.Http2.Frame.encode headers)
      "encode unauthenticated request headers"
    discard <| expectOk (← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned
        rejectedRegistry rejectedState headerWire emitRejected)
      "reject unauthenticated request headers"
    expect ((← rejectedAuthorizerCalls.get) == 1)
      "request-header authorizer did not run exactly once at END_HEADERS"
    expect ((← rejectedHandlerCalls.get) == 0)
      "unauthenticated headers entered the RPC handler"
    let status ← rejectedStatus (← rejectedFrames.get)
    expect (status.code == .unauthenticated)
      "header-time rejection emitted the wrong gRPC status"
    let responseHeaderCount := (← rejectedFrames.get).countP
      (fun frame => frame.header.frameType == .headers)

    let bodyWire ← expectOk
      (_root_.Http2.Frame.encode (dataFrame (ByteArray.mk #[0xff, 0x00, 0x01])))
      "encode rejected request body"
    discard <| expectOk (← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned
        rejectedRegistry rejectedState bodyWire emitRejected)
      "drain rejected request body"
    expect ((← rejectedAuthorizerCalls.get) == 1)
      "draining rejected DATA repeated request authorization"
    expect ((← rejectedHandlerCalls.get) == 0)
      "rejected request DATA reached the RPC handler"
    expect ((← rejectedFrames.get).countP
        (fun frame => frame.header.frameType == .headers) == responseHeaderCount)
      "draining rejected DATA emitted a second application response"
  finally
    discard <| Std.Async.Async.block <|
      Grpc.Http2.Connection.cancelActiveSharedOwned rejectedState

  let acceptedAuthorizerCalls ← IO.mkRef 0
  let acceptedHandlerCalls ← IO.mkRef 0
  let acceptedRegistry :=
    authenticatedRegistry acceptedAuthorizerCalls acceptedHandlerCalls
  let acceptedState ← Std.Mutex.new readyState
  let acceptedFrames ← IO.mkRef (#[] : Array _root_.Http2.Frame)
  let emitAccepted (frames : Array _root_.Http2.Frame) : IO Unit :=
    acceptedFrames.modify fun emitted => emitted.append frames
  try
    let headers ← headersFrame (some "TestScheme local-test-token")
    let headerWire ← expectOk (_root_.Http2.Frame.encode headers)
      "encode authenticated request headers"
    discard <| expectOk (← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned
        acceptedRegistry acceptedState headerWire emitAccepted)
      "authorize request headers"
    expect ((← acceptedAuthorizerCalls.get) == 1)
      "accepted request was not authorized exactly once"
    expect ((← acceptedHandlerCalls.get) == 0)
      "accepted headers entered the handler before request DATA"

    let requestMessage ← expectOk (Message.encode { data := ByteArray.mk #[1] })
      "encode authenticated request"
    let bodyWire ← expectOk (_root_.Http2.Frame.encode (dataFrame requestMessage))
      "encode authenticated request DATA"
    discard <| expectOk (← Std.Async.Async.block <|
      Grpc.Http2.Connection.processBytesSharedWithOwned
        acceptedRegistry acceptedState bodyWire emitAccepted)
      "dispatch authenticated request"
    waitUntil "authenticated response did not finish" 1000 do
      pure <| (← acceptedFrames.get).any fun frame =>
        frame.header.frameType == .headers
          && _root_.Http2.FrameFlag.has frame.header.flags
            _root_.Http2.FrameFlag.endStream
    expect ((← acceptedAuthorizerCalls.get) == 1)
      "authenticated dispatch repeated header authorization"
    expect ((← acceptedHandlerCalls.get) == 1)
      "authenticated dispatch did not use the captured handler capability"
    let messages ← expectOk (Message.decodeAll (frameData (← acceptedFrames.get)))
      "decode authenticated response"
    expect (messages.size == 1
        && messages[0]!.data == ByteArray.mk #[1, 23])
      "authenticated response lost the state resolved at END_HEADERS"
  finally
    discard <| Std.Async.Async.block <|
      Grpc.Http2.Connection.cancelActiveSharedOwned acceptedState

end Test.EarlyAuthentication

def main : IO Unit := do
  Test.EarlyAuthentication.testAuthorizerInstallersAreLastWins
  Test.EarlyAuthentication.testOwnedConnectionAuthenticatesAtHeaders
  IO.println "gRPC early-authentication tests passed"
