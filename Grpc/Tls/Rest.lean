module

public import Std.Async.TCP
public import Std.Sync.CancellationToken
public import Grpc.Tls.Session

public section

namespace Grpc
namespace Tls
namespace Rest

/-!
A minimal HTTP/1.1 JSON server over TLS 1.3. Terminates TLS (ALPN "http/1.1")
and dispatches each request to a handler returning a JSON body. Intended for
plain REST endpoints; it shares the `ServerSession` record layer with the gRPC
path, so the same certificate/key drives both.

Scope: one request per connection (`Connection: close` semantics), request line
+ headers + optional `Content-Length` body. Enough for JSON REST endpoints; not
a general HTTP server (that is `Std.Http`).
-/

open _root_.Tls
open Std
open Std.Net
open Std.Async

/-- A parsed HTTP request. -/
structure Request where
  method : String
  path : String
  headers : Array (String × String) := #[]
  body : ByteArray := ByteArray.empty

/-- A handler response: a status code, reason, and JSON body string. -/
structure Response where
  status : Nat := 200
  reason : String := "OK"
  json : String

abbrev Handler := Request → IO Response

private def crlf : ByteArray := "\r\n".toUTF8

private def findSubarray (haystack needle : ByteArray) (start : Nat) : Option Nat :=
  if needle.size == 0 || haystack.size < needle.size then none
  else Id.run do
    for i in [start:haystack.size - needle.size + 1] do
      let mut hit := true
      for j in [0:needle.size] do
        if haystack.get! (i + j) != needle.get! j then
          hit := false
          break
      if hit then
        return some i
    return none

private def headerValue? (headers : Array (String × String)) (name : String) : Option String :=
  (headers.find? (fun (k, _) => k.toLower == name.toLower)).map (·.2)

/-- Parse the request head (request line + headers) from `bytes`, returning the
request (with empty body), the declared content length, and the byte offset just
past the blank line. `none` if the head is not yet complete. -/
private def parseHead (bytes : ByteArray) : Except String (Option (Request × Nat × Nat)) := do
  let doubleCrlf := "\r\n\r\n".toUTF8
  match findSubarray bytes doubleCrlf 0 with
  | none => pure none
  | some headEnd =>
      let headBytes := bytes.extract 0 headEnd
      let some headText := String.fromUTF8? headBytes
        | throw "request head is not valid UTF-8"
      let lines := headText.splitOn "\r\n"
      let some requestLine := lines[0]?
        | throw "empty request"
      let parts := requestLine.splitOn " "
      let some method := parts[0]? | throw "malformed request line"
      let some path := parts[1]? | throw "malformed request line"
      let mut headers : Array (String × String) := #[]
      for line in lines.drop 1 do
        if !line.isEmpty then
          match line.splitOn ": " with
          | key :: rest => headers := headers.push (key, ": ".intercalate rest)
          | [] => pure ()
      let contentLength := (headerValue? headers "content-length").bind (·.toNat?) |>.getD 0
      pure (some ({ method, path, headers }, contentLength, headEnd + doubleCrlf.size))

private def encodeResponse (response : Response) : ByteArray :=
  let bodyBytes := response.json.toUTF8
  let head := s!"HTTP/1.1 {response.status} {response.reason}\r\n\
    Content-Type: application/json\r\n\
    Content-Length: {bodyBytes.size}\r\n\
    Connection: close\r\n\r\n"
  head.toUTF8.append bodyBytes

/-- Read a full request (head + body) from the session, dispatch it, and write
the JSON response. Reads on-demand (no eager pump). -/
private partial def serveOneRequest (session : ServerSession) (handler : Handler)
    (buffered : ByteArray) : IO Unit := do
  match parseHead buffered with
  | .error _ => pure ()  -- malformed; drop the connection
  | .ok none =>
      -- Head incomplete; read more.
      match ← session.recvApp with
      | none => pure ()
      | some more => serveOneRequest session handler (buffered.append more)
  | .ok (some (request, contentLength, bodyStart)) =>
      let mut body := buffered.extract bodyStart buffered.size
      -- Read until the declared body is complete.
      let mut open? := true
      while body.size < contentLength && open? do
        match ← session.recvApp with
        | none => open? := false
        | some more => body := body.append more
      let request := { request with body := body.extract 0 (min contentLength body.size) }
      let response ← try handler request
        catch _ => pure { status := 500, reason := "Internal Server Error", json := "{\"error\":\"handler failed\"}" }
      session.send (encodeResponse response)
      session.closeNotify

/-- Static TLS identity for the REST server. -/
structure Config where
  certificateChain : Array ByteArray
  signingKey : ByteArray
  readSize : UInt64 := 16384
  noDelay : Bool := true

/-- A running REST-over-TLS server. -/
structure Server where
  socket : TCP.Socket.Server
  localAddress : SocketAddress
  shutdownToken : Std.CancellationToken

private def serveRestConnection (handler : Handler) (config : Config)
    (client : TCP.Socket.Client) : Async Unit := do
  try
    if config.noDelay then
      client.noDelay
    let entropy ← IO.getRandomBytes 64
    let serverConfig : Server.Config := {
      serverRandom := entropy.extract 0 32
      x25519Private := entropy.extract 32 64
      certificateChain := config.certificateChain
      signingKey := config.signingKey
      alpnProtocols := ["http/1.1"]
    }
    let session ← ServerSession.establish client serverConfig config.readSize
    serveOneRequest session handler ByteArray.empty
  catch _ =>
    pure ()

private inductive AcceptEvent where
  | accepted (client : TCP.Socket.Client)
  | shutdown

private partial def acceptLoop (socket : TCP.Socket.Server) (handler : Handler)
    (config : Config) (token : Std.CancellationToken) : Async Unit := do
  let event ← Selectable.one #[
    Selectable.case socket.acceptSelector fun client => pure (AcceptEvent.accepted client),
    Selectable.case token.selector fun _ => pure AcceptEvent.shutdown
  ]
  match event with
  | AcceptEvent.shutdown => pure ()
  | AcceptEvent.accepted client =>
      discard <| Async.toIO (serveRestConnection handler config client)
      acceptLoop socket handler config token

/-- Bind and serve a JSON REST API over TLS 1.3 (ALPN "http/1.1"). -/
def serve (handler : Handler) (config : Config)
    (address : SocketAddress := .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 8443 }) :
    IO Server := do
  let socket ← TCP.Socket.Server.mk
  socket.bind address
  socket.listen 1024
  if config.noDelay then
    socket.noDelay
  let localAddress ← socket.getSockName
  let token ← Std.CancellationToken.new
  discard <| Async.toIO (acceptLoop socket handler config token)
  pure { socket := socket, localAddress := localAddress, shutdownToken := token }

def shutdown (server : Server) : IO Unit :=
  server.shutdownToken.cancel (reason := Std.CancellationReason.shutdown)

end Rest
end Tls
end Grpc
