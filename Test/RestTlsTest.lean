import Std.Async.TCP

import Grpc.Tls.Rest
import Grpc.Tls.Session
import Tls.Client

open Grpc.Tls
open Tls
open Std.Async
open Std.Net

/-- JSON REST handler: `GET /health` and `POST /echo` (echoes the request body). -/
def handler : Rest.Handler := fun request => do
  match request.method, request.path with
  | "GET", "/health" =>
      pure { json := "{\"status\":\"ok\",\"tls\":true}" }
  | "POST", "/echo" =>
      let body := String.fromUTF8? request.body |>.getD ""
      pure { json := s!"\{\"echo\":\"{body}\"}" }
  | _, _ =>
      pure { status := 404, reason := "Not Found", json := "{\"error\":\"not found\"}" }

/-- Send one HTTP/1.1 request over a TLS client session and read the full
response bytes (until the socket closes). -/
partial def readResponse (session : ClientSession) (acc : ByteArray) : IO ByteArray := do
  let raw? ← try (session.socket.recv? 16384).block catch _ => pure none
  match raw? with
  | none => pure acc
  | some raw =>
      match ← session.feedInbound raw with
      | none => pure (acc)
      | some plaintext => readResponse session (acc.append plaintext)

def httpsRequest (port : UInt16) (requestLine : String) : IO String := do
  let socket ← TCP.Socket.Client.mk
  (socket.connect (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := port })).block
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := some "localhost"
    alpnProtocols := #["http/1.1"]
  }
  let session ← Async.block (ClientSession.establish socket clientConfig)
  session.send requestLine.toUTF8
  let response ← readResponse session ByteArray.empty
  session.close
  pure (String.fromUTF8? response |>.getD "")

def clientWork (port : UInt16) : IO Unit := do
  -- GET /health
  let health ← httpsRequest port "GET /health HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"
  unless (health.splitOn "200").length > 1 do
    throw (IO.userError s!"REST /health: expected 200 status, got: {health}")
  unless (health.splitOn "\"status\":\"ok\"").length > 1 do
    throw (IO.userError s!"REST /health: expected ok JSON, got: {health}")
  unless (health.splitOn "application/json").length > 1 do
    throw (IO.userError "REST /health: expected application/json content type")
  IO.println "REST-over-TLS GET /health ok"

  -- POST /echo
  let bodyText := "hello-rest"
  let echo ← httpsRequest port
    s!"POST /echo HTTP/1.1\r\nHost: localhost\r\nContent-Length: {bodyText.utf8ByteSize}\r\nConnection: close\r\n\r\n{bodyText}"
  unless (echo.splitOn s!"\"echo\":\"{bodyText}\"").length > 1 do
    throw (IO.userError s!"REST /echo: expected echoed body, got: {echo}")
  IO.println "REST-over-TLS POST /echo ok"

  -- 404
  let missing ← httpsRequest port "GET /nope HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"
  unless (missing.splitOn "404").length > 1 do
    throw (IO.userError s!"REST /nope: expected 404, got: {missing}")
  IO.println "REST-over-TLS 404 ok"

def main : IO Unit := do
  let certDer ← IO.FS.readBinFile "Test/Fixtures/Tls/server_cert.der"
  let signingKey ← IO.FS.readBinFile "Test/Fixtures/Tls/server_key.raw"

  let server ← Rest.serve handler
    { certificateChain := #[certDer], signingKey := signingKey }
    (.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 })
  let port := match server.localAddress with
    | .v4 addr => addr.port
    | .v6 addr => addr.port

  let clientTask ← IO.asTask (clientWork port)
  match ← IO.wait clientTask with
  | .ok () => pure ()
  | .error e => throw e

  Rest.shutdown server
  IO.println "all REST/TLS assertions passed"
