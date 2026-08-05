import Std.Async.TCP

import Grpc.Tls.Rest
import Grpc.Tls.Session
import Tls.Client

open Grpc.Tls
open Tls
open Std.Async
open Std.Net

def observeTimeoutMs : Nat := 3000

partial def awaitTaskWithin (task : Task (Except IO.Error α)) (remainingMs : Nat) :
    IO (Option α) := do
  if ← IO.hasFinished task then
    match task.get with
    | .ok value => pure (some value)
    | .error err => throw err
  else if remainingMs == 0 then
    pure none
  else
    IO.sleep 1
    awaitTaskWithin task (remainingMs - 1)

partial def waitUntil (message : String) (remainingMs : Nat) (check : IO Bool) : IO Unit := do
  if ← check then
    pure ()
  else if remainingMs == 0 then
    throw (IO.userError message)
  else
    IO.sleep 1
    waitUntil message (remainingMs - 1) check

partial def drainToEof (client : Std.Async.TCP.Socket.Client) : IO Unit := do
  match ← (client.recv? 8192).block with
  | none => pure ()
  | some _ => drainToEof client

def expectPeerClosed (client : Std.Async.TCP.Socket.Client) (message : String) : IO Unit := do
  let eofTask ← IO.asTask (drainToEof client)
  match ← awaitTaskWithin eofTask observeTimeoutMs with
  | some () => pure ()
  | none =>
      IO.cancel eofTask
      throw (IO.userError message)

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
  let (session, handshakeLeftover) ← Async.block (ClientSession.establish socket clientConfig)
  session.send requestLine.toUTF8
  -- Any 0.5-RTT bytes the server coalesced behind its Finished flight are the
  -- head of the response stream.
  let response ← readResponse session handshakeLeftover
  Async.block session.close
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

def loopbackEphemeral : SocketAddress :=
  .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 }

def serverPort (server : Rest.Server) : UInt16 :=
  match server.localAddress with
  | .v4 addr => addr.port
  | .v6 addr => addr.port

def connectRaw (server : Rest.Server) : IO Std.Async.TCP.Socket.Client := do
  let client ← Std.Async.TCP.Socket.Client.mk
  (client.connect server.localAddress).block
  client.noDelay
  pure client

def awaitServerWait (server : Rest.Server) (message : String) : IO Unit := do
  let waitTask ← IO.asTask (Rest.wait server (drainTimeoutMs := some 1000))
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | some () => pure ()
  | none =>
      IO.cancel waitTask
      throw (IO.userError message)

def hasFailureStage (server : Rest.Server) (stage : Rest.ConnectionFailureStage) : IO Bool := do
  let failures ← Rest.connectionFailures server
  pure (failures.any fun failure => failure.stage == stage)

/-- An accepted peer that never sends ClientHello is still owned by the server;
shutdown interrupts its handshake, `wait` joins it, and the peer sees our FIN. -/
def testShutdownCancelsSilentHandshake (config : Rest.Config) : IO Unit := do
  let server ← Rest.serve handler config loopbackEphemeral
  let client ← connectRaw server
  IO.sleep 20
  Rest.shutdown server
  awaitServerWait server "REST shutdown did not join a silent TLS handshake"
  expectPeerClosed client "REST silent-handshake socket was not retired"
  try (client.shutdown).block catch _ => pure ()

/-- Shutdown also interrupts a completed TLS connection blocked partway through
its declared request body.  No partial request reaches the application handler. -/
def testShutdownCancelsIncompleteRequest (config : Rest.Config) : IO Unit := do
  let invoked ← IO.mkRef false
  let trackedHandler : Rest.Handler := fun request => do
    invoked.set true
    handler request
  let server ← Rest.serve trackedHandler config loopbackEphemeral
  let socket ← connectRaw server
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := some "localhost"
    alpnProtocols := #["http/1.1"]
  }
  let (session, _handshakeLeftover) ← Async.block (ClientSession.establish socket clientConfig)
  session.send
    "POST /echo HTTP/1.1\r\nHost: localhost\r\nContent-Length: 100\r\nConnection: close\r\n\r\nabc".toUTF8
  IO.sleep 20
  Rest.shutdown server
  awaitServerWait server "REST shutdown did not join an incomplete request read"
  unless !(← invoked.get) do
    throw (IO.userError "REST shutdown dispatched an incomplete request")
  expectPeerClosed session.socket "REST incomplete-request socket was not retired"
  try Async.block session.close catch _ => pure ()

/-- An ordinary authenticated peer EOF before `Content-Length` is a malformed,
truncated request.  Reject it without relying on server shutdown cancellation. -/
def testRejectsTruncatedBodyAtPeerEof (config : Rest.Config) : IO Unit := do
  let invoked ← IO.mkRef false
  let trackedHandler : Rest.Handler := fun request => do
    invoked.set true
    handler request
  let server ← Rest.serve trackedHandler config loopbackEphemeral
  let socket ← connectRaw server
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := some "localhost"
    alpnProtocols := #["http/1.1"]
  }
  let (session, _handshakeLeftover) ← Async.block (ClientSession.establish socket clientConfig)
  session.send
    "POST /echo HTTP/1.1\r\nHost: localhost\r\nContent-Length: 100\r\nConnection: close\r\n\r\nabc".toUTF8
  -- Send authenticated close_notify and half-close while the server is still
  -- running normally.  Observing its EOF proves it processed the peer EOF
  -- before `Rest.wait` below cancels the global shutdown token.
  Async.block session.close
  expectPeerClosed session.socket "REST truncated-request socket was not retired after peer EOF"
  if ← invoked.get then
    throw (IO.userError "REST dispatched a body truncated by ordinary peer EOF")
  awaitServerWait server "REST server did not join the rejected truncated request"
  unless ← hasFailureStage server .request do
    throw (IO.userError "REST did not retain an observable truncated-request failure")

/-- `wait` owns accepted application work too: it cannot report completion while
a handler is still producing the one response that precedes close_notify/FIN. -/
def testWaitJoinsRunningHandler (config : Rest.Config) : IO Unit := do
  let started ← IO.mkRef false
  let release ← IO.mkRef false
  let slowHandler : Rest.Handler := fun _request => do
    started.set true
    while !(← release.get) do IO.sleep 1
    pure { json := "{\"owned\":true}" }
  let server ← Rest.serve slowHandler config loopbackEphemeral
  let socket ← connectRaw server
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := some "localhost"
    alpnProtocols := #["http/1.1"]
  }
  let (session, _handshakeLeftover) ← Async.block (ClientSession.establish socket clientConfig)
  session.send "GET /owned HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n".toUTF8
  waitUntil "REST ownership test handler did not start" observeTimeoutMs started.get

  Rest.shutdown server
  let waitTask ← IO.asTask (Rest.wait server (drainTimeoutMs := some 1000))
  IO.sleep 20
  if ← IO.hasFinished waitTask then
    throw (IO.userError "REST wait returned while an accepted handler was still running")
  release.set true
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | none =>
      IO.cancel waitTask
      throw (IO.userError "REST wait did not join its released handler task")
  | some () => pure ()

  let response ← readResponse session ByteArray.empty
  let responseText := String.fromUTF8? response |>.getD ""
  unless (responseText.splitOn "\"owned\":true").length > 1 do
    throw (IO.userError s!"REST shutdown lost the owned handler response: {responseText}")
  try Async.block session.close catch _ => pure ()

/-- A handler exception is visible twice at the intended boundary: the peer gets
a 500 response, while operators can inspect the bounded connection-failure log.
It remains connection-local, so orderly server shutdown still succeeds. -/
def testHandlerFailureObservable (config : Rest.Config) : IO Unit := do
  let failingHandler : Rest.Handler := fun _ =>
    throw (IO.userError "deliberate REST handler failure")
  let server ← Rest.serve failingHandler config loopbackEphemeral
  let response ← httpsRequest (serverPort server)
    "GET /fails HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n"
  unless (response.splitOn "500 Internal Server Error").length > 1 do
    throw (IO.userError s!"REST handler failure did not produce a 500 response: {response}")
  awaitServerWait server "REST server did not join the failed-handler connection"
  unless ← hasFailureStage server .handler do
    throw (IO.userError "REST handler failure was absent from the connection-failure log")

/-- Send a request, drain the client's FIFO writer while closing its write side,
then wait until the blocked handler owns the connection. `ClientSession.send`
is only an enqueue, so draining before the observation removes a scheduler race
between the test's timeout and delivery of the request. Returning still drops
the final client-side socket reference before the handler is released, making
the subsequent server write fail. -/
def closeClientBeforeResponse (server : Rest.Server) (handlerStarted : IO.Ref Bool) : IO Unit := do
  let socket ← connectRaw server
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := some "localhost"
    alpnProtocols := #["http/1.1"]
  }
  let (session, _handshakeLeftover) ← Async.block (ClientSession.establish socket clientConfig)
  session.send "GET /late-write HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n".toUTF8
  -- `close` drains records in FIFO order before its bounded write-side
  -- shutdown, so the complete request precedes close_notify on the wire.
  Async.block session.close
  waitUntil "REST late-writer test handler did not start" observeTimeoutMs handlerStarted.get

/-- `ServerSession.send` is an enqueue, not delivery. If the sole record writer
later fails, retirement must inspect its stored error and publish it rather than
letting the connection look successful. -/
def testLateWriterFailureObservable (config : Rest.Config) : IO Unit := do
  let started ← IO.mkRef false
  let release ← IO.mkRef false
  let largeBody := String.fromUTF8! <| ByteArray.mk (Array.replicate (1024 * 1024) 120)
  let delayedHandler : Rest.Handler := fun _ => do
    started.set true
    while !(← release.get) do IO.sleep 1
    pure { json := largeBody }
  let server ← Rest.serve delayedHandler config loopbackEphemeral
  closeClientBeforeResponse server started
  -- Let the peer's close reach the server TCP state before enqueueing a large
  -- response. The server task is still parked in the handler during this delay.
  IO.sleep 250
  release.set true
  waitUntil "REST did not expose the asynchronous TLS record-writer failure"
    observeTimeoutMs (hasFailureStage server .recordWriter)
  awaitServerWait server "REST server did not join the late-writer failure"

/-- The forced timeout path transfers ownership out of the registry, cancels and
boundedly joins exact owners, and returns with no retained accepted clients. -/
def testForcedWaitClearsOwnership (config : Rest.Config) : IO Unit := do
  let started ← IO.mkRef false
  let blockedHandler : Rest.Handler := fun _ => do
    started.set true
    -- Longer than the zero graceful-drain deadline but shorter than the bounded
    -- forced-owner join, so this exercises forced transfer without manufacturing
    -- an uncooperative user task that cannot be killed by Lean's cooperative
    -- `IO.cancel`.
    IO.sleep 50
    pure { json := "{\"released\":true}" }
  let server ← Rest.serve blockedHandler config loopbackEphemeral
  let socket ← connectRaw server
  let entropy ← IO.getRandomBytes 96
  let clientConfig : Client.Config := {
    clientRandom := entropy.extract 0 32
    x25519Private := entropy.extract 32 64
    legacySessionId := entropy.extract 64 96
    serverName := some "localhost"
    alpnProtocols := #["http/1.1"]
  }
  let (session, _handshakeLeftover) ← Async.block (ClientSession.establish socket clientConfig)
  session.send "GET /forced HTTP/1.1\r\nHost: localhost\r\nConnection: close\r\n\r\n".toUTF8
  waitUntil "REST forced-ownership test handler did not start" observeTimeoutMs started.get
  let waitTask ← IO.asTask (Rest.wait server (drainTimeoutMs := some 0))
  match ← awaitTaskWithin waitTask observeTimeoutMs with
  | none =>
      IO.cancel waitTask
      throw (IO.userError "REST forced wait exceeded its bounded owner join")
  | some () => pure ()
  unless (← Rest.activeConnectionCount server) == 0 do
    throw (IO.userError "REST forced wait retained accepted connection owners")
  expectPeerClosed session.socket "REST forced wait did not retire the accepted socket"
  try Async.block session.close catch _ => pure ()

def testRequests (config : Rest.Config) : IO Unit := do
  let server ← Rest.serve handler config loopbackEphemeral
  let port := serverPort server

  clientWork port

  Rest.shutdown server
  awaitServerWait server "REST server did not join completed request tasks"

def main : IO Unit := do
  let certDer ← IO.FS.readBinFile "Test/Fixtures/Tls/server_cert.der"
  let signingKey ← IO.FS.readBinFile "Test/Fixtures/Tls/server_key.raw"
  let config : Rest.Config := {
    certificateChain := #[certDer],
    signingKey := signingKey
  }

  testRequests config
  testShutdownCancelsSilentHandshake config
  testShutdownCancelsIncompleteRequest config
  testRejectsTruncatedBodyAtPeerEof config
  testWaitJoinsRunningHandler config
  testHandlerFailureObservable config
  testLateWriterFailureObservable config
  testForcedWaitClearsOwnership config
  IO.println "all REST/TLS assertions passed"
