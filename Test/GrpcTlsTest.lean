import Std.Async.TCP

import Grpc

open Grpc
open Std.Async

def echoMethod : MethodName := { service := "grpc.tls.test.EchoService", method := "Echo" }
def failMethod : MethodName := { service := "grpc.tls.test.EchoService", method := "Fail" }

def registry : Registry :=
  Registry.empty
    |>.registerUnary echoMethod (fun request => do
        pure { metadata := Metadata.empty.insert "served-over" "tls", data := request.data, status := Status.ok })
    |>.registerUnary failMethod (fun _ => do
        throw (Status.invalidArgument "denied over TLS"))

def repeatByte (count : Nat) (value : UInt8) : ByteArray :=
  ByteArray.mk (Array.replicate count value)

/-- The client side of the loopback: connect over TLS (validating the self-signed
cert against the PEM trust anchor and the SNI hostname), then exercise several
RPCs. Runs as its own task so the main thread does not block the co-located
server during the client's handshake. -/
def clientWork (port : UInt16) (certPem : String) : IO Unit := do
  -- A completed handshake whose post-handshake identity check fails must
  -- release its session and socket; the next connection should still work.
  let hostnameRejected ← try
      let unexpected ← Client.connectTls
        { address := Http2.Server.loopback port }
        {
          serverName := some "not-localhost.invalid"
          trustAnchorsPEM := some certPem
        }
      Client.close unexpected
      pure false
    catch _ =>
      pure true
  unless hostnameRejected do
    throw (IO.userError "TLS client unexpectedly accepted the wrong hostname")

  let client ← Client.connectTls
    { address := Http2.Server.loopback port }
    { serverName := some "localhost", trustAnchorsPEM := some certPem }

  let payload := "hello gRPC over TLS 1.3".toUTF8
  match ← Async.block (Client.call client "/grpc.tls.test.EchoService/Echo" payload) with
  | .error status => throw (IO.userError s!"TLS echo failed: {status.messageD}")
  | .ok (_, response) =>
      if response != payload then throw (IO.userError "TLS echo payload mismatch")
  IO.println "gRPC-over-TLS unary echo ok"

  match ← Async.block (Client.call client "/grpc.tls.test.EchoService/Fail" payload) with
  | .ok _ => throw (IO.userError "expected an error status over TLS")
  | .error status =>
      if status.code != Code.invalidArgument then
        throw (IO.userError "TLS error status code mismatch")
  IO.println "gRPC-over-TLS error propagation ok"

  match ← Async.block (Client.call client "/grpc.tls.test.EchoService/Echo" "again".toUTF8) with
  | .error status => throw (IO.userError s!"TLS second echo failed: {status.messageD}")
  | .ok (_, response) =>
      if response != "again".toUTF8 then throw (IO.userError "TLS second echo mismatch")
  IO.println "gRPC-over-TLS connection reuse ok"

  let big := repeatByte 120000 0x5a
  match ← Async.block (Client.call client "/grpc.tls.test.EchoService/Echo" big) with
  | .error status => throw (IO.userError s!"TLS large echo failed: {status.messageD}")
  | .ok (_, response) =>
      if response != big then throw (IO.userError "TLS large echo mismatch")
  IO.println "gRPC-over-TLS large message ok"

  Client.close client

def main : IO Unit := do
  -- Local policy validation precedes socket creation/connection.
  let invalidTrustError? ← try
      let unexpected ← Client.connectTls
        { address := Http2.Server.loopback 1 }
        { trustAnchorsPEM := some "not a PEM certificate" }
      Client.close unexpected
      pure none
    catch error =>
      pure (some error)
  match invalidTrustError? with
  | some (.userError message) =>
      unless message.startsWith "TLS trust anchors:" do
        throw (IO.userError s!"unexpected invalid-trust error: {message}")
  | some error =>
      throw (IO.userError s!"unexpected invalid-trust error: {error}")
  | none =>
      throw (IO.userError "invalid TLS trust anchors unexpectedly succeeded")

  let certDer ← IO.FS.readBinFile "Test/Fixtures/Tls/server_cert.der"
  let signingKey ← IO.FS.readBinFile "Test/Fixtures/Tls/server_key.raw"
  let certPem ← IO.FS.readFile "Test/Fixtures/Tls/server_cert.pem"

  let server ← Grpc.Server.serveTls registry
    { certificateChain := #[certDer], signingKey := signingKey }
    { address := Http2.Server.loopback 0 }
  let port := match server.localAddress with
    | .v4 addr => addr.port
    | .v6 addr => addr.port

  let clientTask ← IO.asTask (clientWork port certPem)
  match ← IO.wait clientTask with
  | .ok () => pure ()
  | .error e => throw e

  Grpc.Server.shutdown server
  IO.println "all gRPC/TLS assertions passed"
