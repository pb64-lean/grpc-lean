import Tls.Client
import Tls.Server

open Tls

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def expectEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  expect (actual == expected) msg

def ce {α} (r : Except Client.Error α) : IO α := do
  match r with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"client TLS error: {e}")

def se {α} (r : Except Server.Error α) : IO α := do
  match r with
  | .ok v => pure v
  | .error e => throw (IO.userError s!"server TLS error: {e}")

def fill (n : Nat) (b : UInt8) : ByteArray := ByteArray.mk (Array.replicate n b)

/-- Drive a full TLS 1.3 handshake between the ported client machine and the new
server machine with no I/O, then exchange encrypted application data in both
directions. Exercises ServerHello/EE/Certificate/CertificateVerify(Ed25519)/
Finished construction, the record layer, ALPN, and SNI end to end. -/
def main : IO Unit := do
  let certDer ← IO.FS.readBinFile "Test/Fixtures/Tls/server_cert.der"
  let signingKey ← IO.FS.readBinFile "Test/Fixtures/Tls/server_key.raw"
  expectEq signingKey.size 32 "raw Ed25519 signing key should be 32 bytes"

  let clientCfg : Client.Config := {
    clientRandom := fill 32 0x11
    x25519Private := fill 32 0x22
    legacySessionId := fill 32 0x55
    serverName := some "localhost"
    alpnProtocols := #["h2"]
  }
  let serverCfg : Server.Config := {
    serverRandom := fill 32 0x33
    x25519Private := fill 32 0x44
    certificateChain := #[certDer]
    signingKey := signingKey
    alpnProtocols := ["h2"]
  }

  -- 1. ClientHello.
  let clientHello ← ce (Client.start clientCfg)
  -- 2. Server consumes ClientHello, emits ServerHello + encrypted flight.
  let serverStart := Server.start serverCfg
  let serverFlight ← se (Server.feed serverStart clientHello.wireBytes)
  expect (!serverFlight.state.connected) "server not yet connected before client Finished"
  -- 3. Client consumes the flight, verifies CertificateVerify + Finished, emits its Finished.
  let clientDone ← ce (Client.feed clientHello.state serverFlight.wireBytes)
  expect clientDone.state.connected "client should be connected after the server flight"
  expectEq clientDone.state.alpnSelected (some "h2") "client should observe the server's ALPN h2"
  -- 4. Server consumes the client Finished.
  let serverDone ← se (Server.feed serverFlight.state clientDone.wireBytes)
  expect serverDone.state.connected "server should be connected after the client Finished"
  expectEq serverDone.state.alpnSelected (some "h2") "server should negotiate ALPN h2"
  expectEq serverDone.state.peerServerName (some "localhost") "server should surface the SNI host"
  IO.println "TLS 1.3 handshake completed (Ed25519 server auth, ALPN h2, SNI localhost)"

  -- 5. Client -> server application data.
  let request := "hello over TLS".toUTF8
  let sealed ← ce (Client.sealApplication clientDone.state request)
  let received ← se (Server.feed serverDone.state sealed.wireBytes)
  expectEq received.plaintext request "server should decrypt the client's application data"
  IO.println "client -> server application data ok"

  -- 6. Server -> client application data.
  let response := "response over TLS".toUTF8
  let sealed2 ← se (Server.sealApplication received.state response)
  let received2 ← ce (Client.feed sealed.state sealed2.wireBytes)
  expectEq received2.plaintext response "client should decrypt the server's application data"
  IO.println "server -> client application data ok"

  -- 6b. Multiple records sealed separately, then fed to the peer COALESCED into a
  -- single chunk (as TCP may deliver them). This is the case the flaky socket test
  -- pointed at — pure, no concurrency. Uses the latest states (server=sealed2,
  -- client=received2) so sequence numbers line up.
  let m1 := "first".toUTF8
  let m2 := "second-message".toUTF8
  let m3 := "third".toUTF8
  let s1 ← se (Server.sealApplication sealed2.state m1)
  let s2 ← se (Server.sealApplication s1.state m2)
  let s3 ← se (Server.sealApplication s2.state m3)
  let coalesced := (s1.wireBytes.append s2.wireBytes).append s3.wireBytes
  let d ← ce (Client.feed received2.state coalesced)
  expectEq d.plaintext ((m1.append m2).append m3)
    "client should decode three server records delivered in one coalesced chunk"
  IO.println "coalesced multi-record decode ok"

  -- 7. A second, larger message to advance record sequence numbers on both sides.
  let big := fill 40000 0x7a
  let sealedBig ← ce (Client.sealApplication d.state big)
  let receivedBig ← se (Server.feed s3.state sealedBig.wireBytes)
  expectEq receivedBig.plaintext big "server should decrypt a multi-record message"
  IO.println "multi-record application data ok"

  IO.println "all TLS handshake assertions passed"
