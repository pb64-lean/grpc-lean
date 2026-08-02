module

public import Std.Async.TCP
public import Std.Sync.Mutex
public import Std.Sync.Channel
public import Tls.Client
public import Tls.Server

public section

namespace Grpc
namespace Tls

/-!
Socket-driving wrappers over the sans-I/O TLS engines. A `ClientSession` /
`ServerSession` owns a `TCP.Socket.Client` plus the TLS state behind a mutex, and
exposes `send` (application data) and `feedInbound` (raw transport bytes ->
decrypted application data).

TLS records must reach the wire in sequence-number order. Sealing (which advances
the write sequence) happens under the session lock; the resulting record bytes are
enqueued to a single per-session writer task that performs the actual socket write
with no lock held. Because seal-and-enqueue is atomic under the lock and the writer
is a single FIFO consumer, wire order equals sequence order — without ever holding
the lock across a blocking socket write (which would deadlock decrypt against
encrypt on a busy connection).
-/

open _root_.Tls
open Std
open Std.Net
open Std.Async

private def clientErr {α} (result : Except Client.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"TLS client: {error}")

private def serverErr {α} (result : Except Server.Error α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"TLS server: {error}")

/-! ## Handshake drivers (run once, synchronously, at connection setup). -/

/-- Drive a client handshake to completion over `socket`. Sends ClientHello, then
feeds server flights and writes each reply until the connection is established.
Runs in `Async` so its socket waits suspend cooperatively — a blocking handshake
would park a worker, and in a same-process client+server (a loopback test) the few
pool workers can all be parked at once, deadlocking the peer's handshake. -/
private partial def clientHandshakeLoop (socket : TCP.Socket.Client) (readSize : UInt64)
    (state : Client.State) : Async Client.State := do
  if state.connected then
    pure state
  else
    let some chunk ← socket.recv? readSize
      | throw (IO.userError "peer closed the connection during the TLS handshake")
    let output ← clientErr (Client.feed state chunk)
    unless output.wireBytes.isEmpty do
      socket.send output.wireBytes
    clientHandshakeLoop socket readSize output.state

def clientHandshake (socket : TCP.Socket.Client) (config : Client.Config)
    (readSize : UInt64 := 16384) : Async Client.State := do
  let hello ← clientErr (Client.start config)
  socket.send hello.wireBytes
  clientHandshakeLoop socket readSize hello.state

/-- Drive a server handshake to completion over `socket` (cooperatively — see
`clientHandshakeLoop`). Waits for ClientHello, emits the server flight, then
consumes the client Finished. -/
private partial def serverHandshakeLoop (socket : TCP.Socket.Client) (readSize : UInt64)
    (state : Server.State) : Async Server.State := do
  if state.connected then
    pure state
  else
    let some chunk ← socket.recv? readSize
      | throw (IO.userError "peer closed the connection during the TLS handshake")
    let output ← serverErr (Server.feed state chunk)
    unless output.wireBytes.isEmpty do
      socket.send output.wireBytes
    serverHandshakeLoop socket readSize output.state

def serverHandshake (socket : TCP.Socket.Client) (config : Server.Config)
    (readSize : UInt64 := 16384) : Async Server.State :=
  serverHandshakeLoop socket readSize (Server.start config)

/-! ## Sessions. -/

structure ClientSession where
  socket : TCP.Socket.Client
  state : Std.Mutex Client.State
  /-- Sealed record bytes awaiting the socket, drained in FIFO order by the writer
  task so the state lock is never held across a blocking socket write. -/
  outbound : Std.CloseableChannel ByteArray
  /-- Exact writer handle, joined by `close` after the outbound queue drains. -/
  private writer : AsyncTask Unit

structure ServerSession where
  socket : TCP.Socket.Client
  state : Std.Mutex Server.State
  outbound : Std.CloseableChannel ByteArray

/-- The single writer loop: drains sealed record bytes and writes them to the
socket in FIFO order, awaiting each send *cooperatively* (never parking a worker
thread — a blocking `.block` here would exhaust the pool when many TLS
connections write at once, deadlocking readers). -/
private partial def writerLoop (socket : TCP.Socket.Client)
    (outbound : Std.CloseableChannel ByteArray) : Async Unit := do
  match ← await (← outbound.recv) with
  | none => pure ()
  | some bytes =>
      (try socket.send bytes catch _ => pure ())
      writerLoop socket outbound

private def startWriter (socket : TCP.Socket.Client)
    (outbound : Std.CloseableChannel ByteArray) : IO (AsyncTask Unit) :=
  Async.toIO (writerLoop socket outbound)

namespace ClientSession

/-- Establish a TLS client session over an already-connected socket. -/
def establish (socket : TCP.Socket.Client) (config : Client.Config)
    (readSize : UInt64 := 16384) : Async ClientSession := do
  let state ← clientHandshake socket config readSize
  let outbound ← Std.CloseableChannel.new
  let stateMutex ← Std.Mutex.new state
  let writer ← startWriter socket outbound
  pure {
    socket := socket
    state := stateMutex
    outbound := outbound
    writer := writer
  }

/-- The ALPN protocol the peer selected, if any. -/
def alpnSelected (session : ClientSession) : IO (Option String) :=
  session.state.atomically do pure (← get).alpnSelected

/-- The peer's certificate chain (leaf first), as strict-parsed during the
handshake. Used by post-handshake chain/hostname verification policy. -/
def peerCertificates (session : ClientSession) : IO (Array TLS13.X509.Certificate) :=
  session.state.atomically do pure (← get).peerCertificates

/-- Seal application bytes and enqueue the record for the writer task. Sealing
(sequence advance) is atomic under the lock; the socket write is lock-free. -/
def send (session : ClientSession) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then return
  session.state.atomically do
    let state ← get
    let output ← clientErr (Client.sealApplication state bytes)
    set output.state
    discard <| session.outbound.send output.wireBytes

/-- Feed one raw transport chunk. Enqueues any TLS reply (KeyUpdate response,
close_notify) and returns decrypted application bytes; `none` marks an
authenticated close_notify (EOF). -/
def feedInbound (session : ClientSession) (chunk : ByteArray) : IO (Option ByteArray) := do
  session.state.atomically do
    let state ← get
    let output ← clientErr (Client.feed state chunk)
    set output.state
    unless output.wireBytes.isEmpty do
      discard <| session.outbound.send output.wireBytes
    if output.state.closed && output.plaintext.isEmpty then
      pure none
    else
      pure (some output.plaintext)

/-- Enqueue a close_notify (best effort). -/
def closeNotify (session : ClientSession) : IO Unit := do
  session.state.atomically do
    let state ← get
    match Client.closeNotify state with
    | .ok output =>
        set output.state
        discard <| session.outbound.send output.wireBytes
    | .error _ => pure ()

/--
Gracefully close the session, drain and join its exact writer task, then
half-close the socket. Repeated calls are safe.
-/
def close (session : ClientSession) : IO Unit := do
  session.closeNotify
  discard <| session.outbound.close.toBaseIO
  discard <| IO.wait session.writer
  try (session.socket.shutdown).block catch _ => pure ()

end ClientSession

namespace ServerSession

/-- Establish a TLS server session over an accepted socket (runs the handshake). -/
def establish (socket : TCP.Socket.Client) (config : Server.Config)
    (readSize : UInt64 := 16384) : Async ServerSession := do
  let state ← serverHandshake socket config readSize
  let outbound ← Std.CloseableChannel.new
  let stateMutex ← Std.Mutex.new state
  discard <| startWriter socket outbound
  pure { socket := socket, state := stateMutex, outbound := outbound }

/-- The ALPN protocol negotiated with the client, if any (e.g. "h2"). -/
def alpnSelected (session : ServerSession) : IO (Option String) :=
  session.state.atomically do pure (← get).alpnSelected

/-- The SNI host the client requested, if any. -/
def peerServerName (session : ServerSession) : IO (Option String) :=
  session.state.atomically do pure (← get).peerServerName

def send (session : ServerSession) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then return
  session.state.atomically do
    let state ← get
    let output ← serverErr (Server.sealApplication state bytes)
    set output.state
    discard <| session.outbound.send output.wireBytes

/-- Feed one raw transport chunk. Enqueues any TLS reply and returns decrypted
application bytes; `none` marks an authenticated close (EOF). -/
def feedInbound (session : ServerSession) (chunk : ByteArray) : IO (Option ByteArray) := do
  session.state.atomically do
    let state ← get
    let output ← serverErr (Server.feed state chunk)
    set output.state
    unless output.wireBytes.isEmpty do
      discard <| session.outbound.send output.wireBytes
    if output.state.closed && output.plaintext.isEmpty then
      pure none
    else
      pure (some output.plaintext)

/-- Receive and decrypt one non-empty application chunk (on-demand, no eager pump).
Loops over control-only records; `none` at EOF. Used by the HTTP/1.1 `Transport`. -/
partial def recvApp (session : ServerSession) (readSize : UInt64 := 16384) :
    IO (Option ByteArray) := do
  let raw? ← try (session.socket.recv? readSize).block catch _ => pure none
  match raw? with
  | none => pure none
  | some raw =>
      match ← session.feedInbound raw with
      | none => pure none
      | some plaintext =>
          if plaintext.isEmpty then recvApp session readSize else pure (some plaintext)

def closeNotify (session : ServerSession) : IO Unit := do
  session.state.atomically do
    let state ← get
    match Server.closeNotify state with
    | .ok output =>
        set output.state
        discard <| session.outbound.send output.wireBytes
    | .error _ => pure ()

end ServerSession

end Tls
end Grpc
