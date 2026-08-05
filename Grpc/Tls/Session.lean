module

public import Std.Async.TCP
public import Std.Async.Timer
public import Std.Sync.Mutex
public import Std.Sync.Channel
public import Grpc.CancellationToken
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

private inductive ServerHandshakeEvent where
  | received (chunk? : Option ByteArray)
  | stop

private inductive ServerHandshakeSendEvent where
  | sent
  | stop

/-- Adapt an exact `AsyncTask` handle to `Selectable.one`.  The completion mapper
left after another selector wins contains only the inert waiter race — no TLS
state-machine or cleanup continuation. It cannot cancel libuv's pending write
because Lean's TCP API exposes no cancel-send/full-close operation. -/
private def asyncTaskSelector (task : AsyncTask α) : Selector α := {
  tryFn := do
    if ← IO.hasFinished task then
      some <$> Async.ofAsyncTask task
    else
      pure none
  registerFn := fun waiter => do
    discard <| IO.mapTask (t := task) (sync := true) fun result =>
      waiter.race (pure ()) fun promise => promise.resolve result
  unregisterFn := pure ()
}

private def handshakeSendRetireTimeoutMs : Nat := 200

/-- Cancel the exact Lean task and give it a bounded opportunity to observe
completion.  `IO.cancel` is cooperative, so a libuv send already in flight may
remain as a native promise until the peer reads or the OS fails it; critically,
no TLS state-machine or cleanup continuation remains attached to that promise. -/
private def cancelAndRetireHandshakeSend (task : AsyncTask Unit) : Async Unit := do
  IO.cancel task
  let mut finished ← IO.hasFinished task
  for _ in [0:handshakeSendRetireTimeoutMs] do
    if finished then break
    Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 1)
    finished ← IO.hasFinished task
  if finished then
    try Async.ofAsyncTask task catch _ => pure ()

/-- A server handshake write that is lifecycle-aware.  The exact send task is
retained while its completion races the sticky server stop token.  On shutdown
the handshake owner returns after a bounded retirement attempt instead of being
held forever by a client that sent ClientHello but never reads the server flight. -/
private def sendServerHandshakeBytes (socket : TCP.Socket.Client) (bytes : ByteArray)
    (stopToken : Option Std.CancellationToken) : Async Unit := do
  match stopToken with
  | none => socket.send bytes
  | some token =>
      let task ← Async.toIO (socket.send bytes)
      let event ← Selectable.one #[
        Selectable.case (asyncTaskSelector task) fun _ =>
          pure ServerHandshakeSendEvent.sent,
        Selectable.case token.selector fun _ =>
          pure ServerHandshakeSendEvent.stop
      ]
      match event with
      | .sent => pure ()
      | .stop =>
          cancelAndRetireHandshakeSend task
          throw (IO.userError "TLS server handshake send cancelled")

private def nextServerHandshakeEvent (socket : TCP.Socket.Client) (readSize : UInt64)
    (stopToken : Option Std.CancellationToken) : Async ServerHandshakeEvent :=
  match stopToken with
  | none => ServerHandshakeEvent.received <$> socket.recv? readSize
  | some token =>
      Selectable.one #[
        Selectable.case (socket.recvSelector readSize) fun chunk? =>
          pure (ServerHandshakeEvent.received chunk?),
        Selectable.case token.selector fun _ => pure ServerHandshakeEvent.stop
      ]

/-- Drive a server handshake to completion over `socket` (cooperatively — see
`clientHandshakeLoop`). Waits for ClientHello, emits the server flight, then
consumes the client Finished. An optional server lifecycle token makes a silent
pre-handshake peer observable and cancellable during shutdown. -/
private partial def serverHandshakeLoop (socket : TCP.Socket.Client) (readSize : UInt64)
    (state : Server.State) (stopToken : Option Std.CancellationToken) : Async Server.State := do
  if state.connected then
    pure state
  else
    let chunk ← match ← nextServerHandshakeEvent socket readSize stopToken with
      | .stop => throw (IO.userError "TLS server handshake cancelled")
      | .received none =>
          throw (IO.userError "peer closed the connection during the TLS handshake")
      | .received (some chunk) => pure chunk
    let output ← serverErr (Server.feed state chunk)
    unless output.wireBytes.isEmpty do
      sendServerHandshakeBytes socket output.wireBytes stopToken
    serverHandshakeLoop socket readSize output.state stopToken

def serverHandshake (socket : TCP.Socket.Client) (config : Server.Config)
    (readSize : UInt64 := 16384) (stopToken : Option Std.CancellationToken := none) :
    Async Server.State :=
  serverHandshakeLoop socket readSize (Server.start config) stopToken

/-! ## Sessions. -/

private structure RecordWriter where
  task : AsyncTask Unit
  failure : IO.Ref (Option IO.Error)
  failureToken : Std.CancellationToken

structure ClientSession where
  socket : TCP.Socket.Client
  state : Std.Mutex Client.State
  /-- Sealed record bytes awaiting the socket, drained in FIFO order by the writer
  task so the state lock is never held across a blocking socket write. -/
  outbound : Std.CloseableChannel ByteArray
  /-- Exact writer handle, awaited by `close` after the outbound queue drains;
  cancelled if its bounded drain deadline expires. -/
  private writer : RecordWriter

structure ServerSession where
  socket : TCP.Socket.Client
  state : Std.Mutex Server.State
  outbound : Std.CloseableChannel ByteArray
  /-- Exact writer handle, awaited by `drainWriter` so everything already sealed
  reaches the socket before retirement, subject to the bounded drain deadline. -/
  private writer : RecordWriter

/-- The single writer loop: drains sealed record bytes and writes them to the
socket in FIFO order, awaiting each send *cooperatively* (never parking a worker
thread — a blocking `.block` here would exhaust the pool when many TLS
connections write at once, deadlocking readers). -/
private partial def writerLoop (socket : TCP.Socket.Client)
    (outbound : Std.CloseableChannel ByteArray) (failure : IO.Ref (Option IO.Error))
    (failureToken : Std.CancellationToken) : Async Unit := do
  match ← await (← outbound.recv) with
  | none => pure ()
  | some bytes =>
      try
        socket.send bytes
        writerLoop socket outbound failure failureToken
      catch err =>
        failure.set (some err)
        discard <| outbound.close.toBaseIO
        discard <| Grpc.CancellationToken.cancel failureToken
          (reason := Std.CancellationReason.shutdown)

private def startWriter (socket : TCP.Socket.Client)
    (outbound : Std.CloseableChannel ByteArray) : IO RecordWriter := do
  let failure ← IO.mkRef (none : Option IO.Error)
  let failureToken ← Std.CancellationToken.new
  let task ← Async.toIO (writerLoop socket outbound failure failureToken)
  pure { task := task, failure := failure, failureToken := failureToken }

private def enqueueRecord (writer : RecordWriter) (outbound : Std.CloseableChannel ByteArray)
    (bytes : ByteArray) : IO Unit := do
  let sent ← (Std.CloseableChannel.Sync.send outbound bytes).toBaseIO
  match sent with
  | .ok () => pure ()
  | .error _ =>
    match ← writer.failure.get with
    | some err => throw err
    | none => throw (IO.userError "TLS record writer is closed")

private def drainRecordWriter (writer : RecordWriter)
    (outbound : Std.CloseableChannel ByteArray) : Async Unit := do
  discard <| outbound.close.toBaseIO
  let drained ← Async.race
    (do
      try Async.ofAsyncTask writer.task catch _ => pure ()
      pure true)
    (do
      Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 200)
      pure false)
  unless drained do
    IO.cancel writer.task

private def shutdownSocket (socket : TCP.Socket.Client) : Async Unit := do
  try
    Async.race
      socket.shutdown
      (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat 200))
  catch _ =>
    pure ()

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

/-- Resolves exactly when the client record writer's socket send fails. -/
def writerFailureSelector (session : ClientSession) : Std.Async.Selector Unit :=
  session.writer.failureToken.selector

/-- The socket error that stopped the client record writer, if any. -/
def writerFailure? (session : ClientSession) : IO (Option IO.Error) :=
  session.writer.failure.get

/-- Seal application bytes and enqueue the record for the writer task. Sealing
(sequence advance) is atomic under the lock; the socket write is lock-free. -/
def send (session : ClientSession) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then return
  session.state.atomically do
    let state ← get
    let output ← clientErr (Client.sealApplication state bytes)
    set output.state
    enqueueRecord session.writer session.outbound output.wireBytes

/-- Feed one raw transport chunk. Enqueues any TLS reply (KeyUpdate response,
close_notify) and returns decrypted application bytes; `none` marks an
authenticated close_notify (EOF). -/
def feedInbound (session : ClientSession) (chunk : ByteArray) : IO (Option ByteArray) := do
  session.state.atomically do
    let state ← get
    let output ← clientErr (Client.feed state chunk)
    set output.state
    unless output.wireBytes.isEmpty do
      enqueueRecord session.writer session.outbound output.wireBytes
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
        enqueueRecord session.writer session.outbound output.wireBytes
    | .error _ => pure ()

/-- Gracefully close the session without parking a worker: enqueue close_notify,
bound the record-writer drain, then bound the socket write-side shutdown.
Repeated calls are safe. -/
def close (session : ClientSession) : Async Unit := do
  try session.closeNotify catch _ => pure ()
  drainRecordWriter session.writer session.outbound
  shutdownSocket session.socket

end ClientSession

namespace ServerSession

/-- Establish a TLS server session over an accepted socket (runs the handshake). -/
def establish (socket : TCP.Socket.Client) (config : Server.Config)
    (readSize : UInt64 := 16384) (stopToken : Option Std.CancellationToken := none) :
    Async ServerSession := do
  let state ← serverHandshake socket config readSize stopToken
  let outbound ← Std.CloseableChannel.new
  let stateMutex ← Std.Mutex.new state
  let writer ← startWriter socket outbound
  pure { socket := socket, state := stateMutex, outbound := outbound, writer := writer }

/-- The ALPN protocol negotiated with the client, if any (e.g. "h2"). -/
def alpnSelected (session : ServerSession) : IO (Option String) :=
  session.state.atomically do pure (← get).alpnSelected

/-- The SNI host the client requested, if any. -/
def peerServerName (session : ServerSession) : IO (Option String) :=
  session.state.atomically do pure (← get).peerServerName

/-- Resolves exactly when the record writer's socket send fails. -/
def writerFailureSelector (session : ServerSession) : Std.Async.Selector Unit :=
  session.writer.failureToken.selector

/-- The socket error that stopped the record writer, if any. -/
def writerFailure? (session : ServerSession) : IO (Option IO.Error) :=
  session.writer.failure.get

def send (session : ServerSession) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then return
  session.state.atomically do
    let state ← get
    let output ← serverErr (Server.sealApplication state bytes)
    set output.state
    enqueueRecord session.writer session.outbound output.wireBytes

/-- Feed one raw transport chunk. Enqueues any TLS reply and returns decrypted
application bytes; `none` marks an authenticated close (EOF). -/
def feedInbound (session : ServerSession) (chunk : ByteArray) : IO (Option ByteArray) := do
  session.state.atomically do
    let state ← get
    let output ← serverErr (Server.feed state chunk)
    set output.state
    unless output.wireBytes.isEmpty do
      enqueueRecord session.writer session.outbound output.wireBytes
    if output.state.closed && output.plaintext.isEmpty then
      pure none
    else
      pure (some output.plaintext)

/-- Receive and decrypt one non-empty application chunk (on-demand, no eager pump).
Loops over control-only records; `none` at EOF. Used by the HTTP/1.1 `Transport`. -/
partial def recvApp (session : ServerSession) (readSize : UInt64 := 16384)
    (stopToken : Option Std.CancellationToken := none) : Async (Option ByteArray) := do
  let raw? ← try
      match stopToken with
      | none => session.socket.recv? readSize
      | some token =>
          Selectable.one #[
            Selectable.case (session.socket.recvSelector readSize) pure,
            Selectable.case token.selector fun _ => pure none
          ]
    catch _ => pure none
  match raw? with
  | none => pure none
  | some raw =>
      match ← session.feedInbound raw with
      | none => pure none
      | some plaintext =>
          if plaintext.isEmpty then recvApp session readSize stopToken else pure (some plaintext)

def closeNotify (session : ServerSession) : IO Unit := do
  session.state.atomically do
    let state ← get
    match Server.closeNotify state with
    | .ok output =>
        set output.state
        enqueueRecord session.writer session.outbound output.wireBytes
    | .error _ => pure ()

/-- Close the record queue and cooperatively await its exact writer. The normal
path preserves wire order through the last sealed record (GOAWAY/close_notify);
after 200 ms a stalled writer is cancelled so a non-reading peer cannot make
server teardown unbounded. No worker is parked in either path. -/
def drainWriter (session : ServerSession) : Async Unit := do
  drainRecordWriter session.writer session.outbound

end ServerSession

end Tls
end Grpc
