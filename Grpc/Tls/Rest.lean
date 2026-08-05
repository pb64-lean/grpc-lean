module

public import Std.Async.TCP
public import Std.Async.Timer
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

/-- The phase in which one REST connection encountered a connection-local
failure.  These failures do not stop the accept loop or make `wait` fail: a
hostile or abruptly disconnected peer is local to its connection.  They are
retained in a bounded log so failures after an asynchronous TLS enqueue are not
mistaken for successful delivery. -/
inductive ConnectionFailureStage where
  | handshake
  | request
  | handler
  | responseSend
  | recordWriter
  | connectionTask
  deriving Inhabited, Repr, BEq

/-- One observable connection-local failure. -/
structure ConnectionFailure where
  connectionId : Nat
  stage : ConnectionFailureStage
  message : String
  deriving Inhabited, Repr

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
    (shutdownToken : Std.CancellationToken)
    (reportFailure : ConnectionFailureStage → String → IO Unit)
    (buffered : ByteArray) : Async Unit := do
  match parseHead buffered with
  | .error message =>
      reportFailure .request message
  | .ok none =>
      -- Head incomplete; read more.
      match ← session.recvApp (stopToken := some shutdownToken) with
      | none =>
          unless ← shutdownToken.isCancelled do
            reportFailure .request "peer closed before completing the request head"
      | some more =>
          serveOneRequest session handler shutdownToken reportFailure (buffered.append more)
  | .ok (some (request, contentLength, bodyStart)) =>
      let mut body := buffered.extract bodyStart buffered.size
      -- Read until the declared body is complete.
      let mut open? := true
      while body.size < contentLength && open? do
        match ← session.recvApp (stopToken := some shutdownToken) with
        | none => open? := false
        | some more => body := body.append more
      -- EOF before the declared body length is a truncated request, not a
      -- shorter valid body.  It must never reach the application handler.
      if body.size < contentLength then
        unless ← shutdownToken.isCancelled do
          reportFailure .request
            s!"peer closed after {body.size} of {contentLength} request-body bytes"
      else
        -- Do not start new application work once shutdown has won a request read.
        -- A handler already running is allowed to complete its one response; its
        -- owning connection task remains visible to `wait` and is bounded there.
        unless ← shutdownToken.isCancelled do
          let request := { request with body := body.extract 0 contentLength }
          let response ← try handler request
            catch err =>
              reportFailure .handler (toString err)
              pure { status := 500, reason := "Internal Server Error", json := "{\"error\":\"handler failed\"}" }
          try
            session.send (encodeResponse response)
          catch err =>
            reportFailure .responseSend (toString err)

/-- Static TLS identity for the REST server. -/
structure Config where
  certificateChain : Array ByteArray
  signingKey : ByteArray
  readSize : UInt64 := 16384
  noDelay : Bool := true

private structure ConnectionTask where
  id : Nat
  client : TCP.Socket.Client
  task : AsyncTask Unit

/-- A running REST-over-TLS server.  The private task handles are exact owners:
`wait` can observe the accept loop and every accepted connection rather than
leaving either kind of task detached. -/
structure Server where
  socket : TCP.Socket.Server
  localAddress : SocketAddress
  shutdownToken : Std.CancellationToken
  private acceptTask : AsyncTask Unit
  private connectionTasks : Std.Mutex (Array ConnectionTask)
  private failureLog : Std.Mutex (Array ConnectionFailure)

/-- Keep observability bounded for a long-lived endpoint under hostile traffic. -/
private def maxConnectionFailures : Nat := 64

private def recordConnectionFailure (failures : Std.Mutex (Array ConnectionFailure))
    (failure : ConnectionFailure) : IO Unit := do
  failures.atomically do
    let failures := (← get).push failure
    let excess := failures.size - maxConnectionFailures
    set (failures.extract excess failures.size)

/-- The last (at most) 64 connection-local failures, oldest first.  These are
diagnostic records rather than server-fatal errors: malformed peers, handler
exceptions, and transport failures remain scoped to their accepted connection. -/
def connectionFailures (server : Server) : IO (Array ConnectionFailure) :=
  server.failureLog.atomically get

/-- Number of accepted connection owners currently retained by the server.
After `wait` returns successfully this is zero, including after forced timeout
retirement. -/
def activeConnectionCount (server : Server) : IO Nat := do
  pure (← server.connectionTasks.atomically get).size

/-- Bound the write-side shutdown.  The current `Std.Async.TCP` API has no
full socket close, so a peer that stops reading can otherwise leave
`uv_shutdown` pending indefinitely. -/
private def closeFlushTimeoutMs : Nat := 200

private def shutdownSocket (client : TCP.Socket.Client) : Async Unit := do
  try
    Async.race
      client.shutdown
      (Std.Async.sleep (Std.Time.Millisecond.Offset.ofNat closeFlushTimeoutMs))
  catch _ =>
    pure ()

/-- Finish a one-request REST session in wire order: application response,
TLS `close_notify`, bounded writer drain, then transport half-close. The normal
path delivers the coalesced response/alert before EOF; a non-reading peer cannot
hold teardown open indefinitely. -/
private def retireSession (session : ServerSession)
    (reportFailure : ConnectionFailureStage → String → IO Unit) : Async Unit := do
  try session.closeNotify catch _ => pure ()
  try
    session.drainWriter
  catch err =>
    reportFailure .recordWriter (toString err)
  -- `ServerSession.send` only enqueues sealed bytes.  A later socket error is
  -- stored by the exact record-writer task, so inspect it after the drain before
  -- declaring this connection complete.
  match ← session.writerFailure? with
  | none => pure ()
  | some err => reportFailure .recordWriter (toString err)
  shutdownSocket session.socket

private def serveRestConnection (connectionId : Nat) (handler : Handler) (config : Config)
    (shutdownToken : Std.CancellationToken)
    (failures : Std.Mutex (Array ConnectionFailure))
    (client : TCP.Socket.Client) : Async Unit := do
  let reportFailure (stage : ConnectionFailureStage) (message : String) : IO Unit :=
    recordConnectionFailure failures { connectionId, stage, message }
  let established : Except IO.Error ServerSession ← try
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
      Except.ok <$> ServerSession.establish client serverConfig config.readSize
        (stopToken := some shutdownToken)
    catch err =>
      pure (Except.error err)
  match established with
  | Except.error err =>
      -- Cancellation during server shutdown is expected; a peer or handshake
      -- failure while serving remains observable and connection-local.
      unless ← shutdownToken.isCancelled do
        reportFailure .handshake (toString err)
      shutdownSocket client
  | Except.ok session =>
      -- Cleanup is deliberately outside request processing so every exit after
      -- a successful handshake closes the record queue and retires the socket.
      try
        serveOneRequest session handler shutdownToken reportFailure ByteArray.empty
      catch err =>
        unless ← shutdownToken.isCancelled do
          reportFailure .request (toString err)
      retireSession session reportFailure

private inductive AcceptEvent where
  | accepted (client : TCP.Socket.Client)
  | shutdown

private def retainConnectionTask (tasks : Std.Mutex (Array ConnectionTask))
    (owner : ConnectionTask) : IO Unit :=
  tasks.atomically do modify fun owners => owners.push owner

/-- Reap completed owners during normal serving so a long-lived REST server's
ownership registry is proportional to live connections, not historical traffic. -/
private def pruneFinishedConnectionTasks (tasks : Std.Mutex (Array ConnectionTask))
    (failures : Std.Mutex (Array ConnectionFailure)) : IO Unit := do
  let owners ← tasks.atomically get
  let mut finishedIds : Array Nat := #[]
  for owner in owners do
    if ← IO.hasFinished owner.task then
      match owner.task.get with
      | .ok () => pure ()
      | .error err =>
          recordConnectionFailure failures {
            connectionId := owner.id
            stage := .connectionTask
            message := toString err
          }
      finishedIds := finishedIds.push owner.id
  unless finishedIds.isEmpty do
    tasks.atomically do
      modify fun owners => owners.filter fun owner => !(finishedIds.contains owner.id)

private def spawnRestConnection (handler : Handler) (config : Config)
    (shutdownToken : Std.CancellationToken) (tasks : Std.Mutex (Array ConnectionTask))
    (failures : Std.Mutex (Array ConnectionFailure))
    (nextConnectionId : IO.Ref Nat) (client : TCP.Socket.Client) : IO Unit := do
  let id ← nextConnectionId.get
  nextConnectionId.set (id + 1)
  let task ← Async.toIO
    (serveRestConnection id handler config shutdownToken failures client)
  retainConnectionTask tasks { id := id, client := client, task := task }
  pruneFinishedConnectionTasks tasks failures

private partial def acceptLoop (socket : TCP.Socket.Server) (handler : Handler)
    (config : Config) (token : Std.CancellationToken)
    (tasks : Std.Mutex (Array ConnectionTask))
    (failures : Std.Mutex (Array ConnectionFailure))
    (nextConnectionId : IO.Ref Nat) : Async Unit := do
  let event ← Selectable.one #[
    Selectable.case socket.acceptSelector fun client => pure (AcceptEvent.accepted client),
    Selectable.case token.selector fun _ => pure AcceptEvent.shutdown
  ]
  match event with
  | AcceptEvent.shutdown => pure ()
  | AcceptEvent.accepted client =>
      -- Accept and shutdown can become ready together.  Do not publish a new
      -- connection after shutdown has won; retire the accepted socket instead.
      if ← token.isCancelled then
        shutdownSocket client
      else
        spawnRestConnection handler config token tasks failures nextConnectionId client
        acceptLoop socket handler config token tasks failures nextConnectionId

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
  let connectionTasks ← Std.Mutex.new (#[] : Array ConnectionTask)
  let failureLog ← Std.Mutex.new (#[] : Array ConnectionFailure)
  let nextConnectionId ← IO.mkRef 0
  let acceptTask ← Async.toIO
    (acceptLoop socket handler config token connectionTasks failureLog nextConnectionId)
  pure {
    socket := socket,
    localAddress := localAddress,
    shutdownToken := token,
    acceptTask := acceptTask,
    connectionTasks := connectionTasks,
    failureLog := failureLog
  }

def shutdown (server : Server) : IO Unit :=
  server.shutdownToken.cancel (reason := Std.CancellationReason.shutdown)

private def ownedTasksFinished (server : Server) : IO Bool := do
  if !(← IO.hasFinished server.acceptTask) then
    return false
  let owners ← server.connectionTasks.atomically get
  for owner in owners do
    if !(← IO.hasFinished owner.task) then
      return false
  pure true

private partial def waitOwnedTasks (server : Server) (remainingMs : Option Nat) : IO Bool := do
  if ← ownedTasksFinished server then
    pure true
  else
    match remainingMs with
    | some 0 => pure false
    | _ =>
        IO.sleep 1
        waitOwnedTasks server (remainingMs.map (· - 1))

private def takeConnectionTasks (server : Server) : IO (Array ConnectionTask) := do
  server.connectionTasks.atomically do
    let owners ← get
    set (#[] : Array ConnectionTask)
    pure owners

private def joinConnectionOwner (server : Server) (owner : ConnectionTask)
    (recordTaskError : Bool := true) : IO Bool := do
  if !(← IO.hasFinished owner.task) then
    return false
  match owner.task.get with
  | .ok () => pure ()
  | .error err =>
      if recordTaskError then
        recordConnectionFailure server.failureLog {
          connectionId := owner.id
          stage := .connectionTask
          message := toString err
        }
  pure true

private def joinFinishedOwners (server : Server) : IO (Option IO.Error) := do
  -- `ownedTasksFinished` established these gets are non-blocking. Taking the
  -- registry transfers ownership locally and clears every retained client/task
  -- before this function returns.
  let acceptError? := match server.acceptTask.get with
    | .ok () => none
    | .error err => some err
  let owners ← takeConnectionTasks server
  for owner in owners do
    discard <| joinConnectionOwner server owner
  pure acceptError?

private def taskSetFinished (acceptTask : AsyncTask Unit)
    (owners : Array ConnectionTask) : IO Bool := do
  if !(← IO.hasFinished acceptTask) then
    return false
  for owner in owners do
    if !(← IO.hasFinished owner.task) then
      return false
  pure true

private def waitCancelledOwners (acceptTask : AsyncTask Unit)
    (owners : Array ConnectionTask) : IO Bool := do
  for _ in [0:closeFlushTimeoutMs + 1] do
    if ← taskSetFinished acceptTask owners then
      return true
    IO.sleep 1
  pure false

private def forceRetireOwners (server : Server) : IO (Option IO.Error) := do
  let acceptWasFinished ← IO.hasFinished server.acceptTask
  let preexistingAcceptError? := if acceptWasFinished then
      match server.acceptTask.get with
      | .ok () => none
      | .error err => some err
    else
      none
  IO.cancel server.acceptTask
  -- The sticky shutdown token prevents the accept loop from publishing after
  -- shutdown wins. Give an accept that was already between selection and its
  -- token re-check a bounded opportunity to close that publication fence.
  for _ in [0:closeFlushTimeoutMs + 1] do
    if ← IO.hasFinished server.acceptTask then break
    IO.sleep 1
  -- Only a joined accept owner closes publication. If it misses this bound we
  -- still retire the owners currently visible, but return an ownership error;
  -- any exceptionally late publication remains in the registry rather than
  -- being silently orphaned.
  let acceptFenceClosed ← IO.hasFinished server.acceptTask
  let owners ← takeConnectionTasks server
  let mut cancelledOwners : Array ConnectionTask := #[]
  let mut retireTasks : Array (AsyncTask Unit) := #[]
  for owner in owners do
    if ← IO.hasFinished owner.task then
      discard <| joinConnectionOwner server owner
    else
      IO.cancel owner.task
      cancelledOwners := cancelledOwners.push owner
      retireTasks := retireTasks.push (← Async.toIO (shutdownSocket owner.client))
  -- All bounded shutdowns start before the bounded exact-owner join. They are
  -- retained and joined below, so forced retirement creates no detached cleanup.
  discard <| waitCancelledOwners server.acceptTask cancelledOwners
  for task in retireTasks do
    discard <| IO.wait task
  let mut everyOwnerJoined := true
  let mut unfinishedOwners : Array ConnectionTask := #[]
  for owner in cancelledOwners do
    -- An error caused by the deliberate force-path cancellation is not a
    -- connection failure. Genuine errors from owners already complete before
    -- cancellation were recorded in the loop above.
    unless ← joinConnectionOwner server owner (recordTaskError := false) do
      everyOwnerJoined := false
      unfinishedOwners := unfinishedOwners.push owner
  unless unfinishedOwners.isEmpty do
    -- Never turn an uncooperative user handler into an untracked task. Preserve
    -- exact ownership for a later `wait`/diagnostic even though this wait reports
    -- that its bounded cancellation contract could not be met.
    server.connectionTasks.atomically do
      modify fun retained => retained ++ unfinishedOwners
  if !acceptFenceClosed || !everyOwnerJoined then
    pure (some (IO.userError
      "REST shutdown could not join every cancelled task within the retirement bound"))
  else
    -- Like cancelled connection owners, an error produced only after our
    -- deliberate accept-task cancellation is expected force-path control flow.
    pure preexistingAcceptError?

/-- Initiate shutdown (idempotently), then join the accept loop and every
accepted connection.  The default deadline bounds the whole cooperative drain;
at expiry, remaining task owners are cancelled and all retained sockets begin a
bounded write-side shutdown concurrently.  Passing `none` deliberately requests
an unbounded graceful wait. `IO.cancel` is cooperative: if user code ignores
cancellation past the forced-join bound, `wait` throws and retains that exact
owner so a later `wait` can still observe it rather than orphaning the task. -/
def wait (server : Server) (drainTimeoutMs : Option Nat := some 30000) : IO Unit := do
  shutdown server
  let error? ← if ← waitOwnedTasks server drainTimeoutMs then
    joinFinishedOwners server
  else
    forceRetireOwners server
  match error? with
  | none => pure ()
  | some err => throw err

end Rest
end Tls
end Grpc
