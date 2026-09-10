import Grpc

open Std.Async

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def failed (ack : IO.Promise (Except IO.Error Unit)) : IO Unit := do
  check (← IO.hasFinished ack.result?) "gRPC writer acknowledgement stranded"
  match ack.result?.get with
  | some (.error _) => pure ()
  | _ => throw (IO.userError "failed gRPC write acknowledged as success")

private partial def drainPeer (peer : TCP.Socket.Client) : Async Unit := do
  match ← peer.recv? 65536 with
  | none => pure ()
  | some _ => drainPeer peer

private def finishFixture (connection : Grpc.Client.Connection)
    (peer : TCP.Socket.Client) : IO Unit := do
  -- Bounded close may leave the intentionally stalled native send pending.
  -- Reading through FIN releases it before the test process exits.
  let draining ← Async.toIO (drainPeer peer)
  for _ in [:5000] do
    if (← IO.hasFinished draining) && (← Grpc.Client.backgroundTasksFinished connection) then break
    IO.sleep 1
  unless ← IO.hasFinished draining do
    IO.cancel draining
    throw (IO.userError "gRPC fixture peer did not reach EOF")
  (Async.ofAsyncTask draining).block
  check (← Grpc.Client.backgroundTasksFinished connection) "gRPC fixture retained background tasks"

private def actualClient (overflow : Bool) : IO Unit := do
  let listener ← TCP.Socket.Server.mk
  listener.bind (Grpc.Server.loopback 0)
  listener.listen 1
  let accepted ← Async.toIO listener.accept
  let connection ← Grpc.Client.connect {
    address := ← listener.getSockName
    writerLimits := { maxBytes := 32 * 1024 * 1024, maxItems := 2 } }
  let peer ← (Async.ofAsyncTask accepted).block
  let some preface ← (peer.recv? 4096).block | throw (IO.userError "gRPC preface missing")
  check (!preface.isEmpty) "empty gRPC preface"
  let .ok first ← Grpc.Client.TestSupport.enqueueAcknowledged connection
      ⟨Array.replicate (16 * 1024 * 1024) 42⟩ | throw (IO.userError "first gRPC write")
  let some _ ← (peer.recv? 1).block | throw (IO.userError "gRPC writer never sent")
  check (!(← IO.hasFinished first.result?)) "fixture did not stall native writer"
  let .ok second ← Grpc.Client.TestSupport.enqueueAcknowledged connection ⟨#[7]⟩
    | throw (IO.userError "second gRPC write")
  check ((← connection.writerBudget.snapshot).items == 2) "gRPC writer must charge in-flight item"
  if overflow then
    check (!(← Grpc.Client.TestSupport.enqueueAcknowledged connection ⟨#[8]⟩).isOk) "gRPC item overflow accepted"
  else (Grpc.Client.close connection).block
  failed first
  failed second
  check ((← Grpc.Client.TestSupport.pendingAcknowledgements connection) == 0) "gRPC completion registry retained tickets"
  let stats ← connection.writerBudget.snapshot
  check (stats.peakItems == 2 && stats.peakBytes ≤ 32 * 1024 * 1024) "gRPC writer exceeded limits"
  (Grpc.Client.close connection).block
  finishFixture connection peer
  try peer.shutdown.block catch _ => pure ()

def main : IO Unit := do
  for limits in #[({ maxBytes := 0 } : _root_.Http2.WriterLimits), { maxItems := 0 }] do
    let rejected ← try discard <| Grpc.Client.connect { writerLimits := limits }; pure false
      catch error => pure ((toString error).contains "writer bounds must be positive")
    check rejected "gRPC client invalid writer limits reached network"
    let rejected ← try discard <| Grpc.Server.serve Grpc.Registry.empty { writerLimits := limits }; pure false
      catch error => pure ((toString error).contains "writer bounds must be positive")
    check rejected "gRPC server invalid writer limits reached listener"
  actualClient true
  actualClient false
  IO.println "gRPC real writer saturation and acknowledgement tests passed"
