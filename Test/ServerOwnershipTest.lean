import Std.Async.TCP

import Grpc

open Grpc

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

partial def waitUntil (message : String) (remainingMs : Nat) (check : IO Bool) : IO Unit := do
  if ← check then
    pure ()
  else if remainingMs == 0 then
    throw (IO.userError message)
  else
    IO.sleep 1
    waitUntil message (remainingMs - 1) check

def ownedConnectionCount (server : Http2.Server.Server) : IO Nat := do
  match server.connectionTasks with
  | none => pure 0
  | some tasksMutex => tasksMutex.atomically do pure (← get).size

def activeConnectionCount (server : Http2.Server.Server) : IO Nat := do
  match server.activeConnections with
  | none => pure 0
  | some connectionsMutex => connectionsMutex.atomically do pure (← get).size

def receiveServerPreface (client : Std.Async.TCP.Socket.Client) : IO Unit := do
  match ← (client.recv? 1024).block with
  | some bytes =>
      expect (!bytes.isEmpty) "managed server emitted an empty HTTP/2 preface"
  | none =>
      throw (IO.userError "managed server closed before its HTTP/2 preface")

def main : IO Unit := do
  let connectionCount := 64
  let server ← Grpc.Server.serve Registry.empty
    { address := Grpc.Server.loopback 0 }
  let mut clients := #[]
  for _ in [0:connectionCount] do
    let client ← Std.Async.TCP.Socket.Client.mk
    (client.connect server.localAddress).block
    clients := clients.push client

  waitUntil "accept loop did not publish every accepted connection owner" 2000 do
    pure ((← ownedConnectionCount server) == connectionCount)
  waitUntil "accepted connections were not registered before their tasks started" 2000 do
    pure ((← activeConnectionCount server) == connectionCount)

  let receiveTask ← IO.asTask do
    for client in clients do
      receiveServerPreface client
    pure (some ())
  let timeoutTask ← IO.asTask do
    IO.sleep 2000
    pure (none : Option Unit)
  match ← IO.waitAny [receiveTask, timeoutTask] with
  | .error err => throw err
  | .ok (some ()) => IO.cancel timeoutTask
  | .ok none =>
      IO.cancel receiveTask
      throw (IO.userError "retained connections did not emit their HTTP/2 prefaces")

  let mut shutdownTasks := #[]
  for _ in [0:32] do
    shutdownTasks := shutdownTasks.push (← IO.asTask (Grpc.Server.shutdown server))
  for task in shutdownTasks do
    match task.get with
    | .ok () => pure ()
    | .error err => throw err
  Http2.Server.wait server (drainTimeoutMs := some 2000)
  expect ((← ownedConnectionCount server) == 0)
    "server wait returned with retained connection task owners"
  expect ((← activeConnectionCount server) == 0)
    "server wait returned with active connections"

  for client in clients do
    try
      (client.shutdown).block
    catch _ =>
      pure ()
