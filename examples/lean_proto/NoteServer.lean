import Grpc
import LeanProtoExample.note

namespace LeanProtoExampleServer

def service : _root_.lean.example.proto.NoteService := {
  handleEcho := fun note => do
    pure { note with title := note.title ++ " echoed" }
  handleSlow := fun note => do
    IO.sleep 20
    pure { note with title := note.title ++ " slow" }
  handleFail := fun _note => do
    throw (Grpc.Status.invalidArgument "invalid note from generated service")
  handleMeta := fun metaValue => do
    pure { metaValue with owner := metaValue.owner ++ " echoed" }
  handleList := fun note => do
    Grpc.MessageStream.ofArray #[
      { note with title := note.title ++ " one" },
      { note with title := note.title ++ " two" }
    ]
  handleCollect := fun noteStream => do
    let notes ← noteStream.collect
    let title := String.intercalate "," (notes.toList.map (fun note => note.title))
    let priority := notes.foldl (fun total note => total + note.priority) (0 : Int32)
    pure {
      title := title ++ " collected",
      priority := priority,
      tags := #["client-streaming"],
      counts := {},
      memo := none,
      color := .BLUE,
      details := none,
      «meta» := "collected"
    }
  handleChat := fun noteStream => do
    let notes ← noteStream.collect
    Grpc.MessageStream.ofArray <| notes.map fun note => { note with title := note.title ++ " chat" }
}

def registry : Grpc.Registry :=
  Grpc.Services.Reflection.registerWith
    { files := _root_.lean.example.proto.NoteService.fileDescriptors } <|
    _root_.lean.example.proto.NoteService.register Grpc.Registry.empty service

def portFromArgs (args : List String) : UInt16 :=
  match args with
  | port :: _ => UInt16.ofNat (port.toNat?.getD 50051)
  | [] => 50051

end LeanProtoExampleServer

def main (args : List String) : IO Unit := do
  let port := LeanProtoExampleServer.portFromArgs args
  let server ← Grpc.Server.serve LeanProtoExampleServer.registry {
    address := Grpc.Server.loopback port
  }
  IO.println s!"Lean gRPC h2c server listening on {server.localAddress}"
  (← IO.getStdout).flush
  Grpc.Server.wait server
