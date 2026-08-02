import Grpc
import Protobuf
import LeanProtoExample.note

open Protobuf Encoding

namespace LeanProtoExampleTest

def ofExcept {α} (e : Except ProtoError α) : IO α := do
  match e with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

def assert (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def assertEq [BEq α] (actual expected : α) (msg : String) : IO Unit := do
  assert (actual == expected) msg

def runGrpcM (action : Grpc.GrpcM α) : IO α := do
  match (← action.run) with
  | .ok value => pure value
  | .error status => throw (IO.userError status.messageD)

def testRoundTrip : IO Unit := do
  let counts := ({} : Std.HashMap String Int32)
    |>.insert "alpha" 3
    |>.insert "beta" 5
  let note : _root_.lean.example.proto.Note := {
    title := "lean proto",
    priority := 7,
    tags := #["bazel", "proto3"],
    counts := counts,
    memo := some "pure Lean codegen",
    color := .RED,
    details := some {
      owner := "roundtrip",
      created_at_unix := (1700000000 : Int64)
    },
    «meta» := "keyword field"
  }

  let encoded ← ofExcept (_root_.lean.example.proto.Note.encode note)
  let decoded ← ofExcept (_root_.lean.example.proto.Note.decode encoded)

  assertEq decoded.title "lean proto" "title did not round-trip"
  assertEq decoded.priority 7 "priority did not round-trip"
  assertEq decoded.tags #["bazel", "proto3"] "repeated string field did not round-trip"
  assertEq (decoded.counts.get? "alpha") (some 3) "map entry alpha did not round-trip"
  assertEq (decoded.counts.get? "beta") (some 5) "map entry beta did not round-trip"
  assertEq decoded.memo (some "pure Lean codegen") "optional string did not round-trip"
  assertEq decoded.color _root_.lean.example.proto.Color.RED "enum field did not round-trip"
  assertEq (decoded.details.map (fun details => details.owner)) (some "roundtrip")
    "imported message field did not round-trip"
  assertEq decoded.«meta» "keyword field"
    "Lean keyword-like proto field did not round-trip"

def testGeneratedService : IO Unit := do
  let service : _root_.lean.example.proto.NoteService := {
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
  let registry := _root_.lean.example.proto.NoteService.register Grpc.Registry.empty service
  let request : _root_.lean.example.proto.Note := {
    title := "lean proto",
    priority := 11,
    tags := #["grpc", "proto3"],
    counts := {},
    memo := none,
    color := .BLUE,
    details := some {
      owner := "generated-service",
      created_at_unix := (1700000100 : Int64)
    },
    «meta» := "service keyword field"
  }
  let requestData ← ofExcept (_root_.lean.example.proto.Note.encode request)
  let requestBody ← match (Grpc.Message.encode { data := requestData }) with
    | .ok body => pure body
    | .error status => throw (IO.userError status.messageD)
  let headers := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Echo"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let response ← runGrpcM (registry.dispatchUnary headers requestBody)
  let decoded ← ofExcept (_root_.lean.example.proto.Note.decode response.data)
  assertEq decoded.title "lean proto echoed" "generated service handler did not run"
  assertEq decoded.priority request.priority "generated service should preserve payload fields"
  assertEq (decoded.details.map (fun details => details.owner)) (some "generated-service")
    "generated service should preserve imported message fields"
  assertEq decoded.«meta» "service keyword field"
    "generated service should preserve Lean keyword-like proto fields"
  assertEq response.status.code Grpc.Code.ok "generated service response should be OK"

  let slowHeaders := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Slow"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
    |>.insert "grpc-timeout" "1m"
  let slowStatus ← match (← (registry.dispatchUnary slowHeaders requestBody).run) with
    | .ok _ => throw (IO.userError "generated slow service should exceed grpc-timeout")
    | .error status => pure status
  assertEq slowStatus.code Grpc.Code.deadlineExceeded
    "generated slow service should map grpc-timeout to DEADLINE_EXCEEDED"

  let failHeaders := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Fail"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let failStatus ← match (← (registry.dispatchUnary failHeaders requestBody).run) with
    | .ok _ => throw (IO.userError "generated failing service should return non-OK status")
    | .error status => pure status
  assertEq failStatus.code Grpc.Code.invalidArgument
    "generated failing service should preserve explicit handler status code"
  assertEq failStatus.message (some "invalid note from generated service")
    "generated failing service should preserve explicit handler status message"

  let metaHeaders := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Meta"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let metaRequest : _root_.lean.example.proto.NoteMeta := {
    owner := "imported-service-type",
    created_at_unix := (1700000200 : Int64)
  }
  let metaRequestData ← ofExcept (_root_.lean.example.proto.NoteMeta.encode metaRequest)
  let metaRequestBody ← match (Grpc.Message.encode { data := metaRequestData }) with
    | .ok body => pure body
    | .error status => throw (IO.userError status.messageD)
  let metaResponse ← runGrpcM (registry.dispatchUnary metaHeaders metaRequestBody)
  let metaDecoded ← ofExcept (_root_.lean.example.proto.NoteMeta.decode metaResponse.data)
  assertEq metaDecoded.owner "imported-service-type echoed"
    "generated service should dispatch RPCs whose input/output types come from imports"
  assertEq metaDecoded.created_at_unix metaRequest.created_at_unix
    "generated imported service types should preserve int64 fields"
  assertEq metaResponse.status.code Grpc.Code.ok
    "generated imported-type unary response should be OK"

  let streamHeaders := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/List"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let streamResponse ← runGrpcM (registry.dispatchServerStreaming streamHeaders requestBody)
  assertEq streamResponse.messages.size 2 "generated server-streaming handler should emit two messages"
  let first ← ofExcept (_root_.lean.example.proto.Note.decode streamResponse.messages[0]!)
  let second ← ofExcept (_root_.lean.example.proto.Note.decode streamResponse.messages[1]!)
  assertEq first.title "lean proto one" "first generated server-streaming response did not decode"
  assertEq second.title "lean proto two" "second generated server-streaming response did not decode"
  assertEq streamResponse.status.code Grpc.Code.ok "generated server-streaming response should be OK"

  let collectHeaders := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Collect"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let request2 : _root_.lean.example.proto.Note := { request with title := "second", priority := 13 }
  let request2Data ← ofExcept (_root_.lean.example.proto.Note.encode request2)
  let request2Body ← match (Grpc.Message.encode { data := request2Data }) with
    | .ok body => pure body
    | .error status => throw (IO.userError status.messageD)
  let collectResponse ← runGrpcM (registry.dispatchClientStreaming collectHeaders (requestBody.append request2Body))
  let collected ← ofExcept (_root_.lean.example.proto.Note.decode collectResponse.data)
  assertEq collected.title "lean proto,second collected" "generated client-streaming response title mismatch"
  assertEq collected.priority (24 : Int32) "generated client-streaming response should aggregate priority"
  assertEq collectResponse.status.code Grpc.Code.ok "generated client-streaming response should be OK"

  let chatHeaders := Grpc.Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":path" "/lean.example.proto.NoteService/Chat"
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"
  let chatResponse ← runGrpcM (registry.dispatchBidirectionalStreaming chatHeaders (requestBody.append request2Body))
  assertEq chatResponse.messages.size 2 "generated bidirectional-streaming handler should emit two messages"
  let chatFirst ← ofExcept (_root_.lean.example.proto.Note.decode chatResponse.messages[0]!)
  let chatSecond ← ofExcept (_root_.lean.example.proto.Note.decode chatResponse.messages[1]!)
  assertEq chatFirst.title "lean proto chat" "first generated bidirectional-streaming response did not decode"
  assertEq chatSecond.title "second chat" "second generated bidirectional-streaming response did not decode"
  assertEq chatResponse.status.code Grpc.Code.ok "generated bidirectional-streaming response should be OK"

end LeanProtoExampleTest

def main : IO Unit := do
  LeanProtoExampleTest.testRoundTrip
  LeanProtoExampleTest.testGeneratedService
