import Grpc
import Grpc.Services.StandardDescriptors
import ReflectionProto2.reflection_descriptor_proto2

open Grpc.Services.Reflection

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

def bytes (values : List UInt8) : ByteArray :=
  ByteArray.mk values.toArray

def descriptor (name : String) (payload : ByteArray)
    (symbols : Array String := #[]) (dependencies : Array String := #[])
    (extensions : Array ExtensionDescriptor := #[]) : FileDescriptor := {
  name
  symbols
  dependencies
  fileDescriptorProto := payload
  extensions
}

def testMerge : IO Unit := do
  let shared := descriptor "shared.proto" (bytes [1]) #["example.Shared"]
  let first := descriptor "first.proto" (bytes [2]) #[] #["shared.proto"]
  let second := descriptor "second.proto" (bytes [3]) #[] #["shared.proto"]
  let merged ← match mergeDescriptorSets #[#[first, shared], #[second, shared]] with
    | .ok files => pure files
    | .error error => throw (IO.userError error.message)
  expect (merged.map (fun file => file.name) == #["first.proto", "shared.proto", "second.proto"])
    "descriptor merge changed first-seen order or retained a shared import twice"

  match mergeDescriptorSets #[#[shared], #[{ shared with fileDescriptorProto := bytes [9] }]] with
  | .error (.conflictingFile "shared.proto") => pure ()
  | _ => throw (IO.userError "same-name conflicting descriptor was accepted")
  match mergeDescriptorSets #[#[shared], #[{ shared with symbols := #["example.Changed"] }]] with
  | .error (.conflictingFile "shared.proto") => pure ()
  | _ => throw (IO.userError "same-name conflicting descriptor metadata was accepted")

  let missing := descriptor "root.proto" (bytes [4]) #[] #["absent.proto"]
  match mergeDescriptorSets #[#[missing]] with
  | .error (.missingDependency "root.proto" "absent.proto") => pure ()
  | _ => throw (IO.userError "missing descriptor dependency was accepted")

  let symbolA := descriptor "a.proto" (bytes [5]) #["example.Duplicate"]
  let symbolB := descriptor "b.proto" (bytes [6]) #["example.Duplicate"]
  match mergeDescriptorSets #[#[symbolA, symbolB]] with
  | .error (.conflictingSymbol "example.Duplicate" "a.proto" "b.proto") => pure ()
  | _ => throw (IO.userError "cross-file duplicate symbol was accepted")

  let extension : ExtensionDescriptor := {
    containingType := "example.Message"
    extensionNumber := 100
  }
  let extensionA := descriptor "a.proto" (bytes [7]) #[] #[] #[extension]
  let extensionB := descriptor "b.proto" (bytes [8]) #[] #[] #[extension]
  match mergeDescriptorSets #[#[extensionA, extensionB]] with
  | .error (.conflictingExtension "example.Message" 100 "a.proto" "b.proto") => pure ()
  | _ => throw (IO.userError "cross-file duplicate extension was accepted")

def testStandardDescriptors : IO Unit := do
  let [health] := Grpc.Services.Health.fileDescriptors.toList
    | throw (IO.userError "health descriptor set shape changed")
  expect (health.name == "grpc/health/v1/health.proto") "wrong health descriptor filename"
  for symbol in #[
      "grpc.health.v1.Health",
      "grpc.health.v1.Health.Check",
      "grpc.health.v1.HealthCheckResponse.ServingStatus"] do
    expect (health.symbols.contains symbol) s!"health descriptor omitted {symbol}"

  let [reflection] := v1FileDescriptors.toList
    | throw (IO.userError "v1 reflection descriptor set shape changed")
  expect (reflection.name == "grpc/reflection/v1/reflection.proto")
    "wrong v1 reflection descriptor filename"
  for symbol in #[
      "grpc.reflection.v1.ServerReflection",
      "grpc.reflection.v1.ServerReflection.ServerReflectionInfo",
      "grpc.reflection.v1.ServerReflectionRequest"] do
    expect (reflection.symbols.contains symbol) s!"v1 descriptor omitted {symbol}"

def expectDescriptorResponse (response : Response) (expected : Array ByteArray) (message : String) :
    IO Unit := do
  match response.kind with
  | some (.fileDescriptorResponse files) =>
      expect (files.fileDescriptorProto == expected) message
  | _ => throw (IO.userError message)

def testProto2Descriptors : IO Unit := do
  let files := _root_.ReflectionProto2.FileDescriptors.reflection_descriptor_proto2_files
  let [root, base] := files.toList
    | throw (IO.userError "proto2 descriptor set shape changed")
  expect (root.dependencies == #["Test/reflection_descriptor_proto2_base.proto"])
    "proto2 root lost its imported descriptor"
  expect (base.symbols.contains "test.reflection.Extendee.State")
    "proto2 nested enum was not indexed"
  expect (root.extensions.contains {
      containingType := "test.reflection.Extendee"
      extensionNumber := 100
    }) "proto2 extension was not indexed"
  let config : Config := { files }
  expectDescriptorResponse (respond config {
      kind := some (.fileContainingSymbol "test.reflection.Extendee.State")
    }) #[base.fileDescriptorProto] "proto2 enum symbol did not resolve to its descriptor"
  expectDescriptorResponse (respond config {
      kind := some (.fileContainingExtension {
        containingType := "test.reflection.Extendee"
        extensionNumber := 100
      })
    }) #[root.fileDescriptorProto, base.fileDescriptorProto]
      "proto2 extension did not return its closed descriptor set"
  match (respond config {
      kind := some (.allExtensionNumbersOfType "test.reflection.Extendee")
    }).kind with
  | some (.allExtensionNumbersResponse numbers) =>
      expect (numbers.extensionNumber == #[100])
        "proto2 extension-number lookup returned the wrong numbers"
  | _ => throw (IO.userError "proto2 extension-number lookup returned the wrong response")

def main : IO Unit := do
  testMerge
  testStandardDescriptors
  testProto2Descriptors
