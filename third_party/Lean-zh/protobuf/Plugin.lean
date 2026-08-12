module

import Protobuf.Encoding
import Protobuf.Base64
import Protobuf.Internal.Desc
meta import Protobuf.Notation
meta import Protobuf.Elab
import Protobuf.Notation.Syntax
import Protobuf.Versions

open Protobuf Encoding Notation
open Lean

section

-- we use internal representation from `Protobuf.Internal.Desc`
-- NOTE: the internal representation is not perfect aligned with proto2 semantics
--    but I believe `protoc` will recognize the encoded result.
#load_proto_file "proto/google/protobuf/compiler/plugin.proto" in "proto"

open google.protobuf
open google.protobuf.compiler

/-!
Helpers for embedding serialized `FileDescriptorProto`s in generated modules so
servers can answer gRPC server reflection (`FileByFilename` /
`FileContainingSymbol`) without shipping `.proto` sources.
-/
namespace DescriptorEmbed

private def joinDotted (a b : String) : String :=
  if a.isEmpty then b else a ++ "." ++ b

/-- Fully-qualified names of the messages (recursively) and their nested enums
declared in `msg`, prefixed by `prefix_`. -/
private partial def messageSymbols (prefix_ : String) (msg : DescriptorProto)
    (acc : Array String) : Array String :=
  match msg.name with
  | none => acc
  | some name =>
    let full := joinDotted prefix_ name
    let acc := acc.push full
    let acc := msg.enum_type.foldl (init := acc) fun acc e =>
      match e.name with
      | some enumName => acc.push (joinDotted full enumName)
      | none => acc
    msg.nested_type.foldl (init := acc) fun acc nested => messageSymbols full nested acc

/-- Fully-qualified message, enum, service, and method names declared in
`file`, for `FileContainingSymbol` lookups. -/
def fileSymbols (file : FileDescriptorProto) : Array String :=
  let pkg := file.package.getD ""
  let acc := file.message_type.foldl (init := (#[] : Array String)) fun acc msg =>
    messageSymbols pkg msg acc
  let acc := file.enum_type.foldl (init := acc) fun acc e =>
    match e.name with
    | some enumName => acc.push (joinDotted pkg enumName)
    | none => acc
  file.service.foldl (init := acc) fun acc s =>
    match s.name with
    | some serviceName =>
      let serviceFull := joinDotted pkg serviceName
      let acc := acc.push serviceFull
      s.method.foldl (init := acc) fun acc m =>
        match m.name with
        | some methodName => acc.push (joinDotted serviceFull methodName)
        | none => acc
    | none => acc

private def stripLeadingDot (name : String) : String :=
  if name.startsWith "." then (name.drop 1).toString else name

private def extensionEntry (field : FieldDescriptorProto) : Option (String × Int32) := do
  let extendee ← field.extendee
  let number ← field.number
  pure (stripLeadingDot extendee, number)

private partial def messageExtensions (msg : DescriptorProto)
    (acc : Array (String × Int32)) : Array (String × Int32) :=
  let acc := msg.extension.foldl (init := acc) fun acc field =>
    match extensionEntry field with
    | some entry => acc.push entry
    | none => acc
  msg.nested_type.foldl (init := acc) fun acc nested => messageExtensions nested acc

/-- `(containing type, extension number)` pairs declared in `file` (including
nested `extend` blocks), for `FileContainingExtension` lookups. -/
def fileExtensions (file : FileDescriptorProto) : Array (String × Int32) :=
  let acc := file.extension.foldl (init := (#[] : Array (String × Int32))) fun acc field =>
    match extensionEntry field with
    | some entry => acc.push entry
    | none => acc
  file.message_type.foldl (init := acc) fun acc msg => messageExtensions msg acc

private partial def closureAux (descByName : Std.HashMap String FileDescriptorProto)
    (name : String) (seen : Array String) : Array String :=
  if seen.contains name then
    seen
  else
    let seen := seen.push name
    match descByName[name]? with
    | none => seen
    | some file => file.dependency.foldl (init := seen) fun seen dep =>
        closureAux descByName dep seen

/-- Proto paths in the transitive import closure of `root` (root first, in
depth-first order). -/
def closure (descByName : Std.HashMap String FileDescriptorProto) (root : String) :
    Array String :=
  closureAux descByName root #[]

private def renderStringArray (values : Array String) : String :=
  "#[" ++ String.intercalate ", " (values.toList.map String.quote) ++ "]"

/-- Renders `def «constName» : Grpc.Services.Reflection.FileDescriptor := { … }`
with the serialized descriptor embedded as a base64 literal decoded at module
initialization. -/
def renderFileDescriptorDef (constName : String) (file : FileDescriptorProto) :
    Except String String := do
  let name ← file.name.getDM (throw "file descriptor missing name")
  -- Reflection conventionally serves descriptors without source info; dropping
  -- it also keeps the embedded literal small.
  let stripped : FileDescriptorProto := { file with source_code_info := none }
  let bytes ← match stripped.encode with
    | .ok bytes => pure bytes
    | .error err => throw s!"failed to serialize descriptor for {name}: {err}"
  let symbols := fileSymbols file
  let extensions := fileExtensions file
  let mut fields : Array String := #[]
  fields := fields.push s!"  name := {String.quote name}"
  let package := file.package.getD ""
  if !package.isEmpty then
    fields := fields.push s!"  package := {String.quote package}"
  if !symbols.isEmpty then
    fields := fields.push s!"  symbols := {renderStringArray symbols}"
  if !file.dependency.isEmpty then
    fields := fields.push s!"  dependencies := {renderStringArray file.dependency}"
  fields := fields.push
    s!"  fileDescriptorProto := Protobuf.Base64.decode! {String.quote (Protobuf.Base64.encode bytes)}"
  if !extensions.isEmpty then
    let entries := extensions.toList.map fun (containingType, number) =>
      "{ containingType := " ++ String.quote containingType ++
        s!", extensionNumber := ({number} : Int32) " ++ "}"
    fields := fields.push ("  extensions := #[" ++ String.intercalate ", " entries ++ "]")
  pure <| s!"def «{constName}» : Grpc.Services.Reflection.FileDescriptor := " ++ "{\n" ++
    String.intercalate ",\n" fields.toList ++ "\n}"

end DescriptorEmbed


-- bool compiler::GenerateCode(
--      const CodeGeneratorRequest & request,
--      const CodeGenerator & generator,
--      CodeGeneratorResponse * response,
--      std::string * error_msg)
def generate_code (request : CodeGeneratorRequest) : ExceptT String IO CodeGeneratorResponse := do
  let parseOptions (param? : Option String) : Std.HashMap String String :=
    match param? with
    | none => {}
    | some param =>
      let entries := param.splitOn ","
      entries.foldl (init := {}) fun acc entry =>
        let entry := entry.trimAscii.toString
        if entry.isEmpty then acc
        else
          match entry.splitOn "=" with
          | [] => acc
          | key :: rest =>
            let key := key.trimAscii.toString
            if key.isEmpty then acc
            else
              let value := (String.intercalate "=" rest).trimAscii.toString
              acc.insert key value

  let normalizePath (path : String) : String :=
    path.map fun c => if c == '\\' then '/' else c

  let rec last? (xs : List String) : Option String :=
    match xs with
    | [] => none
    | [x] => some x
    | _ :: xs => last? xs

  let baseName (path : String) : String :=
    let parts := (normalizePath path).splitOn "/"
    (last? parts).getD ""

  let moduleNameFromPath (path : String) : String :=
    let path := normalizePath path
    let path := if path.startsWith "./" then (path.drop 2).toString else path
    let path := if path.endsWith ".proto" then (path.dropEnd ".proto".length).toString else path
    let parts := path.splitOn "/" |>.filter (fun p => !p.isEmpty)
    String.intercalate "." parts

  let withPrefix (prefix_ : String) (mod : String) : String :=
    if prefix_.isEmpty then mod
    else if mod.isEmpty then prefix_
    else prefix_ ++ "." ++ mod

  let leanIdent (name : String) : String :=
    "«" ++ name ++ "»"

  let qualifiedName (name : String) : String :=
    let parts := name.splitOn "." |>.filter (fun p => !p.isEmpty)
    String.intercalate "." (parts.map leanIdent)

  let rootTypeName (name : String) : String :=
    let name := if name.startsWith "." then (name.drop 1).toString else name
    "_root_." ++ qualifiedName name

  let fullServiceName (package service : String) : String :=
    if package.isEmpty then service else package ++ "." ++ service

  let renderUnaryService (fileDescriptorsRef : String) (file : FileDescriptorProto) :
      Except String String := do
    let package := file.package.getD ""
    if file.service.isEmpty then
      pure ""
    else if file.syntax.getD "" != "proto3" then
      pure ""
    else
      let mut blocks : Array String := #[]
      for service in file.service do
        let serviceName ← service.name.getDM (throw "service descriptor missing name")
        let serviceIdent := leanIdent serviceName
        let serviceFullName := fullServiceName package serviceName
        let mut fields : Array String := #[]
        let mut registrations : Array String := #[]
        let mut methodDefs : Array String := #[]
        for method in service.method do
          let methodName ← method.name.getDM (throw s!"service {serviceFullName} has a method without a name")
          let isClientStreaming := method.client_streaming.getD false
          let isServerStreaming := method.server_streaming.getD false
          let inputType ← method.input_type.getDM (throw s!"method {serviceFullName}/{methodName} is missing input_type")
          let outputType ← method.output_type.getDM (throw s!"method {serviceFullName}/{methodName} is missing output_type")
          let inputType := rootTypeName inputType
          let outputType := rootTypeName outputType
          let handlerField := leanIdent ("handle" ++ methodName)
          let methodDef := leanIdent (methodName ++ "Method")
          if isClientStreaming && isServerStreaming then
            fields := fields.push s!"  {handlerField} : Grpc.TypedBidirectionalStreamingStreamHandler {inputType} {outputType}"
          else if isClientStreaming then
            fields := fields.push s!"  {handlerField} : Grpc.TypedClientStreamingStreamHandler {inputType} {outputType}"
          else if isServerStreaming then
            fields := fields.push s!"  {handlerField} : Grpc.TypedServerStreamingStreamHandler {inputType} {outputType}"
          else
            fields := fields.push s!"  {handlerField} : Grpc.TypedUnaryHandler {inputType} {outputType}"
          methodDefs := methodDefs.push <| String.intercalate "\n" [
            s!"def {methodDef} : Grpc.MethodName := " ++ "{",
            s!"  service := \"{serviceFullName}\",",
            s!"  method := \"{methodName}\"",
            "}"
          ]
          if isClientStreaming && isServerStreaming then
            registrations := registrations.push <| String.intercalate "\n" [
              s!"    |>.registerBidirectionalStreamingStreamCodec {methodDef} {inputType}.decode {outputType}.encode service.{handlerField}"
            ]
          else if isClientStreaming then
            registrations := registrations.push <| String.intercalate "\n" [
              s!"    |>.registerClientStreamingStreamCodec {methodDef} {inputType}.decode {outputType}.encode service.{handlerField}"
            ]
          else if isServerStreaming then
            registrations := registrations.push <| String.intercalate "\n" [
              s!"    |>.registerServerStreamingStreamCodec {methodDef} {inputType}.decode {outputType}.encode service.{handlerField}"
            ]
          else
            registrations := registrations.push <| String.intercalate "\n" [
              s!"    |>.registerUnaryCodec {methodDef} {inputType}.decode {outputType}.encode service.{handlerField}"
            ]
        let fieldLines := String.intercalate "\n" fields.toList
        let methodDefLines := String.intercalate "\n\n" methodDefs.toList
        let registerBody :=
          if registrations.isEmpty then
            "  registry"
          else
            String.intercalate "\n" ("  registry" :: registrations.toList)
        let fileDescriptorsDef := String.intercalate "\n" [
          "/-- File descriptors (this file plus its transitive imports) to serve gRPC",
          "server reflection for this service, e.g. via",
          "`Grpc.Services.Reflection.registerWith { files := fileDescriptors }`. -/",
          "def fileDescriptors : Array Grpc.Services.Reflection.FileDescriptor :=",
          s!"  {fileDescriptorsRef}"
        ]
        blocks := blocks.push <| String.intercalate "\n\n" [
          s!"structure {serviceIdent} where\n{fieldLines}",
          s!"namespace {serviceIdent}",
          methodDefLines,
          fileDescriptorsDef,
          String.intercalate "\n" [
            s!"def register (registry : Grpc.Registry) (service : {serviceIdent}) : Grpc.Registry :=",
            registerBody
          ],
          s!"end {serviceIdent}"
        ]
      let body := String.intercalate "\n\n" blocks.toList
      if package.isEmpty then
        pure body
      else
        pure <| String.intercalate "\n\n" [
          s!"namespace {qualifiedName package}",
          body,
          s!"end {qualifiedName package}"
        ]

  let options := parseOptions request.parameter
  let lean4Prefix ← options["lean4_prefix"]?.getDM (throw "lean4_prefix is not specified, you should specify by --lean4_opt=lean4_prefix=...")
  let reflectionDescriptorsOnly :=
    options["reflection_descriptors_only"]? == some "true"

  -- Cross-target dependencies: proto files generated by *other* invocations
  -- under their own module prefixes. Format:
  --   --lean4_opt=dep_modules=path/a.proto@PrefixA;path/b.proto@PrefixB
  let depModules : Std.HashMap String String :=
    match options["dep_modules"]? with
    | none => {}
    | some spec =>
      (spec.splitOn ";").foldl (init := {}) fun acc entry =>
        match entry.splitOn "@" with
        | [path, prefix_] =>
          if path.isEmpty || prefix_.isEmpty then acc else acc.insert path prefix_
        | _ => acc

  -- Well-known types provided by the runtime library instead of per-target
  -- generation (mirroring the descriptor.proto special case).
  let wellKnownModule? (dep : String) : Option String :=
    if dep == "google/protobuf/descriptor.proto" then
      some "Protobuf.Internal.Desc"
    else if dep == "google/protobuf/timestamp.proto" || dep == "google/protobuf/duration.proto" then
      some "Protobuf.WellKnown"
    else
      none

  let filesToGenerate := request.file_to_generate
  let targetSet : Std.HashMap String PUnit :=
    filesToGenerate.foldl (init := {}) fun acc name => acc.insert name ()
  let supportedFeatures : UInt64 := 1
  let sourceMap : Std.HashMap String FileDescriptorProto :=
    request.source_file_descriptors.foldl (init := {}) fun acc (file : FileDescriptorProto) =>
      match file.name with
      | some name => acc.insert name file
      | none => acc
  let protoFiles : Array FileDescriptorProto :=
    request.proto_file.map fun (file : FileDescriptorProto) =>
      match file.name with
      | some name =>
        match sourceMap[name]? with
        | some full => full
        | none => file
      | none => file
  let descByName : Std.HashMap String FileDescriptorProto :=
    protoFiles.foldl (init := {}) fun acc file =>
      match file.name with
      | some name => acc.insert name file
      | none => acc

  -- Reflection descriptor embedding: every generated module carries its file's
  -- serialized FileDescriptorProto under `<prefix>.FileDescriptors.«<base>»`
  -- plus a `«<base>_files»` transitive-closure array for reflection configs.
  let protoConstBase (path : String) : String :=
    let base := baseName path
    if base.endsWith ".proto" then (base.dropEnd ".proto".length).toString else base

  let sanitizeIdentPart (path : String) : String :=
    (normalizePath path).map fun c => if c.isAlphanum then c else '_'

  let fileDescRef (prefix_ : String) (constName : String) : String :=
    "_root_." ++ qualifiedName prefix_ ++ ".FileDescriptors.«" ++ constName ++ "»"

  let renderDescriptorSection (name : String) (fileDesc : FileDescriptorProto) :
      Except String String := do
    let selfBase := protoConstBase name
    let namespaceName := qualifiedName lean4Prefix ++ ".FileDescriptors"
    let mut defs : Array String := #[]
    let mut elems : Array String := #[]
    for depName in DescriptorEmbed.closure descByName name do
      if depName == name then
        elems := elems.push ("«" ++ selfBase ++ "»")
      else if reflectionDescriptorsOnly then
        -- Descriptor-only outputs are self-contained and have no generated
        -- dependency imports. Embed every transitive dependency locally;
        -- callers can merge independently generated roots by filename.
        let depDesc ← match descByName[depName]? with
          | some depDesc => pure depDesc
          | none => throw s!"dependency {depName} of {name} was not found in protoc input"
        let constName := selfBase ++ "_dep_" ++ sanitizeIdentPart depName
        defs := defs.push (← DescriptorEmbed.renderFileDescriptorDef constName depDesc)
        elems := elems.push ("«" ++ constName ++ "»")
      else if targetSet.contains depName then
        -- Generated by this invocation: its module (transitively publicly
        -- imported alongside the generated types) defines the constant.
        elems := elems.push (fileDescRef lean4Prefix (protoConstBase depName))
      else if let some depPrefix := depModules[depName]? then
        -- Generated by another lean_proto_library: reference it under that
        -- target's module prefix.
        elems := elems.push (fileDescRef depPrefix (protoConstBase depName))
      else
        -- No generated module carries this dependency (well-known or
        -- option-only import), so embed its descriptor locally.
        let depDesc ← match descByName[depName]? with
          | some depDesc => pure depDesc
          | none => throw s!"dependency {depName} of {name} was not found in protoc input"
        let constName := selfBase ++ "_dep_" ++ sanitizeIdentPart depName
        defs := defs.push (← DescriptorEmbed.renderFileDescriptorDef constName depDesc)
        elems := elems.push ("«" ++ constName ++ "»")
    defs := defs.push (← DescriptorEmbed.renderFileDescriptorDef selfBase fileDesc)
    defs := defs.push <| String.intercalate "\n" [
      s!"/-- `{name}` and its transitive imports, for gRPC server reflection. -/",
      s!"def «{selfBase}_files» : Array Grpc.Services.Reflection.FileDescriptor :=",
      "  #[" ++ String.intercalate ", " elems.toList ++ "]"
    ]
    pure <| String.intercalate "\n\n" [
      s!"namespace {namespaceName}",
      String.intercalate "\n\n" defs.toList,
      s!"end {namespaceName}"
    ]

  if filesToGenerate.isEmpty then
    let response : CodeGeneratorResponse := {
      file := #[]
      supported_features := some supportedFeatures
    }
    return response

  if !reflectionDescriptorsOnly then
    for name in filesToGenerate do
      let fileDesc ← match descByName[name]? with
        | some file => pure file
        | none => throw s!"file_to_generate {name} was not found in protoc input"
      match fileDesc.syntax with
      | some stx =>
          if stx == "proto3" then
            pure ()
          else
            throw s!"protoc-gen-lean4 only supports proto3 targets; {name} declares syntax = {stx}"
      | none =>
          throw s!"protoc-gen-lean4 only supports proto3 targets; {name} omits syntax and defaults to proto2"

  let desc : FileDescriptorSet := { file := protoFiles }

  let compileTargets (desc : FileDescriptorSet)
      (targets : Std.HashMap String PUnit) :
      Protobuf.Versions.M (Std.HashMap String (Array Command)) := do
    let names ← desc.file.mapM fun (file : FileDescriptorProto) =>
      match file.name with
      | some name => pure name
      | none => throw "file descriptor missing name"
    let deps := names.zip <| desc.file.map fun (file : FileDescriptorProto) => file.dependency
    let deps := Std.HashMap.ofList deps.toList
    let sccs := names.topoSortSCCHash deps |>.reverse
    for scc in sccs do
      if scc.size > 1 then
        let cycle := scc.toList
        throw s!"{decl_name%}: mutual recursion in file imports: {String.intercalate ", " cycle}"
    let sortedNames := sccs.flatten
    let mut nameIndex : Std.HashMap String Nat := {}
    for i in [:sortedNames.size] do
      nameIndex := nameIndex.insert sortedNames[i]! i
    let sorted := desc.file.toList.mergeSort (fun x y =>
      let ix := nameIndex[(x.name.getD "")]?.getD 0
      let iy := nameIndex[(y.name.getD "")]?.getD 0
      ix ≤ iy)
    let mut outputs : Std.HashMap String (Array Command) := {}
    for file in sorted do
      let name := file.name.getD ""
      if targets.contains name then
        let cmds ←
          match file.syntax with
          | some "proto3" =>
              Protobuf.Versions.Proto3.compile_file file
          | some stx =>
              throw s!"protoc-gen-lean4 only supports proto3 targets; {name} declares syntax = {stx}"
          | none =>
              throw s!"protoc-gen-lean4 only supports proto3 targets; {name} omits syntax and defaults to proto2"
        outputs := outputs.insert name cmds
    return outputs

  let outputs ← if reflectionDescriptorsOnly then
      pure {}
    else
      liftM (m := Except String) (n := ExceptT String IO ) <|
        Protobuf.Versions.M.run (compileTargets desc targetSet)

  let renderCommands (cmds : Array Command) : Except String String := do
    let cmds ← cmds.mapM fun x =>
      match x.raw.getKind with
      | ``enumDec => pure <| PrettyPrinter.enumDec.pprint <| TSyntax.mk x.raw
      | ``oneofDec => pure <| PrettyPrinter.oneofDec.pprint <| TSyntax.mk x.raw
      | ``messageDec => pure <| PrettyPrinter.messageDec.pprint <| TSyntax.mk x.raw
      | ``proto_mutual_stx => pure <| PrettyPrinter.proto_mutual_stx.pprint <| TSyntax.mk x.raw
      | ``extendDec => pure <| PrettyPrinter.extendDec.pprint <| TSyntax.mk x.raw
      | ``Lean.Parser.Command.attribute =>
          match PrettyPrinter.deprecatedAttr.pprint <| TSyntax.mk x.raw with
          | some cmd => pure cmd
          | none => throw s!"{decl_name%}: unsupported generated attribute command"
      | kind => throw s!"{decl_name%}: unknown generated syntax kind {kind}"
    pure (String.intercalate "\n\n" cmds.toList)

  let renderFile (imports : Array String) (cmds : Array Command) (descriptors : String)
      (services : String) : Except String String := do
    let body ← if reflectionDescriptorsOnly then pure "" else renderCommands cmds
    let importLines := if reflectionDescriptorsOnly then [] else
      imports.toList.map fun m => s!"public import {m}"
    -- Descriptor-only modules depend just on base64 decoding and the
    -- reflection data model. This lets grpc-lean generate descriptors for its
    -- own standard services without a cycle through the full runtime.
    let header := if reflectionDescriptorsOnly then
        String.intercalate "\n"
          [ "module"
          , ""
          , "public import Protobuf.Base64"
          , "public import Grpc.Services.Reflection.Descriptor"
          , ""
          , "public section"
          , ""
          ]
      else
        String.intercalate "\n"
          [ "module"
          , ""
          , "public import Protobuf.Encoding"
          , "public import Protobuf.Base64"
          , "public import Grpc"
          , "meta import Protobuf.Notation"
          , String.intercalate "\n" importLines
          , ""
          , "public section"
          , ""
          , "open Protobuf Encoding"
          , "open scoped Protobuf.Notation"
          , ""
          ]
    let contentParts := #[body, descriptors, services].filter (fun part => !part.isEmpty)
    let r := header ++ String.intercalate "\n\n" contentParts.toList
    pure <| if r.endsWith "\n" then r else r ++ "\n"

  let outputFileName (name : String) : String :=
    let base := baseName name
    if base.endsWith ".proto" then
      (base.dropEnd ".proto".length).toString ++ ".lean"
    else
      base ++ ".lean"

  let mut filesOut := #[]
  for name in filesToGenerate do
    let fileDesc ← match descByName[name]? with
      | some file => pure file
      | none => throw s!"file_to_generate {name} was not found in protoc input"
    let deps :=
      fileDesc.dependency
    let importModules ← do
      let mut seen : Std.HashSet String := {}
      let mut out : Array String := #[]
      for dep in deps do
        let mod? : Option String :=
          if let some mod := wellKnownModule? dep then
            some mod
          else if targetSet.contains dep then
            -- Dependencies generated in this invocation live under lean4Prefix.
            some (withPrefix lean4Prefix (moduleNameFromPath (baseName dep)))
          else if let some depPrefix := depModules[dep]? then
            -- Dependencies generated by another lean_proto_library live under
            -- that target's module prefix.
            some (withPrefix depPrefix (moduleNameFromPath (baseName dep)))
          else
            -- Other imports (e.g. option-only imports such as
            -- buf/validate/validate.proto) have no generated module to
            -- import; their extension payloads are carried in Unknown.Fields
            -- and do not affect generated types.
            none
        if let some mod := mod? then
          if !mod.isEmpty && !seen.contains mod then
            seen := seen.insert mod
            out := out.push mod
      pure out
    let cmds ← if reflectionDescriptorsOnly then
        pure #[]
      else
        match outputs[name]? with
        | some cmds => pure cmds
        | none => throw s!"file_to_generate {name} was not found in protoc input"
    let descriptors ← liftM (m := Except String) (n := ExceptT String IO) <|
      renderDescriptorSection name fileDesc
    let fileDescriptorsRef := fileDescRef lean4Prefix (protoConstBase name ++ "_files")
    let services ← if reflectionDescriptorsOnly then
        pure ""
      else
        liftM (m := Except String) (n := ExceptT String IO) <|
          renderUnaryService fileDescriptorsRef fileDesc
    let content ← liftM (m := Except String) (n := ExceptT String IO) <|
      renderFile importModules cmds descriptors services
    let outName := outputFileName name
    let file : CodeGeneratorResponse.File := { name := some outName, content := some content }
    filesOut := filesOut.push file

  let response : CodeGeneratorResponse := {
    file := filesOut
    supported_features := some supportedFeatures
  }
  return response

def exeName : String := "protoc-gen-lean4"

public def main : IO UInt32 := do
  let stdIn ← IO.getStdin
  let stdErr ← IO.getStderr
  let stdOut ← IO.getStdout
  let input ← stdIn.readBinToEnd
  let request := CodeGeneratorRequest.decode input
  let request ← match request with
    | .ok r => pure r
    | .error _ =>
      stdErr.putStrLn s!"{exeName}: protoc sent unparseable request to plugin."
      return 1
  let result ← generate_code request
  let result ← match result with
    | .ok r => pure r
    | .error err =>
      stdErr.putStrLn s!"{exeName}: {err}"
      return 1
  let resultBin ← match result.encode with
    | .ok r => pure r
    | .error err =>
      stdErr.putStrLn s!"{exeName}: failed to serialize protobuf: {err}"
      return 1
  stdOut.write resultBin
  return 0
