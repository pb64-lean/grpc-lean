module

public import Grpc.Server
public import Protobuf.Encoding

public section

namespace Grpc
namespace Services
namespace Reflection

namespace Wire

abbrev ProtoMessage := Protobuf.Encoding.Message
abbrev ProtoVal := Protobuf.Encoding.ProtoVal
abbrev ProtoError := Protobuf.Encoding.ProtoError

private def decodeProtoMessage (bytes : ByteArray) : Except ProtoError ProtoMessage := do
  Protobuf.Encoding.protoDecodeParseResultExcept
    (Binary.Get.run (Binary.getThe ProtoMessage) bytes).toExcept

private def encodeProtoMessage (message : ProtoMessage) : Except ProtoError ByteArray := do
  message.validate
  pure (Binary.Put.run (Binary.put message))

private def setString (message : ProtoMessage) (fieldNum : Nat) (value : String) :
    Except ProtoError ProtoMessage := do
  let value ← Protobuf.Encoding.ProtoVal.ofString value
  pure (message.set fieldNum value)

private def setStringIfNotEmpty (message : ProtoMessage) (fieldNum : Nat) (value : String) :
    Except ProtoError ProtoMessage := do
  if value.isEmpty then
    pure message
  else
    setString message fieldNum value

private def setBytes (message : ProtoMessage) (fieldNum : Nat) (value : ByteArray) :
    Except ProtoError ProtoMessage := do
  let value ← Protobuf.Encoding.ProtoVal.ofBytes value
  pure (message.set fieldNum value)

private def setInt32 (message : ProtoMessage) (fieldNum : Nat) (value : Int32) :
    Except ProtoError ProtoMessage := do
  let value ← Protobuf.Encoding.ProtoVal.ofVarint_int32 value
  pure (message.set fieldNum value)

private def setMessage (message : ProtoMessage) (fieldNum : Nat) (value : ProtoMessage) :
    Except ProtoError ProtoMessage := do
  let value ← Protobuf.Encoding.ProtoVal.ofMessage value
  pure (message.set fieldNum value)

end Wire

open Wire

def v1ServiceName : String :=
  "grpc.reflection.v1.ServerReflection"

def v1alphaServiceName : String :=
  "grpc.reflection.v1alpha.ServerReflection"

def methodNameForService (service : String) : MethodName :=
  { service := service, method := "ServerReflectionInfo" }

def v1MethodName : MethodName :=
  methodNameForService v1ServiceName

def v1alphaMethodName : MethodName :=
  methodNameForService v1alphaServiceName

def reflectionServiceNames : Array String :=
  #[v1ServiceName, v1alphaServiceName]

structure ExtensionRequest where
  containingType : String := ""
  extensionNumber : Int32 := 0
  deriving Inhabited, Repr, DecidableEq

inductive RequestKind where
  | fileByFilename (filename : String)
  | fileContainingSymbol (symbol : String)
  | fileContainingExtension (extensionRequest : ExtensionRequest)
  | allExtensionNumbersOfType (typeName : String)
  | listServices (value : String)
  deriving Repr, DecidableEq

structure Request where
  host : String := ""
  kind : Option RequestKind := none
  deriving Inhabited, Repr, DecidableEq

structure FileDescriptorResponse where
  fileDescriptorProto : Array ByteArray := #[]
  deriving Inhabited, DecidableEq

structure ExtensionNumberResponse where
  baseTypeName : String := ""
  extensionNumber : Array Int32 := #[]
  deriving Inhabited, Repr, DecidableEq

structure ServiceResponse where
  name : String
  deriving Inhabited, Repr, DecidableEq

structure ListServiceResponse where
  service : Array ServiceResponse := #[]
  deriving Inhabited, Repr, DecidableEq

structure ErrorResponse where
  errorCode : Int32 := 0
  errorMessage : String := ""
  deriving Inhabited, Repr, DecidableEq

inductive ResponseKind where
  | fileDescriptorResponse (response : FileDescriptorResponse)
  | allExtensionNumbersResponse (response : ExtensionNumberResponse)
  | listServicesResponse (response : ListServiceResponse)
  | errorResponse (response : ErrorResponse)
  deriving DecidableEq

structure Response where
  validHost : String := ""
  originalRequest : Request := {}
  kind : Option ResponseKind := none
  deriving Inhabited, DecidableEq

namespace ExtensionRequest

def fromMessage (message : ProtoMessage) : Except ProtoError ExtensionRequest := do
  let containingType := (← message.getString? 1).getD ""
  let extensionNumber := (← message.getVarint_int32? 2).getD 0
  pure { containingType := containingType, extensionNumber := extensionNumber }

def toMessage (request : ExtensionRequest) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  message ← setStringIfNotEmpty message 1 request.containingType
  if request.extensionNumber != 0 then
    message ← setInt32 message 2 request.extensionNumber
  pure message

end ExtensionRequest

namespace Request

private def decodeKindRecord (record : Protobuf.Encoding.Record) :
    Except ProtoError (Option RequestKind) := do
  let message : ProtoMessage := { records := #[record] }
  match record.fieldNum with
  | 3 =>
      match ← message.getString? 3 with
      | some value => pure (some (.fileByFilename value))
      | none => pure none
  | 4 =>
      match ← message.getString? 4 with
      | some value => pure (some (.fileContainingSymbol value))
      | none => pure none
  | 5 =>
      match ← message.getMessage? 5 with
      | some value => pure (some (.fileContainingExtension (← ExtensionRequest.fromMessage value)))
      | none => pure none
  | 6 =>
      match ← message.getString? 6 with
      | some value => pure (some (.allExtensionNumbersOfType value))
      | none => pure none
  | 7 =>
      match ← message.getString? 7 with
      | some value => pure (some (.listServices value))
      | none => pure none
  | _ => pure none

def fromMessage (message : ProtoMessage) : Except ProtoError Request := do
  let host := (← message.getString? 1).getD ""
  let mut kind := none
  for record in message.records do
    match ← decodeKindRecord record with
    | some requestKind => kind := some requestKind
    | none => pure ()
  pure { host := host, kind := kind }

def toMessage (request : Request) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  message ← setStringIfNotEmpty message 1 request.host
  match request.kind with
  | none => pure message
  | some (.fileByFilename filename) => setString message 3 filename
  | some (.fileContainingSymbol symbol) => setString message 4 symbol
  | some (.fileContainingExtension extensionRequest) => do
      setMessage message 5 (← ExtensionRequest.toMessage extensionRequest)
  | some (.allExtensionNumbersOfType typeName) => setString message 6 typeName
  | some (.listServices value) => setString message 7 value

def decode (bytes : ByteArray) : Except ProtoError Request := do
  fromMessage (← decodeProtoMessage bytes)

def encode (request : Request) : Except ProtoError ByteArray := do
  encodeProtoMessage (← toMessage request)

end Request

namespace FileDescriptorResponse

def toMessage (response : FileDescriptorResponse) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  for descriptor in response.fileDescriptorProto do
    message ← setBytes message 1 descriptor
  pure message

def fromMessage (message : ProtoMessage) : Except ProtoError FileDescriptorResponse := do
  let descriptors ← message.getExpandedBytes 1
  pure { fileDescriptorProto := descriptors }

end FileDescriptorResponse

namespace ExtensionNumberResponse

def toMessage (response : ExtensionNumberResponse) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  message ← setStringIfNotEmpty message 1 response.baseTypeName
  for number in response.extensionNumber do
    message ← setInt32 message 2 number
  pure message

end ExtensionNumberResponse

namespace ServiceResponse

def toMessage (response : ServiceResponse) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  setString message 1 response.name

def fromMessage (message : ProtoMessage) : Except ProtoError ServiceResponse := do
  pure { name := (← message.getString? 1).getD "" }

end ServiceResponse

namespace ListServiceResponse

def toMessage (response : ListServiceResponse) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  for service in response.service do
    message ← setMessage message 1 (← ServiceResponse.toMessage service)
  pure message

def fromMessage (message : ProtoMessage) : Except ProtoError ListServiceResponse := do
  let services ← message.getExpandedMessage 1
  let services ← services.mapM ServiceResponse.fromMessage
  pure { service := services }

end ListServiceResponse

namespace ErrorResponse

def toMessage (response : ErrorResponse) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  if response.errorCode != 0 then
    message ← setInt32 message 1 response.errorCode
  message ← setStringIfNotEmpty message 2 response.errorMessage
  pure message

def fromMessage (message : ProtoMessage) : Except ProtoError ErrorResponse := do
  pure {
    errorCode := (← message.getVarint_int32? 1).getD 0,
    errorMessage := (← message.getString? 2).getD ""
  }

end ErrorResponse

namespace Response

private def decodeKindRecord (record : Protobuf.Encoding.Record) :
    Except ProtoError (Option ResponseKind) := do
  let message : ProtoMessage := { records := #[record] }
  match record.fieldNum with
  | 4 =>
      match ← message.getMessage? 4 with
      | some value => pure (some (.fileDescriptorResponse (← FileDescriptorResponse.fromMessage value)))
      | none => pure none
  | 5 =>
      match ← message.getMessage? 5 with
      | some value =>
          let baseTypeName := (← value.getString? 1).getD ""
          let extensionNumber := (← value.getRepeatedVarint_int32 2)
          pure (some (.allExtensionNumbersResponse {
            baseTypeName := baseTypeName,
            extensionNumber := extensionNumber
          }))
      | none => pure none
  | 6 =>
      match ← message.getMessage? 6 with
      | some value => pure (some (.listServicesResponse (← ListServiceResponse.fromMessage value)))
      | none => pure none
  | 7 =>
      match ← message.getMessage? 7 with
      | some value => pure (some (.errorResponse (← ErrorResponse.fromMessage value)))
      | none => pure none
  | _ => pure none

def fromMessage (message : ProtoMessage) : Except ProtoError Response := do
  let validHost := (← message.getString? 1).getD ""
  let originalRequest ←
    match ← message.getMessage? 2 with
    | some value => Request.fromMessage value
    | none => pure {}
  let mut kind := none
  for record in message.records do
    match ← decodeKindRecord record with
    | some responseKind => kind := some responseKind
    | none => pure ()
  pure { validHost := validHost, originalRequest := originalRequest, kind := kind }

def toMessage (response : Response) : Except ProtoError ProtoMessage := do
  let mut message := Protobuf.Encoding.Message.empty
  message ← setStringIfNotEmpty message 1 response.validHost
  message ← setMessage message 2 (← Request.toMessage response.originalRequest)
  match response.kind with
  | none => pure message
  | some (.fileDescriptorResponse fileResponse) =>
      setMessage message 4 (← FileDescriptorResponse.toMessage fileResponse)
  | some (.allExtensionNumbersResponse extensionResponse) =>
      setMessage message 5 (← ExtensionNumberResponse.toMessage extensionResponse)
  | some (.listServicesResponse listResponse) =>
      setMessage message 6 (← ListServiceResponse.toMessage listResponse)
  | some (.errorResponse errorResponse) =>
      setMessage message 7 (← ErrorResponse.toMessage errorResponse)

def decode (bytes : ByteArray) : Except ProtoError Response := do
  fromMessage (← decodeProtoMessage bytes)

def encode (response : Response) : Except ProtoError ByteArray := do
  encodeProtoMessage (← toMessage response)

end Response

structure ExtensionDescriptor where
  containingType : String
  extensionNumber : Int32
  deriving Inhabited, Repr, DecidableEq

structure FileDescriptor where
  name : String
  package : String := ""
  symbols : Array String := #[]
  dependencies : Array String := #[]
  fileDescriptorProto : ByteArray
  extensions : Array ExtensionDescriptor := #[]
  extensionNumbers : Array (String × Array Int32) := #[]
  deriving Inhabited

structure Config where
  serviceNames : Array String := #[]
  files : Array FileDescriptor := #[]
  includeReflectionServices : Bool := true
  deriving Inhabited

private def pushUniqueString (values : Array String) (value : String) : Array String :=
  if value.isEmpty || values.contains value then
    values
  else
    values.push value

private def uniqueStrings (values : Array String) : Array String :=
  values.foldl pushUniqueString #[]

private def registryServiceNames (registry : Registry) : Array String :=
  let names := registry.methods.foldl
    (init := #[])
    (fun names method => pushUniqueString names method.name.service)
  let names := registry.serverStreamingMethods.foldl
    (init := names)
    (fun names method => pushUniqueString names method.name.service)
  let names := registry.serverStreamingStreamMethods.foldl
    (init := names)
    (fun names method => pushUniqueString names method.name.service)
  let names := registry.clientStreamingMethods.foldl
    (init := names)
    (fun names method => pushUniqueString names method.name.service)
  let names := registry.clientStreamingStreamMethods.foldl
    (init := names)
    (fun names method => pushUniqueString names method.name.service)
  let names := registry.bidirectionalStreamingMethods.foldl
    (init := names)
    (fun names method => pushUniqueString names method.name.service)
  registry.bidirectionalStreamingStreamMethods.foldl
    (init := names)
    (fun names method => pushUniqueString names method.name.service)

private def configServiceNames (config : Config) (registry : Registry) : Array String :=
  let names := uniqueStrings (registryServiceNames registry ++ config.serviceNames)
  if config.includeReflectionServices then
    uniqueStrings (names ++ reflectionServiceNames)
  else
    names

private def findFileByName? (config : Config) (name : String) : Option FileDescriptor :=
  config.files.find? (fun file => file.name == name)

private def findFileContainingSymbol? (config : Config) (symbol : String) :
    Option FileDescriptor :=
  config.files.find? (fun file => file.symbols.contains symbol)

private def findFileContainingExtension? (config : Config) (extensionRequest : ExtensionRequest) :
    Option FileDescriptor :=
  config.files.find? fun file =>
    file.extensions.any fun extension =>
      extension.containingType == extensionRequest.containingType
        && extension.extensionNumber == extensionRequest.extensionNumber

private def pushUniqueInt32 (values : Array Int32) (value : Int32) : Array Int32 :=
  if values.contains value then values else values.push value

private def extensionNumbersFor? (config : Config) (typeName : String) : Option (Array Int32) :=
  let values := config.files.foldl
    (init := #[])
    (fun values file =>
      let values := file.extensionNumbers.foldl
        (init := values)
        (fun values entry =>
          if entry.1 == typeName then
            entry.2.foldl pushUniqueInt32 values
          else
            values)
      file.extensions.foldl
        (init := values)
        (fun values extension =>
          if extension.containingType == typeName then
            pushUniqueInt32 values extension.extensionNumber
          else
            values))
  if values.isEmpty then none else some values


private partial def collectFileClosure (config : Config) (file : FileDescriptor)
    (seen : Array String := #[]) (out : Array ByteArray := #[]) :
    Array String × Array ByteArray :=
  if seen.contains file.name then
    (seen, out)
  else
    let seen := seen.push file.name
    let out := out.push file.fileDescriptorProto
    file.dependencies.foldl
      (init := (seen, out))
      (fun state dep =>
        let (seen, out) := state
        match findFileByName? config dep with
        | some depFile => collectFileClosure config depFile seen out
        | none => (seen, out))

private def statusCodeNumber (code : Code) : Int32 :=
  Int32.ofInt (Int.ofNat code.toNat)

private def errorResponse (request : Request) (code : Code) (message : String) : Response := {
  validHost := request.host,
  originalRequest := request,
  kind := some (.errorResponse {
    errorCode := statusCodeNumber code,
    errorMessage := message
  })
}

private def fileDescriptorResponse (request : Request) (descriptors : Array ByteArray) : Response := {
  validHost := request.host,
  originalRequest := request,
  kind := some (.fileDescriptorResponse { fileDescriptorProto := descriptors })
}

private def listServicesResponse (serviceNames : Array String) (request : Request) : Response := {
  validHost := request.host,
  originalRequest := request,
  kind := some (.listServicesResponse {
    service := serviceNames.map (fun name => { name := name })
  })
}

private def allExtensionNumbersResponse (request : Request) (typeName : String)
    (numbers : Array Int32) : Response := {
  validHost := request.host,
  originalRequest := request,
  kind := some (.allExtensionNumbersResponse {
    baseTypeName := typeName,
    extensionNumber := numbers
  })
}

def respond (config : Config) (request : Request) : Response :=
  match request.kind with
  | none =>
      errorResponse request .unimplemented "not implemented MESSAGE_REQUEST_NOT_SET"
  | some (.listServices _) =>
      listServicesResponse config.serviceNames request
  | some (.fileByFilename filename) =>
      match findFileByName? config filename with
      | some file =>
          let (_, descriptors) := collectFileClosure config file
          fileDescriptorResponse request descriptors
      | none =>
          errorResponse request .notFound s!"file not found: {filename}"
  | some (.fileContainingSymbol symbol) =>
      match findFileContainingSymbol? config symbol with
      | some file =>
          let (_, descriptors) := collectFileClosure config file
          fileDescriptorResponse request descriptors
      | none =>
          errorResponse request .notFound s!"symbol not found: {symbol}"
  | some (.fileContainingExtension extensionRequest) =>
      match findFileContainingExtension? config extensionRequest with
      | some file =>
          let (_, descriptors) := collectFileClosure config file
          fileDescriptorResponse request descriptors
      | none =>
          errorResponse request .notFound
            s!"extension not found: {extensionRequest.containingType}/{extensionRequest.extensionNumber}"
  | some (.allExtensionNumbersOfType typeName) =>
      match extensionNumbersFor? config typeName with
      | some numbers => allExtensionNumbersResponse request typeName numbers
      | none => errorResponse request .notFound s!"type not found: {typeName}"

def service (config : Config) : TypedBidirectionalStreamingStreamHandler Request Response :=
  fun requests => do
    pure (requests.mapM fun request => pure (respond config request))

def registerWith (config : Config) (registry : Registry) : Registry :=
  let config := { config with serviceNames := configServiceNames config registry }
  registry
    |>.registerBidirectionalStreamingStreamCodec v1MethodName Request.decode Response.encode (service config)
    |>.registerBidirectionalStreamingStreamCodec v1alphaMethodName Request.decode Response.encode
      (service config)

def register (registry : Registry) : Registry :=
  registerWith {} registry

end Reflection
end Services
end Grpc
