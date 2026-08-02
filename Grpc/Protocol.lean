module

public import Std.Sync.Channel
public import Grpc.Framing
public import Grpc.Metadata

public section

namespace Grpc

structure MethodName where
  service : String
  method : String
  deriving Repr, DecidableEq

namespace MethodName

def path (method : MethodName) : String :=
  "/" ++ method.service ++ "/" ++ method.method

def parsePath? (path : String) : Option MethodName :=
  match path.splitToList (· == '/') with
  | "" :: service :: method :: [] =>
      if service.isEmpty || method.isEmpty then none else some { service, method }
  | _ => none

end MethodName

inductive TimeoutUnit where
  | hour
  | minute
  | second
  | millisecond
  | microsecond
  | nanosecond
  deriving Repr, DecidableEq

namespace TimeoutUnit

def ofChar? : Char -> Option TimeoutUnit
  | 'H' => some .hour
  | 'M' => some .minute
  | 'S' => some .second
  | 'm' => some .millisecond
  | 'u' => some .microsecond
  | 'n' => some .nanosecond
  | _ => none

def nanoseconds : TimeoutUnit -> Nat
  | .hour => 3600000000000
  | .minute => 60000000000
  | .second => 1000000000
  | .millisecond => 1000000
  | .microsecond => 1000
  | .nanosecond => 1

end TimeoutUnit

structure Timeout where
  value : Nat
  unit : TimeoutUnit
  deriving Repr, DecidableEq

namespace Timeout

private def digit? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else
    none

private partial def parseDigits (chars : List Char) (value : Nat) : Option Nat :=
  match chars with
  | [] => some value
  | c :: rest =>
      match digit? c with
      | some digit => parseDigits rest (value * 10 + digit)
      | none => none

def parse? (raw : String) : Option Timeout :=
  match raw.toList.reverse with
  | [] => none
  | unitChar :: reversedDigits =>
      let digits := reversedDigits.reverse
      if digits.isEmpty || digits.length > 8 then
        none
      else
        match TimeoutUnit.ofChar? unitChar, parseDigits digits 0 with
        | some unit, some value =>
            if value == 0 then none else some { value := value, unit := unit }
        | _, _ => none

def toNanoseconds (timeout : Timeout) : Nat :=
  timeout.value * timeout.unit.nanoseconds

def toMillisecondsCeil (timeout : Timeout) : Nat :=
  (timeout.toNanoseconds + 999999) / 1000000

end Timeout

structure MessageStream (α : Type) where
  recv? : GrpcM (Option α)
  cancel : GrpcM Unit := pure ()

namespace MessageStream

inductive Event (α : Type) where
  | item : α -> Event α
  | error : Status -> Event α

structure Producer (α : Type) where
  stream : MessageStream α
  send : α -> GrpcM Unit
  fail : Status -> GrpcM Unit
  close : GrpcM Unit
  cancel : GrpcM Unit

def ofArray (items : Array α) : GrpcM (MessageStream α) := do
  let cursor ← IO.mkRef 0
  pure {
    recv? := do
      let i ← cursor.get
      match items[i]? with
      | none => pure none
      | some item =>
          cursor.set (i + 1)
          pure (some item)
    cancel := pure ()
  }

def mapM (stream : MessageStream α) (f : α -> GrpcM β) : MessageStream β :=
  {
    recv? := do
      match ← stream.recv? with
      | none => pure none
      | some item => pure (some (← f item))
    cancel := stream.cancel
  }

partial def collect (stream : MessageStream α) (out : Array α := #[]) : GrpcM (Array α) := do
  match ← stream.recv? with
  | none => pure out
  | some item => collect stream (out.push item)

def empty : GrpcM (MessageStream α) :=
  ofArray #[]

private def channelClosedStatus : Status :=
  Status.cancelled "gRPC message stream is closed"

private def channelErrorStatus : Std.CloseableChannel.Error -> Status
  | .closed => channelClosedStatus
  | .alreadyClosed => channelClosedStatus

private def sendEvent (ch : Std.CloseableChannel.Sync (Event α)) (event : Event α) : GrpcM Unit := do
  -- Run the synchronous channel action in the current task. Spawning a second
  -- task and immediately waiting for it can exhaust the default task pool when
  -- several producers run concurrently (and is unnecessary for an unbounded
  -- channel, whose underlying send always returns an already-resolved task).
  let result ← (Std.CloseableChannel.Sync.send ch event).toBaseIO
  GrpcM.ofExcept <| result.mapError channelErrorStatus

private def closeChannel (ch : Std.CloseableChannel.Sync (Event α)) : GrpcM Unit := do
  let result ← (Std.CloseableChannel.Sync.close ch).toBaseIO
  match result with
  | Except.ok () => pure ()
  | .error .alreadyClosed => pure ()
  | .error err => GrpcM.ofExcept (.error (channelErrorStatus err))

def pipe (capacity : Option Nat := some 16) : GrpcM (Producer α) := do
  let ch ← Std.CloseableChannel.Sync.new (α := Event α) capacity
  let stream : MessageStream α := {
    recv? := do
      match ← Std.CloseableChannel.Sync.recv ch with
      | none => pure none
      | some (.item item) => pure (some item)
      | some (.error status) => throw status
    cancel := closeChannel ch
  }
  pure {
    stream := stream,
    send := fun item => sendEvent ch (.item item),
    fail := fun status => do
      sendEvent ch (.error status)
      closeChannel ch,
    close := closeChannel ch,
    cancel := closeChannel ch
  }

end MessageStream

structure UnaryRequest where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  data : ByteArray

structure ClientStreamingRequest where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  messages : Array ByteArray := #[]

structure ClientStreamingStreamRequest where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  messages : MessageStream ByteArray

structure UnaryResponse where
  metadata : Metadata := Metadata.empty
  data : ByteArray := ByteArray.empty
  status : Status := Status.ok
  trailers : Metadata := Metadata.empty

structure ServerStreamingResponse where
  metadata : Metadata := Metadata.empty
  messages : Array ByteArray := #[]
  status : Status := Status.ok
  trailers : Metadata := Metadata.empty

structure ServerStreamingStreamResponse where
  metadata : Metadata := Metadata.empty
  messages : MessageStream ByteArray
  status : Status := Status.ok
  trailers : Metadata := Metadata.empty

namespace Percent

private def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('A'.toNat + (n - 10))

private def fromHex? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if 'A' <= c && c <= 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else if 'a' <= c && c <= 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else
    none

private def unreserved (byte : UInt8) : Bool :=
  let n := byte.toNat
  (0x30 <= n && n <= 0x39)
    || (0x41 <= n && n <= 0x5a)
    || (0x61 <= n && n <= 0x7a)
    || n == 0x2d || n == 0x2e || n == 0x5f || n == 0x7e || n == 0x20

def encode (message : String) : String :=
  let bytes := message.toUTF8
  let out := bytes.foldl (init := "") fun acc byte =>
    if unreserved byte then
      acc.push (Char.ofNat byte.toNat)
    else
      acc.push '%' |>.push (hexDigit (byte.toNat / 16)) |>.push (hexDigit (byte.toNat % 16))
  out

private partial def decodeLoop (chars : List Char) (out : ByteArray) : Except String ByteArray :=
  match chars with
  | [] => .ok out
  | '%' :: a :: b :: rest =>
      match fromHex? a, fromHex? b with
      | some hi, some lo => decodeLoop rest (out.push (UInt8.ofNat (hi * 16 + lo)))
      | _, _ => .error "invalid percent escape"
  | '%' :: _ => .error "truncated percent escape"
  | c :: rest => decodeLoop rest (out.push c.toUInt8)

def decode (message : String) : Except String String := do
  let bytes ← decodeLoop message.toList ByteArray.empty
  match String.fromUTF8? bytes with
  | some value => pure value
  | none => throw "percent-decoded grpc-message is not valid UTF-8"

end Percent

namespace Headers

def contentType (metadata : Metadata) : Option String :=
  metadata.get? "content-type"

def isGrpcContentType (value : String) : Bool :=
  value == "application/grpc" || value == "application/grpc+proto"

private def singletonHeader? (metadata : Metadata) (name : String) : Except Status (Option String) := do
  let values := metadata.getAll name
  if values.size > 1 then
    throw (Status.invalidArgument s!"duplicate {Header.normalizeName name} header")
  else
    pure values[0]?

def timeout? (metadata : Metadata) : Except Status (Option Timeout) := do
  match ← singletonHeader? metadata "grpc-timeout" with
  | none => pure none
  | some value =>
      match Timeout.parse? value with
      | some timeout => pure (some timeout)
      | none => throw (Status.invalidArgument s!"invalid grpc-timeout header {value}")

def contentLength? (metadata : Metadata) : Except Status (Option Nat) := do
  match ← singletonHeader? metadata "content-length" with
  | none => pure none
  | some value =>
      match value.toNat? with
      | some length => pure (some length)
      | none => throw (Status.invalidArgument s!"invalid content-length header {value}")

def validateContentLength (metadata : Metadata) (actual : Nat) : Except Status Unit := do
  match ← contentLength? metadata with
  | none => pure ()
  | some expected =>
      if expected == actual then
        pure ()
      else
        throw (Status.invalidArgument s!"content-length {expected} does not match request body size {actual}")

def identityEncoding : String := "identity"

def gzipEncoding : String := "gzip"

def acceptedEncodings : String := s!"{identityEncoding},{gzipEncoding}"

/-- The validated `grpc-encoding` of a request: `none`/`identity` mean no
compression, `gzip` means gzip-compressed messages. Other encodings reject
with `UNIMPLEMENTED` per the gRPC spec. Returns whether gzip is in use. -/
def requestUsesGzip (metadata : Metadata) : Except Status Bool := do
  match ← singletonHeader? metadata "grpc-encoding" with
  | none => pure false
  | some value =>
      if value == identityEncoding then
        pure false
      else if value == gzipEncoding then
        pure true
      else
        throw (Status.unimplemented s!"unsupported grpc-encoding {value}")

def validateRequestEncoding (metadata : Metadata) : Except Status Unit := do
  discard <| requestUsesGzip metadata

/-- Whether the client's `grpc-accept-encoding` header advertises gzip. -/
def clientAcceptsGzip (metadata : Metadata) : Bool :=
  metadata.getAll "grpc-accept-encoding" |>.any fun value =>
    value.splitOn "," |>.any fun token => token.trim == gzipEncoding

def validateUnaryRequestHeaders (metadata : Metadata) : Except Status MethodName := do
  Metadata.validate metadata

  match metadata.get? ":method" with
  | some "POST" => pure ()
  | some _ => throw (Status.invalidArgument "gRPC requests must use POST")
  | none => throw (Status.invalidArgument "missing :method header")

  match metadata.get? ":scheme" with
  | some "http" => pure ()
  | some "https" => pure ()
  | some value => throw (Status.invalidArgument s!"unsupported gRPC scheme {value}")
  | none => throw (Status.invalidArgument "missing :scheme header")

  match metadata.get? ":status" with
  | some _ => throw (Status.invalidArgument "gRPC requests must not include :status")
  | none => pure ()

  let path ← match metadata.get? ":path" with
    | some path => pure path
    | none => throw (Status.invalidArgument "missing :path header")

  let method ← match MethodName.parsePath? path with
    | some method => pure method
    | none => throw (Status.invalidArgument s!"invalid gRPC method path {path}")

  match ← singletonHeader? metadata "content-type" with
  | some value =>
      if isGrpcContentType value then pure () else
        throw (Status.invalidArgument s!"unsupported content-type {value}")
  | none => throw (Status.invalidArgument "missing content-type header")

  match ← singletonHeader? metadata "te" with
  | some "trailers" => pure ()
  | some _ => throw (Status.invalidArgument "gRPC requests must send te: trailers")
  | none => throw (Status.invalidArgument "missing te header")

  discard <| timeout? metadata
  discard <| contentLength? metadata
  validateRequestEncoding metadata

  pure method

def responseHeaders : Metadata :=
  Metadata.empty
    |>.insert ":status" "200"
    |>.insert "content-type" "application/grpc"
    |>.insert "grpc-accept-encoding" acceptedEncodings

private def reservedResponseMetadataName (name : String) : Bool :=
  name.startsWith ":"
    || name == "content-type"
    || name == "grpc-status"
    || name == "grpc-message"
    || name == "grpc-status-details-bin"
    || name == "grpc-accept-encoding"

private def reservedResponseTrailerName (name : String) : Bool :=
  name.startsWith ":"
    || name == "content-type"
    || name == "grpc-status"
    || name == "grpc-message"
    || name == "grpc-accept-encoding"

private def validateOutboundHeader (kind : String) (reserved : String -> Bool)
    (header : Header) : Except Status Unit := do
  let name := Header.normalizeName header.name
  if reserved name then
    throw (Status.internal s!"reserved gRPC {kind} metadata name {name}")
  match Metadata.validateHeader { header with name := name } with
  | .ok _ => pure ()
  | .error status => throw (Status.internal status.messageD)

def validateResponseMetadata (metadata : Metadata) : Except Status Unit :=
  metadata.forM (validateOutboundHeader "response" reservedResponseMetadataName)

def validateResponseTrailers (metadata : Metadata) : Except Status Unit :=
  metadata.forM (validateOutboundHeader "trailer" reservedResponseTrailerName)

def trailers (status : Status) (extra : Metadata := Metadata.empty) : Metadata :=
  let base := Metadata.empty.insert "grpc-status" status.code.toHeaderValue
  let base := match status.message with
    | none => base
    | some message => base.insert "grpc-message" (Percent.encode message)
  base.append extra

def statusFromTrailers (metadata : Metadata) : Except Status Status := do
  Metadata.validate metadata
  let codeValue ← match ← singletonHeader? metadata "grpc-status" with
    | some value => pure value
    | none => throw (Status.unknown "missing grpc-status trailer")
  let code ← match Code.ofString? codeValue with
    | some code => pure code
    | none => throw (Status.unknown s!"invalid grpc-status trailer {codeValue}")
  let message? ← match ← singletonHeader? metadata "grpc-message" with
    | none => pure none
    | some value =>
        match Percent.decode value with
        | .ok message => pure (some message)
        | .error err => throw (Status.unknown s!"invalid grpc-message trailer: {err}")
  pure { code := code, message := message? }

end Headers

end Grpc
