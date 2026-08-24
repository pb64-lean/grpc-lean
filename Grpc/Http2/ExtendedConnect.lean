module

public import Std.Async
public import Grpc.Http2.Frame
public import Grpc.Metadata

public section

namespace Grpc
namespace Http2
namespace ExtendedConnect

open Std.Async

/-- A validated extended CONNECT request.  `headers` contains only ordinary
HTTP fields; the five request pseudo-fields are projected into named fields. -/
structure Request where
  protocol : String
  scheme : String
  authority : String
  path : String
  headers : Metadata := #[]
  deriving Inhabited, Repr, DecidableEq

/-- A final extended CONNECT response.  `headers` excludes `:status`. -/
structure Response where
  status : Nat
  headers : Metadata := #[]
  deriving Inhabited, Repr, DecidableEq

/-- A bidirectional byte stream carried by one HTTP/2 stream.

The implementation closures are supplied by the owning HTTP/2 connection.
Applications should use the namespace operations below rather than invoking
the fields directly. -/
structure Tunnel where
  sendBytesImpl : ByteArray → Async (Except Status Unit)
  recvBytesImpl : Async (Except Status (Option ByteArray))
  closeSendImpl : Async (Except Status Unit)
  cancelImpl : Async Unit
  waitImpl : Async (Except Status Unit)

namespace Tunnel

/-- Send bytes in order, waiting for HTTP/2 connection and stream credit. -/
def send (tunnel : Tunnel) (bytes : ByteArray) : Async (Except Status Unit) :=
  tunnel.sendBytesImpl bytes

/-- Receive the next nonempty byte chunk. `none` is the peer's END_STREAM. -/
def recv? (tunnel : Tunnel) : Async (Except Status (Option ByteArray)) :=
  tunnel.recvBytesImpl

/-- Half-close the local side with DATA + END_STREAM. Idempotent. -/
def closeSend (tunnel : Tunnel) : Async (Except Status Unit) :=
  tunnel.closeSendImpl

/-- Abort the stream with RST_STREAM(CANCEL). Idempotent. -/
def cancel (tunnel : Tunnel) : Async Unit :=
  tunnel.cancelImpl

/-- Wait until both halves have ended or a terminal failure is observed. -/
def wait (tunnel : Tunnel) : Async (Except Status Unit) :=
  tunnel.waitImpl

end Tunnel

structure Acceptance where
  status : Nat := 200
  headers : Metadata := #[]
  run : Tunnel → Async Unit

structure Rejection where
  status : Nat
  headers : Metadata := #[]
  deriving Inhabited, Repr, DecidableEq

inductive Decision where
  | accept (value : Acceptance)
  | reject (value : Rejection)

abbrev Handler := Request → Async Decision

inductive OpenResult where
  | accepted (response : Response) (tunnel : Tunnel)
  | rejected (response : Response)

private def singletonPseudo (metadata : Metadata) (name : String) : Except Status String := do
  let values := metadata.getAll name
  if values.size != 1 then
    throw (Status.invalidArgument s!"extended CONNECT requires exactly one {name} pseudo-header")
  pure values[0]!

private def isTokenChar (c : Char) : Bool :=
  let n := c.toNat
  (0x30 <= n && n <= 0x39) || (0x41 <= n && n <= 0x5a) ||
    (0x61 <= n && n <= 0x7a) ||
    c == '!' || c == '#' || c == '$' || c == '%' || c == '&' ||
    c == '\'' || c == '*' || c == '+' || c == '-' || c == '.' || c == '^' ||
    c == '_' || c == '`' || c == '|' || c == '~'

/-- HTTP token syntax used by the `:protocol` pseudo-header. -/
def validProtocolToken (value : String) : Bool :=
  !value.isEmpty && value.all isTokenChar

private def requestPseudoHeader (name : String) : Bool :=
  name == ":method" || name == ":protocol" || name == ":scheme" ||
    name == ":authority" || name == ":path"

private def forbiddenHttp2FieldName (name : String) : Bool :=
  name == "connection" || name == "keep-alive" ||
    name == "proxy-connection" || name == "transfer-encoding" ||
    name == "upgrade"

private def validHttp2FieldName (name : String) : Bool :=
  !name.isEmpty && name.all fun c =>
    c.toLower == c && isTokenChar c

private def httpFieldValueChar (c : Char) : Bool :=
  let n := c.toNat
  n == 0x09 || (0x20 <= n && n != 0x7f)

private def optionalWhitespace (c : Char) : Bool :=
  c == ' ' || c.toNat == 0x09

/-- HTTP field-content permits visible bytes and internal SP/HTAB, but not
control characters or leading/trailing optional whitespace. -/
private def validHttp2FieldValue (value : String) : Bool :=
  value.all httpFieldValueChar &&
    (match value.toList with
    | [] => true
    | first :: rest =>
        !optionalWhitespace first &&
          !(optionalWhitespace (rest.getLastD first)))

private def validateOrdinaryHttp2Header (header : Header) : Except Status Unit := do
  if !validHttp2FieldName header.name then
    throw (Status.invalidArgument s!"invalid HTTP/2 field name {header.name}")
  if forbiddenHttp2FieldName header.name then
    throw (Status.invalidArgument s!"HTTP/2 connection-specific field is forbidden: {header.name}")
  if header.name == "te" && header.value.toLower != "trailers" then
    throw (Status.invalidArgument "HTTP/2 TE field value must be trailers")
  if !validHttp2FieldValue header.value then
    throw (Status.invalidArgument s!"invalid HTTP/2 field value for {header.name}")

private def validateExtendedHeader (header : Header) : Except Status Unit := do
  if header.name.startsWith ":" then
    if !requestPseudoHeader header.name then
      throw (Status.invalidArgument s!"invalid extended CONNECT pseudo-header {header.name}")
    if !validHttp2FieldValue header.value then
      throw (Status.invalidArgument s!"invalid extended CONNECT pseudo-header value for {header.name}")
  else
    validateOrdinaryHttp2Header header

private def ordinaryHeaders (metadata : Metadata) : Metadata :=
  metadata.filter fun header => !header.name.startsWith ":"

/-- Validate and project an RFC 8441-style extended CONNECT request field
section.  This validator deliberately accepts `:protocol` only in this
context; ordinary gRPC request validation remains unchanged. -/
def decodeRequest (metadata : Metadata) : Except Status Request := do
  Metadata.validatePseudoHeaders metadata
  metadata.forM validateExtendedHeader
  let method ← singletonPseudo metadata ":method"
  if method != "CONNECT" then
    throw (Status.invalidArgument "extended CONNECT requires :method CONNECT")
  let protocol ← singletonPseudo metadata ":protocol"
  if !validProtocolToken protocol then
    throw (Status.invalidArgument "extended CONNECT :protocol is not a valid HTTP token")
  let scheme ← singletonPseudo metadata ":scheme"
  if scheme.isEmpty then
    throw (Status.invalidArgument "extended CONNECT :scheme must not be empty")
  let authority ← singletonPseudo metadata ":authority"
  if authority.isEmpty then
    throw (Status.invalidArgument "extended CONNECT :authority must not be empty")
  let path ← singletonPseudo metadata ":path"
  if path.isEmpty then
    throw (Status.invalidArgument "extended CONNECT :path must not be empty")
  pure { protocol, scheme, authority, path, headers := ordinaryHeaders metadata }

private def validateOrdinaryOutbound (kind : String) (metadata : Metadata) : Except Status Unit := do
  for header in metadata do
    if header.name.startsWith ":" then
      throw (Status.invalidArgument s!"{kind} headers must not contain pseudo-header {header.name}")
    validateOrdinaryHttp2Header header

/-- Construct a validated extended CONNECT request field section. -/
def encodeRequest (request : Request) : Except Status Metadata := do
  if !validProtocolToken request.protocol then
    throw (Status.invalidArgument "extended CONNECT :protocol is not a valid HTTP token")
  if request.scheme.isEmpty || request.authority.isEmpty || request.path.isEmpty then
    throw (Status.invalidArgument "extended CONNECT scheme, authority, and path must not be empty")
  validateOrdinaryOutbound "extended CONNECT request" request.headers
  pure <| Metadata.empty
    |>.insert ":method" "CONNECT"
    |>.insert ":protocol" request.protocol
    |>.insert ":scheme" request.scheme
    |>.insert ":authority" request.authority
    |>.insert ":path" request.path
    |>.append request.headers

private def parseStatus (value : String) : Option Nat := do
  if value.utf8ByteSize != 3 then none else pure ()
  let status ← value.toNat?
  if 100 ≤ status && status ≤ 599 then some status else none

/-- Validate and project one HTTP/2 response field section.  Interim response
policy and final-response sequencing are maintained by the connection state. -/
def decodeResponse (metadata : Metadata) : Except Status Response := do
  Metadata.validatePseudoHeaders metadata
  for header in metadata do
    if header.name.startsWith ":" then
      if header.name != ":status" then
        throw (Status.invalidArgument s!"invalid extended CONNECT response pseudo-header {header.name}")
      if !validHttp2FieldValue header.value then
        throw (Status.invalidArgument "invalid extended CONNECT :status value")
    else
      validateOrdinaryHttp2Header header
  let raw ← singletonPseudo metadata ":status"
  let status ← match parseStatus raw with
    | some status => pure status
    | none => throw (Status.invalidArgument s!"invalid HTTP/2 :status {raw}")
  if status == 101 then
    throw (Status.invalidArgument "HTTP/2 responses must not use status 101")
  pure { status, headers := ordinaryHeaders metadata }

/-- Construct a final response field section. -/
def encodeResponse (response : Response) : Except Status Metadata := do
  if response.status < 200 || response.status > 599 then
    throw (Status.invalidArgument "extended CONNECT final response status is outside 200..599")
  validateOrdinaryOutbound "extended CONNECT response" response.headers
  pure <| (Metadata.singleton ":status" (toString response.status)).append response.headers

def isSuccess (response : Response) : Bool :=
  200 ≤ response.status && response.status < 300

end ExtendedConnect
end Http2
end Grpc
