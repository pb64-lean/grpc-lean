module

public import Grpc.Status

public section

namespace Grpc

structure Header where
  name : String
  value : String
  deriving Inhabited, Repr, DecidableEq

abbrev Metadata := Array Header

namespace Header

def normalizeName (name : String) : String :=
  name.toLower

def of (name value : String) : Header :=
  { name := normalizeName name, value := value }

def isBinary (header : Header) : Bool :=
  header.name.endsWith "-bin"

end Header

namespace Metadata

def empty : Metadata := #[]

def insert (metadata : Metadata) (name value : String) : Metadata :=
  metadata.push (Header.of name value)

def singleton (name value : String) : Metadata :=
  empty.insert name value

def getAll (metadata : Metadata) (name : String) : Array String :=
  let key := Header.normalizeName name
  metadata.filterMap fun header =>
    if header.name == key then some header.value else none

def get? (metadata : Metadata) (name : String) : Option String :=
  (getAll metadata name)[0]?

def contains (metadata : Metadata) (name value : String) : Bool :=
  (getAll metadata name).contains value

def append (left right : Metadata) : Metadata :=
  right.foldl (fun acc header => acc.push header) left

def headerListEntrySize (header : Header) : Nat :=
  header.name.toUTF8.size + header.value.toUTF8.size + 32

def headerListSize (metadata : Metadata) : Nat :=
  metadata.foldl (fun total header => total + headerListEntrySize header) 0

def validateHeaderListSize (maxSize? : Option Nat) (metadata : Metadata) : Except Status Unit := do
  match maxSize? with
  | none => pure ()
  | some maxSize =>
      let actual := headerListSize metadata
      if actual > maxSize then
        throw (Status.resourceExhausted s!"HTTP/2 header list exceeds configured size limit {maxSize}")
      else
        pure ()

end Metadata

namespace Ascii

def isLowercaseHeaderNameChar (c : Char) : Bool :=
  c.isLower || c.isDigit || c == '-' || c == '_' || c == '.'

def validHeaderName (name : String) : Bool :=
  !name.isEmpty && name.all isLowercaseHeaderNameChar

def isVisible (c : Char) : Bool :=
  let n := c.toNat
  0x20 <= n && n <= 0x7e

end Ascii

namespace Base64

private def alphabet : Array UInt8 :=
  #[
    65, 66, 67, 68, 69, 70, 71, 72,
    73, 74, 75, 76, 77, 78, 79, 80,
    81, 82, 83, 84, 85, 86, 87, 88,
    89, 90, 97, 98, 99, 100, 101, 102,
    103, 104, 105, 106, 107, 108, 109, 110,
    111, 112, 113, 114, 115, 116, 117, 118,
    119, 120, 121, 122, 48, 49, 50, 51,
    52, 53, 54, 55, 56, 57, 43, 47
  ]

private def alphabetByte (i : Nat) : UInt8 :=
  alphabet[i]!

private def alphabetChar (i : Nat) : Char :=
  Char.ofNat (alphabetByte i).toNat

private def decodeChar? (c : Char) : Option Nat :=
  if 'A' <= c && c <= 'Z' then
    some (c.toNat - 'A'.toNat)
  else if 'a' <= c && c <= 'z' then
    some (26 + (c.toNat - 'a'.toNat))
  else if '0' <= c && c <= '9' then
    some (52 + (c.toNat - '0'.toNat))
  else if c == '+' then
    some 62
  else if c == '/' then
    some 63
  else
    none

private def encodeLoop (bytes : ByteArray) (i : Nat) : List Char :=
  if h : i < bytes.size then
    if h1 : i + 1 < bytes.size then
      if h2 : i + 2 < bytes.size then
        alphabetChar (bytes[i].toNat / 4)
          :: alphabetChar (((bytes[i].toNat % 4) * 16) + (bytes[i + 1].toNat / 16))
          :: alphabetChar (((bytes[i + 1].toNat % 16) * 4) + (bytes[i + 2].toNat / 64))
          :: alphabetChar (bytes[i + 2].toNat % 64)
          :: encodeLoop bytes (i + 3)
      else
        [alphabetChar (bytes[i].toNat / 4),
          alphabetChar (((bytes[i].toNat % 4) * 16) + (bytes[i + 1].toNat / 16)),
          alphabetChar ((bytes[i + 1].toNat % 16) * 4), '=']
    else
      [alphabetChar (bytes[i].toNat / 4), alphabetChar ((bytes[i].toNat % 4) * 16), '=', '=']
  else
    []
  termination_by bytes.size - i
  decreasing_by omega

def encodeBytes (bytes : ByteArray) : String :=
  String.ofList (encodeLoop bytes 0)

private def dropLeadingPadding : List Char -> List Char
  | '=' :: rest => dropLeadingPadding rest
  | chars => chars

def encodeBytesUnpadded (bytes : ByteArray) : String :=
  String.ofList ((dropLeadingPadding (encodeBytes bytes).toList.reverse).reverse)

private def decodeQuad (a b : Nat) (c d : Option Nat) : ByteArray :=
  let byte0 := UInt8.ofNat ((a * 4) + (b / 16))
  match c with
  | none => ByteArray.empty.push byte0
  | some c =>
      let byte1 := UInt8.ofNat (((b % 16) * 16) + (c / 4))
      match d with
      | none => ByteArray.empty.push byte0 |>.push byte1
      | some d =>
          let byte2 := UInt8.ofNat (((c % 4) * 64) + d)
          ByteArray.empty.push byte0 |>.push byte1 |>.push byte2

private def decodeLoop (chars : List Char) (out : ByteArray) : Except String ByteArray :=
  match chars with
  | [] => .ok out
  | a :: b :: c :: d :: rest =>
      match decodeChar? a, decodeChar? b with
      | some va, some vb =>
          let vc? := if c == '=' then none else decodeChar? c
          let vd? := if d == '=' then none else decodeChar? d
          if c == '=' && d != '=' then
            .error "invalid base64 padding"
          else if c != '=' && vc?.isNone then
            .error "invalid base64 character"
          else if d != '=' && vd?.isNone then
            .error "invalid base64 character"
          else if (c == '=' || d == '=') && !rest.isEmpty then
            .error "base64 padding before end"
          else
            decodeLoop rest (out ++ decodeQuad va vb vc? vd?)
      | _, _ => .error "invalid base64 character"
  | _ => .error "base64 length is not a multiple of 4"

private def paddedInput (value : String) : Except String String :=
  match value.toList.length % 4 with
  | 0 => .ok value
  | 2 => .ok (value ++ "==")
  | 3 => .ok (value ++ "=")
  | _ => .error "base64 length is invalid"

def decodeBytes (value : String) : Except String ByteArray := do
  let value ← paddedInput value
  decodeLoop value.toList ByteArray.empty

end Base64

namespace Metadata

private def binaryKey (name : String) : String :=
  let key := Header.normalizeName name
  if key.endsWith "-bin" then key else key ++ "-bin"

def insertBinary (metadata : Metadata) (name : String) (bytes : ByteArray) : Metadata :=
  metadata.insert (binaryKey name) (Base64.encodeBytesUnpadded bytes)

private def binaryValues (value : String) : List String :=
  value.splitOn ","

private def decodeBinaryValue (name value : String) : Except String ByteArray :=
  match Base64.decodeBytes value with
  | .ok bytes => .ok bytes
  | .error err => .error s!"invalid binary gRPC metadata {name}: {err}"

private def decodeBinaryHeaderValue (name value : String) : Except String (Array ByteArray) :=
  (binaryValues value).foldlM (init := #[]) fun values part => do
    pure (values.push (← decodeBinaryValue name part))

def getBinaryAll (metadata : Metadata) (name : String) : Except String (Array ByteArray) :=
  let key := binaryKey name
  (metadata.getAll key).foldlM (init := #[]) fun values value => do
    pure (values.append (← decodeBinaryHeaderValue key value))

def getBinary? (metadata : Metadata) (name : String) : Except String (Option ByteArray) := do
  pure (← metadata.getBinaryAll name)[0]?

private def knownPseudoHeader (name : String) : Bool :=
  name == ":method"
    || name == ":scheme"
    || name == ":path"
    || name == ":authority"
    || name == ":status"

def validHeaderName (name : String) : Bool :=
  if name.startsWith ":" then
    knownPseudoHeader name
  else
    Ascii.validHeaderName name

private def forbiddenHttp2HeaderName (name : String) : Bool :=
  name == "connection"
    || name == "keep-alive"
    || name == "proxy-connection"
    || name == "transfer-encoding"
    || name == "upgrade"

private def validatePseudoHeaders (metadata : Metadata) : Except Status Unit := do
  let _ ← metadata.foldlM (init := (false, (#[] : Array String))) fun state header => do
    let (seenRegular, seenPseudo) := state
    let name := header.name
    if name.startsWith ":" then
      if seenRegular then
        throw (Status.invalidArgument s!"HTTP/2 pseudo-header {name} appeared after regular metadata")
      else if seenPseudo.contains name then
        throw (Status.invalidArgument s!"duplicate HTTP/2 pseudo-header {name}")
      else
        pure (seenRegular, seenPseudo.push name)
    else
      pure (true, seenPseudo)
  pure ()

def validateHeader (header : Header) : Except Status Unit := do
  if !validHeaderName header.name then
    throw (Status.invalidArgument s!"invalid gRPC metadata name {header.name}")
  if forbiddenHttp2HeaderName header.name then
    throw (Status.invalidArgument s!"HTTP/2 connection-specific metadata is forbidden: {header.name}")
  if header.isBinary then
    match decodeBinaryHeaderValue header.name header.value with
    | .ok _ => pure ()
    | .error err => throw (Status.invalidArgument err)
  else if header.value.all Ascii.isVisible then
    pure ()
  else
    throw (Status.invalidArgument s!"invalid ASCII gRPC metadata value for {header.name}")

def validate (metadata : Metadata) : Except Status Unit := do
  validatePseudoHeaders metadata
  metadata.forM validateHeader

end Metadata

end Grpc
