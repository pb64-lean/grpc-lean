module

public import Grpc.Http2.Frame
public import Grpc.Metadata

public section

namespace Grpc
namespace Http2
namespace Hpack

def defaultDynamicTableSize : Nat := 4096

structure State where
  dynamic : Array Header := #[]
  maxSize : Nat := defaultDynamicTableSize
  maxAllowedSize : Nat := defaultDynamicTableSize
  pendingSizeUpdate : Option Nat := none
  deriving Inhabited, Repr

structure IntegerResult where
  value : Nat
  next : Nat
  deriving Inhabited, Repr, DecidableEq

private def prefixMax (prefixBits : Nat) : Nat :=
  (2 ^ prefixBits) - 1

private partial def encodeIntegerRest (value : Nat) (out : ByteArray) : ByteArray :=
  if value >= 128 then
    encodeIntegerRest (value / 128) (out.push (UInt8.ofNat ((value % 128) + 128)))
  else
    out.push (UInt8.ofNat value)

def encodeInteger (prefixBits : Nat) (prefixMask : Nat) (value : Nat) :
    Except Status ByteArray := do
  if prefixBits == 0 || prefixBits > 8 then
    throw (Status.internal "HPACK integer prefix width must be between 1 and 8 bits")
  let max := prefixMax prefixBits
  if value < max then
    pure (ByteArray.empty.push (UInt8.ofNat (prefixMask + value)))
  else
    pure (encodeIntegerRest (value - max) (ByteArray.empty.push (UInt8.ofNat (prefixMask + max))))

private partial def decodeIntegerRest (bytes : ByteArray) (offset value shift : Nat) :
    Except Status IntegerResult := do
  if offset >= bytes.size then
    throw (Status.internal "truncated HPACK integer")
  let byte := bytes[offset]!.toNat
  let value := value + ((byte % 128) * (2 ^ shift))
  if byte < 128 then
    pure { value := value, next := offset + 1 }
  else
    decodeIntegerRest bytes (offset + 1) value (shift + 7)

def decodeInteger (prefixBits : Nat) (bytes : ByteArray) (offset : Nat) :
    Except Status IntegerResult := do
  if prefixBits == 0 || prefixBits > 8 then
    throw (Status.internal "HPACK integer prefix width must be between 1 and 8 bits")
  if offset >= bytes.size then
    throw (Status.internal "missing HPACK integer")
  let max := prefixMax prefixBits
  let value := bytes[offset]!.toNat % (2 ^ prefixBits)
  if value < max then
    pure { value := value, next := offset + 1 }
  else
    decodeIntegerRest bytes (offset + 1) max 0

structure StringResult where
  value : String
  next : Nat
  deriving Inhabited, Repr, DecidableEq

private def huffmanEOSSymbol : Nat := 256

private def huffmanCodes : Array Nat := #[
  0x1ff8, 0x7fffd8, 0xfffffe2, 0xfffffe3, 0xfffffe4, 0xfffffe5, 0xfffffe6, 0xfffffe7,
  0xfffffe8, 0xffffea, 0x3ffffffc, 0xfffffe9, 0xfffffea, 0x3ffffffd, 0xfffffeb, 0xfffffec,
  0xfffffed, 0xfffffee, 0xfffffef, 0xffffff0, 0xffffff1, 0xffffff2, 0x3ffffffe, 0xffffff3,
  0xffffff4, 0xffffff5, 0xffffff6, 0xffffff7, 0xffffff8, 0xffffff9, 0xffffffa, 0xffffffb,
  0x14, 0x3f8, 0x3f9, 0xffa, 0x1ff9, 0x15, 0xf8, 0x7fa,
  0x3fa, 0x3fb, 0xf9, 0x7fb, 0xfa, 0x16, 0x17, 0x18,
  0x0, 0x1, 0x2, 0x19, 0x1a, 0x1b, 0x1c, 0x1d,
  0x1e, 0x1f, 0x5c, 0xfb, 0x7ffc, 0x20, 0xffb, 0x3fc,
  0x1ffa, 0x21, 0x5d, 0x5e, 0x5f, 0x60, 0x61, 0x62,
  0x63, 0x64, 0x65, 0x66, 0x67, 0x68, 0x69, 0x6a,
  0x6b, 0x6c, 0x6d, 0x6e, 0x6f, 0x70, 0x71, 0x72,
  0xfc, 0x73, 0xfd, 0x1ffb, 0x7fff0, 0x1ffc, 0x3ffc, 0x22,
  0x7ffd, 0x3, 0x23, 0x4, 0x24, 0x5, 0x25, 0x26,
  0x27, 0x6, 0x74, 0x75, 0x28, 0x29, 0x2a, 0x7,
  0x2b, 0x76, 0x2c, 0x8, 0x9, 0x2d, 0x77, 0x78,
  0x79, 0x7a, 0x7b, 0x7ffe, 0x7fc, 0x3ffd, 0x1ffd, 0xffffffc,
  0xfffe6, 0x3fffd2, 0xfffe7, 0xfffe8, 0x3fffd3, 0x3fffd4, 0x3fffd5, 0x7fffd9,
  0x3fffd6, 0x7fffda, 0x7fffdb, 0x7fffdc, 0x7fffdd, 0x7fffde, 0xffffeb, 0x7fffdf,
  0xffffec, 0xffffed, 0x3fffd7, 0x7fffe0, 0xffffee, 0x7fffe1, 0x7fffe2, 0x7fffe3,
  0x7fffe4, 0x1fffdc, 0x3fffd8, 0x7fffe5, 0x3fffd9, 0x7fffe6, 0x7fffe7, 0xffffef,
  0x3fffda, 0x1fffdd, 0xfffe9, 0x3fffdb, 0x3fffdc, 0x7fffe8, 0x7fffe9, 0x1fffde,
  0x7fffea, 0x3fffdd, 0x3fffde, 0xfffff0, 0x1fffdf, 0x3fffdf, 0x7fffeb, 0x7fffec,
  0x1fffe0, 0x1fffe1, 0x3fffe0, 0x1fffe2, 0x7fffed, 0x3fffe1, 0x7fffee, 0x7fffef,
  0xfffea, 0x3fffe2, 0x3fffe3, 0x3fffe4, 0x7ffff0, 0x3fffe5, 0x3fffe6, 0x7ffff1,
  0x3ffffe0, 0x3ffffe1, 0xfffeb, 0x7fff1, 0x3fffe7, 0x7ffff2, 0x3fffe8, 0x1ffffec,
  0x3ffffe2, 0x3ffffe3, 0x3ffffe4, 0x7ffffde, 0x7ffffdf, 0x3ffffe5, 0xfffff1, 0x1ffffed,
  0x7fff2, 0x1fffe3, 0x3ffffe6, 0x7ffffe0, 0x7ffffe1, 0x3ffffe7, 0x7ffffe2, 0xfffff2,
  0x1fffe4, 0x1fffe5, 0x3ffffe8, 0x3ffffe9, 0xffffffd, 0x7ffffe3, 0x7ffffe4, 0x7ffffe5,
  0xfffec, 0xfffff3, 0xfffed, 0x1fffe6, 0x3fffe9, 0x1fffe7, 0x1fffe8, 0x7ffff3,
  0x3fffea, 0x3fffeb, 0x1ffffee, 0x1ffffef, 0xfffff4, 0xfffff5, 0x3ffffea, 0x7ffff4,
  0x3ffffeb, 0x7ffffe6, 0x3ffffec, 0x3ffffed, 0x7ffffe7, 0x7ffffe8, 0x7ffffe9, 0x7ffffea,
  0x7ffffeb, 0xffffffe, 0x7ffffec, 0x7ffffed, 0x7ffffee, 0x7ffffef, 0x7fffff0, 0x3ffffee,
  0x3fffffff
]

private def huffmanCodeLengths : Array Nat := #[
  13, 23, 28, 28, 28, 28, 28, 28, 28, 24, 30, 28, 28, 30, 28, 28,
  28, 28, 28, 28, 28, 28, 30, 28, 28, 28, 28, 28, 28, 28, 28, 28,
  6, 10, 10, 12, 13, 6, 8, 11, 10, 10, 8, 11, 8, 6, 6, 6,
  5, 5, 5, 6, 6, 6, 6, 6, 6, 6, 7, 8, 15, 6, 12, 10,
  13, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 7, 7, 7, 7, 7, 8, 7, 8, 13, 19, 13, 14, 6,
  15, 5, 6, 5, 6, 5, 6, 6, 6, 5, 7, 7, 6, 6, 6, 5,
  6, 7, 6, 5, 5, 6, 7, 7, 7, 7, 7, 15, 11, 14, 13, 28,
  20, 22, 20, 20, 22, 22, 22, 23, 22, 23, 23, 23, 23, 23, 24, 23,
  24, 24, 22, 23, 24, 23, 23, 23, 23, 21, 22, 23, 22, 23, 23, 24,
  22, 21, 20, 22, 22, 23, 23, 21, 23, 22, 22, 24, 21, 22, 23, 23,
  21, 21, 22, 21, 23, 22, 23, 23, 20, 22, 22, 22, 23, 22, 22, 23,
  26, 26, 20, 19, 22, 23, 22, 25, 26, 26, 26, 27, 27, 26, 24, 25,
  19, 21, 26, 27, 27, 26, 27, 24, 21, 21, 26, 26, 28, 27, 27, 27,
  20, 24, 20, 21, 22, 21, 21, 23, 22, 22, 25, 25, 24, 24, 26, 23,
  26, 27, 26, 26, 27, 27, 27, 27, 27, 28, 27, 27, 27, 27, 27, 26,
  30
]

private partial def findHuffmanSymbol? (code bits i : Nat) : Option Nat :=
  if i >= huffmanCodes.size then
    none
  else if huffmanCodes[i]! == code && huffmanCodeLengths[i]! == bits then
    some i
  else
    findHuffmanSymbol? code bits (i + 1)

private def bitAt (byte : UInt8) (bit : Nat) : Nat :=
  (byte.toNat / (2 ^ bit)) % 2

private def validHuffmanPadding (code bits : Nat) : Bool :=
  bits == 0 || (bits <= 7 && code == prefixMax bits)

private partial def decodeHuffmanBits
    (bytes : ByteArray) (offset bit code bits : Nat) (out : ByteArray) :
    Except Status ByteArray := do
  if offset >= bytes.size then
    if validHuffmanPadding code bits then
      pure out
    else
      throw (Status.internal "invalid HPACK Huffman padding")
  else
    let b := bitAt bytes[offset]! bit
    let code := code * 2 + b
    let bits := bits + 1
    let (code, bits, out) ←
      match findHuffmanSymbol? code bits 0 with
      | some symbol =>
          if symbol == huffmanEOSSymbol then
            throw (Status.internal "HPACK Huffman EOS appeared in data")
          else
            pure (0, 0, out.push (UInt8.ofNat symbol))
      | none =>
          if bits > 30 then
            throw (Status.internal "invalid HPACK Huffman code")
          else
            pure (code, bits, out)
    if bit == 0 then
      decodeHuffmanBits bytes (offset + 1) 7 code bits out
    else
      decodeHuffmanBits bytes offset (bit - 1) code bits out

def decodeHuffman (bytes : ByteArray) : Except Status ByteArray :=
  decodeHuffmanBits bytes 0 7 0 0 ByteArray.empty

private partial def encodeHuffmanFlush (acc bits : Nat) (out : ByteArray) : Nat × Nat × ByteArray :=
  if bits >= 8 then
    let shift := bits - 8
    encodeHuffmanFlush (acc % (2 ^ shift)) shift (out.push (UInt8.ofNat (acc / (2 ^ shift))))
  else
    (acc, bits, out)

def encodeHuffman (bytes : ByteArray) : ByteArray :=
  let (acc, bits, out) := bytes.foldl
    (init := ((0 : Nat), (0 : Nat), ByteArray.empty))
    fun (acc, bits, out) byte =>
      let code := huffmanCodes[byte.toNat]!
      let len := huffmanCodeLengths[byte.toNat]!
      encodeHuffmanFlush (acc * (2 ^ len) + code) (bits + len) out
  if bits == 0 then
    out
  else
    let pad := 8 - bits
    out.push (UInt8.ofNat (acc * (2 ^ pad) + (prefixMax pad)))

/-- Values larger than this are emitted raw: Huffman coding of very large
values costs CPU for little relative gain, and header fields this large are
dominated by frame overhead anyway. -/
def huffmanMaxEncodeLength : Nat := 1024

def encodeString (value : String) : Except Status ByteArray := do
  let bytes := value.toUTF8
  let huffman :=
    if bytes.size <= huffmanMaxEncodeLength then encodeHuffman bytes else bytes
  if huffman.size < bytes.size then
    let prefixBytes ← encodeInteger 7 128 huffman.size
    pure (prefixBytes.append huffman)
  else
    let prefixBytes ← encodeInteger 7 0 bytes.size
    pure (prefixBytes.append bytes)

def decodeString (bytes : ByteArray) (offset : Nat) : Except Status StringResult := do
  if offset >= bytes.size then
    throw (Status.internal "missing HPACK string")
  let huffman := bytes[offset]!.toNat >= 128
  let length ← decodeInteger 7 bytes offset
  let endPos := length.next + length.value
  if endPos > bytes.size then
    throw (Status.internal "truncated HPACK string")
  let raw := bytes.extract length.next endPos
  let raw ← if huffman then decodeHuffman raw else pure raw
  match String.fromUTF8? raw with
  | some decoded => pure { value := decoded, next := endPos }
  | none => throw (Status.internal "HPACK string is not valid UTF-8")

def staticEntries : Array Header :=
  #[
    Header.of ":authority" "",
    Header.of ":method" "GET",
    Header.of ":method" "POST",
    Header.of ":path" "/",
    Header.of ":path" "/index.html",
    Header.of ":scheme" "http",
    Header.of ":scheme" "https",
    Header.of ":status" "200",
    Header.of ":status" "204",
    Header.of ":status" "206",
    Header.of ":status" "304",
    Header.of ":status" "400",
    Header.of ":status" "404",
    Header.of ":status" "500",
    Header.of "accept-charset" "",
    Header.of "accept-encoding" "gzip, deflate",
    Header.of "accept-language" "",
    Header.of "accept-ranges" "",
    Header.of "accept" "",
    Header.of "access-control-allow-origin" "",
    Header.of "age" "",
    Header.of "allow" "",
    Header.of "authorization" "",
    Header.of "cache-control" "",
    Header.of "content-disposition" "",
    Header.of "content-encoding" "",
    Header.of "content-language" "",
    Header.of "content-length" "",
    Header.of "content-location" "",
    Header.of "content-range" "",
    Header.of "content-type" "",
    Header.of "cookie" "",
    Header.of "date" "",
    Header.of "etag" "",
    Header.of "expect" "",
    Header.of "expires" "",
    Header.of "from" "",
    Header.of "host" "",
    Header.of "if-match" "",
    Header.of "if-modified-since" "",
    Header.of "if-none-match" "",
    Header.of "if-range" "",
    Header.of "if-unmodified-since" "",
    Header.of "last-modified" "",
    Header.of "link" "",
    Header.of "location" "",
    Header.of "max-forwards" "",
    Header.of "proxy-authenticate" "",
    Header.of "proxy-authorization" "",
    Header.of "range" "",
    Header.of "referer" "",
    Header.of "refresh" "",
    Header.of "retry-after" "",
    Header.of "server" "",
    Header.of "set-cookie" "",
    Header.of "strict-transport-security" "",
    Header.of "transfer-encoding" "",
    Header.of "user-agent" "",
    Header.of "vary" "",
    Header.of "via" "",
    Header.of "www-authenticate" ""
  ]

def staticTableSize : Nat :=
  staticEntries.size

def entrySize (header : Header) : Nat :=
  header.name.toUTF8.size + header.value.toUTF8.size + 32

def dynamicSize (entries : Array Header) : Nat :=
  entries.foldl (fun size header => size + entrySize header) 0

private partial def evictTo (maxSize : Nat) (entries : Array Header) : Array Header :=
  if dynamicSize entries <= maxSize then
    entries
  else if entries.isEmpty then
    entries
  else
    evictTo maxSize entries.pop

private def prepend (header : Header) (entries : Array Header) : Array Header :=
  entries.foldl (fun acc entry => acc.push entry) #[header]

def resize (state : State) (maxSize : Nat) : State :=
  { state with maxSize := maxSize, dynamic := evictTo maxSize state.dynamic }

def setMaxAllowedSize (state : State) (maxSize : Nat) : State :=
  let pending := if maxSize != state.maxSize then some maxSize else state.pendingSizeUpdate
  { (resize state maxSize) with maxAllowedSize := maxSize, pendingSizeUpdate := pending }

def resizeChecked (state : State) (maxSize : Nat) : Except Status State := do
  if maxSize > state.maxAllowedSize then
    throw (Status.internal s!"HPACK dynamic table size update exceeds configured maximum {state.maxAllowedSize}")
  else
    pure (resize state maxSize)

def insert (state : State) (header : Header) : State :=
  if entrySize header > state.maxSize then
    { state with dynamic := #[] }
  else
    { state with dynamic := evictTo state.maxSize (prepend header state.dynamic) }

def get? (state : State) (index : Nat) : Option Header :=
  if index == 0 then
    none
  else if index <= staticEntries.size then
    staticEntries[index - 1]?
  else
    state.dynamic[index - staticEntries.size - 1]?

private partial def findExactIn (entries : Array Header) (header : Header) (i start : Nat) : Option Nat :=
  if i >= entries.size then
    none
  else
    let entry := entries[i]!
    if entry.name == header.name && entry.value == header.value then
      some (start + i)
    else
      findExactIn entries header (i + 1) start

private partial def findNameIn (entries : Array Header) (name : String) (i start : Nat) : Option Nat :=
  if i >= entries.size then
    none
  else
    let entry := entries[i]!
    if entry.name == Header.normalizeName name then
      some (start + i)
    else
      findNameIn entries name (i + 1) start

def findExact? (state : State) (header : Header) : Option Nat :=
  match findExactIn staticEntries header 0 1 with
  | some index => some index
  | none => findExactIn state.dynamic header 0 (staticEntries.size + 1)

def findName? (state : State) (name : String) : Option Nat :=
  match findNameIn staticEntries name 0 1 with
  | some index => some index
  | none => findNameIn state.dynamic name 0 (staticEntries.size + 1)

structure DecodeResult where
  headers : Array Header
  state : State

private def decodeLiteralName (state : State) (index : Nat) (block : ByteArray) (offset : Nat) :
    Except Status (String × Nat) := do
  if index == 0 then
    let name ← decodeString block offset
    if Header.normalizeName name.value != name.value then
      throw (Status.internal s!"HTTP/2 header field name must be lowercase: {name.value}")
    else
      pure (name.value, name.next)
  else
    match get? state index with
    | some header => pure (header.name, offset)
    | none => throw (Status.internal s!"unknown HPACK name index {index}")

private def decodeLiteral (state : State) (block : ByteArray) (offset prefixBits : Nat)
    (incremental : Bool) : Except Status (Header × State × Nat) := do
  let index ← decodeInteger prefixBits block offset
  let (name, next) ← decodeLiteralName state index.value block index.next
  let value ← decodeString block next
  let header : Header := { name := name, value := value.value }
  let state := if incremental then insert state header else state
  pure (header, state, value.next)

private partial def decodeLoop (block : ByteArray) (offset : Nat) (state : State)
    (headers : Array Header) (sawHeader : Bool) : Except Status DecodeResult := do
  if offset >= block.size then
    pure { headers := headers, state := state }
  else
    let byte := block[offset]!.toNat
    if byte >= 128 then
      let index ← decodeInteger 7 block offset
      match get? state index.value with
      | some header => decodeLoop block index.next state (headers.push header) true
      | none => throw (Status.internal s!"unknown HPACK header index {index.value}")
    else if byte >= 64 then
      let (header, state, next) ← decodeLiteral state block offset 6 true
      decodeLoop block next state (headers.push header) true
    else if byte >= 32 then
      if sawHeader then
        throw (Status.internal "HPACK dynamic table size update must precede header fields")
      let size ← decodeInteger 5 block offset
      let state ← resizeChecked state size.value
      decodeLoop block size.next state headers false
    else if byte >= 16 then
      let (header, state, next) ← decodeLiteral state block offset 4 false
      decodeLoop block next state (headers.push header) true
    else
      let (header, state, next) ← decodeLiteral state block offset 4 false
      decodeLoop block next state (headers.push header) true

def decodeHeaderBlock (state : State) (block : ByteArray) : Except Status DecodeResult :=
  decodeLoop block 0 state #[] false

private def encodeIndexed (index : Nat) : Except Status ByteArray :=
  if index == 0 then
    throw (Status.internal "HPACK index 0 is invalid")
  else
    encodeInteger 7 128 index

private def encodeLiteralNameAndValue (state : State) (header : Header) (prefixBits prefixMask : Nat) :
    Except Status ByteArray := do
  match findName? state header.name with
  | some index =>
      let prefixBytes ← encodeInteger prefixBits prefixMask index
      let value ← encodeString header.value
      pure (prefixBytes.append value)
  | none =>
      let prefixBytes ← encodeInteger prefixBits prefixMask 0
      let name ← encodeString header.name
      let value ← encodeString header.value
      pure (prefixBytes.append name |>.append value)

def encodeLiteralWithoutIndexing (state : State) (header : Header) : Except Status ByteArray :=
  encodeLiteralNameAndValue state header 4 0

/--
Encode a header using HPACK's "never indexed" literal representation.

Unlike ordinary non-indexed literals, this representation tells every
intermediary that the field is sensitive and must not be inserted into a
dynamic table while forwarding the block.
-/
def encodeLiteralNeverIndexed (state : State) (header : Header) : Except Status ByteArray :=
  encodeLiteralNameAndValue state header 4 16

def encodeLiteralWithIndexing (state : State) (header : Header) : Except Status (ByteArray × State) := do
  let bytes ← encodeLiteralNameAndValue state header 6 64
  pure (bytes, insert state header)

private def mustNeverIndex (header : Header) : Bool :=
  let name := Header.normalizeName header.name
  name == "authorization" || name == "proxy-authorization"

def encodeHeader (state : State) (header : Header) : Except Status (ByteArray × State) := do
  if mustNeverIndex header then
    pure (← encodeLiteralNeverIndexed state header, state)
  else
    match findExact? state header with
    | some index => do
        let bytes ← encodeIndexed index
        pure (bytes, state)
    | none => encodeLiteralWithIndexing state header

def encodeHeaderBlock (state : State) (headers : Array Header) : Except Status (ByteArray × State) := do
  let (out, state) ←
    match state.pendingSizeUpdate with
    | some size => do
        let update ← encodeInteger 5 32 size
        pure (update, { state with pendingSizeUpdate := none })
    | none => pure (ByteArray.empty, state)
  headers.foldlM (init := (out, state)) fun (out, state) header => do
    let (encoded, state) ← encodeHeader state header
    pure (out.append encoded, state)

end Hpack
end Http2
end Grpc
