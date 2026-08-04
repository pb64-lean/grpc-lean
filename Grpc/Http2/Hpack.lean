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

private def encodeIntegerRest (value : Nat) (out : ByteArray) : ByteArray :=
  if value >= 128 then
    encodeIntegerRest (value / 128) (out.push (UInt8.ofNat ((value % 128) + 128)))
  else
    out.push (UInt8.ofNat value)
  termination_by value
  decreasing_by omega

def encodeInteger (prefixBits : Nat) (prefixMask : Nat) (value : Nat) :
    Except Status ByteArray :=
  if prefixBits == 0 || prefixBits > 8 then
    .error (Status.internal "HPACK integer prefix width must be between 1 and 8 bits")
  else if value < prefixMax prefixBits then
    .ok (ByteArray.empty.push (UInt8.ofNat (prefixMask + value)))
  else
    .ok (encodeIntegerRest (value - prefixMax prefixBits)
      (ByteArray.empty.push (UInt8.ofNat (prefixMask + prefixMax prefixBits))))

private def decodeIntegerRest (bytes : ByteArray) (offset value shift : Nat) :
    Except Status IntegerResult :=
  if offset >= bytes.size then
    .error (Status.internal "truncated HPACK integer")
  else if bytes[offset]!.toNat < 128 then
    .ok { value := value + ((bytes[offset]!.toNat % 128) * (2 ^ shift)), next := offset + 1 }
  else
    decodeIntegerRest bytes (offset + 1)
      (value + ((bytes[offset]!.toNat % 128) * (2 ^ shift))) (shift + 7)
  termination_by bytes.size - offset
  decreasing_by omega

def decodeInteger (prefixBits : Nat) (bytes : ByteArray) (offset : Nat) :
    Except Status IntegerResult :=
  if prefixBits == 0 || prefixBits > 8 then
    .error (Status.internal "HPACK integer prefix width must be between 1 and 8 bits")
  else if offset >= bytes.size then
    .error (Status.internal "missing HPACK integer")
  else if bytes[offset]!.toNat % (2 ^ prefixBits) < prefixMax prefixBits then
    .ok { value := bytes[offset]!.toNat % (2 ^ prefixBits), next := offset + 1 }
  else
    decodeIntegerRest bytes (offset + 1) (prefixMax prefixBits) 0

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

private def findHuffmanSymbol? (code bits i : Nat) : Option Nat :=
  if i >= huffmanCodes.size then
    none
  else if huffmanCodes[i]! == code && huffmanCodeLengths[i]! == bits then
    some i
  else
    findHuffmanSymbol? code bits (i + 1)
  termination_by huffmanCodes.size - i
  decreasing_by omega

private def bitAt (byte : UInt8) (bit : Nat) : Nat :=
  (byte.toNat / (2 ^ bit)) % 2

private def validHuffmanPadding (code bits : Nat) : Bool :=
  bits == 0 || (bits <= 7 && code == prefixMax bits)

set_option maxRecDepth 4096 in
private def decodeHuffmanBits
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
    if bit = 0 then
      decodeHuffmanBits bytes (offset + 1) 7 code bits out
    else
      decodeHuffmanBits bytes offset (bit - 1) code bits out
  termination_by (bytes.size - offset) * 8 + bit
  decreasing_by
    · omega
    · omega

def decodeHuffman (bytes : ByteArray) : Except Status ByteArray :=
  decodeHuffmanBits bytes 0 7 0 0 ByteArray.empty

private def encodeHuffmanFlush (acc bits : Nat) (out : ByteArray) : Nat × Nat × ByteArray :=
  if bits >= 8 then
    encodeHuffmanFlush (acc % (2 ^ (bits - 8))) (bits - 8)
      (out.push (UInt8.ofNat (acc / (2 ^ (bits - 8)))))
  else
    (acc, bits, out)
  termination_by bits
  decreasing_by omega

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

def encodeString (value : String) : Except Status ByteArray :=
  let bytes := value.toUTF8
  let huffman :=
    if bytes.size <= huffmanMaxEncodeLength then encodeHuffman bytes else bytes
  if huffman.size < bytes.size then
    match encodeInteger 7 128 huffman.size with
    | .error status => .error status
    | .ok prefixBytes => .ok (prefixBytes.append huffman)
  else
    match encodeInteger 7 0 bytes.size with
    | .error status => .error status
    | .ok prefixBytes => .ok (prefixBytes.append bytes)

def decodeString (bytes : ByteArray) (offset : Nat) : Except Status StringResult :=
  if offset >= bytes.size then
    .error (Status.internal "missing HPACK string")
  else
    match decodeInteger 7 bytes offset with
    | .error status => .error status
    | .ok length =>
        if length.next + length.value > bytes.size then
          .error (Status.internal "truncated HPACK string")
        else
          match (if bytes[offset]!.toNat >= 128 then
              decodeHuffman (bytes.extract length.next (length.next + length.value))
            else
              .ok (bytes.extract length.next (length.next + length.value))) with
          | .error status => .error status
          | .ok raw =>
              match String.fromUTF8? raw with
              | some decoded => .ok { value := decoded, next := length.next + length.value }
              | none => .error (Status.internal "HPACK string is not valid UTF-8")

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

private def evictTo (maxSize : Nat) (entries : Array Header) : Array Header :=
  if dynamicSize entries <= maxSize then
    entries
  else if hempty : entries.isEmpty then
    entries
  else
    evictTo maxSize entries.pop
  termination_by entries.size
  decreasing_by
    simp only [Array.isEmpty, decide_eq_true_eq] at hempty
    simp only [Array.size_pop]
    omega

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

private def findExactIn (entries : Array Header) (header : Header) (i start : Nat) : Option Nat :=
  if i >= entries.size then
    none
  else
    let entry := entries[i]!
    if entry.name == header.name && entry.value == header.value then
      some (start + i)
    else
      findExactIn entries header (i + 1) start
  termination_by entries.size - i
  decreasing_by omega

private def findNameIn (entries : Array Header) (name : String) (i start : Nat) : Option Nat :=
  if i >= entries.size then
    none
  else
    let entry := entries[i]!
    if entry.name == Header.normalizeName name then
      some (start + i)
    else
      findNameIn entries name (i + 1) start
  termination_by entries.size - i
  decreasing_by omega

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

/-!
### Codec laws

* `decodeInteger_encodeInteger` — HPACK integer roundtrip with residual
  bytes: decoding `encodeInteger prefixBits prefixMask value ++ rest` at
  offset 0 recovers `value` and stops exactly at the encoded length, for any
  prefix mask that leaves the low `prefixBits` bits clear and fits with the
  filled prefix in one byte (every call site in this file satisfies both).
* `dynamicSize_resize_le` / `dynamicSize_insert_le` /
  `dynamicSize_resizeChecked_le` / `dynamicSize_setMaxAllowedSize_le` — the
  dynamic-table size invariant: after any resize, insert, or checked resize
  the accounted table size (RFC 7541 §4.1: name + value bytes + 32 per
  entry) never exceeds the applicable maximum.
* `huffmanPrefixFree` — the fixed 257-entry Huffman table is prefix-free
  (`huffmanPrefixFreeCheck` spells out the pairwise bit-prefix test).
-/

private theorem getElem_push_eq (a : ByteArray) (x : UInt8)
    {h : a.size < (a.push x).size} : (a.push x)[a.size] = x := by
  rcases a with ⟨data⟩
  show (Array.push data x)[data.size] = x
  exact Array.getElem_push_eq ..

private theorem getElem_push_lt (a : ByteArray) (x : UInt8) (i : Nat) (hi : i < a.size)
    {h : i < (a.push x).size} : (a.push x)[i] = a[i] := by
  rcases a with ⟨data⟩
  show (Array.push data x)[i] = data[i]
  exact Array.getElem_push_lt hi

private theorem encodeIntegerRest_size_lt (value : Nat) (out : ByteArray) :
    out.size < (encodeIntegerRest value out).size := by
  fun_induction encodeIntegerRest value out
  next value out h ih =>
    have hpush : (out.push (UInt8.ofNat (value % 128 + 128))).size = out.size + 1 :=
      ByteArray.size_push
    omega
  next value out h =>
    simp [ByteArray.size_push]

private theorem encodeIntegerRest_getElem_prefix (value : Nat) (out : ByteArray) :
    ∀ (i : Nat) (hi : i < out.size),
      ∀ {h : i < (encodeIntegerRest value out).size},
        (encodeIntegerRest value out)[i] = out[i]'hi := by
  fun_induction encodeIntegerRest value out
  next value out hge ih =>
    intro i hi h
    have hpush : (out.push (UInt8.ofNat (value % 128 + 128))).size = out.size + 1 :=
      ByteArray.size_push
    have step := ih i (by omega) (h := h)
    rw [step, getElem_push_lt _ _ _ hi]
  next value out hlt =>
    intro i hi h
    exact getElem_push_lt _ _ _ hi

/-- Decoding the continuation bytes emitted by `encodeIntegerRest` recovers
the encoded value scaled into the accumulator, and stops exactly at the end
of the emitted bytes. -/
private theorem decodeIntegerRest_encodeIntegerRest (value : Nat) (out : ByteArray) :
    ∀ (rest : ByteArray) (base shift : Nat),
      decodeIntegerRest (encodeIntegerRest value out ++ rest) out.size base shift
        = .ok { value := base + value * 2 ^ shift,
                next := (encodeIntegerRest value out).size } := by
  fun_induction encodeIntegerRest value out
  next value out hge ih =>
    intro rest base shift
    have hb : UInt8.ofNat (value % 128 + 128) = UInt8.ofNat (value % 128 + 128) := rfl
    generalize hbdef : UInt8.ofNat (value % 128 + 128) = b at *
    have hpush : (out.push b).size = out.size + 1 := ByteArray.size_push
    have hsize : (out.push b).size < (encodeIntegerRest (value / 128) (out.push b)).size :=
      encodeIntegerRest_size_lt ..
    have happsz : (encodeIntegerRest (value / 128) (out.push b) ++ rest).size
        = (encodeIntegerRest (value / 128) (out.push b)).size + rest.size :=
      ByteArray.size_append
    have hbyte : (encodeIntegerRest (value / 128) (out.push b) ++ rest)[out.size]!
        = b := by
      rw [getElem!_pos (encodeIntegerRest (value / 128) (out.push b) ++ rest) out.size
        (by omega)]
      rw [ByteArray.getElem_append_left (by omega)]
      rw [encodeIntegerRest_getElem_prefix (value / 128) (out.push b) out.size (by omega)]
      exact getElem_push_eq ..
    have hbn : b.toNat = value % 128 + 128 := by
      rw [← hbdef]
      simp only [UInt8.toNat_ofNat', Nat.reducePow]
      omega
    rw [decodeIntegerRest.eq_def]
    rw [if_neg (by omega)]
    rw [hbyte]
    rw [if_neg (by omega)]
    have hmod : (b.toNat % 128) = value % 128 := by omega
    rw [hmod]
    have hoff : out.size + 1 = (out.push b).size := hpush.symm
    rw [hoff, ih rest (base + value % 128 * 2 ^ shift) (shift + 7)]
    have harith : base + value % 128 * 2 ^ shift + value / 128 * 2 ^ (shift + 7)
        = base + value * 2 ^ shift := by
      rw [Nat.pow_add]
      have h1 : value / 128 * (2 ^ shift * 2 ^ 7) = value / 128 * 2 ^ 7 * 2 ^ shift := by
        rw [Nat.mul_comm (2 ^ shift) (2 ^ 7), ← Nat.mul_assoc]
      rw [h1, Nat.add_assoc, ← Nat.add_mul]
      have h2 : value % 128 + value / 128 * 2 ^ 7 = value := by
        simp only [Nat.reducePow]
        omega
      rw [h2]
    rw [harith]
  next value out hlt =>
    intro rest base shift
    generalize hbdef : UInt8.ofNat value = b at *
    have hpush : (out.push b).size = out.size + 1 := ByteArray.size_push
    have happsz : (out.push b ++ rest).size = (out.push b).size + rest.size :=
      ByteArray.size_append
    have hbyte : (out.push b ++ rest)[out.size]! = b := by
      rw [getElem!_pos (out.push b ++ rest) out.size (by omega)]
      rw [ByteArray.getElem_append_left (by omega)]
      exact getElem_push_eq ..
    have hbn : b.toNat = value := by
      rw [← hbdef]
      simp only [UInt8.toNat_ofNat', Nat.reducePow]
      omega
    rw [decodeIntegerRest.eq_def]
    rw [if_neg (by omega)]
    rw [hbyte]
    rw [if_pos (by omega)]
    have hmod : (b.toNat % 128) = value := by omega
    rw [hmod, hpush.symm]

/-- HPACK integer roundtrip with residual bytes: decoding
`encodeInteger prefixBits prefixMask value ++ rest` at offset 0 recovers
`value` and stops exactly at the end of the encoded bytes. The mask must
leave the low `prefixBits` bits clear and fit in one byte together with the
filled prefix; every encoder call site in this file satisfies both. -/
theorem decodeInteger_encodeInteger {prefixBits prefixMask value : Nat}
    {encoded : ByteArray}
    (hmask : prefixMask % 2 ^ prefixBits = 0)
    (hfits : prefixMask + 2 ^ prefixBits ≤ 256)
    (henc : encodeInteger prefixBits prefixMask value = .ok encoded)
    (rest : ByteArray) :
    decodeInteger prefixBits (encoded ++ rest) 0
      = .ok { value := value, next := encoded.size } := by
  have hpm : prefixMax prefixBits = 2 ^ prefixBits - 1 := rfl
  have hpow : 0 < 2 ^ prefixBits := Nat.two_pow_pos prefixBits
  unfold encodeInteger at henc
  split at henc
  next => cases henc
  next hguard =>
    split at henc
    next hsmall =>
      cases henc
      have hlt : prefixMask + value < 256 := by omega
      have hb : (ByteArray.empty.push (UInt8.ofNat (prefixMask + value))).size = 1 := rfl
      have happsz : (ByteArray.empty.push (UInt8.ofNat (prefixMask + value)) ++ rest).size
          = 1 + rest.size := by
        rw [ByteArray.size_append, hb]
      have hbyte : (ByteArray.empty.push (UInt8.ofNat (prefixMask + value)) ++ rest)[(0 : Nat)]!
          = UInt8.ofNat (prefixMask + value) := by
        rw [getElem!_pos _ _ (by omega)]
        rw [ByteArray.getElem_append_left (by omega)]
        rfl
      have hbn : (UInt8.ofNat (prefixMask + value)).toNat = prefixMask + value := by
        simp only [UInt8.toNat_ofNat', Nat.reducePow]
        omega
      have hmod : (prefixMask + value) % 2 ^ prefixBits = value := by
        rw [Nat.add_mod, hmask, Nat.zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega)
      unfold decodeInteger
      rw [if_neg hguard]
      rw [if_neg (by omega)]
      rw [hbyte]
      rw [hbn, hmod]
      rw [if_pos (by omega)]
      rw [hb]
    next hbig =>
      cases henc
      have hfill : prefixMask + prefixMax prefixBits < 256 := by omega
      have hb : (ByteArray.empty.push
          (UInt8.ofNat (prefixMask + prefixMax prefixBits))).size = 1 := rfl
      have hsz := encodeIntegerRest_size_lt (value - prefixMax prefixBits)
        (ByteArray.empty.push (UInt8.ofNat (prefixMask + prefixMax prefixBits)))
      have happsz : (encodeIntegerRest (value - prefixMax prefixBits)
            (ByteArray.empty.push (UInt8.ofNat (prefixMask + prefixMax prefixBits)))
          ++ rest).size
          = (encodeIntegerRest (value - prefixMax prefixBits)
              (ByteArray.empty.push (UInt8.ofNat (prefixMask + prefixMax prefixBits)))).size
            + rest.size :=
        ByteArray.size_append
      have hbyte : (encodeIntegerRest (value - prefixMax prefixBits)
            (ByteArray.empty.push (UInt8.ofNat (prefixMask + prefixMax prefixBits)))
          ++ rest)[(0 : Nat)]!
          = UInt8.ofNat (prefixMask + prefixMax prefixBits) := by
        rw [getElem!_pos _ _ (by omega)]
        rw [ByteArray.getElem_append_left (by omega)]
        rw [encodeIntegerRest_getElem_prefix _ _ 0 (by omega)]
        rfl
      have hbn : (UInt8.ofNat (prefixMask + prefixMax prefixBits)).toNat
          = prefixMask + prefixMax prefixBits := by
        simp only [UInt8.toNat_ofNat', Nat.reducePow]
        omega
      have hmod : (prefixMask + prefixMax prefixBits) % 2 ^ prefixBits
          = prefixMax prefixBits := by
        rw [Nat.add_mod, hmask, Nat.zero_add, Nat.mod_mod]
        exact Nat.mod_eq_of_lt (by omega)
      unfold decodeInteger
      rw [if_neg hguard]
      rw [if_neg (by omega)]
      rw [hbyte]
      rw [hbn, hmod]
      rw [if_neg (by omega)]
      have hoff : (0 : Nat) + 1 = (ByteArray.empty.push
          (UInt8.ofNat (prefixMask + prefixMax prefixBits))).size := by rw [hb]
      rw [hoff]
      rw [decodeIntegerRest_encodeIntegerRest (value - prefixMax prefixBits) _ rest
        (prefixMax prefixBits) 0]
      have hval : prefixMax prefixBits + (value - prefixMax prefixBits) * 2 ^ 0 = value := by
        simp only [Nat.pow_zero, Nat.mul_one]
        omega
      rw [hval]

/-!
#### Dynamic-table size invariant
-/

private theorem dynamicSize_empty : dynamicSize #[] = 0 := rfl

private theorem dynamicSize_evictTo_le (maxSize : Nat) (entries : Array Header) :
    dynamicSize (evictTo maxSize entries) ≤ maxSize := by
  fun_induction evictTo maxSize entries
  next entries h => exact h
  next entries h hempty =>
    have hsz : entries.size = 0 := by
      simpa [Array.isEmpty] using hempty
    have hnil : entries = #[] := Array.size_eq_zero_iff.mp hsz
    rw [hnil] at h
    exact absurd (dynamicSize_empty ▸ Nat.zero_le maxSize) h
  next entries h hempty ih => exact ih

/-- After `resize`, the accounted dynamic-table size fits the new maximum. -/
theorem dynamicSize_resize_le (state : State) (maxSize : Nat) :
    dynamicSize (resize state maxSize).dynamic ≤ maxSize :=
  dynamicSize_evictTo_le maxSize state.dynamic

/-- After `insert`, the accounted dynamic-table size still fits the table
maximum. -/
theorem dynamicSize_insert_le (state : State) (header : Header) :
    dynamicSize (insert state header).dynamic ≤ state.maxSize := by
  unfold insert
  split
  next =>
    show dynamicSize #[] ≤ state.maxSize
    simp [dynamicSize_empty]
  next => exact dynamicSize_evictTo_le ..

/-- After a checked resize, the accounted dynamic-table size fits the newly
requested maximum. -/
theorem dynamicSize_resizeChecked_le {state state' : State} {maxSize : Nat}
    (h : resizeChecked state maxSize = .ok state') :
    dynamicSize state'.dynamic ≤ maxSize := by
  unfold resizeChecked at h
  simp only [pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    cases h
    exact dynamicSize_resize_le ..

/-- After acknowledging a peer's maximum, the accounted dynamic-table size
fits the new maximum. -/
theorem dynamicSize_setMaxAllowedSize_le (state : State) (maxSize : Nat) :
    dynamicSize (setMaxAllowedSize state maxSize).dynamic ≤ maxSize :=
  dynamicSize_resize_le state maxSize

/-!
#### Huffman table prefix-freeness
-/

/-- `code₁` (of bit length `len₁`) is a bit-prefix of `code₂` (of bit length
`len₂`). -/
def isBitPrefix (len₁ code₁ len₂ code₂ : Nat) : Bool :=
  len₁ ≤ len₂ && code₂ / 2 ^ (len₂ - len₁) == code₁

/-- The pairwise prefix-freeness test over a `(code, length)` table: no
entry's code is a bit-prefix of a different entry's code. -/
def pairwiseNoBitPrefix : List (Nat × Nat) -> Bool
  | [] => true
  | (code, len) :: tail =>
      (tail.all fun (code', len') =>
        !isBitPrefix len code len' code' && !isBitPrefix len' code' len code)
        && pairwiseNoBitPrefix tail

/-- The full 257-entry HPACK Huffman table paired as `(code, length)`. -/
def huffmanCodeTable : List (Nat × Nat) :=
  huffmanCodes.toList.zip huffmanCodeLengths.toList

set_option maxRecDepth 4096 in
/-- The fixed HPACK Huffman table (all 256 byte symbols plus EOS) is
prefix-free: no assigned code is a bit-prefix of another entry's code, so a
Huffman decoder can never confuse one symbol's code with the start of
another's. -/
theorem huffmanPrefixFree : pairwiseNoBitPrefix huffmanCodeTable = true := by
  decide

end Hpack
end Http2
end Grpc
