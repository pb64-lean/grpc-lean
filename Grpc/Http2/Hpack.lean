module

public import Grpc.Bytes
public import Grpc.Http2.Frame
public import Grpc.Metadata

public section

open Grpc.Bytes

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

def huffmanCodes : Array Nat := #[
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

def huffmanCodeLengths : Array Nat := #[
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

/-- The RFC table is canonical: codes of each bit length form one contiguous
range.  These three small tables describe each range and index a fourth table
ordered by `(length, code)`. -/
private def huffmanFirstCodeByLength : Array Nat := #[
  0, 0, 0, 0, 0, 0x0, 0x14, 0x5c, 0xf8, 0, 0x3f8, 0x7fa, 0xffa, 0x1ff8,
  0x3ffc, 0x7ffc, 0, 0, 0, 0x7fff0, 0xfffe6, 0x1fffdc, 0x3fffd2, 0x7fffd8,
  0xffffea, 0x1ffffec, 0x3ffffe0, 0x7ffffde, 0xfffffe2, 0, 0x3ffffffc
]

private def huffmanCodeCountByLength : Array Nat := #[
  0, 0, 0, 0, 0, 10, 26, 32, 6, 0, 5, 3, 2, 6, 2, 3, 0, 0, 0, 3, 8, 13,
  26, 29, 12, 4, 15, 19, 29, 0, 4
]

private def huffmanSymbolOffsetByLength : Array Nat := #[
  0, 0, 0, 0, 0, 0, 10, 36, 68, 74, 74, 79, 82, 84, 90, 92, 95, 95, 95, 95,
  98, 106, 119, 145, 174, 186, 190, 205, 224, 253, 253
]

private def huffmanSymbolsByCode : Array Nat := #[
  48, 49, 50, 97, 99, 101, 105, 111, 115, 116, 32, 37, 45, 46, 47, 51,
  52, 53, 54, 55, 56, 57, 61, 65, 95, 98, 100, 102, 103, 104, 108, 109,
  110, 112, 114, 117, 58, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76,
  77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 89, 106, 107, 113, 118,
  119, 120, 121, 122, 38, 42, 44, 59, 88, 90, 33, 34, 40, 41, 63, 39,
  43, 124, 35, 62, 0, 36, 64, 91, 93, 126, 94, 125, 60, 96, 123, 92,
  195, 208, 128, 130, 131, 162, 184, 194, 224, 226, 153, 161, 167, 172,
  176, 177, 179, 209, 216, 217, 227, 229, 230, 129, 132, 133, 134, 136,
  146, 154, 156, 160, 163, 164, 169, 170, 173, 178, 181, 185, 186, 187,
  189, 190, 196, 198, 228, 232, 233, 1, 135, 137, 138, 139, 140, 141,
  143, 147, 149, 150, 151, 152, 155, 157, 158, 165, 166, 168, 174, 175,
  180, 182, 183, 188, 191, 197, 231, 239, 9, 142, 144, 145, 148, 159,
  171, 206, 215, 225, 236, 237, 199, 207, 234, 235, 192, 193, 200, 201,
  202, 205, 210, 213, 218, 219, 238, 240, 242, 243, 255, 203, 204, 211,
  212, 214, 221, 222, 223, 241, 244, 245, 246, 247, 248, 250, 251, 252,
  253, 254, 2, 3, 4, 5, 6, 7, 8, 11, 12, 14, 15, 16, 17, 18, 19, 20,
  21, 23, 24, 25, 26, 27, 28, 29, 30, 31, 127, 220, 249, 10, 13, 22, 256
]

/-- Bounded executable lookup for `findHuffmanSymbol?`.  The `i` argument is
retained because the proof-facing definition supports searches beginning at
an arbitrary table index, even though the decoder always starts at zero. -/
def findHuffmanSymbolLookup? (code bits i : Nat) : Option Nat :=
  if bits >= huffmanCodeCountByLength.size then
    none
  else
    let firstCode := huffmanFirstCodeByLength[bits]!
    if code < firstCode then
      none
    else
      let codeOffset := code - firstCode
      if codeOffset >= huffmanCodeCountByLength[bits]! then
        none
      else
        let symbol := huffmanSymbolsByCode[huffmanSymbolOffsetByLength[bits]! + codeOffset]!
        if symbol >= i then some symbol else none

/-- Linear specification used by the Huffman codec proof.  The bounded decoder
is differentially checked against this specification. -/
def findHuffmanSymbol? (code bits i : Nat) : Option Nat :=
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

set_option maxRecDepth 4096 in
private def decodeHuffmanLookupBits
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
      match findHuffmanSymbolLookup? code bits 0 with
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
      decodeHuffmanLookupBits bytes (offset + 1) 7 code bits out
    else
      decodeHuffmanLookupBits bytes offset (bit - 1) code bits out
  termination_by (bytes.size - offset) * 8 + bit
  decreasing_by
    · omega
    · omega

/-- Audited bit-serial specification retained for differential testing. -/
def decodeHuffmanReference (bytes : ByteArray) : Except Status ByteArray :=
  decodeHuffmanBits bytes 0 7 0 0 ByteArray.empty

/-- Bounded Huffman decoder used by executable HPACK paths. -/
def decodeHuffmanLookup (bytes : ByteArray) : Except Status ByteArray :=
  decodeHuffmanLookupBits bytes 0 7 0 0 ByteArray.empty

/-- HPACK Huffman decoding.  The proof-facing definition remains the audited
bit-serial specification; generated code uses the bounded lookup decoder. -/
@[implemented_by decodeHuffmanLookup]
def decodeHuffman (bytes : ByteArray) : Except Status ByteArray :=
  decodeHuffmanReference bytes

private def encodeHuffmanFlush (acc bits : Nat) (out : ByteArray) : Nat × Nat × ByteArray :=
  if bits >= 8 then
    encodeHuffmanFlush (acc % (2 ^ (bits - 8))) (bits - 8)
      (out.push (UInt8.ofNat (acc / (2 ^ (bits - 8)))))
  else
    (acc, bits, out)
  termination_by bits
  decreasing_by omega

/-- One encoding step: append a symbol's code bits to the pending
accumulator and flush whole bytes out of it. -/
private def encodeHuffmanStep (state : Nat × Nat × ByteArray) (byte : UInt8) :
    Nat × Nat × ByteArray :=
  encodeHuffmanFlush
    (state.1 * (2 ^ huffmanCodeLengths[byte.toNat]!) + huffmanCodes[byte.toNat]!)
    (state.2.1 + huffmanCodeLengths[byte.toNat]!) state.2.2

def encodeHuffman (bytes : ByteArray) : ByteArray :=
  let (acc, bits, out) := bytes.data.foldl encodeHuffmanStep
    ((0 : Nat), (0 : Nat), ByteArray.empty)
  if bits == 0 then
    out
  else
    out.push (UInt8.ofNat (acc * (2 ^ (8 - bits)) + (prefixMax (8 - bits))))

/-- Values larger than this are emitted raw: Huffman coding of very large
values costs CPU for little relative gain, and header fields this large are
dominated by frame overhead anyway. -/
def huffmanMaxEncodeLength : Nat := 1024

/-- The candidate Huffman coding `encodeString` compares against the raw
bytes: the Huffman form for values worth compressing, the raw bytes
otherwise (which then lose the size comparison and are emitted literally). -/
def huffmanCandidate (bytes : ByteArray) : ByteArray :=
  if bytes.size <= huffmanMaxEncodeLength then encodeHuffman bytes else bytes

def encodeString (value : String) : Except Status ByteArray :=
  let bytes := value.toUTF8
  let huffman := huffmanCandidate bytes
  if huffman.size < bytes.size then
    match encodeInteger 7 128 huffman.size with
    | .error status => .error status
    | .ok prefixBytes => .ok (prefixBytes.append huffman)
  else
    match encodeInteger 7 0 bytes.size with
    | .error status => .error status
    | .ok prefixBytes => .ok (prefixBytes.append bytes)

/-! Keep the proof-facing and executable string decoders separately callable so
tests can compare the complete length/UTF-8 wrapper as well as the Huffman
kernel. -/

def decodeStringReference (bytes : ByteArray) (offset : Nat) : Except Status StringResult :=
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
              decodeHuffmanReference (bytes.extract length.next (length.next + length.value))
            else
              .ok (bytes.extract length.next (length.next + length.value))) with
          | .error status => .error status
          | .ok raw =>
              match String.fromUTF8? raw with
              | some decoded => .ok { value := decoded, next := length.next + length.value }
              | none => .error (Status.internal "HPACK string is not valid UTF-8")

def decodeStringLookup (bytes : ByteArray) (offset : Nat) : Except Status StringResult :=
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
              decodeHuffmanLookup (bytes.extract length.next (length.next + length.value))
            else
              .ok (bytes.extract length.next (length.next + length.value))) with
          | .error status => .error status
          | .ok raw =>
              match String.fromUTF8? raw with
              | some decoded => .ok { value := decoded, next := length.next + length.value }
              | none => .error (Status.internal "HPACK string is not valid UTF-8")

@[implemented_by decodeStringLookup]
def decodeString (bytes : ByteArray) (offset : Nat) : Except Status StringResult :=
  decodeStringReference bytes offset

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

/-- Disable the encoder dynamic table while retaining the peer-advertised
upper bound.  A pending size update of zero makes the choice explicit to the
decoder.  With a zero-sized table every encoded field is independent of prior
response blocks, which is the safe mode for concurrently completing HTTP/2
streams without serializing their handlers. -/
def withoutDynamicTable (state : State := {}) : State :=
  {
    state with
    dynamic := #[],
    maxSize := 0,
    pendingSizeUpdate := if state.maxSize == 0 then state.pendingSizeUpdate else some 0
  }

/-- Record a peer's new decoder-table limit while keeping this encoder's
chosen dynamic-table size at zero. -/
def setMaxAllowedSizeWithoutDynamicTable (state : State) (maxAllowedSize : Nat) : State :=
  { (withoutDynamicTable state) with maxAllowedSize := maxAllowedSize }

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
* `decodeString_encodeString` — literal string roundtrip with residual
  bytes, for both the raw and the Huffman representation.
* `dynamicSize_resize_le` / `dynamicSize_insert_le` /
  `dynamicSize_resizeChecked_le` / `dynamicSize_setMaxAllowedSize_le` — the
  dynamic-table size invariant: after any resize, insert, or checked resize
  the accounted table size (RFC 7541 §4.1: name + value bytes + 32 per
  entry) never exceeds the applicable maximum.
* `huffmanPrefixFree` — the fixed 257-entry Huffman table is prefix-free
  (`pairwiseNoBitPrefix` spells out the pairwise bit-prefix test), with
  `huffmanCode_not_bitPrefix` reading it off at a pair of table indices and
  `findHuffmanSymbol?_proper_prefix_eq_none` / `findHuffmanSymbol?_self`
  turning it into what the bit-serial decoder needs: the table search
  returns `none` at every position strictly inside a symbol's code and the
  symbol's own index at its end.
* `decodeHuffman_encodeHuffman` — the Huffman coder roundtrip. The decoder
  is shown equivalent to a decoder over an explicit bit list, the encoder is
  shown to emit exactly the concatenated code bits plus at most seven
  padding ones, and prefix-freeness makes both the symbol boundaries and the
  padding unambiguous (an all-ones run shorter than the EOS code is a proper
  prefix of it).
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
#### Shared byte-array and integer-encoding helpers
-/

private theorem get!_append_left {bytes rest : ByteArray} {i : Nat} (hi : i < bytes.size) :
    (bytes ++ rest)[i]! = bytes[i] := by
  have h : i < (bytes ++ rest).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (bytes ++ rest) i h, ByteArray.getElem_append_left hi]

private theorem encodeInteger_ok_size {prefixBits prefixMask value : Nat} {encoded : ByteArray}
    (henc : encodeInteger prefixBits prefixMask value = .ok encoded) : 0 < encoded.size := by
  unfold encodeInteger at henc
  split at henc
  next => cases henc
  next =>
    split at henc
    next =>
      cases henc
      show 0 < (ByteArray.empty.push _).size
      rw [ByteArray.size_push]
      omega
    next =>
      cases henc
      have hlt := encodeIntegerRest_size_lt (value - prefixMax prefixBits)
        (ByteArray.empty.push (UInt8.ofNat (prefixMask + prefixMax prefixBits)))
      have hb : (ByteArray.empty.push
          (UInt8.ofNat (prefixMask + prefixMax prefixBits))).size = 1 := by
        rw [ByteArray.size_push]
        rfl
      omega

/-- The leading byte of a `prefixMask = 0` HPACK integer has its high bit
clear, so a literal string encoded with the raw representation is decoded as
raw rather than Huffman. -/
private theorem encodeInteger_raw_head {value : Nat} {encoded : ByteArray}
    (henc : encodeInteger 7 0 value = .ok encoded) : encoded[0]!.toNat < 128 := by
  unfold encodeInteger at henc
  split at henc
  next => cases henc
  next =>
    split at henc
    next hsmall =>
      cases henc
      have hb : (ByteArray.empty.push (UInt8.ofNat (0 + value))).size = 1 := by
        rw [ByteArray.size_push]
        rfl
      rw [getElem!_pos _ 0 (by omega)]
      rw [show (ByteArray.empty.push (UInt8.ofNat (0 + value)))[0] = UInt8.ofNat (0 + value) from
        getElem_push_eq ..]
      have : prefixMax 7 = 127 := rfl
      simp only [UInt8.toNat_ofNat', Nat.reducePow]
      omega
    next =>
      cases henc
      have hb : (ByteArray.empty.push (UInt8.ofNat (0 + prefixMax 7))).size = 1 := by
        rw [ByteArray.size_push]
        rfl
      have hlt := encodeIntegerRest_size_lt (value - prefixMax 7)
        (ByteArray.empty.push (UInt8.ofNat (0 + prefixMax 7)))
      rw [getElem!_pos _ 0 (by omega)]
      rw [encodeIntegerRest_getElem_prefix _ _ 0 (by omega)]
      rw [show (ByteArray.empty.push (UInt8.ofNat (0 + prefixMax 7)))[0]
          = UInt8.ofNat (0 + prefixMax 7) from getElem_push_eq ..]
      have : prefixMax 7 = 127 := rfl
      simp only [UInt8.toNat_ofNat', Nat.reducePow, this]
      omega

private theorem fromUTF8?_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  rw [String.toUTF8_eq_toByteArray]
  have hv : s.toByteArray.IsValidUTF8 := ⟨s.toList, String.utf8Encode_toList.symm⟩
  unfold String.fromUTF8?
  split
  next => rfl
  next h => exact absurd hv h

/-!
#### Dynamic-table size invariant
-/

theorem dynamicSize_empty : dynamicSize #[] = 0 := by rfl

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
theorem maxSize_setMaxAllowedSize (state : State) (maxSize : Nat) :
    (setMaxAllowedSize state maxSize).maxSize = maxSize := by rfl

theorem dynamicSize_setMaxAllowedSize_le (state : State) (maxSize : Nat) :
    dynamicSize (setMaxAllowedSize state maxSize).dynamic ≤ maxSize :=
  dynamicSize_resize_le state maxSize

theorem maxSize_withoutDynamicTable (state : State) :
    (withoutDynamicTable state).maxSize = 0 := by
  rfl

theorem dynamicSize_withoutDynamicTable (state : State) :
    dynamicSize (withoutDynamicTable state).dynamic = 0 := by
  simp [withoutDynamicTable, dynamicSize_empty]

theorem maxSize_setMaxAllowedSizeWithoutDynamicTable (state : State) (maxAllowedSize : Nat) :
    (setMaxAllowedSizeWithoutDynamicTable state maxAllowedSize).maxSize = 0 := by
  rfl

theorem dynamicSize_setMaxAllowedSizeWithoutDynamicTable
    (state : State) (maxAllowedSize : Nat) :
    dynamicSize (setMaxAllowedSizeWithoutDynamicTable state maxAllowedSize).dynamic ≤ 0 := by
  simp [setMaxAllowedSizeWithoutDynamicTable, withoutDynamicTable, dynamicSize_empty]

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

/-- A successful table search returns an in-range index whose code and length
are exactly the ones searched for. -/
private theorem findHuffmanSymbol?_eq_some (code bits i : Nat) :
    ∀ j, findHuffmanSymbol? code bits i = some j ->
      j < huffmanCodes.size ∧ huffmanCodes[j]! = code ∧ huffmanCodeLengths[j]! = bits := by
  fun_induction findHuffmanSymbol? code bits i
  next i hge =>
    intro j hj
    cases hj
  next i hge hmatch =>
    intro j hj
    injection hj with hji
    subst hji
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    exact ⟨by omega, hmatch.1, hmatch.2⟩
  next i hge hmatch ih => exact ih

/-- The pairwise prefix-freeness check, read off at a pair of distinct
indices. -/
private theorem pairwiseNoBitPrefix_getElem :
    ∀ {l : List (Nat × Nat)}, pairwiseNoBitPrefix l = true ->
      ∀ (i j : Nat) (hi : i < l.length) (hj : j < l.length), i ≠ j ->
        isBitPrefix l[i].2 l[i].1 l[j].2 l[j].1 = false := by
  intro l
  induction l with
  | nil => intro _ i j hi; exact absurd hi (by simp)
  | cons head tail ih =>
      intro h i j hi hj hij
      rw [pairwiseNoBitPrefix] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨hall, htail⟩ := h
      have hallmem : ∀ x ∈ tail,
          (!isBitPrefix head.2 head.1 x.2 x.1 && !isBitPrefix x.2 x.1 head.2 head.1) = true := by
        intro x hx
        have := List.all_eq_true.mp hall x hx
        simpa using this
      match i, j with
      | 0, 0 => exact absurd rfl hij
      | 0, j + 1 =>
          have hjt : j < tail.length := by simpa using hj
          have := hallmem tail[j] (List.getElem_mem hjt)
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
          simpa using this.1
      | i + 1, 0 =>
          have hit : i < tail.length := by simpa using hi
          have := hallmem tail[i] (List.getElem_mem hit)
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
          simpa using this.2
      | i + 1, j + 1 =>
          have hit : i < tail.length := by simpa using hi
          have hjt : j < tail.length := by simpa using hj
          have := ih htail i j hit hjt (by omega)
          simpa using this

set_option maxRecDepth 8192 in
private theorem huffmanCodeLengths_size : huffmanCodeLengths.size = huffmanCodes.size := by
  rfl

private theorem huffmanCodeTable_length : huffmanCodeTable.length = huffmanCodes.size := by
  rw [huffmanCodeTable, List.length_zip, Array.length_toList, Array.length_toList,
    huffmanCodeLengths_size, Nat.min_self]

private theorem huffmanCodeTable_getElem {i : Nat} (h : i < huffmanCodeTable.length) :
    huffmanCodeTable[i] = (huffmanCodes[i]!, huffmanCodeLengths[i]!) := by
  have hi : i < huffmanCodes.size := by rw [huffmanCodeTable_length] at h; exact h
  have hl : i < huffmanCodeLengths.size := by rw [huffmanCodeLengths_size]; exact hi
  simp only [huffmanCodeTable, List.getElem_zip, Array.getElem_toList,
    getElem!_pos huffmanCodes i hi, getElem!_pos huffmanCodeLengths i hl]

/-- Prefix-freeness at a pair of distinct table indices. -/
theorem huffmanCode_not_bitPrefix {i j : Nat} (hi : i < huffmanCodes.size)
    (hj : j < huffmanCodes.size) (hij : i ≠ j) :
    isBitPrefix huffmanCodeLengths[i]! huffmanCodes[i]! huffmanCodeLengths[j]! huffmanCodes[j]!
      = false := by
  have hi' : i < huffmanCodeTable.length := by rw [huffmanCodeTable_length]; exact hi
  have hj' : j < huffmanCodeTable.length := by rw [huffmanCodeTable_length]; exact hj
  have h := pairwiseNoBitPrefix_getElem huffmanPrefixFree i j hi' hj' hij
  rwa [huffmanCodeTable_getElem hi', huffmanCodeTable_getElem hj'] at h

/-- The decoder cannot stop early: no proper bit-prefix of an assigned
Huffman code is itself an assigned code, so scanning bit by bit the table
search returns `none` at every position strictly inside a symbol's code.
This is the property `huffmanPrefixFree` buys the decoder. -/
theorem findHuffmanSymbol?_proper_prefix_eq_none {i k : Nat} (hi : i < huffmanCodes.size)
    (hk : k < huffmanCodeLengths[i]!) :
    findHuffmanSymbol? (huffmanCodes[i]! / 2 ^ (huffmanCodeLengths[i]! - k)) k 0 = none := by
  cases hfind : findHuffmanSymbol?
      (huffmanCodes[i]! / 2 ^ (huffmanCodeLengths[i]! - k)) k 0 with
  | none => rfl
  | some j =>
      obtain ⟨hj, hcode, hlen⟩ := findHuffmanSymbol?_eq_some _ _ _ j hfind
      exfalso
      have hne : j ≠ i := by
        intro heq
        rw [heq] at hlen
        omega
      have hpref : isBitPrefix huffmanCodeLengths[j]! huffmanCodes[j]!
          huffmanCodeLengths[i]! huffmanCodes[i]! = true := by
        rw [isBitPrefix, hcode, hlen]
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨by omega, by first | rfl | trivial⟩
      rw [huffmanCode_not_bitPrefix hj hi hne] at hpref
      exact absurd hpref (by simp)

/-- The linear table search returns the first index at or after `i` whose
`(code, length)` pair matches. -/
private theorem findHuffmanSymbol?_of_hit (code bits : Nat) : ∀ i n : Nat, i ≤ n ->
    n < huffmanCodes.size -> huffmanCodes[n]! = code -> huffmanCodeLengths[n]! = bits ->
    (∀ m, i ≤ m -> m < n -> ¬(huffmanCodes[m]! = code ∧ huffmanCodeLengths[m]! = bits)) ->
    findHuffmanSymbol? code bits i = some n := by
  intro i
  fun_induction findHuffmanSymbol? code bits i
  next i hge => intro n hin hn _ _ _; omega
  next i hge hmatch =>
    intro n hin hn hcode hlen hnone
    simp only [Bool.and_eq_true, beq_iff_eq] at hmatch
    have : ¬ i < n := fun hlt => hnone i (Nat.le_refl i) hlt ⟨hmatch.1, hmatch.2⟩
    have : i = n := by omega
    rw [this]
  next i hge hmatch ih =>
    intro n hin hn hcode hlen hnone
    have hne : i ≠ n := by
      intro heq
      rw [heq] at hmatch
      rw [hcode, hlen] at hmatch
      simp at hmatch
    exact ih n (by omega) hn hcode hlen (fun m hm hmn => hnone m (by omega) hmn)

/-- The table search is exact: given an assigned code and its length, it
returns that symbol's own index. Together with
`findHuffmanSymbol?_proper_prefix_eq_none` this pins down the bit-serial
decoder's symbol boundaries. -/
theorem findHuffmanSymbol?_self {i : Nat} (hi : i < huffmanCodes.size) :
    findHuffmanSymbol? huffmanCodes[i]! huffmanCodeLengths[i]! 0 = some i := by
  refine findHuffmanSymbol?_of_hit _ _ 0 i (Nat.zero_le i) hi rfl rfl ?_
  intro m _ hmi hm
  have hmsize : m < huffmanCodes.size := by omega
  have hpf := huffmanCode_not_bitPrefix hmsize hi (by omega)
  rw [isBitPrefix, hm.1, hm.2] at hpf
  simp at hpf

/-!
#### Bit-list model of the Huffman decoder

`decodeHuffmanBits` walks a byte/bit cursor; every proof about it is easier
against an explicit list of the bits still to be read. `decodeHuffmanBits_eq`
shows the two agree.
-/

/-- The bits of `bytes` from `(offset, bit)` onwards, most significant
first. -/
private def bitsFrom (bytes : ByteArray) (offset bit : Nat) : List Nat :=
  if offset >= bytes.size then
    []
  else
    bitAt bytes[offset]! bit ::
      (if bit = 0 then bitsFrom bytes (offset + 1) 7 else bitsFrom bytes offset (bit - 1))
  termination_by (bytes.size - offset) * 8 + bit
  decreasing_by
    · omega
    · omega

/-- `decodeHuffmanBits` as a function of the remaining bits. -/
private def decodeBits : List Nat -> Nat -> Nat -> ByteArray -> Except Status ByteArray
  | [], code, bits, out =>
      if validHuffmanPadding code bits then
        .ok out
      else
        .error (Status.internal "invalid HPACK Huffman padding")
  | b :: rest, code, bits, out =>
      match findHuffmanSymbol? (code * 2 + b) (bits + 1) 0 with
      | some symbol =>
          if symbol == huffmanEOSSymbol then
            .error (Status.internal "HPACK Huffman EOS appeared in data")
          else
            decodeBits rest 0 0 (out.push (UInt8.ofNat symbol))
      | none =>
          if bits + 1 > 30 then
            .error (Status.internal "invalid HPACK Huffman code")
          else
            decodeBits rest (code * 2 + b) (bits + 1) out

private theorem except_bind_ok {α β : Type} (a : α) (f : α -> Except Status β) :
    (Except.ok a >>= f) = f a := rfl

private theorem except_bind_error {α β : Type} (e : Status) (f : α -> Except Status β) :
    ((Except.error e : Except Status α) >>= f) = .error e := rfl

private theorem ite_bool_true {α : Type} (a b : α) :
    (if (true : Bool) = true then a else b) = a := rfl

private theorem ite_bool_false {α : Type} (a b : α) :
    (if (false : Bool) = true then a else b) = b := rfl

/-- The cursor-driven decoder and the bit-list decoder agree. -/
private theorem decodeHuffmanBits_eq (bytes : ByteArray) (offset bit : Nat) :
    ∀ code bits out, decodeHuffmanBits bytes offset bit code bits out
      = decodeBits (bitsFrom bytes offset bit) code bits out := by
  fun_induction bitsFrom bytes offset bit
  next offset bit hge =>
    intro code bits out
    rw [decodeHuffmanBits, if_pos (by omega), decodeBits]
    split <;> rfl
  next offset bit hge hzero hsucc =>
    intro code bits out
    have hstep : ∀ c b o,
        (if bit = 0 then decodeHuffmanBits bytes (offset + 1) 7 c b o
          else decodeHuffmanBits bytes offset (bit - 1) c b o)
        = decodeBits (if bit = 0 then bitsFrom bytes (offset + 1) 7
            else bitsFrom bytes offset (bit - 1)) c b o := by
      intro c b o
      by_cases hb : bit = 0
      · rw [if_pos hb, if_pos hb]
        exact hzero hb c b o
      · rw [if_neg hb, if_neg hb]
        exact hsucc hb c b o
    rw [decodeHuffmanBits, if_neg (by omega), decodeBits]
    simp only [bind, Except.bind]
    split
    next symbol hfind =>
      split
      next => rfl
      next => exact hstep 0 0 (out.push (UInt8.ofNat symbol))
    next hfind =>
      split
      next => rfl
      next => exact hstep (code * 2 + bitAt bytes[offset]! bit) (bits + 1) out

/-- Huffman decoding, as a function of the input's bit list. -/
private theorem decodeHuffman_eq (bytes : ByteArray) :
    decodeHuffman bytes = decodeBits (bitsFrom bytes 0 7) 0 0 ByteArray.empty :=
  decodeHuffmanBits_eq bytes 0 7 0 0 ByteArray.empty

/-!
#### The bit-list decoder recovers encoded symbols
-/

/-- The `len` least significant bits of `value`, most significant first. -/
private def natBits (len value : Nat) : List Nat :=
  match len with
  | 0 => []
  | len + 1 => (value / 2 ^ len) % 2 :: natBits len value

/-- The Huffman code bits of one symbol. -/
private def symbolBits (symbol : Nat) : List Nat :=
  natBits huffmanCodeLengths[symbol]! huffmanCodes[symbol]!

set_option maxRecDepth 8192 in
private theorem huffmanCodes_size : huffmanCodes.size = 257 := by rfl

set_option maxRecDepth 8192 in
/-- Every table entry has a positive length of at most 30 bits and a code
that fits in that many bits. -/
theorem huffmanCodeTableBounded :
    huffmanCodeTable.all (fun entry => entry.1 < 2 ^ entry.2 && 0 < entry.2 && entry.2 ≤ 30)
      = true := by
  decide

private theorem huffmanCode_bounds {i : Nat} (hi : i < huffmanCodes.size) :
    huffmanCodes[i]! < 2 ^ huffmanCodeLengths[i]! ∧ 0 < huffmanCodeLengths[i]!
      ∧ huffmanCodeLengths[i]! ≤ 30 := by
  have hi' : i < huffmanCodeTable.length := by rw [huffmanCodeTable_length]; exact hi
  have h := List.all_eq_true.mp huffmanCodeTableBounded huffmanCodeTable[i]
    (List.getElem_mem hi')
  rw [huffmanCodeTable_getElem hi'] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- Decoding the tail of a symbol's code: with `j` of the code's bits still
to read and the leading bits already accumulated, the decoder consumes
exactly those `j` bits and emits the symbol. -/
private theorem decodeBits_natBits (s : Nat) (hs : s < huffmanCodes.size)
    (hne : s ≠ huffmanEOSSymbol) (rest : List Nat) (out : ByteArray) :
    ∀ j, 1 ≤ j -> j ≤ huffmanCodeLengths[s]! ->
      decodeBits (natBits j huffmanCodes[s]! ++ rest)
          (huffmanCodes[s]! / 2 ^ j) (huffmanCodeLengths[s]! - j) out
        = decodeBits rest 0 0 (out.push (UInt8.ofNat s)) := by
  obtain ⟨hcodelt, hlenpos, hlen30⟩ := huffmanCode_bounds hs
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
      intro _ hle
      have hdiv : huffmanCodes[s]! / 2 ^ (j + 1) = huffmanCodes[s]! / 2 ^ j / 2 := by
        rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
      have hcode : huffmanCodes[s]! / 2 ^ (j + 1) * 2 + huffmanCodes[s]! / 2 ^ j % 2
          = huffmanCodes[s]! / 2 ^ j := by
        rw [hdiv]
        omega
      have hbits : huffmanCodeLengths[s]! - (j + 1) + 1 = huffmanCodeLengths[s]! - j := by
        omega
      rw [natBits, List.cons_append, decodeBits, hcode, hbits]
      by_cases hj : j = 0
      · subst hj
        rw [show huffmanCodes[s]! / 2 ^ 0 = huffmanCodes[s]! from by
          rw [Nat.pow_zero, Nat.div_one]]
        rw [show huffmanCodeLengths[s]! - 0 = huffmanCodeLengths[s]! from by omega]
        simp only [findHuffmanSymbol?_self hs]
        rw [show (s == huffmanEOSSymbol) = false from by
          simp only [beq_eq_false_iff_ne]
          exact hne]
        rw [ite_bool_false, natBits, List.nil_append]
      · have hprefix : findHuffmanSymbol? (huffmanCodes[s]! / 2 ^ j)
            (huffmanCodeLengths[s]! - j) 0 = none := by
          have h := findHuffmanSymbol?_proper_prefix_eq_none hs
            (k := huffmanCodeLengths[s]! - j) (by omega)
          rwa [show huffmanCodeLengths[s]! - (huffmanCodeLengths[s]! - j) = j from by omega] at h
        simp only [hprefix]
        rw [if_neg (show ¬ (huffmanCodeLengths[s]! - j > 30) from by omega)]
        exact ih (by omega) (by omega)

/-- One symbol's Huffman code decodes to exactly that symbol, leaving the
rest of the bit stream untouched. -/
private theorem decodeBits_symbolBits {s : Nat} (hs : s < 256) (rest : List Nat)
    (out : ByteArray) :
    decodeBits (symbolBits s ++ rest) 0 0 out
      = decodeBits rest 0 0 (out.push (UInt8.ofNat s)) := by
  have hsize : s < huffmanCodes.size := by rw [huffmanCodes_size]; omega
  have hne : s ≠ huffmanEOSSymbol := by
    show s ≠ 256
    omega
  obtain ⟨hcodelt, hlenpos, hlen30⟩ := huffmanCode_bounds hsize
  have h := decodeBits_natBits s hsize hne rest out huffmanCodeLengths[s]! hlenpos
    (Nat.le_refl _)
  rw [show huffmanCodes[s]! / 2 ^ huffmanCodeLengths[s]! = 0 from
      Nat.div_eq_of_lt hcodelt,
    Nat.sub_self] at h
  exact h

/-!
#### Padding and whole-stream decoding
-/

private theorem pow_sub_one_div (j d : Nat) : (2 ^ (j + d) - 1) / 2 ^ d = 2 ^ j - 1 := by
  have hd : 0 < 2 ^ d := Nat.two_pow_pos d
  have hj : 0 < 2 ^ j := Nat.two_pow_pos j
  have hle : 2 ^ d ≤ 2 ^ j * 2 ^ d := Nat.le_mul_of_pos_left _ hj
  have hsplit : 2 ^ (j + d) - 1 = (2 ^ d - 1) + (2 ^ j - 1) * 2 ^ d := by
    rw [Nat.pow_add, Nat.sub_mul, Nat.one_mul]
    omega
  rw [hsplit, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt (by omega), Nat.zero_add]

set_option maxRecDepth 8192 in
private theorem huffmanEOS_code : huffmanCodes[256]! = 2 ^ 30 - 1 := by
  rfl

set_option maxRecDepth 8192 in
private theorem huffmanEOS_length : huffmanCodeLengths[256]! = 30 := by
  rfl

/-- An all-ones bit run shorter than the EOS code is never a complete code:
it is a proper prefix of the (all-ones) EOS code, which prefix-freeness
excludes. This is what makes trailing Huffman padding unambiguous. -/
private theorem findHuffmanSymbol?_ones {k : Nat} (hk : k ≤ 7) :
    findHuffmanSymbol? (2 ^ k - 1) k 0 = none := by
  have hsize : 256 < huffmanCodes.size := by rw [huffmanCodes_size]; omega
  have h := findHuffmanSymbol?_proper_prefix_eq_none hsize
    (k := k) (by rw [huffmanEOS_length]; omega)
  rw [huffmanEOS_code, huffmanEOS_length] at h
  rwa [show (30 : Nat) - k = 30 - k from rfl,
    show (2 : Nat) ^ 30 - 1 = 2 ^ (k + (30 - k)) - 1 from by
      rw [show k + (30 - k) = 30 from by omega],
    pow_sub_one_div] at h

/-- Trailing padding of at most seven one bits decodes to nothing. -/
private theorem decodeBits_ones (out : ByteArray) : ∀ n k, n + k ≤ 7 ->
    decodeBits (List.replicate n 1) (2 ^ k - 1) k out = .ok out := by
  intro n
  induction n with
  | zero =>
      intro k hk
      rw [List.replicate_zero, decodeBits, if_pos]
      show validHuffmanPadding (2 ^ k - 1) k = true
      rw [validHuffmanPadding]
      simp only [prefixMax, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      exact Or.inr ⟨by omega, by first | rfl | trivial⟩
  | succ n ih =>
      intro k hk
      rw [List.replicate_succ, decodeBits]
      have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
      rw [show (2 ^ k - 1) * 2 + 1 = 2 ^ (k + 1) - 1 from by
        rw [Nat.pow_succ]
        omega]
      rw [findHuffmanSymbol?_ones (by omega)]
      rw [if_neg (show ¬ (k + 1 > 30) from by omega)]
      exact ih (k + 1) (by omega)

private theorem foldl_push_eq (l : List UInt8) : ∀ out : ByteArray,
    l.foldl ByteArray.push out = out ++ l.toByteArray := by
  induction l with
  | nil =>
      intro out
      rw [List.foldl_nil, show ([] : List UInt8).toByteArray = ByteArray.empty from rfl,
        ByteArray.append_empty]
  | cons b rest ih =>
      intro out
      rw [List.foldl_cons, ih,
        show (b :: rest).toByteArray = ByteArray.empty.push b ++ rest.toByteArray from by
          rw [show b :: rest = [b] ++ rest from rfl, List.toByteArray_append]
          rfl,
        byteArray_push_eq_append out b, ByteArray.append_assoc]

private theorem toByteArray_data_toList (bytes : ByteArray) :
    bytes.data.toList.toByteArray = bytes := by
  apply ByteArray.ext_getElem
  · rw [List.size_toByteArray, Array.length_toList]
    rfl
  · intro i h1 h2
    rw [List.getElem_toByteArray, Array.getElem_toList]
    rfl

/-- The bit-list decoder recovers exactly the byte sequence whose Huffman
codes it is given, ignoring up to seven trailing padding ones. -/
private theorem decodeBits_symbolBits_flatMap (pad : Nat) (hpad : pad ≤ 7) :
    ∀ (symbols : List UInt8) (out : ByteArray),
      decodeBits (symbols.flatMap (fun b => symbolBits b.toNat) ++ List.replicate pad 1)
          0 0 out
        = .ok (out ++ symbols.toByteArray) := by
  intro symbols
  induction symbols with
  | nil =>
      intro out
      rw [List.flatMap_nil, List.nil_append,
        show ([] : List UInt8).toByteArray = ByteArray.empty from rfl, ByteArray.append_empty]
      have h := decodeBits_ones out pad 0 (by omega)
      rw [show (2 : Nat) ^ 0 - 1 = 0 from rfl] at h
      exact h
  | cons b rest ih =>
      intro out
      rw [List.flatMap_cons, List.append_assoc]
      rw [decodeBits_symbolBits (s := b.toNat) (by
        have := UInt8.toNat_lt b
        omega)]
      rw [UInt8.ofNat_toNat, ih]
      rw [show (b :: rest).toByteArray = ByteArray.empty.push b ++ rest.toByteArray from by
          rw [show b :: rest = [b] ++ rest from rfl, List.toByteArray_append]
          rfl,
        byteArray_push_eq_append out b, ByteArray.append_assoc]

/-!
#### Bit lists of byte arrays
-/

private theorem natBits_add (m : Nat) : ∀ n v,
    natBits (m + n) v = natBits m (v / 2 ^ n) ++ natBits n v := by
  induction m with
  | zero => intro n v; rw [Nat.zero_add, natBits, List.nil_append]
  | succ m ih =>
      intro n v
      rw [show m + 1 + n = m + n + 1 from by omega]
      show (v / 2 ^ (m + n)) % 2 :: natBits (m + n) v
        = ((v / 2 ^ n / 2 ^ m) % 2 :: natBits m (v / 2 ^ n)) ++ natBits n v
      rw [ih n v, show v / 2 ^ n / 2 ^ m = v / 2 ^ (m + n) from by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_comm]]
      rfl

private theorem natBits_congr (n : Nat) : ∀ v w, v % 2 ^ n = w % 2 ^ n ->
    natBits n v = natBits n w := by
  induction n with
  | zero => intro v w _; rfl
  | succ n ih =>
      intro v w h
      have hhead : ∀ x : Nat, x / 2 ^ n % 2 = x % 2 ^ (n + 1) / 2 ^ n := by
        intro x
        rw [Nat.pow_succ, Nat.mod_mul_right_div_self]
      have hdvd : (2 : Nat) ^ n ∣ 2 ^ (n + 1) := ⟨2, Nat.pow_succ 2 n⟩
      have htail : v % 2 ^ n = w % 2 ^ n := by
        rw [← Nat.mod_mod_of_dvd v hdvd, h, Nat.mod_mod_of_dvd w hdvd]
      show (v / 2 ^ n) % 2 :: natBits n v = (w / 2 ^ n) % 2 :: natBits n w
      rw [hhead v, hhead w, h, ih v w htail]

private theorem natBits_mod (n v : Nat) : natBits n (v % 2 ^ n) = natBits n v :=
  natBits_congr n _ _ (Nat.mod_mod_of_dvd v (Nat.dvd_refl _))

private theorem natBits_ones : ∀ n, natBits n (2 ^ n - 1) = List.replicate n 1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
      have hsplit : 2 ^ (n + 1) - 1 = (2 ^ n - 1) + 1 * 2 ^ n := by
        rw [Nat.pow_succ]
        omega
      show ((2 ^ (n + 1) - 1) / 2 ^ n) % 2 :: natBits n (2 ^ (n + 1) - 1)
        = List.replicate (n + 1) 1
      rw [hsplit, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt (by omega), Nat.zero_add,
        natBits_congr n (2 ^ n - 1 + 1 * 2 ^ n) (2 ^ n - 1)
          (by rw [Nat.add_mul_mod_self_right]),
        ih, List.replicate_succ]

/-- The bit stream a byte array carries, most significant bit first. -/
private def bitsOf (bytes : ByteArray) : List Nat :=
  bytes.data.toList.flatMap (fun byte => natBits 8 byte.toNat)

private theorem bitsOf_push (out : ByteArray) (b : UInt8) :
    bitsOf (out.push b) = bitsOf out ++ natBits 8 b.toNat := by
  rw [bitsOf, bitsOf, ByteArray.data_push, Array.toList_push, List.flatMap_append]
  rfl

private theorem bitsFrom_byte (bytes : ByteArray) (offset : Nat) (h : offset < bytes.size) :
    ∀ bit, bitsFrom bytes offset bit
      = natBits (bit + 1) bytes[offset]!.toNat ++ bitsFrom bytes (offset + 1) 7 := by
  intro bit
  induction bit with
  | zero =>
      rw [bitsFrom, if_neg (by omega), if_pos rfl]
      rfl
  | succ bit ih =>
      rw [bitsFrom, if_neg (by omega), if_neg (by omega)]
      show bitAt bytes[offset]! (bit + 1) :: bitsFrom bytes offset (bit + 1 - 1) = _
      rw [show bit + 1 - 1 = bit from by omega, ih]
      rfl

private theorem bitsFrom_eq_drop (bytes : ByteArray) : ∀ n offset, bytes.size - offset = n ->
    bitsFrom bytes offset 7
      = (bytes.data.toList.drop offset).flatMap (fun byte => natBits 8 byte.toNat) := by
  intro n
  induction n with
  | zero =>
      intro offset hn
      have hsz : bytes.data.size = bytes.size := rfl
      rw [bitsFrom, if_pos (by omega)]
      rw [List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)]
      rfl
  | succ n ih =>
      intro offset hn
      have hlt : offset < bytes.size := by omega
      have hlist : offset < bytes.data.toList.length := by
        rw [Array.length_toList]
        exact hlt
      rw [bitsFrom_byte bytes offset hlt 7, ih (offset + 1) (by omega),
        List.drop_eq_getElem_cons hlist, List.flatMap_cons]
      rw [show bytes.data.toList[offset] = bytes[offset]! from by
        rw [Array.getElem_toList, getElem!_pos bytes offset hlt]
        rfl]

private theorem bitsFrom_eq_bitsOf (bytes : ByteArray) : bitsFrom bytes 0 7 = bitsOf bytes := by
  rw [bitsFrom_eq_drop bytes bytes.size 0 (by omega), bitsOf, List.drop_zero]

/-!
#### The encoder emits exactly the symbols' code bits
-/

private theorem encodeHuffmanFlush_spec (acc bits : Nat) (out : ByteArray) :
    acc < 2 ^ bits ->
    ∀ acc' bits' out', encodeHuffmanFlush acc bits out = (acc', bits', out') ->
      bits' < 8 ∧ acc' < 2 ^ bits'
        ∧ bitsOf out' ++ natBits bits' acc' = bitsOf out ++ natBits bits acc := by
  fun_induction encodeHuffmanFlush acc bits out
  next acc bits out hge ih =>
    intro hacc acc' bits' out' heq
    have hpos : 0 < 2 ^ (bits - 8) := Nat.two_pow_pos _
    have hmod : acc % 2 ^ (bits - 8) < 2 ^ (bits - 8) := Nat.mod_lt _ hpos
    obtain ⟨h1, h2, h3⟩ := ih hmod acc' bits' out' heq
    refine ⟨h1, h2, ?_⟩
    rw [h3, bitsOf_push]
    rw [show (UInt8.ofNat (acc / 2 ^ (bits - 8))).toNat
        = (acc / 2 ^ (bits - 8)) % 2 ^ 8 from by
      simp only [UInt8.toNat_ofNat']]
    rw [natBits_mod 8 (acc / 2 ^ (bits - 8)), natBits_mod (bits - 8) acc,
      List.append_assoc, ← natBits_add 8 (bits - 8) acc,
      show 8 + (bits - 8) = bits from by omega]
  next acc bits out hlt =>
    intro hacc acc' bits' out' heq
    have heq' : (acc, bits, out) = (acc', bits', out') := heq
    cases heq'
    exact ⟨by omega, hacc, rfl⟩

private theorem encodeHuffmanStep_spec (acc bits : Nat) (out : ByteArray) (byte : UInt8)
    (hbits : bits < 8) (hacc : acc < 2 ^ bits) :
    ∀ acc' bits' out', encodeHuffmanStep (acc, bits, out) byte = (acc', bits', out') ->
      bits' < 8 ∧ acc' < 2 ^ bits'
        ∧ bitsOf out' ++ natBits bits' acc'
          = bitsOf out ++ natBits bits acc ++ symbolBits byte.toNat := by
  intro acc' bits' out' heq
  have hsym : byte.toNat < huffmanCodes.size := by
    rw [huffmanCodes_size]
    have := UInt8.toNat_lt byte
    omega
  obtain ⟨hcodelt, hlenpos, hlen30⟩ := huffmanCode_bounds hsym
  have hlenpow : 0 < 2 ^ huffmanCodeLengths[byte.toNat]! := Nat.two_pow_pos _
  have hbitspow : 0 < 2 ^ bits := Nat.two_pow_pos bits
  have hmul : acc * 2 ^ huffmanCodeLengths[byte.toNat]!
      ≤ 2 ^ bits * 2 ^ huffmanCodeLengths[byte.toNat]!
        - 2 ^ huffmanCodeLengths[byte.toNat]! := by
    have h := Nat.mul_le_mul_right (k := 2 ^ huffmanCodeLengths[byte.toNat]!)
      (show acc ≤ 2 ^ bits - 1 from by omega)
    rwa [Nat.sub_mul, Nat.one_mul] at h
  have hle : 2 ^ huffmanCodeLengths[byte.toNat]!
      ≤ 2 ^ bits * 2 ^ huffmanCodeLengths[byte.toNat]! :=
    Nat.le_mul_of_pos_left _ hbitspow
  have hsum : acc * 2 ^ huffmanCodeLengths[byte.toNat]! + huffmanCodes[byte.toNat]!
      < 2 ^ (bits + huffmanCodeLengths[byte.toNat]!) := by
    rw [Nat.pow_add]
    omega
  obtain ⟨h1, h2, h3⟩ := encodeHuffmanFlush_spec _ _ out hsum acc' bits' out' heq
  refine ⟨h1, h2, ?_⟩
  rw [h3, natBits_add bits huffmanCodeLengths[byte.toNat]!]
  rw [show (acc * 2 ^ huffmanCodeLengths[byte.toNat]! + huffmanCodes[byte.toNat]!)
      / 2 ^ huffmanCodeLengths[byte.toNat]! = acc from by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hlenpow,
      Nat.div_eq_of_lt hcodelt, Nat.zero_add]]
  rw [natBits_congr huffmanCodeLengths[byte.toNat]!
      (acc * 2 ^ huffmanCodeLengths[byte.toNat]! + huffmanCodes[byte.toNat]!)
      huffmanCodes[byte.toNat]! (by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right])]
  rw [symbolBits, List.append_assoc]

private theorem encodeHuffman_fold_spec : ∀ (l : List UInt8) (acc bits : Nat) (out : ByteArray),
    bits < 8 -> acc < 2 ^ bits ->
    ∀ acc' bits' out', l.foldl encodeHuffmanStep (acc, bits, out) = (acc', bits', out') ->
      bits' < 8 ∧ acc' < 2 ^ bits'
        ∧ bitsOf out' ++ natBits bits' acc'
          = bitsOf out ++ natBits bits acc ++ l.flatMap (fun b => symbolBits b.toNat) := by
  intro l
  induction l with
  | nil =>
      intro acc bits out hbits hacc acc' bits' out' heq
      have heq' : (acc, bits, out) = (acc', bits', out') := heq
      cases heq'
      exact ⟨hbits, hacc, by rw [List.flatMap_nil, List.append_nil]⟩
  | cons b rest ih =>
      intro acc bits out hbits hacc acc' bits' out' heq
      rw [List.foldl_cons] at heq
      cases hstep : encodeHuffmanStep (acc, bits, out) b with
      | mk acc₁ rest₁ =>
        cases rest₁ with
        | mk bits₁ out₁ =>
          obtain ⟨s1, s2, s3⟩ := encodeHuffmanStep_spec acc bits out b hbits hacc
            acc₁ bits₁ out₁ hstep
          rw [hstep] at heq
          obtain ⟨t1, t2, t3⟩ := ih acc₁ bits₁ out₁ s1 s2 acc' bits' out' heq
          refine ⟨t1, t2, ?_⟩
          rw [t3, s3, List.flatMap_cons, List.append_assoc, List.append_assoc]

/-- Huffman encoding emits exactly the concatenated code bits of the input
bytes, followed by at most seven padding one bits. -/
private theorem bitsOf_encodeHuffman (bytes : ByteArray) :
    ∃ pad, pad ≤ 7 ∧ bitsOf (encodeHuffman bytes)
      = bytes.data.toList.flatMap (fun b => symbolBits b.toNat) ++ List.replicate pad 1 := by
  have hfold := encodeHuffman_fold_spec bytes.data.toList 0 0 ByteArray.empty (by omega)
    (by omega)
  cases hres : bytes.data.toList.foldl encodeHuffmanStep (0, 0, ByteArray.empty) with
  | mk acc rest =>
    cases rest with
    | mk bits out =>
      obtain ⟨h1, h2, h3⟩ := hfold acc bits out hres
      rw [show bitsOf ByteArray.empty = [] from rfl, natBits, List.append_nil,
        List.nil_append] at h3
      have hunfold : encodeHuffman bytes
          = if bits == 0 then out
            else out.push (UInt8.ofNat (acc * (2 ^ (8 - bits)) + (prefixMax (8 - bits)))) := by
        rw [encodeHuffman, ← Array.foldl_toList, hres]
      by_cases hzero : bits = 0
      · subst hzero
        refine ⟨0, by omega, ?_⟩
        rw [hunfold, show ((0 : Nat) == 0) = true from rfl, ite_bool_true]
        rw [List.replicate_zero, List.append_nil]
        rw [natBits, List.append_nil] at h3
        exact h3
      · have hpad : 0 < 8 - bits ∧ 8 - bits ≤ 7 := by omega
        have hpow : 0 < 2 ^ (8 - bits) := Nat.two_pow_pos _
        have hprefix : prefixMax (8 - bits) = 2 ^ (8 - bits) - 1 := rfl
        have hlt : acc * 2 ^ (8 - bits) + (2 ^ (8 - bits) - 1) < 2 ^ 8 := by
          have h := Nat.mul_le_mul_right (k := 2 ^ (8 - bits))
            (show acc ≤ 2 ^ bits - 1 from by omega)
          rw [Nat.sub_mul, Nat.one_mul] at h
          have hsplit : 2 ^ bits * 2 ^ (8 - bits) = 2 ^ 8 := by
            rw [← Nat.pow_add, show bits + (8 - bits) = 8 from by omega]
          have hle : 2 ^ (8 - bits) ≤ 2 ^ bits * 2 ^ (8 - bits) :=
            Nat.le_mul_of_pos_left _ (Nat.two_pow_pos bits)
          omega
        refine ⟨8 - bits, hpad.2, ?_⟩
        rw [hunfold, if_neg (by simpa using hzero), bitsOf_push, hprefix]
        rw [show (UInt8.ofNat (acc * 2 ^ (8 - bits) + (2 ^ (8 - bits) - 1))).toNat
            = (acc * 2 ^ (8 - bits) + (2 ^ (8 - bits) - 1)) % 2 ^ 8 from by
          simp only [UInt8.toNat_ofNat']]
        have hadd : ∀ V, natBits 8 V
            = natBits bits (V / 2 ^ (8 - bits)) ++ natBits (8 - bits) V := by
          have h := natBits_add bits (8 - bits)
          rwa [show bits + (8 - bits) = 8 from by omega] at h
        rw [natBits_mod 8 _, hadd]
        rw [show (acc * 2 ^ (8 - bits) + (2 ^ (8 - bits) - 1)) / 2 ^ (8 - bits) = acc from by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpow,
            Nat.div_eq_of_lt (by omega), Nat.zero_add]]
        rw [natBits_congr (8 - bits) (acc * 2 ^ (8 - bits) + (2 ^ (8 - bits) - 1))
            (2 ^ (8 - bits) - 1) (by rw [Nat.add_comm, Nat.add_mul_mod_self_right]),
          natBits_ones (8 - bits)]
        rw [← List.append_assoc, h3]

/-- Huffman decoding inverts Huffman encoding. -/
theorem decodeHuffman_encodeHuffman (bytes : ByteArray) :
    decodeHuffman (encodeHuffman bytes) = .ok bytes := by
  obtain ⟨pad, hpad, hbits⟩ := bitsOf_encodeHuffman bytes
  rw [decodeHuffman_eq, bitsFrom_eq_bitsOf, hbits,
    decodeBits_symbolBits_flatMap pad hpad bytes.data.toList ByteArray.empty,
    ByteArray.empty_append, toByteArray_data_toList]

/-!
#### Literal string codec (both representations)
-/

/-- The leading byte of a `prefixMask = 128` HPACK integer has its high bit
set, so a literal string encoded with the Huffman representation is decoded
as Huffman. -/
private theorem encodeInteger_huffman_head {value : Nat} {encoded : ByteArray}
    (henc : encodeInteger 7 128 value = .ok encoded) : 128 ≤ encoded[0]!.toNat := by
  unfold encodeInteger at henc
  split at henc
  next => cases henc
  next =>
    split at henc
    next hsmall =>
      cases henc
      have hb : (ByteArray.empty.push (UInt8.ofNat (128 + value))).size = 1 := by
        rw [ByteArray.size_push]
        rfl
      rw [getElem!_pos _ 0 (by omega)]
      rw [show (ByteArray.empty.push (UInt8.ofNat (128 + value)))[0]
          = UInt8.ofNat (128 + value) from getElem_push_eq ..]
      have : prefixMax 7 = 127 := rfl
      simp only [UInt8.toNat_ofNat', Nat.reducePow]
      omega
    next =>
      cases henc
      have hb : (ByteArray.empty.push (UInt8.ofNat (128 + prefixMax 7))).size = 1 := by
        rw [ByteArray.size_push]
        rfl
      have hlt := encodeIntegerRest_size_lt (value - prefixMax 7)
        (ByteArray.empty.push (UInt8.ofNat (128 + prefixMax 7)))
      rw [getElem!_pos _ 0 (by omega)]
      rw [encodeIntegerRest_getElem_prefix _ _ 0 (by omega)]
      rw [show (ByteArray.empty.push (UInt8.ofNat (128 + prefixMax 7)))[0]
          = UInt8.ofNat (128 + prefixMax 7) from getElem_push_eq ..]
      have : prefixMax 7 = 127 := rfl
      simp only [UInt8.toNat_ofNat', Nat.reducePow, this]
      omega

/-- Decoding a length-prefixed literal string, given that the payload decodes
(raw or Huffman, as the prefix's high bit selects) to the value's UTF-8. -/
private theorem decodeString_prefixed {value : String} {payload prefixBytes : ByteArray}
    {mask : Nat} (hmask : mask % 2 ^ 7 = 0) (hfits : mask + 2 ^ 7 ≤ 256)
    (hint : encodeInteger 7 mask payload.size = .ok prefixBytes) (rest : ByteArray)
    (hbranch : (if (prefixBytes ++ payload ++ rest)[0]!.toNat ≥ 128 then
        decodeHuffmanReference payload
        else .ok payload) = .ok value.toUTF8) :
    decodeString (prefixBytes ++ payload ++ rest) 0
      = .ok { value := value, next := (prefixBytes ++ payload).size } := by
  have hpre : 0 < prefixBytes.size := encodeInteger_ok_size hint
  have hsz : (prefixBytes ++ payload ++ rest).size
      = prefixBytes.size + payload.size + rest.size := by
    simp only [ByteArray.size_append]
  have hassoc : prefixBytes ++ payload ++ rest = prefixBytes ++ (payload ++ rest) :=
    ByteArray.append_assoc
  have hdec : decodeInteger 7 (prefixBytes ++ payload ++ rest) 0
      = .ok { value := payload.size, next := prefixBytes.size } := by
    rw [hassoc]
    exact decodeInteger_encodeInteger hmask hfits hint (payload ++ rest)
  have hextract : (prefixBytes ++ payload ++ rest).extract prefixBytes.size
      (prefixBytes.size + payload.size) = payload := by
    rw [hassoc, ByteArray.extract_append, Nat.sub_self]
    rw [show prefixBytes.extract prefixBytes.size (prefixBytes.size + payload.size)
        = ByteArray.empty from ByteArray.extract_eq_empty_iff.mpr (by omega)]
    rw [ByteArray.empty_append]
    exact ByteArray.extract_append_eq_left (by omega)
  unfold decodeString decodeStringReference
  rw [if_neg (by omega), hdec]
  simp only
  rw [if_neg (by omega), hextract, hbranch]
  simp only [fromUTF8?_toUTF8]
  rw [ByteArray.size_append]

/-- Residual-byte inversion for HPACK literal strings: decoding
`encodeString value ++ rest` recovers the string and stops exactly at the
encoded length, whichever of the two representations — raw or Huffman — the
encoder chose. -/
theorem decodeString_encodeString {value : String} {encoded : ByteArray}
    (henc : encodeString value = .ok encoded) (rest : ByteArray) :
    decodeString (encoded ++ rest) 0 = .ok { value := value, next := encoded.size } := by
  unfold encodeString at henc
  simp only at henc
  split at henc
  next hshorter =>
    -- The Huffman representation won the size comparison, so the candidate is
    -- the Huffman coding itself (the raw fallback cannot be shorter than raw).
    have hcand : huffmanCandidate value.toUTF8 = encodeHuffman value.toUTF8 := by
      unfold huffmanCandidate
      split
      next => rfl
      next hbig => exact absurd hshorter (by unfold huffmanCandidate; rw [if_neg hbig]; omega)
    split at henc
    next => cases henc
    next prefixBytes hint =>
      cases henc
      have hpre : 0 < prefixBytes.size := encodeInteger_ok_size hint
      refine decodeString_prefixed (by rfl) (by omega) hint rest ?_
      rw [if_pos (by
        rw [show prefixBytes ++ huffmanCandidate value.toUTF8 ++ rest
            = prefixBytes ++ (huffmanCandidate value.toUTF8 ++ rest) from ByteArray.append_assoc,
          get!_append_left hpre]
        have h := encodeInteger_huffman_head hint
        rw [getElem!_pos prefixBytes 0 hpre] at h
        omega)]
      rw [hcand]
      simpa [decodeHuffman] using (decodeHuffman_encodeHuffman value.toUTF8)
  next hraw =>
    split at henc
    next => cases henc
    next prefixBytes hint =>
      cases henc
      have hpre : 0 < prefixBytes.size := encodeInteger_ok_size hint
      refine decodeString_prefixed (by rfl) (by omega) hint rest ?_
      rw [if_neg (by
        rw [show prefixBytes ++ value.toUTF8 ++ rest
            = prefixBytes ++ (value.toUTF8 ++ rest) from ByteArray.append_assoc,
          get!_append_left hpre]
        have h := encodeInteger_raw_head hint
        rw [getElem!_pos prefixBytes 0 hpre] at h
        omega)]


end Hpack
end Http2
end Grpc
