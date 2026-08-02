module

public import Grpc.Status
import Zlib.Gzip

public section

namespace Grpc

inductive CompressionFlag where
  | identity
  | compressed
  deriving Inhabited, Repr, DecidableEq

namespace CompressionFlag

def toUInt8 : CompressionFlag -> UInt8
  | .identity => 0
  | .compressed => 1

def ofUInt8? : UInt8 -> Option CompressionFlag
  | 0 => some .identity
  | 1 => some .compressed
  | _ => none

end CompressionFlag

structure Message where
  compressed : CompressionFlag := .identity
  data : ByteArray
  deriving Inhabited, DecidableEq

namespace Message

def maxWireLength : Nat := 4294967295

/-- Length of the per-message wire prefix: 1 compressed-flag byte + 4 length bytes. -/
def prefixLength : Nat := 5

private def uint32BE (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (UInt8.ofNat ((n / 16777216) % 256))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

private def readUInt32BE (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 16777216
    + bytes[offset + 1]!.toNat * 65536
    + bytes[offset + 2]!.toNat * 256
    + bytes[offset + 3]!.toNat

def encode (message : Message) : Except Status ByteArray :=
  let len := message.data.size
  if len > maxWireLength then
    .error (Status.internal "gRPC message exceeds 32-bit wire length")
  else
    .ok <| ByteArray.empty
      |>.push message.compressed.toUInt8
      |>.append (uint32BE len)
      |>.append message.data

structure DecodeState where
  buffered : ByteArray := ByteArray.empty
  messages : Array Message := #[]
  deriving Inhabited

private def checkDataSize (maxDataSize? : Option Nat) (len : Nat) : Except Status Unit := do
  match maxDataSize? with
  | none => pure ()
  | some maxDataSize =>
      if len > maxDataSize then
        throw (Status.resourceExhausted s!"gRPC message exceeds configured size limit {maxDataSize}")
      else
        pure ()

private partial def parseBuffered (maxDataSize? : Option Nat) (buffered : ByteArray)
    (messages : Array Message) :
    Except Status DecodeState := do
  if buffered.size < 5 then
    pure { buffered := buffered, messages := messages }
  else
    let flagByte := buffered[0]!
    let flag ← match CompressionFlag.ofUInt8? flagByte with
      | some flag => pure flag
      | none => throw (Status.internal s!"invalid gRPC compression flag {flagByte.toNat}")
    let len := readUInt32BE buffered 1
    checkDataSize maxDataSize? len
    if buffered.size < 5 + len then
      pure { buffered := buffered, messages := messages }
    else
      let data := buffered.extract 5 (5 + len)
      let rest := buffered.extract (5 + len) buffered.size
      parseBuffered maxDataSize? rest (messages.push { compressed := flag, data := data })

def decodeChunkWithLimit (maxDataSize? : Option Nat) (state : DecodeState) (chunk : ByteArray) :
    Except Status DecodeState :=
  parseBuffered maxDataSize? (state.buffered.append chunk) #[]

def decodeChunk (state : DecodeState) (chunk : ByteArray) : Except Status DecodeState :=
  decodeChunkWithLimit none state chunk

def decodeAllWithLimit (maxDataSize? : Option Nat) (bytes : ByteArray) :
    Except Status (Array Message) := do
  let state ← decodeChunkWithLimit maxDataSize? {} bytes
  if state.buffered.isEmpty then
    pure state.messages
  else
    throw (Status.internal "incomplete gRPC message")

def decodeAll (bytes : ByteArray) : Except Status (Array Message) := do
  decodeAllWithLimit none bytes

/-- Default cap on the inflated size of a single gzip-compressed message. -/
def defaultMaxDecompressedSize : Nat := 4194304

/-- Messages at or above this size are gzip-compressed when response
compression is negotiated; smaller messages keep the identity flag. -/
def gzipCompressThreshold : Nat := 1024

private def clampUInt32 (n : Nat) : UInt32 :=
  if n < 4294967296 then UInt32.ofNat n else 4294967295

/-- Resolve a message's per-message compression flag. `usesGzip` records
whether the request declared `grpc-encoding: gzip`. A compressed flag without
a matching encoding is an `INTERNAL` error per the gRPC spec. -/
def decompress (usesGzip : Bool) (maxSize : Nat) (message : Message) :
    Except Status Message := do
  match message.compressed with
  | .identity => pure message
  | .compressed =>
      if !usesGzip then
        throw (Status.internal
          "gRPC message has the compressed flag set without a message encoding")
      else
        match Zlib.Gzip.decompress message.data (clampUInt32 maxSize) with
        | some data => pure { compressed := .identity, data := data }
        | none => throw (Status.internal "failed to decompress gzip gRPC message")

/-- Build a message for `data`, gzip-compressing it when it meets the size
threshold; smaller payloads keep the identity flag (allowed per-message). -/
def gzipped (data : ByteArray) : Message :=
  if data.size >= gzipCompressThreshold then
    { compressed := .compressed, data := Zlib.Gzip.compress data }
  else
    { data := data }

/-- Decode a length-prefixed request body, decompress any gzip-compressed
messages, and re-encode with identity flags so downstream handlers see plain
payloads. Bodies with no compressed messages pass through unchanged. -/
def decompressBody (usesGzip : Bool) (maxDataSize? : Option Nat) (body : ByteArray) :
    Except Status ByteArray := do
  let messages ← decodeAllWithLimit maxDataSize? body
  if messages.all (fun message => message.compressed == .identity) then
    pure body
  else
    let maxSize := maxDataSize?.getD defaultMaxDecompressedSize
    messages.foldlM (init := ByteArray.empty) fun out message => do
      let message ← decompress usesGzip maxSize message
      let encoded ← encode message
      pure (out.append encoded)

end Message

end Grpc
