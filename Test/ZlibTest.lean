import Zlib.Gzip
import Grpc

open Grpc

def expect (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

partial def repeatByte (n : Nat) (byte : UInt8) (out : ByteArray := ByteArray.empty) : ByteArray :=
  if n == 0 then
    out
  else
    repeatByte (n - 1) byte (out.push byte)

def roundTrip (label : String) (data : ByteArray) : IO Unit := do
  let compressed := Zlib.Gzip.compress data
  expect (compressed.size >= 2) s!"{label}: compressed output too short"
  expect (compressed[0]! == 0x1f && compressed[1]! == 0x8b)
    s!"{label}: missing gzip magic bytes"
  match Zlib.Gzip.decompress compressed (UInt32.ofNat (data.size + 16)) with
  | some restored => expect (restored == data) s!"{label}: round-trip mismatch"
  | none => throw (IO.userError s!"{label}: decompress returned none")

def main : IO Unit := do
  -- Round trips across sizes.
  roundTrip "empty" ByteArray.empty
  roundTrip "one byte" (ByteArray.empty.push 0x42)
  let oneMiB := repeatByte 1048576 0x61
  roundTrip "1MiB repetitive" oneMiB

  -- Repetitive data should actually compress.
  expect ((Zlib.Gzip.compress oneMiB).size < 1048576 / 100)
    "1MiB of 'a' should compress well"

  -- Corrupt input is rejected.
  expect (Zlib.Gzip.decompress (ByteArray.mk #[0xde, 0xad, 0xbe, 0xef]) 4096 |>.isNone)
    "corrupt input should decompress to none"
  let truncated := (Zlib.Gzip.compress oneMiB).extract 0 10
  expect (Zlib.Gzip.decompress truncated 4194304 |>.isNone)
    "truncated input should decompress to none"

  -- Decompression-bomb guard: 1MiB of zeros capped at 1000 bytes.
  let zeros := repeatByte 1048576 0
  expect (Zlib.Gzip.decompress (Zlib.Gzip.compress zeros) 1000 |>.isNone)
    "maxLen guard should reject oversized inflation"
  expect (Zlib.Gzip.decompress (Zlib.Gzip.compress zeros) 1048576 |>.isSome)
    "exact maxLen should be accepted"

  -- gRPC framing integration: compressed message round-trip.
  let payload := repeatByte 4096 0x7a
  let framed := Zlib.Gzip.compress payload
  let message : Message := { compressed := .compressed, data := framed }
  match Message.decompress true 4194304 message with
  | .ok restored =>
      expect (restored.data == payload && restored.compressed == .identity)
        "Message.decompress should inflate gzip messages"
  | .error status => throw (IO.userError status.messageD)

  -- Compressed flag without gzip encoding must be INTERNAL.
  match Message.decompress false 4194304 message with
  | .ok _ => throw (IO.userError "compressed flag without encoding should reject")
  | .error status =>
      expect (status.code == Code.internal)
        "compressed flag without encoding should be INTERNAL"

  -- decompressBody rewrites bodies to identity framing.
  let encoded ← match Message.encode message with
    | .ok bytes => pure bytes
    | .error status => throw (IO.userError status.messageD)
  let body ← match Message.decompressBody true none encoded with
    | .ok body => pure body
    | .error status => throw (IO.userError status.messageD)
  match Message.decodeAll body with
  | .ok messages =>
      expect (messages.size == 1 && messages[0]!.data == payload
        && messages[0]!.compressed == .identity)
        "decompressBody should produce identity-framed messages"
  | .error status => throw (IO.userError status.messageD)

  -- gzipped applies the 1 KiB threshold.
  expect ((Message.gzipped (repeatByte 16 0x01)).compressed == .identity)
    "small messages should stay identity"
  expect ((Message.gzipped payload).compressed == .compressed)
    "large messages should be gzip-compressed"

  -- Header helpers.
  expect (Headers.acceptedEncodings == "identity,gzip")
    "server should advertise identity,gzip"
  expect (Headers.clientAcceptsGzip
      (Metadata.empty.insert "grpc-accept-encoding" "identity, gzip"))
    "client accept-encoding list containing gzip should be detected"
  expect (!Headers.clientAcceptsGzip
      (Metadata.empty.insert "grpc-accept-encoding" "identity"))
    "identity-only accept-encoding should not enable gzip"

  IO.println "zlib gzip tests passed"
