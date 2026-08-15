import Grpc

open Grpc

private def benchmarkSource : ByteArray := Id.run do
  let sample :=
    ":method POST :scheme https :path /acme.widgets.v1.WidgetService/ListWidgets " ++
    "content-type application/grpc grpc-encoding identity user-agent grpc-lean-benchmark "
  let mut out := ByteArray.empty
  for _ in [0:4] do
    out := out.append sample.toUTF8
  pure out

private def decodeRepeated (decode : ByteArray → Except Status ByteArray)
    (encoded : ByteArray) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    match decode encoded with
    | .ok decoded => checksum := checksum + decoded.size
    | .error status => throw (IO.userError status.messageD)
  pure checksum

private def measureDecoder (decode : ByteArray → Except Status ByteArray)
    (encoded : ByteArray) (iterations : Nat) : IO (Nat × Nat) := do
  let _ ← decodeRepeated decode encoded 20
  let started ← IO.monoNanosNow
  let checksum ← decodeRepeated decode encoded iterations
  pure ((← IO.monoNanosNow) - started, checksum)

private def printMeasurement (label : String) (elapsed checksum decodedBytes : Nat) : IO Unit := do
  let mibTimes100 :=
    if elapsed = 0 then 0 else decodedBytes * 100 * 1000000000 / elapsed / (1024 * 1024)
  IO.println s!"{label}: elapsed_ns={elapsed} decoded_bytes={decodedBytes} checksum={checksum}"
  IO.println s!"{label}: throughput_mib_s={mibTimes100 / 100}.{mibTimes100 % 100}"

private def parseIterations (args : List String) : Nat :=
  match args.head? >>= String.toNat? with
  | some n => n
  | none => 1000

def main (args : List String) : IO Unit := do
  let iterations := parseIterations args
  let source := benchmarkSource
  let encoded := Http2.Hpack.encodeHuffman source
  let decodedBytes := source.size * iterations
  IO.println s!"HPACK Huffman decode: {iterations} iterations, {source.size} decoded bytes/op"
  let (referenceElapsed, referenceChecksum) ←
    measureDecoder Http2.Hpack.decodeHuffmanReference encoded iterations
  let (lookupElapsed, lookupChecksum) ←
    measureDecoder Http2.Hpack.decodeHuffmanLookup encoded iterations
  printMeasurement "reference" referenceElapsed referenceChecksum decodedBytes
  printMeasurement "lookup" lookupElapsed lookupChecksum decodedBytes
  let speedupTimes100 := if lookupElapsed = 0 then 0 else referenceElapsed * 100 / lookupElapsed
  IO.println s!"speedup_x={speedupTimes100 / 100}.{speedupTimes100 % 100}"
