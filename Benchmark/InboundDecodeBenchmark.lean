import Grpc

open Grpc

/-!
# Incremental inbound decoder benchmark

Measures the exact HTTP/2 and gRPC incremental decoders on the ordinary
empty-buffer input and on a fragmented input that must append residue. A
bounded split-point pass validates both paths against `decodeAll`; the reuse
labels report whether an incomplete first chunk is retained by identity.
-/

private def framePayload : ByteArray :=
  "acme.widgets inbound frame payload used for exact decoder timing".toUTF8

private def frameWire : IO ByteArray := do
  let payload := framePayload
  match Http2.Frame.encode {
      header := {
        length := payload.size
        frameType := .data
        flags := Http2.FrameFlag.endStream
        streamId := 1
      }
      payload := payload
    } with
  | .ok wire => pure wire
  | .error status => throw (IO.userError status.messageD)

private def messageWire : IO ByteArray := do
  match Message.encode { data := framePayload } with
  | .ok wire => pure wire
  | .error status => throw (IO.userError status.messageD)

private def decodeFrameChunk (state : Http2.Frame.DecodeState) (chunk : ByteArray) :
    IO Http2.Frame.DecodeState := do
  match Http2.Frame.decodeChunk state chunk with
  | .ok decoded => pure decoded
  | .error status => throw (IO.userError status.messageD)

private def decodeMessageChunk (state : Message.DecodeState) (chunk : ByteArray) :
    IO Message.DecodeState := do
  match Message.decodeChunk state chunk with
  | .ok decoded => pure decoded
  | .error status => throw (IO.userError status.messageD)

private def validateFrameSplits (wire : ByteArray) : IO Unit := do
  let expected ← match Http2.Frame.decodeAll wire with
    | .ok frames => pure frames
    | .error status => throw (IO.userError status.messageD)
  for split in [0:wire.size + 1] do
    let first ← decodeFrameChunk {} (wire.extract 0 split)
    let second ← decodeFrameChunk { buffered := first.buffered }
      (wire.extract split wire.size)
    unless first.frames.append second.frames == expected && second.buffered.isEmpty do
      throw (IO.userError s!"HTTP/2 split-point validation failed at {split}")

private def validateMessageSplits (wire : ByteArray) : IO Unit := do
  let expected ← match Message.decodeAll wire with
    | .ok messages => pure messages
    | .error status => throw (IO.userError status.messageD)
  for split in [0:wire.size + 1] do
    let first ← decodeMessageChunk {} (wire.extract 0 split)
    let second ← decodeMessageChunk { buffered := first.buffered }
      (wire.extract split wire.size)
    unless first.messages.append second.messages == expected && second.buffered.isEmpty do
      throw (IO.userError s!"gRPC split-point validation failed at {split}")

private def frameCompleteRepeated (wire : ByteArray) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let decoded ← decodeFrameChunk {} wire
    checksum := checksum + decoded.frames.size + decoded.buffered.size
  pure checksum

private def frameFragmentedRepeated (firstChunk secondChunk : ByteArray)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let first ← decodeFrameChunk {} firstChunk
    let second ← decodeFrameChunk { buffered := first.buffered } secondChunk
    checksum := checksum + first.frames.size + second.frames.size + second.buffered.size
  pure checksum

private def messageCompleteRepeated (wire : ByteArray) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let decoded ← decodeMessageChunk {} wire
    checksum := checksum + decoded.messages.size + decoded.buffered.size
  pure checksum

private def messageFragmentedRepeated (firstChunk secondChunk : ByteArray)
    (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let first ← decodeMessageChunk {} firstChunk
    let second ← decodeMessageChunk { buffered := first.buffered } secondChunk
    checksum := checksum + first.messages.size + second.messages.size + second.buffered.size
  pure checksum

private def measureDecode (sink : IO.Ref Nat) (run : Nat → IO Nat)
    (iterations : Nat) : IO Nat := do
  let warmup ← run (Nat.min iterations 500)
  unless warmup > 0 do
    throw (IO.userError "inbound decoder warmup checksum was zero")
  let started ← IO.monoNanosNow
  sink.set (← run iterations)
  let elapsed := (← IO.monoNanosNow) - started
  unless (← sink.get) == iterations do
    throw (IO.userError "inbound decoder checksum mismatch")
  pure elapsed

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value ≤ head then value :: head :: tail
      else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def printSamples (label : String) (samples : Array Nat) (iterations : Nat) : IO Unit := do
  let elapsed := median samples
  let perOperation := if iterations == 0 then 0 else elapsed * 100 / iterations
  IO.println s!"{label}_samples_ns={formatSamples samples}"
  IO.println s!"{label}_median_ns_per_op={formatHundredths perOperation}"

private def parseNatArg (args : List String) (index fallback : Nat) : Nat :=
  match args[index]? >>= String.toNat? with
  | some value => Nat.max 1 value
  | none => fallback

unsafe def main (args : List String) : IO Unit := do
  let iterations := parseNatArg args 0 200000
  let rounds := parseNatArg args 1 9
  let frameWire ← frameWire
  let messageWire ← messageWire
  validateFrameSplits frameWire
  validateMessageSplits messageWire

  let framePartial := frameWire.extract 0 4
  let messagePartial := messageWire.extract 0 2
  let frameRetained ← decodeFrameChunk {} framePartial
  let messageRetained ← decodeMessageChunk {} messagePartial
  IO.println s!"frame_empty_input_reused={ptrEq framePartial frameRetained.buffered}"
  IO.println s!"message_empty_input_reused={ptrEq messagePartial messageRetained.buffered}"
  IO.println <| s!"inbound_decode_validation=pass split_points=" ++
    s!"{frameWire.size + 1 + messageWire.size + 1}"

  let frameFirst := frameWire.extract 0 4
  let frameSecond := frameWire.extract 4 frameWire.size
  let messageFirst := messageWire.extract 0 2
  let messageSecond := messageWire.extract 2 messageWire.size
  let sink ← IO.mkRef 0
  let mut frameComplete := #[]
  let mut frameFragmented := #[]
  let mut messageComplete := #[]
  let mut messageFragmented := #[]
  for _ in [0:rounds] do
    frameComplete := frameComplete.push
      (← measureDecode sink (frameCompleteRepeated frameWire) iterations)
    frameFragmented := frameFragmented.push
      (← measureDecode sink (frameFragmentedRepeated frameFirst frameSecond) iterations)
    messageComplete := messageComplete.push
      (← measureDecode sink (messageCompleteRepeated messageWire) iterations)
    messageFragmented := messageFragmented.push
      (← measureDecode sink (messageFragmentedRepeated messageFirst messageSecond) iterations)
  IO.println s!"inbound decoder: {rounds} rounds x {iterations} operations"
  printSamples "frame_complete" frameComplete iterations
  printSamples "frame_fragmented" frameFragmented iterations
  printSamples "message_complete" messageComplete iterations
  printSamples "message_fragmented" messageFragmented iterations
  IO.println "inbound_decode_checks=pass benchmark_kind=informative thresholds=none"
