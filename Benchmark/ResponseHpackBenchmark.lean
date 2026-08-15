import Grpc

open Grpc

abbrev Blocks := Http2.Transport.TestSupport.ResponseHeaderBlocks
abbrev Encoder := Http2.Hpack.State → Bool → Except Status Blocks

private def reusableState : Http2.Hpack.State :=
  { (Http2.Hpack.withoutDynamicTable {}) with
    maxAllowedSize := 137, pendingSizeUpdate := none }

private def headersFor (gzip : Bool) : Metadata :=
  if gzip then
    Headers.responseHeaders.insert "grpc-encoding" Headers.gzipEncoding
  else
    Headers.responseHeaders

/-- Exact pre-cache production work, retained locally as the benchmark oracle. -/
private def genericBlocks (state : Http2.Hpack.State) (gzip : Bool) :
    Except Status Blocks := do
  let initial ← Http2.Hpack.encodeHeaderBlock state (headersFor gzip)
  let trailers ← Http2.Hpack.encodeHeaderBlock initial.2 (Headers.trailers Status.ok)
  pure { initial := initial.1, trailers := trailers.1, state := trailers.2 }

private def cachedBlocks (state : Http2.Hpack.State) (gzip : Bool) :
    Except Status Blocks :=
  Http2.Transport.TestSupport.encodeCommonResponseHeaderBlocks state gzip

private def sameState (left right : Http2.Hpack.State) : Bool :=
  left.dynamic == right.dynamic && left.maxSize == right.maxSize &&
    left.maxAllowedSize == right.maxAllowedSize &&
    left.pendingSizeUpdate == right.pendingSizeUpdate

private def sameBlocks (left right : Blocks) : Bool :=
  left.initial.data == right.initial.data && left.trailers.data == right.trailers.data &&
    sameState left.state right.state

private def checkedEncode (encode : Encoder) (state : Http2.Hpack.State)
    (gzip : Bool) : IO Blocks := do
  match encode state gzip with
  | .ok blocks => pure blocks
  | .error status => throw (IO.userError status.messageD)

private def verifyOracle (gzip : Bool) : IO Unit := do
  let expected ← checkedEncode genericBlocks reusableState gzip
  let actual ← checkedEncode cachedBlocks reusableState gzip
  unless sameBlocks actual expected do
    throw (IO.userError s!"cached response blocks differ from generic oracle for gzip={gzip}")

private def encodeRepeated (encode : Encoder) (state : Http2.Hpack.State)
    (gzip : Bool) (iterations : Nat) : IO Nat := do
  let mut checksum := 0
  for _ in [0:iterations] do
    let blocks ← checkedEncode encode state gzip
    checksum := checksum + blocks.initial.size + blocks.trailers.size +
      blocks.state.maxAllowedSize
  pure checksum

private def measureEncoder (encode : Encoder) (state : Http2.Hpack.State)
    (gzip : Bool) (iterations : Nat) : IO (Nat × Nat) := do
  discard <| encodeRepeated encode state gzip (Nat.min iterations 200)
  let started ← IO.monoNanosNow
  let checksum ← encodeRepeated encode state gzip iterations
  pure ((← IO.monoNanosNow) - started, checksum)

private def measurePair (gzip : Bool) (iterations : Nat) (reverse : Bool) :
    IO (Nat × Nat) := do
  if reverse then
    let candidate ← measureEncoder cachedBlocks reusableState gzip iterations
    let baseline ← measureEncoder genericBlocks reusableState gzip iterations
    unless candidate.2 == baseline.2 do
      throw (IO.userError s!"response HPACK checksum mismatch for gzip={gzip}")
    pure (baseline.1, candidate.1)
  else
    let baseline ← measureEncoder genericBlocks reusableState gzip iterations
    let candidate ← measureEncoder cachedBlocks reusableState gzip iterations
    unless candidate.2 == baseline.2 do
      throw (IO.userError s!"response HPACK checksum mismatch for gzip={gzip}")
    pure (baseline.1, candidate.1)

private def insertSorted (value : Nat) : List Nat → List Nat
  | [] => [value]
  | head :: tail =>
      if value <= head then value :: head :: tail else head :: insertSorted value tail

private def median (samples : Array Nat) : Nat :=
  let sorted := samples.toList.foldl (fun values sample => insertSorted sample values) []
  sorted[sorted.length / 2]?.getD 0

private def formatSamples (samples : Array Nat) : String :=
  String.intercalate "," (samples.toList.map toString)

private def formatHundredths (value : Nat) : String :=
  let fraction := value % 100
  let fractionText := if fraction < 10 then s!"0{fraction}" else toString fraction
  s!"{value / 100}.{fractionText}"

private def reportAndGate (label : String) (iterations : Nat)
    (baselineSamples candidateSamples : Array Nat) : IO Unit := do
  let baseline := median baselineSamples
  let candidate := median candidateSamples
  let baselinePerOp := if iterations == 0 then 0 else baseline * 100 / iterations
  let candidatePerOp := if iterations == 0 then 0 else candidate * 100 / iterations
  let speedup := if candidate == 0 then 0 else baseline * 100 / candidate
  IO.println s!"{label}_generic_samples_ns={formatSamples baselineSamples}"
  IO.println s!"{label}_cached_samples_ns={formatSamples candidateSamples}"
  IO.println s!"{label}_generic_median_ns_per_pair={formatHundredths baselinePerOp}"
  IO.println s!"{label}_cached_median_ns_per_pair={formatHundredths candidatePerOp}"
  IO.println s!"{label}_speedup_x={formatHundredths speedup}"
  if candidate * 2 > baseline then
    throw (IO.userError s!"{label} response HPACK cache missed the required 2x gate")

private def parseNat (value? : Option String) (fallback : Nat) : Nat :=
  (value? >>= String.toNat?).getD fallback

def main (args : List String) : IO Unit := do
  let iterations := parseNat args.head? 50000
  let rounds := Nat.max 3 (parseNat (args.drop 1).head? 7)
  verifyOracle false
  verifyOracle true
  IO.println s!"common response HPACK: {rounds} alternating rounds x {iterations} block pairs"
  let mut identityGeneric := #[]
  let mut identityCached := #[]
  let mut gzipGeneric := #[]
  let mut gzipCached := #[]
  for round in [0:rounds] do
    let reverse := round % 2 == 1
    if reverse then
      let gzip ← measurePair true iterations reverse
      gzipGeneric := gzipGeneric.push gzip.1
      gzipCached := gzipCached.push gzip.2
      let identity ← measurePair false iterations reverse
      identityGeneric := identityGeneric.push identity.1
      identityCached := identityCached.push identity.2
    else
      let identity ← measurePair false iterations reverse
      identityGeneric := identityGeneric.push identity.1
      identityCached := identityCached.push identity.2
      let gzip ← measurePair true iterations reverse
      gzipGeneric := gzipGeneric.push gzip.1
      gzipCached := gzipCached.push gzip.2
  reportAndGate "identity" iterations identityGeneric identityCached
  reportAndGate "gzip" iterations gzipGeneric gzipCached
  IO.println "response HPACK cache benchmark gates passed"
