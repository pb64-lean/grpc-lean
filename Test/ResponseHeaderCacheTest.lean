import Grpc

open Grpc

namespace Test.ResponseHeaderCache

def fail (message : String) : IO α :=
  throw (IO.userError message)

def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do fail message

def expectEq [BEq α] (actual expected : α) (message : String) : IO Unit :=
  expect (actual == expected) message

def expectOk (result : Except Status α) (context : String) : IO α :=
  match result with
  | .ok value => pure value
  | .error status => fail s!"{context}: {status.code}: {status.messageD}"

def sameBytes (left right : ByteArray) : Bool :=
  left.data == right.data

def expectSameState (actual expected : Http2.Hpack.State) (message : String) : IO Unit := do
  expectEq actual.dynamic expected.dynamic s!"{message}: dynamic table changed"
  expectEq actual.maxSize expected.maxSize s!"{message}: selected table size changed"
  expectEq actual.maxAllowedSize expected.maxAllowedSize
    s!"{message}: peer table limit changed"
  expectEq actual.pendingSizeUpdate expected.pendingSizeUpdate
    s!"{message}: pending table update changed"

def eligibleState (maxAllowedSize : Nat := Http2.Hpack.defaultDynamicTableSize) :
    Http2.Hpack.State :=
  { (Http2.Hpack.withoutDynamicTable {}) with
    maxAllowedSize := maxAllowedSize, pendingSizeUpdate := none }

def headersFor (gzip : Bool) : Metadata :=
  if gzip then
    Headers.responseHeaders.insert "grpc-encoding" Headers.gzipEncoding
  else
    Headers.responseHeaders

def genericCommonBlocks (state : Http2.Hpack.State) (gzip : Bool) :
    Except Status Http2.Transport.TestSupport.ResponseHeaderBlocks := do
  let initial ← Http2.Hpack.encodeHeaderBlock state (headersFor gzip)
  let trailers ← Http2.Hpack.encodeHeaderBlock initial.2 (Headers.trailers Status.ok)
  pure { initial := initial.1, trailers := trailers.1, state := trailers.2 }

def expectSameBlocks (actual expected : Http2.Transport.TestSupport.ResponseHeaderBlocks)
    (context : String) : IO Unit := do
  expect (sameBytes actual.initial expected.initial) s!"{context}: initial block differs"
  expect (sameBytes actual.trailers expected.trailers) s!"{context}: trailer block differs"
  expectSameState actual.state expected.state context

def testEligibilityGuards : IO Unit := do
  let reusable := eligibleState 123
  expect reusable.canReuseHeaderBlock
    "zero-table state without entries or a pending update should be reusable"
  expect ({ reusable with maxAllowedSize := 0 }).canReuseHeaderBlock
    "peer upper bound should not affect zero-table block reuse"
  expect (!(Http2.Hpack.withoutDynamicTable {}).canReuseHeaderBlock)
    "pending zero-size update must prevent block reuse"
  expect (!({} : Http2.Hpack.State).canReuseHeaderBlock)
    "enabled dynamic table must prevent block reuse"
  expect (!({ reusable with dynamic := #[Header.of "x-stale" "entry"] }).canReuseHeaderBlock)
    "stale dynamic entries must prevent block reuse"
  expect (!({ reusable with maxSize := 1 }).canReuseHeaderBlock)
    "nonzero selected table size must prevent block reuse"

def testCachedBlocksMatchGeneric : IO Unit := do
  let state := eligibleState 91
  for gzip in [false, true] do
    let expected ← expectOk (genericCommonBlocks state gzip) "encode generic oracle"
    let actual ← expectOk
      (Http2.Transport.TestSupport.encodeCommonResponseHeaderBlocks state gzip)
      "encode cached common blocks"
    expectSameBlocks actual expected s!"gzip={gzip}"
    expectSameState actual.state state s!"gzip={gzip}: reusable encoding"
    let initial ← expectOk (Http2.Hpack.decodeHeaderBlock state actual.initial)
      "decode cached initial block"
    expectEq (Metadata.get? initial.headers "grpc-encoding")
      (if gzip then some "gzip" else none)
      s!"gzip={gzip}: wrong grpc-encoding"
    let trailers ← expectOk
      (Http2.Hpack.decodeHeaderBlock initial.state actual.trailers)
      "decode cached trailer block"
    expectEq (Metadata.get? trailers.headers "grpc-status") (some "0")
      s!"gzip={gzip}: cached trailers lost OK status"

def testGenericFallbackStates : IO Unit := do
  let pending := Http2.Hpack.withoutDynamicTable {}
  let pendingExpected ← expectOk (genericCommonBlocks pending false)
    "encode pending-update oracle"
  let pendingActual ← expectOk
    (Http2.Transport.TestSupport.encodeCommonResponseHeaderBlocks pending false)
    "encode pending-update fallback"
  expectSameBlocks pendingActual pendingExpected "pending-update fallback"
  expect pendingActual.state.pendingSizeUpdate.isNone
    "generic fallback did not consume the pending table-size update"
  expectEq pendingActual.initial.data[0]? (some (UInt8.ofNat 0x20))
    "first response did not lead with the zero-size table update"

  let dynamic : Http2.Hpack.State := {}
  let dynamicExpected ← expectOk (genericCommonBlocks dynamic true)
    "encode dynamic-table oracle"
  let dynamicActual ← expectOk
    (Http2.Transport.TestSupport.encodeCommonResponseHeaderBlocks dynamic true)
    "encode dynamic-table fallback"
  expectSameBlocks dynamicActual dynamicExpected "dynamic-table fallback"
  expect (!dynamicActual.state.dynamic.isEmpty)
    "dynamic-table fallback failed to advance encoder state"

def testMetadataTrailerAndStatusGuards : IO Unit := do
  let state := eligibleState
  let response : UnaryResponse := {
    metadata := Metadata.empty.insert "x-response" "present",
    status := { code := .ok, message := some "unusual ok" },
    trailers := Metadata.empty.insert "x-trailer" "present",
    data := ByteArray.empty.push 7
  }
  let encoded ← expectOk
    (Http2.Transport.encodeUnaryResponseFrames state 9 response) "encode guarded response"
  expectEq encoded.1.size 3 "guarded unary response should use headers, data, trailers"
  let initial ← expectOk
    (Http2.Hpack.decodeHeaderBlock state encoded.1[0]!.payload) "decode guarded headers"
  expectEq (Metadata.get? initial.headers "x-response") (some "present")
    "custom response metadata was displaced by the cache"
  let trailers ← expectOk
    (Http2.Hpack.decodeHeaderBlock initial.state encoded.1[2]!.payload)
    "decode guarded trailers"
  expectEq (Metadata.get? trailers.headers "grpc-status") (some "0")
    "OK status was displaced by the cache"
  expectEq (Metadata.get? trailers.headers "grpc-message") (some "unusual ok")
    "noncanonical OK message incorrectly used cached trailers"
  expectEq (Metadata.get? trailers.headers "x-trailer") (some "present")
    "custom response trailers were displaced by the cache"

  let failure : UnaryResponse := {
    status := Status.error .invalidArgument "bad input",
    data := ByteArray.empty
  }
  let failed ← expectOk
    (Http2.Transport.encodeUnaryResponseFrames state 11 failure) "encode trailers-only failure"
  expectEq failed.1.size 1 "failure should remain a single trailers-only block"
  let failedHeaders ← expectOk
    (Http2.Hpack.decodeHeaderBlock state failed.1[0]!.payload)
    "decode trailers-only failure"
  expectEq (Metadata.get? failedHeaders.headers "grpc-status") (some "3")
    "failure status incorrectly used cached OK trailers"

def testConnectionIndependentFrames : IO Unit := do
  let state := eligibleState 17
  let response : UnaryResponse := { data := ByteArray.empty.push 42, status := Status.ok }
  let first ← expectOk
    (Http2.Transport.encodeUnaryResponseFrames state 1 response
      Http2.defaultMaxFramePayloadLength true)
    "encode first common response"
  let second ← expectOk
    (Http2.Transport.encodeUnaryResponseFrames state 3 response
      Http2.defaultMaxFramePayloadLength true)
    "encode concurrent common response"
  expectEq first.1.size 3 "first common response should have three frames"
  expectEq second.1.size 3 "second common response should have three frames"
  expect (sameBytes first.1[0]!.payload second.1[0]!.payload)
    "concurrent initial header payloads differed"
  expect (sameBytes first.1[2]!.payload second.1[2]!.payload)
    "concurrent trailer payloads differed"
  expect (first.1.all fun frame => frame.header.streamId == 1)
    "cached payload reused a frame header from another stream"
  expect (second.1.all fun frame => frame.header.streamId == 3)
    "cached payload reused a frame header from another stream"
  expectSameState first.2 state "first concurrent response"
  expectSameState second.2 state "second concurrent response"

def testCachedBlockContinuationSplitting : IO Unit := do
  let state := eligibleState
  let cached ← expectOk
    (Http2.Transport.TestSupport.encodeCommonResponseHeaderBlocks state false)
    "encode cached blocks for splitting oracle"
  let response : UnaryResponse := { data := ByteArray.empty, status := Status.ok }
  let encoded ← expectOk
    (Http2.Transport.encodeUnaryResponseFrames state 5 response 3 false)
    "encode split cached response"
  expect (encoded.1.any fun frame => frame.header.frameType == .continuation)
    "small frame limit did not split cached HPACK blocks"
  let mut initial := ByteArray.empty
  let mut trailers := ByteArray.empty
  let mut inTrailers := false
  for frame in encoded.1 do
    if frame.header.frameType == .data then
      inTrailers := true
    else if inTrailers then
      trailers := trailers.append frame.payload
    else
      initial := initial.append frame.payload
  expect (sameBytes initial cached.initial)
    "initial cached block changed while splitting into CONTINUATION frames"
  expect (sameBytes trailers cached.trailers)
    "cached trailers changed while splitting into CONTINUATION frames"

end Test.ResponseHeaderCache

def main : IO Unit := do
  Test.ResponseHeaderCache.testEligibilityGuards
  Test.ResponseHeaderCache.testCachedBlocksMatchGeneric
  Test.ResponseHeaderCache.testGenericFallbackStates
  Test.ResponseHeaderCache.testMetadataTrailerAndStatusGuards
  Test.ResponseHeaderCache.testConnectionIndependentFrames
  Test.ResponseHeaderCache.testCachedBlockContinuationSplitting
  IO.println "response header cache tests passed"
