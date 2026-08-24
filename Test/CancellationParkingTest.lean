import Grpc

open Grpc

namespace Test.CancellationParking

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def expectEq [BEq α] (actual expected : α) (message : String) : IO Unit := do
  expect (actual == expected) message

private def expectOk (result : Except Status α) (description : String) : IO α := do
  match result with
  | .ok value => pure value
  | .error status =>
      throw (IO.userError s!"{description}: {status.code}: {status.messageD}")

/- Timing is only a watchdog around causally ordered Promise/task joins. No
assertion below depends on elapsed time. -/
private def watchdogMilliseconds : Nat := 5000

private partial def awaitTaskResultWithin (task : Task α) (remaining : Nat) :
    IO (Option α) := do
  if ← IO.hasFinished task then
    pure (some task.get)
  else if remaining == 0 then
    pure none
  else
    IO.sleep 1
    awaitTaskResultWithin task (remaining - 1)

private def awaitTaskResult (task : Task α) (description : String) : IO α := do
  match ← awaitTaskResultWithin task watchdogMilliseconds with
  | some result => pure result
  | none =>
      IO.cancel task
      throw (IO.userError s!"{description}: watchdog expired")

private def settleTask (task : Task α) : IO Unit := do
  match ← awaitTaskResultWithin task watchdogMilliseconds with
  | some _ => pure ()
  | none => IO.cancel task

private def awaitPromise (promise : IO.Promise α) (description : String) : IO α := do
  let waiter ← IO.asTask do
    match ← IO.wait promise.result? with
    | some value => pure value
    | none => throw (IO.userError s!"{description}: promise was dropped")
  match ← awaitTaskResult waiter description with
  | .ok value => pure value
  | .error error => throw error

private partial def awaitCondition (description : String) (remaining : Nat)
    (condition : IO Bool) : IO Unit := do
  if ← condition then
    pure ()
  else if remaining == 0 then
    throw (IO.userError s!"{description}: watchdog expired")
  else
    IO.sleep 1
    awaitCondition description (remaining - 1) condition

private def awaitProcess
    (task : Task (Except IO.Error (Except Status Unit)))
    (description : String) : IO Unit := do
  match ← awaitTaskResult task description with
  | .error error => throw error
  | .ok result => discard <| expectOk result description

private def service : String := "lean.test.CancellationParking"

private def methodNamed (method : String) : MethodName :=
  { service, method }

private def requestMetadata (method : MethodName) : Metadata :=
  Metadata.empty
    |>.insert ":method" "POST"
    |>.insert ":scheme" "http"
    |>.insert ":authority" "localhost"
    |>.insert ":path" method.path
    |>.insert "content-type" "application/grpc"
    |>.insert "te" "trailers"

private structure EncodedRequest where
  wire : ByteArray
  hpack : Http2.Hpack.State

private def frameWire (frameType : Http2.FrameType) (flags : UInt8)
    (streamId : Nat) (payload : ByteArray) : IO ByteArray := do
  let frame : Http2.Frame := {
    header := {
      length := payload.size
      frameType
      flags
      streamId
    }
    payload
  }
  expectOk (Http2.Frame.encode frame) "encode HTTP/2 test frame"

private def requestWire (hpack : Http2.Hpack.State) (streamId : Nat)
    (method : MethodName) (payload : ByteArray) : IO EncodedRequest := do
  let encoded ← expectOk
    (Http2.Hpack.encodeHeaderBlock hpack (requestMetadata method))
    "encode request header block"
  let headers ← frameWire .headers Http2.FrameFlag.endHeaders streamId encoded.1
  let message ← expectOk (Message.encode { data := payload })
    "encode gRPC request message"
  let data ← frameWire .data Http2.FrameFlag.endStream streamId message
  pure { wire := headers.append data, hpack := encoded.2 }

private def resetWire (streamId : Nat) : IO ByteArray := do
  let frame ← expectOk (Http2.RstStream.frame streamId .cancel)
    "construct peer RST_STREAM"
  expectOk (Http2.Frame.encode frame) "encode peer RST_STREAM"

private structure ConnectionHarness where
  state : Std.Mutex Http2.Connection.State
  emitted : IO.Ref (Array Http2.Frame)

private def ConnectionHarness.new : IO ConnectionHarness := do
  let state ← Std.Mutex.new ({
    prefaceReceived := true
    clientSettingsReceived := true
  } : Http2.Connection.State)
  let emitted ← IO.mkRef (#[] : Array Http2.Frame)
  pure { state, emitted }

private def ConnectionHarness.emit (harness : ConnectionHarness)
    (frames : Array Http2.Frame) : IO Unit :=
  harness.emitted.modify fun emitted => emitted.append frames

private def ConnectionHarness.process (harness : ConnectionHarness)
    (registry : Registry) (wire : ByteArray) : IO (Except Status Unit) :=
  Http2.Connection.processBytesSharedWith registry harness.state wire harness.emit

private def streamIsActive (harness : ConnectionHarness) (streamId : Nat) : IO Bool :=
  harness.state.atomically do
    let state ← get
    pure (state.activeDispatches.any fun dispatch => dispatch.streamId == streamId)

private def expectResetCleanupEntered (harness : ConnectionHarness) : IO Unit := do
  awaitCondition "RST_STREAM did not detach the cancelled dispatch"
    watchdogMilliseconds do
      pure (!(← streamIsActive harness 1))
  let state ← harness.state.atomically get
  expectEq state.lastClientStreamId 1
    "a later stream was processed before reset cleanup finished"

private def expectFastResponseEventually (harness : ConnectionHarness)
    (entered : IO.Promise Unit) : IO Unit := do
  awaitPromise entered "wait for the later stream handler"
  awaitCondition "the later stream dispatch did not retire"
    watchdogMilliseconds do
      pure (!(← streamIsActive harness 3))
  let emitted ← harness.emitted.get
  expect (emitted.any fun frame =>
    frame.header.streamId == 3 && frame.header.frameType == .data)
    "the later stream handler ran without emitting response DATA"
  expect (!(emitted.any fun frame =>
    frame.header.streamId == 3 && frame.header.frameType == .rstStream))
    "the later stream was reset instead of completing normally"

private def cancelHarness (harness : ConnectionHarness) : IO Unit := do
  try
    discard <| Http2.Connection.cancelActiveShared harness.state
  catch _ =>
    pure ()

/- A peer reset removes the stream from connection state before joining its
exact handler task. A handler suspended on a Promise deliberately ignores task
cancellation; the next decoded stream must remain behind that join and then
run normally once the original task is released. -/
private def testResetWaitsForUncooperativeHandler : IO Unit := do
  let slowMethod := methodNamed "SlowUnary"
  let fastMethod := methodNamed "FastAfterUnaryReset"
  let handlerEntered ← IO.Promise.new
  let releaseHandler ← IO.Promise.new
  let fastEntered ← IO.Promise.new
  let registry := Registry.empty
    |>.registerUnary slowMethod (fun request => do
      handlerEntered.resolve ()
      match ← IO.wait releaseHandler.result? with
      | none => throw (Status.internal "slow unary release gate was dropped")
      | some () =>
          pure { data := request.data, status := Status.ok })
    |>.registerUnary fastMethod (fun request => do
      fastEntered.resolve ()
      pure { data := request.data, status := Status.ok })
  let harness ← ConnectionHarness.new
  let processingRef ← IO.mkRef
    (none : Option (Task (Except IO.Error (Except Status Unit))))
  try
    let slow ← requestWire {} 1 slowMethod "slow".toUTF8
    discard <| expectOk (← harness.process registry slow.wire)
      "publish the slow unary dispatch"
    awaitPromise handlerEntered "wait for the slow unary handler"

    let fast ← requestWire slow.hpack 3 fastMethod "fast".toUTF8
    let reset ← resetWire 1
    let processing ← IO.asTask (harness.process registry (reset.append fast.wire))
    processingRef.set (some processing)

    expectResetCleanupEntered harness
    expect (!(← IO.hasFinished processing))
      "frame processing escaped an uncooperative cancelled handler"
    expect (!(← fastEntered.isResolved))
      "the later stream entered while cancelled-handler cleanup was blocked"

    releaseHandler.resolve ()
    awaitProcess processing "finish reset-time handler cleanup"
    expectFastResponseEventually harness fastEntered
  finally
    releaseHandler.resolve ()
    if let some processing ← processingRef.get then settleTask processing
    cancelHarness harness

/- Response-stream cancellation is taken exactly once before the cancelled
dispatch is joined. Holding that callback proves that later frames on the same
connection remain parked; releasing it also wakes the cancelled recv task so
the owner can retire and process the following stream. -/
private def testResetWaitsForUncooperativeStreamCancel : IO Unit := do
  let streamMethod := methodNamed "SlowResponseStream"
  let fastMethod := methodNamed "FastAfterStreamReset"
  let recvEntered ← IO.Promise.new
  let releaseRecv ← IO.Promise.new
  let cancelEntered ← IO.Promise.new
  let releaseCancel ← IO.Promise.new
  let cancelCount ← IO.mkRef 0
  let fastEntered ← IO.Promise.new
  let registry := Registry.empty
    |>.registerServerStreamingStream streamMethod (fun _ => do
      pure {
        messages := {
          recv? := do
            recvEntered.resolve ()
            match ← IO.wait releaseRecv.result? with
            | none => throw (Status.internal "response recv release gate was dropped")
            | some () => pure none
          cancel := do
            cancelCount.modify fun count => count + 1
            cancelEntered.resolve ()
            match ← IO.wait releaseCancel.result? with
            | none => throw (Status.internal "response cancel release gate was dropped")
            | some () =>
                releaseRecv.resolve ()
        }
        status := Status.ok
      })
    |>.registerUnary fastMethod (fun request => do
      fastEntered.resolve ()
      pure { data := request.data, status := Status.ok })
  let harness ← ConnectionHarness.new
  let processingRef ← IO.mkRef
    (none : Option (Task (Except IO.Error (Except Status Unit))))
  try
    let slow ← requestWire {} 1 streamMethod "stream".toUTF8
    discard <| expectOk (← harness.process registry slow.wire)
      "publish the response-stream dispatch"
    awaitPromise recvEntered "wait for the response stream recv callback"

    let fast ← requestWire slow.hpack 3 fastMethod "fast".toUTF8
    let reset ← resetWire 1
    let processing ← IO.asTask (harness.process registry (reset.append fast.wire))
    processingRef.set (some processing)

    awaitPromise cancelEntered "wait for the response stream cancel callback"
    expectResetCleanupEntered harness
    expectEq (← cancelCount.get) 1
      "reset must take the response stream cancel callback exactly once"
    expect (!(← IO.hasFinished processing))
      "frame processing escaped an uncooperative stream cancel callback"
    expect (!(← fastEntered.isResolved))
      "the later stream entered while stream-cancel cleanup was blocked"

    releaseCancel.resolve ()
    awaitProcess processing "finish reset-time response stream cleanup"
    expectFastResponseEventually harness fastEntered
    expectEq (← cancelCount.get) 1
      "response stream cancellation ran more than once during retirement"
  finally
    releaseCancel.resolve ()
    releaseRecv.resolve ()
    if let some processing ← processingRef.get then settleTask processing
    cancelHarness harness

def run : IO Unit := do
  testResetWaitsForUncooperativeHandler
  IO.println "RST_STREAM parks later frames until cancelled handler retirement"
  testResetWaitsForUncooperativeStreamCancel
  IO.println "RST_STREAM parks later frames until stream-cancel retirement"

end Test.CancellationParking

def main : IO Unit :=
  Test.CancellationParking.run
