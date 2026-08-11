module

public import Std.Async
public import Std.Sync.CancellationToken
public import Grpc.CancellationToken

public section

/-!
# Bounded cancellation utilities

The transport-independent cancellation owner used by RPC calls and channel
supervisors.  Keeping it separate from the gRPC call adapter lets small
targets depend on the exact same capability without pulling protocol modules
into their build.

Cancellation here is callback-safe on the pinned toolchain: the stock
`CancellationToken.cancel` resolves selector consumers while holding the
token-state mutex, so a synchronous `Selectable.one` completion can re-enter
that same non-recursive mutex through the winning selector's unregister hook.
`Cancellation.cancel` therefore commits the sticky cancellation transition
through `Grpc.CancellationToken.cancel`, which extracts all consumers under
the mutex and resolves them only after the mutex has been released.
-/

namespace Grpc

open Std.Async

/--
An idempotent external cancellation signal.  The gRPC call owner observes its
selector in the same race as the local deadline and then joins the exact call
before returning.
-/
structure Cancellation where
  private mk ::
  private token : Std.CancellationToken
  private identity : IO.Ref Unit

namespace Cancellation

def create : IO Cancellation := do
  pure (.mk (← Std.CancellationToken.new) (← IO.mkRef ()))

/--
Publish cancellation under the token mutex, then wake consumers only after the
mutex has been released.  The pinned Std implementation resolves consumers
inside `state.atomically`; a selector winner may synchronously run its
`unregisterFn`, which takes the same non-reentrant mutex.
-/
def cancel (cancellation : Cancellation) : BaseIO Unit := do
  discard <| Grpc.CancellationToken.cancel cancellation.token

def isCancelled (cancellation : Cancellation) : IO Bool :=
  cancellation.token.isCancelled

/-- Capability identity without exposing or rendering the underlying signal. -/
def same (left right : Cancellation) : BaseIO Bool :=
  left.identity.ptrEq right.identity

/--
Run one trusted ownership transition while holding the token state lock, but
only if cancellation has not yet linearized. Callers must not recursively
cancel this token from `action`.
-/
def linearizeIfActive
    (cancellation : Cancellation)
    (action : IO α) : IO (Option α) :=
  cancellation.token.state.atomically do
    if (← get).reason.isSome then
      pure none
    else
      some <$> action

def wait (cancellation : Cancellation) : IO Unit := do
  let waiter ← cancellation.token.wait
  waiter.block

/-- Selector projection used only by exact call-owner races. -/
def selector (cancellation : Cancellation) : Selector Unit := {
  tryFn := do
    if ← cancellation.isCancelled then
      pure (some ())
    else
      pure none
  registerFn := fun waiter => do
    let resolveNow ← cancellation.token.state.atomically do
      let state ← get
      if state.reason.isSome then
        pure true
      else
        set { state with
          consumers := state.consumers.enqueue (.select waiter)
        }
        pure false
    if resolveNow then
      let _ ← (Std.CancellationToken.Consumer.select waiter).resolve
      pure ()
    else
      pure ()
  unregisterFn := do
    cancellation.token.state.atomically do
      let state ← get
      let consumers ← state.consumers.filterM fun
        | .normal _ => pure true
        | .select waiter => do
            pure !(← waiter.checkFinished)
      set { state with consumers }
}

namespace TestSupport

/-- Number of registered waiters; exposed only for bounded-retention tests. -/
def registeredWaiters (cancellation : Cancellation) : BaseIO Nat :=
  cancellation.token.state.atomically do
    let state ← get
    pure (state.consumers.eList.length + state.consumers.dList.length)

end TestSupport

end Cancellation

end Grpc
