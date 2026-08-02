module

public import Std.Sync.CancellationToken

public section

/-!
# Callback-safe cancellation

The pinned Lean runtime resolves cancellation consumers while holding the
token-state mutex.  A synchronous `Selectable.one` consumer unregisters all of
its selectors as part of resolution, which can re-enter the winning token's
non-recursive mutex and deadlock.

This operation commits the sticky cancellation transition and extracts the
consumer set under the mutex, then resolves the consumers after releasing the
mutex.  The Boolean result elects the one caller that performed the transition.
-/

namespace Grpc.CancellationToken

def cancel (token : Std.CancellationToken)
    (reason : Std.CancellationReason := .cancel) : BaseIO Bool := do
  let consumers? ← token.state.atomically do
    let state ← get
    if state.reason.isSome then
      pure none
    else
      set { state with reason := some reason, consumers := ∅ }
      pure (some state.consumers.toArray)
  match consumers? with
  | none => pure false
  | some consumers =>
      for consumer in consumers do
        discard <| consumer.resolve
      pure true

end Grpc.CancellationToken
