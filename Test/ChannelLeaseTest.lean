import Lean.Elab.Tactic.Decide
import Grpc

namespace ChannelLeaseTest

open Grpc.ChannelLease

private def lifecycleTrace : Bool := Id.run do
  let state := State.initial
  let .ok first := acquire state | return false
  let .ok second := acquire first.state | return false
  if second.state.activeCount != 2 then return false
  if first.lease == second.lease then return false

  let closing := beginClose second.state
  if closing.decision != .claimed || closing.state.phase != .draining then
    return false
  match acquire closing.state with
  | .error .draining => pure ()
  | _ => return false
  if (beginClose closing.state).decision != .joined then return false
  match finishClose closing.state with
  | .error (.activeLeases 2) => pure ()
  | _ => return false

  let .ok oneLeft := release closing.state first.lease | return false
  if oneLeft.activeCount != 1 then return false
  match finishClose oneLeft with
  | .error (.activeLeases 1) => pure ()
  | _ => return false
  match release oneLeft first.lease with
  | .error .unknownLease => pure ()
  | _ => return false

  let .ok drained := release oneLeft second.lease | return false
  let .ok closed := finishClose drained | return false
  match acquire closed with
  | .error .closed =>
      return closed.phase == .closed &&
        closed.activeCount == 0 &&
        (beginClose closed).decision == .completed
  | _ => return false

example : lifecycleTrace = true := by native_decide

example :
    State.initial.Invariant := by
  exact State.initial.invariant

def run : IO Unit := do
  if !lifecycleTrace then
    throw (IO.userError "remote channel lifecycle trace failed")
  IO.println "Remote channel ownership tests passed"

end ChannelLeaseTest

def main : IO Unit :=
  ChannelLeaseTest.run
