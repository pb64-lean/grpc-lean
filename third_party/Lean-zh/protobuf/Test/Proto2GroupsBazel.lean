import Protobuf
import Binary.Hex

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/Proto2Groups.proto"

namespace Proto2GroupsBazel

def ofExcept {α} (e : Except ProtoError α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw (IO.userError err.toString)

def assert (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def assertEq [BEq α] (a b : α) (msg : String) : IO Unit := do
  assert (a == b) msg

def testProto2Groups : IO Unit := do
  let opt : _root_.test.proto2groups.GroupHolder.OptionalGroup := { value := some (2 : Int32) }
  let repA : _root_.test.proto2groups.GroupHolder.RepeatedGroup := { name := some "a" }
  let repB : _root_.test.proto2groups.GroupHolder.RepeatedGroup := { name := some "b" }
  let req : _root_.test.proto2groups.GroupHolder.RequiredGroup := { value := some (7 : Int32) }
  let val : _root_.test.proto2groups.GroupHolder := {
    optionalgroup := some opt,
    repeatedgroup := #[repA, repB],
    requiredgroup := some req
  }

  let msg ← ofExcept (_root_.test.proto2groups.GroupHolder.toMessage val)
  match (Message.getRecordsOf msg 1)[0]!.value with
  | .GROUPED _ => pure ()
  | _ => throw (IO.userError "optional group should encode as GROUPED")
  match (Message.getRecordsOf msg 3)[0]!.value with
  | .GROUPED _ => pure ()
  | _ => throw (IO.userError "repeated group should encode as GROUPED")
  match (Message.getRecordsOf msg 5)[0]!.value with
  | .GROUPED _ => pure ()
  | _ => throw (IO.userError "required group should encode as GROUPED")

  let bytes ← ofExcept (_root_.test.proto2groups.GroupHolder.encode val)
  assertEq bytes hex!"0b10020c1b2201611c1b2201621c2b30072c"
    "proto2 groups should use SGROUP/EGROUP wire tags"

  let decoded ← ofExcept (_root_.test.proto2groups.GroupHolder.decode bytes)
  match decoded.optionalgroup with
  | some group => assertEq group.value (some (2 : Int32)) "optional group value mismatch"
  | none => throw (IO.userError "optional group missing")
  assert (decoded.repeatedgroup.size == 2) "repeated group count mismatch"
  assertEq decoded.repeatedgroup[0]!.name (some "a") "first repeated group mismatch"
  assertEq decoded.repeatedgroup[1]!.name (some "b") "second repeated group mismatch"
  match decoded.requiredgroup with
  | some group => assertEq group.value (some (7 : Int32)) "required group value mismatch"
  | none => throw (IO.userError "required group missing")

end Proto2GroupsBazel

def main : IO Unit :=
  Proto2GroupsBazel.testProto2Groups
