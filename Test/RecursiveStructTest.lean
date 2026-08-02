import Protobuf
import RecursiveProtoTest.recursive_struct

open Protobuf Encoding

namespace RecursiveStructTest

def ofExcept {α} (result : Except ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

def expect (condition : Bool) (failureMessage : String) : IO Unit := do
  if condition then pure () else throw (IO.userError failureMessage)

def expectEq [BEq α] (actual expected : α) (failureMessage : String) : IO Unit :=
  expect (actual == expected) failureMessage

def numberValue (number : Float) : _root_.test.recursive.Value :=
  { kind := some (.number_value number) }

def testRecursiveMapRoundTrip : IO Unit := do
  let leaf := numberValue 42.5
  let nestedFields := ({} : RecursiveMap String _root_.test.recursive.Value)
    |>.insert "answer" leaf
  let nestedStruct : _root_.test.recursive.Struct := {
    fields := nestedFields,
    «message» := "nested recursive value"
  }
  let nestedValue : _root_.test.recursive.Value := {
    kind := some (.struct_value nestedStruct)
  }
  let value : _root_.test.recursive.Value := {
    kind := some (.list_value { values := #[nestedValue, leaf] })
  }

  let encoded ← ofExcept (_root_.test.recursive.Value.encode value)
  let decoded ← ofExcept (_root_.test.recursive.Value.decode encoded)
  let some (.list_value decodedList) := decoded.kind
    | throw (IO.userError "recursive list case did not round-trip")
  let some first := decodedList.values[0]?
    | throw (IO.userError "recursive list lost its first value")
  let some (.struct_value decodedStruct) := first.kind
    | throw (IO.userError "recursive struct case did not round-trip")
  let some decodedLeaf := decodedStruct.fields.get? "answer"
    | throw (IO.userError "recursive map lost its entry")
  let some (.number_value decodedNumber) := decodedLeaf.kind
    | throw (IO.userError "recursive map value changed oneof case")
  expectEq decodedNumber 42.5 "recursive map value did not round-trip"
  expectEq decodedStruct.«message» "nested recursive value"
    "protobuf field matching a notation keyword did not round-trip"

def testRecursiveMapMergeRightWins : IO Unit := do
  let left : _root_.test.recursive.Struct := {
    fields := ({} : RecursiveMap String _root_.test.recursive.Value)
      |>.insert "duplicate" (numberValue 1.0)
      |>.insert "left" (numberValue 2.0)
  }
  let right : _root_.test.recursive.Struct := {
    fields := ({} : RecursiveMap String _root_.test.recursive.Value)
      |>.insert "duplicate" (numberValue 9.0)
      |>.insert "right" (numberValue 3.0)
  }
  let merged := _root_.test.recursive.Struct.merge left right
  expect (merged.fields.contains "left") "recursive map merge lost a left-only key"
  expect (merged.fields.contains "right") "recursive map merge lost a right-only key"
  let some duplicate := merged.fields.get? "duplicate"
    | throw (IO.userError "recursive map merge lost its duplicate key")
  let some (.number_value duplicateNumber) := duplicate.kind
    | throw (IO.userError "recursive map merge changed its duplicate value case")
  expectEq duplicateNumber 9.0 "recursive map merge must keep the right-hand value"

end RecursiveStructTest

def main : IO Unit := do
  RecursiveStructTest.testRecursiveMapRoundTrip
  RecursiveStructTest.testRecursiveMapMergeRightWins
  IO.println "recursive protobuf map tests passed"
