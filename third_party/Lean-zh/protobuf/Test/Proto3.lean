module

import Protobuf.Encoding
meta import Protobuf.Notation
meta import Protobuf.Elab
import Binary.Hex

open Protobuf Encoding
open scoped Protobuf.Notation

set_option protobuf.trace.notation true

-- set_option trace.Elab.definition true

#load_proto_file "Test/Proto3.proto"

message RequiredAndDefault {
  required int32 req_int32 = 1 [default = 0];
  optional int32 opt_int32 = 2 [default = 7];
}

extend _root_.test.proto3.All {
  optional int32 ext_int32 = 100;
  repeated int32 ext_rep_int32 = 101 [packed = true];
  optional _root_.test.proto3.Sub ext_sub = 102;
}

def ofExcept {α} (e : Except ProtoError α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw (IO.userError err.toString)

def assert (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def assertEq [BEq α] (a b : α) (msg : String) : IO Unit := do
  assert (a == b) msg

def mkPackedVarints (xs : Array Nat) : ProtoVal :=
  ProtoVal.of_packed (xs.map ProtoVal.VARINT)

def mkPackedI32 (xs : Array UInt32) : ProtoVal :=
  ProtoVal.of_packed (xs.map fun x => ProtoVal.I32 x.toBitVec)

def mkPackedI64 (xs : Array UInt64) : ProtoVal :=
  ProtoVal.of_packed (xs.map fun x => ProtoVal.I64 x.toBitVec)

def mkMapEntry (key : String) (value? : Option Int32 := none) : Except ProtoError ProtoVal := do
  let msg := Message.set Message.empty 1 (.LEN key.toUTF8)
  let msg ← match value? with
    | some value => do
        let protoVal ← ProtoVal.ofVarint_int32 value
        pure (Message.set msg 2 protoVal)
    | none => pure msg
  ProtoVal.ofMessage msg

def testDefaults : IO Unit := do
  let val : _root_.test.proto3.All := default
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert msg.records.isEmpty "proto3 defaults should not serialize"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage Message.empty)
  assertEq decoded.int32_field (0 : Int32) "default int32_field mismatch"
  assertEq decoded.string_field "" "default string_field mismatch"
  assertEq decoded.bool_field false "default bool_field mismatch"
  assertEq decoded.bytes_field ByteArray.empty "default bytes_field mismatch"
  assertEq decoded.float_field (0 : Float32) "default float_field mismatch"
  assertEq decoded.double_field (0 : Float) "default double_field mismatch"
  assertEq decoded.uint32_field (0 : UInt32) "default uint32_field mismatch"
  assertEq decoded.uint64_field (0 : UInt64) "default uint64_field mismatch"
  assertEq decoded.sint32_field (0 : Int32) "default sint32_field mismatch"
  assertEq decoded.sint64_field (0 : Int64) "default sint64_field mismatch"
  assertEq decoded.fixed32_field (0 : UInt32) "default fixed32_field mismatch"
  assertEq decoded.fixed64_field (0 : UInt64) "default fixed64_field mismatch"
  assertEq decoded.sfixed32_field (0 : Int32) "default sfixed32_field mismatch"
  assertEq decoded.sfixed64_field (0 : Int64) "default sfixed64_field mismatch"
  assertEq decoded.color _root_.test.proto3.Color.COLOR_UNSPECIFIED "default enum mismatch"
  assert decoded.sub.isNone "default sub mismatch"
  assertEq decoded.opt_int32 none "default opt_int32 mismatch"
  assertEq decoded.rep_int32 #[] "default rep_int32 mismatch"
  assertEq decoded.rep_int32_unpacked #[] "default rep_int32_unpacked mismatch"
  assertEq decoded.rep_color #[] "default rep_color mismatch"
  assertEq decoded.rep_fixed32 #[] "default rep_fixed32 mismatch"
  assertEq decoded.rep_fixed64 #[] "default rep_fixed64 mismatch"
  assert (decoded.map_str_int32.size == 0) "default map mismatch"
  assert decoded.choice.isNone "default choice mismatch"
  assert decoded.rep_sub.isEmpty "default rep_sub mismatch"

def testOptionalPresence : IO Unit := do
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with opt_int32 := some 0 }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert ((Message.getRecordsOf msg 17).size == 1) "optional field should serialize when set"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.opt_int32 (some (0 : Int32)) "optional presence mismatch"

def testSubPresence : IO Unit := do
  let sub : _root_.test.proto3.Sub := { id := 0, label := "z" }
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with sub := some sub }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert ((Message.getRecordsOf msg 16).size == 1) "message field should serialize when present"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.sub with
  | some v =>
      assertEq v.id (0 : Int32) "message field presence mismatch"
      assertEq v.label "z" "message field nested label mismatch"
  | none => throw (IO.userError "message field presence mismatch")

def testRequiredAndDefaultPresence : IO Unit := do
  let val : RequiredAndDefault := default
  assertEq val.opt_int32 none "optional field with default should start absent"
  let msg ← ofExcept (RequiredAndDefault.toMessage val)
  assert ((Message.getRecordsOf msg 1).size == 1) "required scalar should serialize even at default value"
  assert ((Message.getRecordsOf msg 2).isEmpty) "absent optional default should not serialize"
  let withDefault : RequiredAndDefault := { val with opt_int32 := some 7 }
  let withDefaultMsg ← ofExcept (RequiredAndDefault.toMessage withDefault)
  assert ((Message.getRecordsOf withDefaultMsg 2).size == 1) "present optional default should serialize"
  let decoded ← ofExcept (RequiredAndDefault.fromMessage (Message.set Message.empty 1 (.VARINT 0)))
  assertEq decoded.opt_int32 none "missing optional default should decode as absent"
  match RequiredAndDefault.fromMessage Message.empty with
  | .error (.missingRequiredField _) => pure ()
  | .error err => throw (IO.userError s!"missing required scalar should report missingRequiredField, got {err}")
  | .ok _ => throw (IO.userError "missing required scalar should fail")

def testSingularLastWins : IO Unit := do
  let msg := Message.set Message.empty 1 (.VARINT 1)
  let msg := Message.set msg 1 (.VARINT 9)
  let msg := Message.set msg 2 (.LEN "first".toUTF8)
  let msg := Message.set msg 2 (.LEN "".toUTF8)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.int32_field (9 : Int32) "duplicate singular int32 should keep last value"
  assertEq decoded.string_field "" "duplicate singular string should keep last value, including empty"

def testSubMessageMerge : IO Unit := do
  let sub1 : _root_.test.proto3.Sub := { id := 1, label := "" }
  let sub2 : _root_.test.proto3.Sub := { id := 0, label := "merged" }
  let msg1 ← ofExcept sub1.toMessage
  let msg2 ← ofExcept sub2.toMessage
  let val1 ← ofExcept <| ProtoVal.ofMessage msg1
  let val2 ← ofExcept <| ProtoVal.ofMessage msg2
  let msg := Message.set Message.empty 16 val1
  let msg := Message.set msg 16 val2
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.sub with
  | some v =>
      assertEq v.id (1 : Int32) "submessage merge should retain earlier scalar when later message omits it"
      assertEq v.label "merged" "submessage merge should apply later fields"
  | none => throw (IO.userError "submessage merge presence mismatch")

def testOneof : IO Unit := do
  let choice : _root_.test.proto3.All.choice_Type := _root_.test.proto3.All.choice_Type.oneof_int32 7
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with choice := some choice }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  assert ((Message.getRecordsOf msg 22).size == 1) "oneof field did not serialize"
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.choice with
  | some (.oneof_int32 v) => assertEq v (7 : Int32) "oneof int32 value mismatch"
  | _ => throw (IO.userError "oneof decode mismatch")
  assert ((decoded.«Unknown.Fields».get? 22).isNone) "decoded oneof field should not be preserved as unknown"
  let roundtrip ← ofExcept (_root_.test.proto3.All.toMessage decoded)
  assert ((Message.getRecordsOf roundtrip 22).size == 1) "decoded oneof field should not be duplicated on round-trip"

def testOneofLastWins : IO Unit := do
  let msg := Message.set Message.empty 22 (.VARINT 7)
  let msg := Message.set msg 23 (.LEN "later".toUTF8)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.choice with
  | some (.oneof_string v) => assertEq v "later" "oneof should keep the last wire member"
  | _ => throw (IO.userError "oneof last-one-wins mismatch")

def testOneofMessageMergesSameCase : IO Unit := do
  let sub1 : _root_.test.proto3.Sub := { id := 1, label := "" }
  let sub2 : _root_.test.proto3.Sub := { id := 0, label := "later" }
  let msg1 ← ofExcept sub1.toMessage
  let msg2 ← ofExcept sub2.toMessage
  let val1 ← ofExcept <| ProtoVal.ofMessage msg1
  let val2 ← ofExcept <| ProtoVal.ofMessage msg2
  let msg := Message.set Message.empty 24 val1
  let msg := Message.set msg 24 val2
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.choice with
  | some (.oneof_sub v) =>
      assertEq v.id (1 : Int32) "oneof message merge should retain earlier scalar when later message omits it"
      assertEq v.label "later" "oneof message merge should apply later fields"
  | _ => throw (IO.userError "oneof message merge mismatch")

def testOneofMerge : IO Unit := do
  let base : _root_.test.proto3.All := default
  let leftSub : _root_.test.proto3.Sub := { id := 1, label := "" }
  let rightSub : _root_.test.proto3.Sub := { id := 0, label := "merged" }
  let left : _root_.test.proto3.All := {
    base with choice := some (_root_.test.proto3.All.choice_Type.oneof_sub leftSub)
  }
  let right : _root_.test.proto3.All := {
    base with choice := some (_root_.test.proto3.All.choice_Type.oneof_sub rightSub)
  }
  let merged := _root_.test.proto3.All.merge left right
  match merged.choice with
  | some (_root_.test.proto3.All.choice_Type.oneof_sub sub) =>
      assertEq sub.id (1 : Int32) "merged oneof message case should retain earlier scalar when right omits it"
      assertEq sub.label "merged" "merged oneof message case should apply right-hand fields"
  | _ => throw (IO.userError "merged same oneof message case should remain oneof_sub")
  let replacement : _root_.test.proto3.All := {
    base with choice := some (_root_.test.proto3.All.choice_Type.oneof_int32 5)
  }
  let replaced := _root_.test.proto3.All.merge left replacement
  match replaced.choice with
  | some (_root_.test.proto3.All.choice_Type.oneof_int32 n) =>
      assertEq n (5 : Int32) "different oneof case should replace"
  | _ => throw (IO.userError "different oneof case should replace previous case")

def testPackedAndUnpacked : IO Unit := do
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := {
    base with
    rep_int32 := #[(1 : Int32), 2],
    rep_int32_unpacked := #[(3 : Int32), 4]
  }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  let repPacked := Message.getRecordsOf msg 18
  assert (repPacked.size == 1) "packed repeated field should be a single record"
  match repPacked[0]!.value with
  | .LEN _ => pure ()
  | _ => throw (IO.userError "packed repeated field should use LEN wire type")
  let repUnpacked := Message.getRecordsOf msg 19
  assert (repUnpacked.size == 2) "unpacked repeated field should be multiple records"
  for r in repUnpacked do
    match r.value with
    | .VARINT _ => pure ()
    | _ => throw (IO.userError "unpacked repeated field should use VARINT wire type")
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_int32 #[(1 : Int32), 2] "packed repeated decode mismatch"
  assertEq decoded.rep_int32_unpacked #[(3 : Int32), 4] "unpacked repeated decode mismatch"

def testPackedAcceptsUnpacked : IO Unit := do
  let msg := Message.set Message.empty 18 (.VARINT 1)
  let msg := Message.set msg 18 (.VARINT 2)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_int32 #[(1 : Int32), 2] "packed field should accept unpacked encoding"

def testUnpackedAcceptsPacked : IO Unit := do
  let msg := Message.set Message.empty 19 (mkPackedVarints #[3, 4])
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_int32_unpacked #[(3 : Int32), 4] "unpacked field should accept packed encoding"

def testPackedConcatenatesSegments : IO Unit := do
  let msg := Message.set Message.empty 18 (mkPackedVarints #[1, 2])
  let msg := Message.set msg 18 (mkPackedVarints #[3])
  let msg := Message.set msg 18 (.VARINT 4)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_int32 #[(1 : Int32), 2, 3, 4] "packed repeated field should concatenate multiple packed segments and unpacked records"

def testNegativeInt32Encoding : IO Unit := do
  let base : _root_.test.proto3.All := default
  let int32Msg ← ofExcept (_root_.test.proto3.All.toMessage { base with int32_field := (-1 : Int32) })
  let int32Bytes := Binary.Put.run (Binary.put int32Msg)
  assertEq int32Bytes hex!"08ffffffffffffffffff01" "negative int32 should sign-extend to a 10-byte varint"
  let sint32Msg ← ofExcept (_root_.test.proto3.All.toMessage { base with sint32_field := (-1 : Int32) })
  let sint32Bytes := Binary.Put.run (Binary.put sint32Msg)
  assertEq sint32Bytes hex!"4801" "negative sint32 should use ZigZag encoding"
  let sint64Msg ← ofExcept (_root_.test.proto3.All.toMessage { base with sint64_field := (-1 : Int64) })
  let sint64Bytes := Binary.Put.run (Binary.put sint64Msg)
  assertEq sint64Bytes hex!"5001" "negative sint64 should use ZigZag encoding"
  let repMsg ← ofExcept (_root_.test.proto3.All.toMessage { base with rep_int32 := #[(-1 : Int32)] })
  let repBytes := Binary.Put.run (Binary.put repMsg)
  assertEq repBytes hex!"92010affffffffffffffffff01" "packed negative int32 should contain the sign-extended varint"

def testPackedFixedWidth : IO Unit := do
  let base : _root_.test.proto3.All := default
  let fixed32 := #[(16909060 : UInt32), 84281096]
  let fixed64 := #[(1 : UInt64), 4294967297]
  let val : _root_.test.proto3.All := { base with rep_fixed32 := fixed32, rep_fixed64 := fixed64 }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  let rep32 := Message.getRecordsOf msg 26
  let rep64 := Message.getRecordsOf msg 27
  assert (rep32.size == 1) "packed fixed32 field should be a single record"
  assert (rep64.size == 1) "packed fixed64 field should be a single record"
  match rep32[0]!.value, rep64[0]!.value with
  | .LEN _, .LEN _ => pure ()
  | _, _ => throw (IO.userError "packed fixed-width fields should use LEN wire type")
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_fixed32 fixed32 "packed fixed32 decode mismatch"
  assertEq decoded.rep_fixed64 fixed64 "packed fixed64 decode mismatch"

def testPackedFixedWidthMixedSegments : IO Unit := do
  let msg := Message.set Message.empty 26 (mkPackedI32 #[(16909060 : UInt32), 84281096])
  let msg := Message.set msg 26 (.I32 (168496141 : UInt32).toBitVec)
  let msg := Message.set msg 27 (mkPackedI64 #[(1 : UInt64), 4294967297])
  let msg := Message.set msg 27 (.I64 (18446744073709551615 : UInt64).toBitVec)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.rep_fixed32 #[(16909060 : UInt32), 84281096, 168496141] "fixed32 should accept packed and unpacked records in order"
  assertEq decoded.rep_fixed64 #[(1 : UInt64), 4294967297, 18446744073709551615] "fixed64 should accept packed and unpacked records in order"

def testMapRoundtrip : IO Unit := do
  let map := Std.HashMap.ofList [("a", (1 : Int32)), ("b", (2 : Int32))]
  let base : _root_.test.proto3.All := default
  let val : _root_.test.proto3.All := { base with map_str_int32 := map }
  let msg ← ofExcept (_root_.test.proto3.All.toMessage val)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq (decoded.map_str_int32.get? "a") (some (1 : Int32)) "map value mismatch for key a"
  assertEq (decoded.map_str_int32.get? "b") (some (2 : Int32)) "map value mismatch for key b"

def testMapDuplicateKeyLastWins : IO Unit := do
  let entry1 ← ofExcept <| mkMapEntry "dup" (some 1)
  let entry2 ← ofExcept <| mkMapEntry "dup" (some 9)
  let msg := Message.set Message.empty 21 entry1
  let msg := Message.set msg 21 entry2
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq (decoded.map_str_int32.get? "dup") (some (9 : Int32)) "duplicate map key should keep last value"

def testMapMergeLastWins : IO Unit := do
  let base : _root_.test.proto3.All := default
  let a : _root_.test.proto3.All :=
    { base with map_str_int32 := Std.HashMap.ofList [("dup", (1 : Int32)), ("left", 2)] }
  let b : _root_.test.proto3.All :=
    { base with map_str_int32 := Std.HashMap.ofList [("dup", (9 : Int32)), ("right", 3)] }
  let merged := _root_.test.proto3.All.merge a b
  assertEq (merged.map_str_int32.get? "dup") (some (9 : Int32)) "merged map should keep right-hand duplicate value"
  assertEq (merged.map_str_int32.get? "left") (some (2 : Int32)) "merged map should keep left-only key"
  assertEq (merged.map_str_int32.get? "right") (some (3 : Int32)) "merged map should keep right-only key"

def testMapMissingValueDefaults : IO Unit := do
  let entry ← ofExcept <| mkMapEntry "no_value"
  let msg := Message.set Message.empty 21 entry
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq (decoded.map_str_int32.get? "no_value") (some (0 : Int32)) "map entry with missing value should use default"

def testMapEntryWrongWireFieldsSkipped : IO Unit := do
  let value7 ← ofExcept <| ProtoVal.ofVarint_int32 7
  let entryMsg := Message.set Message.empty 1 (.LEN "valid_key".toUTF8)
  let entryMsg := Message.set entryMsg 1 (.I32 (0 : UInt32).toBitVec)
  let entryMsg := Message.set entryMsg 2 value7
  let entry ← ofExcept <| ProtoVal.ofMessage entryMsg
  let value4 ← ofExcept <| ProtoVal.ofVarint_int32 4
  let entryMsg2 := Message.set Message.empty 1 (.LEN "valid_value".toUTF8)
  let entryMsg2 := Message.set entryMsg2 2 value4
  let entryMsg2 := Message.set entryMsg2 2 (.LEN "not an int32".toUTF8)
  let entry2 ← ofExcept <| ProtoVal.ofMessage entryMsg2
  let msg := Message.set Message.empty 21 entry
  let msg := Message.set msg 21 entry2
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq (decoded.map_str_int32.get? "valid_key") (some (7 : Int32))
    "wrong-wire key field should not override the last valid key"
  assertEq (decoded.map_str_int32.get? "valid_value") (some (4 : Int32))
    "wrong-wire value field should not override the last valid value"

def testUnknownEnum : IO Unit := do
  let msg := Message.set Message.empty 15 (.VARINT 9)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.color with
  | _root_.test.proto3.Color.«Unknown.Value» raw =>
      assertEq raw (9 : Int32) "unknown enum raw value mismatch"
  | _ => throw (IO.userError "unknown enum value should be preserved")

def testUnknownFields : IO Unit := do
  let msg := Message.set Message.empty 99 (.VARINT 123)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  match decoded.«Unknown.Fields».get? 99 with
  | some vals => assert (vals.size == 1) "unknown field should be preserved"
  | none => throw (IO.userError "unknown field missing")
  let roundtrip ← ofExcept (_root_.test.proto3.All.toMessage decoded)
  assert ((Message.getRecordsOf roundtrip 99).size == 1) "unknown field should round-trip"

def testKnownWrongWireTypePreserved : IO Unit := do
  let raw := "not an int32".toUTF8
  let msg := Message.set Message.empty 1 (.LEN raw)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assertEq decoded.int32_field (0 : Int32) "wrong wire type should not update the typed field"
  match decoded.«Unknown.Fields».get? 1 with
  | some vals =>
      assert (vals.size == 1) "wrong wire type should be preserved as one unknown value"
      match vals[0]! with
      | .LEN data => assertEq data raw "wrong-wire unknown payload mismatch"
      | _ => throw (IO.userError "wrong-wire unknown payload should retain LEN value")
  | none => throw (IO.userError "wrong wire type for known field should be preserved as unknown")
  let roundtrip ← ofExcept (_root_.test.proto3.All.toMessage decoded)
  assert ((Message.getRecordsOf roundtrip 1).size == 1) "wrong wire type should round-trip as unknown"

def testExtensions : IO Unit := do
  let base : _root_.test.proto3.All := default
  let withInt ← ofExcept (_root_.test.proto3.All.set_ext_int32 base 3)
  assert (_root_.test.proto3.All.has_ext_int32 withInt) "extension setter should mark field present"
  let extInt ← ofExcept (_root_.test.proto3.All.get_ext_int32? withInt)
  assertEq extInt (some (3 : Int32)) "extension int32 round-trip mismatch"
  let unknownInt := (Std.HashMap.emptyWithCapacity 1).insert 100
    #[.VARINT 3, .LEN "not an int32".toUTF8]
  let rawInt : _root_.test.proto3.All := { base with «Unknown.Fields» := unknownInt }
  assert (_root_.test.proto3.All.has_ext_int32 rawInt) "extension has should report valid typed scalar presence"
  let extInt ← ofExcept (_root_.test.proto3.All.get_ext_int32? rawInt)
  assertEq extInt (some (3 : Int32)) "wrong-wire extension scalar should be skipped"
  let wrongOnlyIntMap := (Std.HashMap.emptyWithCapacity 1).insert 100
    #[.LEN "not an int32".toUTF8]
  let wrongOnlyInt : _root_.test.proto3.All := { base with «Unknown.Fields» := wrongOnlyIntMap }
  assert (!_root_.test.proto3.All.has_ext_int32 wrongOnlyInt) "extension has should ignore wrong-wire-only scalar records"
  let extInt ← ofExcept (_root_.test.proto3.All.get_ext_int32? wrongOnlyInt)
  assertEq extInt none "wrong-wire-only scalar extension should decode as absent"
  let packed := mkPackedVarints #[2, 3]
  let unknownRep := (Std.HashMap.emptyWithCapacity 1).insert 101
    #[.VARINT 1, packed, .I32 (0 : UInt32).toBitVec]
  let rawRep : _root_.test.proto3.All := { base with «Unknown.Fields» := unknownRep }
  assert (_root_.test.proto3.All.has_ext_rep_int32 rawRep) "extension has should report valid repeated values"
  let extRep ← ofExcept (_root_.test.proto3.All.get_ext_rep_int32? rawRep)
  assertEq extRep #[(1 : Int32), 2, 3] "repeated extension should accept packed and unpacked records and skip invalid records"
  let wrongOnlyRepMap := (Std.HashMap.emptyWithCapacity 1).insert 101
    #[.I32 (0 : UInt32).toBitVec]
  let wrongOnlyRep : _root_.test.proto3.All := { base with «Unknown.Fields» := wrongOnlyRepMap }
  assert (!_root_.test.proto3.All.has_ext_rep_int32 wrongOnlyRep) "extension has should ignore wrong-wire-only repeated records"
  let withRep ← ofExcept (_root_.test.proto3.All.set_ext_rep_int32 base #[(4 : Int32), 5])
  let extRep ← ofExcept (_root_.test.proto3.All.get_ext_rep_int32? withRep)
  assertEq extRep #[(4 : Int32), 5] "packed repeated extension setter/getter mismatch"
  let sub1 : _root_.test.proto3.Sub := { id := 7, label := "" }
  let sub2 : _root_.test.proto3.Sub := { id := 0, label := "merged" }
  let subMsg1 ← ofExcept sub1.toMessage
  let subMsg2 ← ofExcept sub2.toMessage
  let subVal1 ← ofExcept <| ProtoVal.ofMessage subMsg1
  let subVal2 ← ofExcept <| ProtoVal.ofMessage subMsg2
  let unknownSub := (Std.HashMap.emptyWithCapacity 1).insert 102
    #[subVal1, .I32 (0 : UInt32).toBitVec, subVal2]
  let rawSub : _root_.test.proto3.All := { base with «Unknown.Fields» := unknownSub }
  assert (_root_.test.proto3.All.has_ext_sub rawSub) "extension has should report valid message extension records"
  let extSub ← ofExcept (_root_.test.proto3.All.get_ext_sub? rawSub)
  match extSub with
  | some sub =>
      assertEq sub.id (7 : Int32) "message extension should merge valid records"
      assertEq sub.label "merged" "message extension should apply later valid record"
  | none => throw (IO.userError "message extension should decode")
  let wrongOnlySubMap := (Std.HashMap.emptyWithCapacity 1).insert 102
    #[.I32 (0 : UInt32).toBitVec]
  let wrongOnlySub : _root_.test.proto3.All := { base with «Unknown.Fields» := wrongOnlySubMap }
  assert (!_root_.test.proto3.All.has_ext_sub wrongOnlySub) "extension has should ignore wrong-wire-only message records"

def testOneofWrongWireTypePreserved : IO Unit := do
  let raw := "not an int32".toUTF8
  let msg := Message.set Message.empty 22 (.LEN raw)
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessage msg)
  assert decoded.choice.isNone "wrong wire type should not set oneof case"
  match decoded.«Unknown.Fields».get? 22 with
  | some vals =>
      assert (vals.size == 1) "wrong oneof wire type should be preserved as one unknown value"
      match vals[0]! with
      | .LEN data => assertEq data raw "wrong oneof unknown payload mismatch"
      | _ => throw (IO.userError "wrong oneof unknown payload should retain LEN value")
  | none => throw (IO.userError "wrong oneof wire type should be preserved as unknown")
  let roundtrip ← ofExcept (_root_.test.proto3.All.toMessage decoded)
  assert ((Message.getRecordsOf roundtrip 22).size == 1) "wrong oneof wire type should round-trip as unknown"

def expectWireDecodeFailure (bytes : ByteArray) (msg : String) : IO Unit := do
  match (Binary.Get.run (Binary.getThe Message) bytes).toExcept with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError msg)

def expectTruncated {α : Type} (e : Except ProtoError α) (msg : String) : IO Unit := do
  match e with
  | .error .truncated => pure ()
  | .error err => throw (IO.userError s!"{msg}: expected truncated, got {err}")
  | .ok _ => throw (IO.userError msg)

def expectInvalidVarint {α : Type} (e : Except ProtoError α) (msg : String) : IO Unit := do
  match e with
  | .error .invalidVarint => pure ()
  | .error err => throw (IO.userError s!"{msg}: expected invalid varint, got {err}")
  | .ok _ => throw (IO.userError msg)

def expectProtoFailure {α : Type} (e : Except ProtoError α) (msg : String) : IO Unit := do
  match e with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError msg)

def expectMessageTooLarge {α : Type} (e : Except ProtoError α) (msg : String) : IO Unit := do
  match e with
  | .error (.messageTooLarge _ _) => pure ()
  | .error err => throw (IO.userError s!"{msg}: expected messageTooLarge, got {err}")
  | .ok _ => throw (IO.userError msg)

def expectRecursionLimit {α : Type} (e : Except ProtoError α) (msg : String) : IO Unit := do
  match e with
  | .error (.recursionLimitExceeded _ _) => pure ()
  | .error err => throw (IO.userError s!"{msg}: expected recursionLimitExceeded, got {err}")
  | .ok _ => throw (IO.userError msg)

def testFieldNumberRange : IO Unit := do
  match (Binary.Get.run (Binary.getThe Message) hex!"f8ffffff0f00").toExcept with
  | .ok msg =>
      let rs := Message.getRecordsOf msg Protobuf.Encoding.maxFieldNumber
      assert (rs.size == 1) "maximum valid field number should decode"
  | .error err => throw (IO.userError s!"maximum valid field number was rejected: {err}")
  expectWireDecodeFailure hex!"808080801000" "field number above protobuf maximum should be rejected"
  let maxMsg := Message.set Message.empty Protobuf.Encoding.maxFieldNumber (.VARINT 7)
  let maxDecoded ← ofExcept (_root_.test.proto3.MaxFieldNumber.fromMessage maxMsg)
  assertEq maxDecoded.value (7 : Int32) "maximum valid schema field number should decode"

def testRejectMalformedWire : IO Unit := do
  expectWireDecodeFailure hex!"00" "field number zero should be rejected"
  expectWireDecodeFailure hex!"0880808080808080808002" "uint64 varint overflow should be rejected"
  expectWireDecodeFailure hex!"0b14" "mismatched group end should be rejected"

def testRejectMalformedPackedPayloads : IO Unit := do
  let fixed32Msg := Message.set Message.empty 26 (.LEN hex!"010203")
  expectTruncated (_root_.test.proto3.All.fromMessage fixed32Msg)
    "truncated packed fixed32 should be rejected"
  let fixed64Msg := Message.set Message.empty 27 (.LEN hex!"01020304050607")
  expectTruncated (_root_.test.proto3.All.fromMessage fixed64Msg)
    "truncated packed fixed64 should be rejected"
  let varintMsg := Message.set Message.empty 18 (.LEN hex!"8080808080808080808002")
  expectInvalidVarint (_root_.test.proto3.All.fromMessage varintMsg)
    "overlong packed varint should be rejected"

def testRejectInvalidUnknownFieldsOnEncode : IO Unit := do
  let base : _root_.test.proto3.All := default
  let invalidFieldNum : _root_.test.proto3.All := {
    base with
    «Unknown.Fields» := (Std.HashMap.emptyWithCapacity 1).insert 0 #[.VARINT 1]
  }
  expectProtoFailure (_root_.test.proto3.All.toMessage invalidFieldNum)
    "invalid unknown field number should not encode"
  let invalidVarint : _root_.test.proto3.All := {
    base with
    «Unknown.Fields» := (Std.HashMap.emptyWithCapacity 1).insert 99 #[.VARINT UInt64.size]
  }
  expectInvalidVarint (_root_.test.proto3.All.toMessage invalidVarint)
    "overflowing unknown varint should not encode"

def testDecodeWithMaxMessageSize : IO Unit := do
  let base : _root_.test.proto3.All := default
  let bytes ← ofExcept (_root_.test.proto3.All.encode { base with string_field := "bounded" })
  let exactLimit := DecodeOptions.withMaxMessageSize bytes.size
  let decoded ← ofExcept (_root_.test.proto3.All.decodeWithOptions exactLimit bytes)
  assertEq decoded.string_field "bounded" "decodeWithOptions should accept messages at the size limit"
  let tightLimit := DecodeOptions.withMaxMessageSize (bytes.size - 1)
  expectMessageTooLarge (_root_.test.proto3.All.decodeWithOptions tightLimit bytes)
    "decodeWithOptions should reject messages above the size limit"

def testNestedDecodeLimits : IO Unit := do
  let subBytes ← ofExcept (_root_.test.proto3.Sub.encode { id := 1, label := "nested" })
  let subRecord := Message.set Message.empty 16 (.LEN subBytes)
  let shallow := DecodeOptions.withMaxRecursionDepth 0
  expectRecursionLimit (_root_.test.proto3.All.fromMessageWithOptions shallow 0 subRecord)
    "nested submessage should respect recursion depth limit"
  let depthOne := DecodeOptions.withMaxRecursionDepth 1
  let decoded ← ofExcept (_root_.test.proto3.All.fromMessageWithOptions depthOne 0 subRecord)
  match decoded.sub with
  | some sub => assertEq sub.label "nested" "nested submessage should decode within depth limit"
  | none => throw (IO.userError "nested submessage missing within depth limit")
  let smallNested := DecodeOptions.withMaxMessageSize (subBytes.size - 1)
  expectMessageTooLarge (_root_.test.proto3.All.fromMessageWithOptions smallNested 0 subRecord)
    "nested submessage should respect message size limit"
  let oneofRecord := Message.set Message.empty 24 (.LEN subBytes)
  expectRecursionLimit (_root_.test.proto3.All.fromMessageWithOptions shallow 0 oneofRecord)
    "oneof submessage should respect recursion depth limit"
  let oneofDecoded ← ofExcept (_root_.test.proto3.All.fromMessageWithOptions depthOne 0 oneofRecord)
  match oneofDecoded.choice with
  | some (.oneof_sub sub) => assertEq sub.label "nested" "oneof submessage should decode within depth limit"
  | _ => throw (IO.userError "oneof submessage missing within depth limit")
  let entry ← ofExcept <| mkMapEntry "limited" (some 1)
  let mapRecord := Message.set Message.empty 21 entry
  expectRecursionLimit (_root_.test.proto3.All.fromMessageWithOptions shallow 0 mapRecord)
    "map entries should respect recursion depth limit"
  let mapDecoded ← ofExcept (_root_.test.proto3.All.fromMessageWithOptions depthOne 0 mapRecord)
  assertEq (mapDecoded.map_str_int32.get? "limited") (some (1 : Int32))
    "map entry should decode within depth limit"
  let groupBytes := hex!"f301f401"
  expectRecursionLimit (_root_.test.proto3.All.decodeWithOptions shallow groupBytes)
    "unknown groups should respect recursion depth limit"
  let groupDecoded ← ofExcept (_root_.test.proto3.All.decodeWithOptions depthOne groupBytes)
  match groupDecoded.«Unknown.Fields».get? 30 with
  | some vals =>
      assert (vals.size == 1) "unknown group should be preserved"
      match vals[0]! with
      | .GROUPED _ => pure ()
      | _ => throw (IO.userError "unknown group should retain GROUPED value")
  | none => throw (IO.userError "unknown group field missing")

def runTest (name : String) (t : IO Unit) (errs : IO.Ref (Array String)) : IO Unit := do
  try
    t
  catch e =>
    errs.modify (·.push s!"{name}: {e.toString}")

def testProto3 : IO Unit := do
  let errs ← IO.mkRef #[]
  runTest "testDefaults" testDefaults errs
  runTest "testOptionalPresence" testOptionalPresence errs
  runTest "testSubPresence" testSubPresence errs
  runTest "testRequiredAndDefaultPresence" testRequiredAndDefaultPresence errs
  runTest "testSingularLastWins" testSingularLastWins errs
  runTest "testSubMessageMerge" testSubMessageMerge errs
  runTest "testOneof" testOneof errs
  runTest "testOneofLastWins" testOneofLastWins errs
  runTest "testOneofMessageMergesSameCase" testOneofMessageMergesSameCase errs
  runTest "testOneofMerge" testOneofMerge errs
  runTest "testPackedAndUnpacked" testPackedAndUnpacked errs
  runTest "testPackedAcceptsUnpacked" testPackedAcceptsUnpacked errs
  runTest "testUnpackedAcceptsPacked" testUnpackedAcceptsPacked errs
  runTest "testPackedConcatenatesSegments" testPackedConcatenatesSegments errs
  runTest "testNegativeInt32Encoding" testNegativeInt32Encoding errs
  runTest "testPackedFixedWidth" testPackedFixedWidth errs
  runTest "testPackedFixedWidthMixedSegments" testPackedFixedWidthMixedSegments errs
  runTest "testMapRoundtrip" testMapRoundtrip errs
  runTest "testMapDuplicateKeyLastWins" testMapDuplicateKeyLastWins errs
  runTest "testMapMergeLastWins" testMapMergeLastWins errs
  runTest "testMapMissingValueDefaults" testMapMissingValueDefaults errs
  runTest "testMapEntryWrongWireFieldsSkipped" testMapEntryWrongWireFieldsSkipped errs
  runTest "testUnknownEnum" testUnknownEnum errs
  runTest "testUnknownFields" testUnknownFields errs
  runTest "testKnownWrongWireTypePreserved" testKnownWrongWireTypePreserved errs
  runTest "testExtensions" testExtensions errs
  runTest "testOneofWrongWireTypePreserved" testOneofWrongWireTypePreserved errs
  runTest "testFieldNumberRange" testFieldNumberRange errs
  runTest "testRejectMalformedWire" testRejectMalformedWire errs
  runTest "testRejectMalformedPackedPayloads" testRejectMalformedPackedPayloads errs
  runTest "testRejectInvalidUnknownFieldsOnEncode" testRejectInvalidUnknownFieldsOnEncode errs
  runTest "testDecodeWithMaxMessageSize" testDecodeWithMaxMessageSize errs
  runTest "testNestedDecodeLimits" testNestedDecodeLimits errs
  let failures ← errs.get
  unless failures.isEmpty do
    let msg := String.intercalate "\n" failures.toList
    throw (IO.userError msg)

#eval! testProto3

def main : IO Unit := testProto3
