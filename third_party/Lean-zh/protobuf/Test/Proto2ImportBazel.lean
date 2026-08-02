import Protobuf

open Protobuf Encoding
open scoped Protobuf.Notation

#load_proto_file "Test/Proto2Defaults.proto"

namespace Proto2ImportBazel

def ofExcept {α} (e : Except ProtoError α) : IO α := do
  match e with
  | .ok v => pure v
  | .error err => throw (IO.userError err.toString)

def assert (cond : Bool) (msg : String) : IO Unit := do
  if cond then pure () else throw (IO.userError msg)

def assertEq [BEq α] (a b : α) (msg : String) : IO Unit := do
  assert (a == b) msg

def assertUnknownVarint (unknowns : Std.HashMap Nat (Array ProtoVal)) (fieldNumber expected : Nat)
    (label : String) : IO Unit := do
  match unknowns.get? fieldNumber with
  | none => throw (IO.userError s!"{label}: missing unknown field")
  | some values =>
      assert (values.size == 1) s!"{label}: expected one unknown record"
      match values[0]! with
      | .VARINT value => assertEq value expected s!"{label}: unknown varint mismatch"
      | _ => throw (IO.userError s!"{label}: expected varint unknown field")

def assertUnknownsHaveVarint (unknowns : Std.HashMap Nat (Array ProtoVal)) (fieldNumber expected : Nat)
    (label : String) : IO Unit := do
  match unknowns.get? fieldNumber with
  | none => throw (IO.userError s!"{label}: missing unknown field")
  | some values =>
      let found := values.any (fun value =>
        match value with
        | .VARINT actual => actual == expected
        | _ => false)
      assert found s!"{label}: missing unknown varint {expected}"

def assertUnknownsHavePackedBytes (unknowns : Std.HashMap Nat (Array ProtoVal)) (fieldNumber : Nat)
    (expected : ByteArray) (label : String) : IO Unit := do
  match unknowns.get? fieldNumber with
  | none => throw (IO.userError s!"{label}: missing unknown field")
  | some values =>
      let found := values.any (fun value =>
        match value with
        | .LEN data => data == expected
        | _ => false)
      assert found s!"{label}: missing packed bytes"

def assertHasVarintRecord (msg : Message) (fieldNumber expected : Nat) (label : String) :
    IO Unit := do
  let records := Message.getRecordsOf msg fieldNumber
  let found := records.any (fun record =>
    match record.value with
    | .VARINT value => value == expected
    | _ => false)
  assert found s!"{label}: missing varint record {expected}"

def mapEntryProtoVal (key : String) (value : Nat) : IO ProtoVal := do
  let entry := Message.set (Message.set Message.empty 1 (.LEN key.toUTF8)) 2 (.VARINT value)
  ofExcept (ProtoVal.ofMessage entry)

def protoValIsMapEntry (protoVal : ProtoVal) (fieldNumber : Nat) (key : String) (value : Nat) :
    IO Bool := do
  match protoVal with
  | .LEN data =>
      let entry? ← ofExcept (Message.getMessage? (Message.set Message.empty fieldNumber (.LEN data)) fieldNumber)
      match entry? with
      | none => pure false
      | some entry =>
          let key? ← ofExcept (Message.getString? entry 1)
          let value? ← ofExcept (Message.getVarint? entry 2)
          pure (key? == some key && value? == some value)
  | _ => pure false

def assertProtoValsHaveMapEntry (values : Array ProtoVal) (fieldNumber : Nat) (key : String)
    (value : Nat) (label : String) : IO Unit := do
  let mut found := false
  for protoVal in values do
    if ← protoValIsMapEntry protoVal fieldNumber key value then
      found := true
  assert found s!"{label}: missing map entry {key}={value}"

def assertUnknownMapEntry (unknowns : Std.HashMap Nat (Array ProtoVal)) (fieldNumber : Nat)
    (key : String) (value : Nat) (label : String) : IO Unit := do
  match unknowns.get? fieldNumber with
  | none => throw (IO.userError s!"{label}: missing unknown map field")
  | some values => assertProtoValsHaveMapEntry values fieldNumber key value label

def assertMessageHasMapEntry (msg : Message) (fieldNumber : Nat) (key : String) (value : Nat)
    (label : String) : IO Unit := do
  assertProtoValsHaveMapEntry ((Message.getRecordsOf msg fieldNumber).map Record.value)
    fieldNumber key value label

def testImportedStringBytesDefaults : IO Unit := do
  let val : _root_.test.proto2defaults.Defaults := default
  assertEq val.req_string "hello" "required string default mismatch"
  assertEq val.req_bytes "world".toUTF8 "required bytes default mismatch"
  assertEq val.req_spaced_string " padded " "required string default should preserve spaces"
  assertEq val.req_spaced_bytes " bytes ".toUTF8 "required bytes default should preserve spaces"
  assertEq val.opt_string none "optional string should start absent"
  assertEq val.opt_bytes none "optional bytes should start absent"

  let msg ← ofExcept (_root_.test.proto2defaults.Defaults.toMessage val)
  assert ((Message.getRecordsOf msg 1).size == 1) "required string default should serialize"
  assert ((Message.getRecordsOf msg 2).size == 1) "required bytes default should serialize"
  assert ((Message.getRecordsOf msg 5).size == 1) "required spaced string default should serialize"
  assert ((Message.getRecordsOf msg 6).size == 1) "required spaced bytes default should serialize"
  let decoded ← ofExcept (_root_.test.proto2defaults.Defaults.fromMessage msg)
  assertEq decoded.req_string "hello" "required string default round-trip mismatch"
  assertEq decoded.req_bytes "world".toUTF8 "required bytes default round-trip mismatch"
  assertEq decoded.req_spaced_string " padded " "required spaced string default round-trip mismatch"
  assertEq decoded.req_spaced_bytes " bytes ".toUTF8 "required spaced bytes default round-trip mismatch"

  let present : _root_.test.proto2defaults.Defaults := {
    val with
    opt_string := some "fallback",
    opt_bytes := some "payload".toUTF8
  }
  let presentMsg ← ofExcept (_root_.test.proto2defaults.Defaults.toMessage present)
  assert ((Message.getRecordsOf presentMsg 3).size == 1) "present optional string default should serialize"
  assert ((Message.getRecordsOf presentMsg 4).size == 1) "present optional bytes default should serialize"
  let decodedPresent ← ofExcept (_root_.test.proto2defaults.Defaults.fromMessage presentMsg)
  assertEq decodedPresent.opt_string (some "fallback") "optional string default round-trip mismatch"
  assertEq decodedPresent.opt_bytes (some "payload".toUTF8) "optional bytes default round-trip mismatch"

  match _root_.test.proto2defaults.Defaults.fromMessage Message.empty with
  | .error (.missingRequiredField _) => pure ()
  | .error err => throw (IO.userError s!"missing required fields should report missingRequiredField, got {err}")
  | .ok _ => throw (IO.userError "missing required fields should fail")

def testClosedEnumUnknowns : IO Unit := do
  let base : _root_.test.proto2defaults.EnumHolder := {
    req_status := .STATUS_ZERO
  }
  let optUnknownMsg :=
    Message.set (Message.set Message.empty 3 (.VARINT 0)) 1 (.VARINT 2)
  let decodedOpt ← ofExcept (_root_.test.proto2defaults.EnumHolder.fromMessage optUnknownMsg)
  assertEq decodedOpt.opt_status none "unknown optional enum should remain absent"
  assertUnknownVarint decodedOpt.«Unknown.Fields» 1 2 "optional enum"

  let mixedRepMsg :=
    Message.set (Message.set (Message.set Message.empty 3 (.VARINT 0)) 2 (.VARINT 1)) 2 (.VARINT 2)
  let decodedRep ← ofExcept (_root_.test.proto2defaults.EnumHolder.fromMessage mixedRepMsg)
  assertEq decodedRep.rep_status #[_root_.test.proto2defaults.Status.STATUS_ONE]
    "known repeated enum should decode"
  assertUnknownVarint decodedRep.«Unknown.Fields» 2 2 "repeated enum"

  let mixedPackedMsg :=
    Message.set (Message.set Message.empty 3 (.VARINT 0)) 4 (.LEN (ByteArray.mk #[1, 2]))
  let decodedPacked ← ofExcept (_root_.test.proto2defaults.EnumHolder.fromMessage mixedPackedMsg)
  assertEq decodedPacked.packed_status #[_root_.test.proto2defaults.Status.STATUS_ONE]
    "known packed repeated enum should decode"
  assertUnknownVarint decodedPacked.«Unknown.Fields» 4 2 "packed repeated enum"

  let reqUnknownMsg := Message.set Message.empty 3 (.VARINT 2)
  match _root_.test.proto2defaults.EnumHolder.fromMessage reqUnknownMsg with
  | .error (.missingRequiredField _) => pure ()
  | .error err => throw (IO.userError s!"unknown required enum should behave as absent, got {err}")
  | .ok _ => throw (IO.userError "unknown required enum should not satisfy required presence")

  let roundTripVal : _root_.test.proto2defaults.EnumHolder := {
    base with
    rep_status := decodedRep.rep_status,
    «Unknown.Fields» := decodedRep.«Unknown.Fields»
  }
  let roundTripMsg ← ofExcept (_root_.test.proto2defaults.EnumHolder.toMessage roundTripVal)
  assertHasVarintRecord roundTripMsg 2 1 "round-trip known repeated enum"
  assertHasVarintRecord roundTripMsg 2 2 "round-trip unknown repeated enum"

  let roundTripPackedVal : _root_.test.proto2defaults.EnumHolder := {
    base with
    packed_status := decodedPacked.packed_status,
    «Unknown.Fields» := decodedPacked.«Unknown.Fields»
  }
  let roundTripPackedMsg ← ofExcept (_root_.test.proto2defaults.EnumHolder.toMessage roundTripPackedVal)
  let hasKnownPacked := (Message.getRecordsOf roundTripPackedMsg 4).any (fun record =>
    match record.value with
    | .LEN data => data == ByteArray.mk #[1]
    | _ => false)
  assert hasKnownPacked "round-trip known packed enum should stay packed"
  assertHasVarintRecord roundTripPackedMsg 4 2 "round-trip unknown packed enum"

  let knownMapEntry ← mapEntryProtoVal "good" 1
  let unknownMapEntry ← mapEntryProtoVal "bad" 2
  let mapMsg :=
    Message.set (Message.set (Message.set Message.empty 2 (.VARINT 0)) 1 knownMapEntry) 1 unknownMapEntry
  let decodedMap ← ofExcept (_root_.test.proto2defaults.EnumMapHolder.fromMessage mapMsg)
  assertEq (decodedMap.status_by_name.get? "good")
    (some _root_.test.proto2defaults.Status.STATUS_ONE)
    "known enum map value should decode"
  assert ((decodedMap.status_by_name.get? "bad").isNone)
    "unknown enum map value should not decode into map"
  assertUnknownMapEntry decodedMap.«Unknown.Fields» 1 "bad" 2 "enum map unknown"

  let roundTripMapMsg ← ofExcept (_root_.test.proto2defaults.EnumMapHolder.toMessage decodedMap)
  assertMessageHasMapEntry roundTripMapMsg 1 "good" 1 "round-trip known enum map entry"
  assertMessageHasMapEntry roundTripMapMsg 1 "bad" 2 "round-trip unknown enum map entry"

def testClosedEnumExtensions : IO Unit := do
  let knownMsg := Message.set Message.empty 100 (.VARINT 1)
  let known ← ofExcept (_root_.test.proto2defaults.ExtendTarget.fromMessage knownMsg)
  let knownExt ← ofExcept (_root_.test.proto2defaults.ExtendTarget.get_ext_status? known)
  assertEq knownExt (some _root_.test.proto2defaults.Status.STATUS_ONE)
    "known enum extension should decode"

  let unknownMsg := Message.set Message.empty 100 (.VARINT 2)
  let unknown ← ofExcept (_root_.test.proto2defaults.ExtendTarget.fromMessage unknownMsg)
  let unknownExt ← ofExcept (_root_.test.proto2defaults.ExtendTarget.get_ext_status? unknown)
  assertEq unknownExt none "unknown closed enum extension should not decode"
  assertUnknownVarint unknown.«Unknown.Fields» 100 2 "unknown enum extension"

  let mixedRepMsg := Message.set (Message.set Message.empty 101 (.VARINT 1)) 101 (.VARINT 2)
  let mixedRep ← ofExcept (_root_.test.proto2defaults.ExtendTarget.fromMessage mixedRepMsg)
  let repExt ← ofExcept (_root_.test.proto2defaults.ExtendTarget.get_ext_rep_status? mixedRep)
  assertEq repExt #[_root_.test.proto2defaults.Status.STATUS_ONE]
    "repeated enum extension should return known values only"
  assertUnknownsHaveVarint mixedRep.«Unknown.Fields» 101 1 "known repeated extension raw value"
  assertUnknownsHaveVarint mixedRep.«Unknown.Fields» 101 2 "unknown repeated extension raw value"

  let mixedPackedMsg := Message.set Message.empty 102 (.LEN (ByteArray.mk #[1, 2]))
  let mixedPacked ← ofExcept (_root_.test.proto2defaults.ExtendTarget.fromMessage mixedPackedMsg)
  let packedExt ← ofExcept (_root_.test.proto2defaults.ExtendTarget.get_ext_packed_status? mixedPacked)
  assertEq packedExt #[_root_.test.proto2defaults.Status.STATUS_ONE]
    "packed enum extension should return known values only"
  assertUnknownsHavePackedBytes mixedPacked.«Unknown.Fields» 102 (ByteArray.mk #[1, 2])
    "packed enum extension raw value"

  let setKnown ← ofExcept (_root_.test.proto2defaults.ExtendTarget.set_ext_status
    (default : _root_.test.proto2defaults.ExtendTarget)
    _root_.test.proto2defaults.Status.STATUS_ONE)
  let setKnownMsg ← ofExcept (_root_.test.proto2defaults.ExtendTarget.toMessage setKnown)
  assertHasVarintRecord setKnownMsg 100 1 "set enum extension"

def testProto2ImportBazel : IO Unit := do
  testImportedStringBytesDefaults
  testClosedEnumUnknowns
  testClosedEnumExtensions

end Proto2ImportBazel

def main : IO Unit :=
  Proto2ImportBazel.testProto2ImportBazel
