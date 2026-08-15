import Protobuf.Encoding
import Protobuf.Notation
import Test.ImportedGeneratedChild
import Test.LegacyChild

open Protobuf Encoding
open scoped Protobuf.Notation

namespace DirectEncodeBazel

message Widget {
  uint64 id = 1;
  string name = 2;
  string sku = 3;
  string description = 4;
  uint32 quantity = 5;
  uint64 owner_id = 6;
}

message ListWidgetsResponse {
  repeated Widget widgets = 1;
}

oneof FallbackChoice {
  int32 number = 10;
  string text = 11;
}

message FallbackEnvelope {
  int32 count = 1;
  map<string, int32> labels = 2;
  FallbackChoice choice = 0;
  repeated Widget widgets = 3;
}

/- This parent is in the direct subset, while each nested child uses the
generic fallback plan. -/
message FallbackList {
  repeated FallbackEnvelope entries = 1;
}

message ImportedGeneratedList {
  repeated ImportedGenerated.Child children = 1;
}

message ImportedLegacyList {
  repeated ImportedLegacy.LegacyChild children = 1;
}

/- These four legal protobuf field names matched PB-02's first helper names.
The remaining internal hook uses a component containing `$`, so all projections
and the adopted direct encoder can coexist. -/
message DirectHelperNameCollision {
  string directPlanWithOptions = 1;
  string directPlan = 2;
  string encodeDirectWithOptions = 3;
  string encodeDirect = 4;
}

def ofExcept {α} (result : Except ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

def assert (condition : Bool) (context : String) : IO Unit := do
  unless condition do
    throw (IO.userError context)

def assertEq [BEq α] (actual expected : α) (context : String) : IO Unit :=
  assert (actual == expected) context

def assertSameOutcome (legacy direct : Except ProtoError ByteArray)
    (context : String) : IO Unit := do
  match legacy, direct with
  | .ok legacyBytes, .ok directBytes =>
      assertEq directBytes legacyBytes s!"{context}: bytes differ"
  | .error legacyError, .error directError =>
      assertEq directError.toString legacyError.toString s!"{context}: errors differ"
  | .ok _, .error directError =>
      throw (IO.userError s!"{context}: direct failed unexpectedly: {directError}")
  | .error legacyError, .ok _ =>
      throw (IO.userError s!"{context}: direct accepted legacy error: {legacyError}")

def legacyEncodeWithOptions {α}
    (toMessageWithOptions : EncodeOptions → α → Except ProtoError Message)
    (options : EncodeOptions) (value : α) : Except ProtoError ByteArray := do
  return Binary.Put.run (Binary.put (← toMessageWithOptions options value))

def assertGenerated (legacy adopted : Except ProtoError ByteArray)
    (context : String) : IO Unit := do
  assertSameOutcome legacy adopted s!"{context}: generated encode"

def widgetCorpus : Array Widget :=
  #[ default
   , { id := 1, name := "a", sku := "s", description := "d", quantity := 1,
       owner_id := 2 }
   , { id := 127, name := "café", sku := "sku-128", description := "雪と🚀",
       quantity := 127, owner_id := 128 }
   , { id := 128, name := String.ofList (List.replicate 128 'n'), sku := "sku-16384",
       description := String.ofList (List.replicate 300 'x'), quantity := 16384,
       owner_id := 16384 }
   , { id := 18446744073709551615, name := "maximum", sku := "all-ones",
       description := "boundary varints", quantity := 4294967295,
       owner_id := 18446744073709551615 }
   ]

def richUnknownFields : Std.HashMap Nat (Array ProtoVal) :=
  let grouped := Message.set Message.empty 1 (.VARINT 9)
  ((((Std.HashMap.emptyWithCapacity 4).insert 100 #[.VARINT 3, .LEN "raw".toUTF8]).insert
      88 #[.I32 (0x01020304 : UInt32).toBitVec]).insert
    87 #[.I64 (0x0102030405060708 : UInt64).toBitVec]).insert 99 #[.GROUPED grouped]

def testWidgetCorpus : IO Unit := do
  for widget in widgetCorpus do
    assertGenerated
      (legacyEncodeWithOptions Widget.toMessageWithOptions EncodeOptions.default widget)
      (Widget.encode widget)
      s!"widget id={widget.id}"
    assertGenerated
      (legacyEncodeWithOptions Widget.toMessageWithOptions
        EncodeOptions.withDeterministic widget)
      (Widget.encodeWithOptions EncodeOptions.withDeterministic widget)
      s!"deterministic widget id={widget.id}"
    let plan ← ofExcept (Widget.«_pb$directPlanWithOptions»
      EncodeOptions.default widget)
    let bytes ← ofExcept (Widget.encode widget)
    assertEq plan.size bytes.size s!"widget plan size id={widget.id}"
    let decoded ← ofExcept (Widget.decode bytes)
    let roundtrip ← ofExcept (Widget.encode decoded)
    assertEq roundtrip bytes s!"widget round-trip id={widget.id}"

def testNestedLists : IO Unit := do
  let lists : Array ListWidgetsResponse :=
    #[ default
     , { widgets := widgetCorpus }
     , { widgets := Array.range 55 |>.map fun i =>
          { id := UInt64.ofNat (i + 1), name := s!"widget-{i}", sku := s!"sku-{i}",
            description := s!"description-{i}-🚀", quantity := UInt32.ofNat (i * 3),
            owner_id := UInt64.ofNat (1000 + i) } }
     ]
  for list in lists do
    assertGenerated
      (legacyEncodeWithOptions ListWidgetsResponse.toMessageWithOptions
        EncodeOptions.default list)
      (ListWidgetsResponse.encode list) s!"list size={list.widgets.size}"
    let plan ← ofExcept (ListWidgetsResponse.«_pb$directPlanWithOptions»
      EncodeOptions.default list)
    let bytes ← ofExcept (ListWidgetsResponse.encode list)
    assertEq plan.size bytes.size s!"list plan size={list.widgets.size}"
    let decoded ← ofExcept (ListWidgetsResponse.decode bytes)
    assertEq decoded.widgets.size list.widgets.size
      s!"list round-trip count={list.widgets.size}"

def testUnknownFields : IO Unit := do
  let base := widgetCorpus[2]!
  let value : Widget := { base with «Unknown.Fields» := richUnknownFields }
  assertGenerated
    (legacyEncodeWithOptions Widget.toMessageWithOptions
      EncodeOptions.withDeterministic value)
    (Widget.encodeWithOptions EncodeOptions.withDeterministic value)
    "deterministic rich unknown fields"
  assertGenerated
    (legacyEncodeWithOptions Widget.toMessageWithOptions EncodeOptions.default value)
    (Widget.encode value)
    "native-order rich unknown fields"

  -- Legacy `wire_mapWithOptions` emits no records for an empty value array, so
  -- an otherwise-invalid key is intentionally not validated in this edge case.
  let emptyInvalid : Widget := {
    base with
    «Unknown.Fields» := (Std.HashMap.emptyWithCapacity 1).insert 0 #[]
  }
  assertGenerated
    (legacyEncodeWithOptions Widget.toMessageWithOptions EncodeOptions.default emptyInvalid)
    (Widget.encode emptyInvalid)
    "empty invalid unknown key"

  let invalidNumber : Widget := {
    base with
    «Unknown.Fields» := (Std.HashMap.emptyWithCapacity 1).insert 0 #[.VARINT 1]
  }
  assertGenerated
    (legacyEncodeWithOptions Widget.toMessageWithOptions EncodeOptions.default invalidNumber)
    (Widget.encode invalidNumber)
    "invalid unknown field number"

  let invalidVarint : Widget := {
    base with
    «Unknown.Fields» :=
      (Std.HashMap.emptyWithCapacity 1).insert 101 #[.VARINT UInt64.size]
  }
  assertGenerated
    (legacyEncodeWithOptions Widget.toMessageWithOptions EncodeOptions.default invalidVarint)
    (Widget.encode invalidVarint)
    "overflowing unknown varint"

  -- Known fields (including nested messages) precede the parent's unknown
  -- fields. Pin that an invalid child is therefore reported before a distinct
  -- invalid parent unknown field.
  let invalidParent : ListWidgetsResponse := {
    widgets := #[invalidVarint]
    «Unknown.Fields» := (Std.HashMap.emptyWithCapacity 1).insert 0 #[.VARINT 1]
  }
  let legacyParent := legacyEncodeWithOptions ListWidgetsResponse.toMessageWithOptions
    EncodeOptions.default invalidParent
  match legacyParent with
  | .error .invalidVarint => pure ()
  | .error err => throw (IO.userError s!"nested first-error oracle changed: {err}")
  | .ok _ => throw (IO.userError "nested first-error oracle unexpectedly succeeded")
  assertGenerated legacyParent (ListWidgetsResponse.encode invalidParent)
    "nested child-before-parent error ordering"

def fallbackValue : FallbackEnvelope :=
  { count := -7
  , labels := Std.HashMap.ofList [("z", (9 : Int32)), ("a", 1)]
  , choice := some (.text "fallback")
  , widgets := widgetCorpus
  }

def testFallbackSemantics : IO Unit := do
  assertGenerated
    (legacyEncodeWithOptions FallbackEnvelope.toMessageWithOptions
      EncodeOptions.withDeterministic fallbackValue)
    (FallbackEnvelope.encodeWithOptions EncodeOptions.withDeterministic fallbackValue)
    "map/oneof fallback"
  let parent : FallbackList := { entries := #[fallbackValue, default] }
  assertGenerated
    (legacyEncodeWithOptions FallbackList.toMessageWithOptions
      EncodeOptions.withDeterministic parent)
    (FallbackList.encodeWithOptions EncodeOptions.withDeterministic parent)
    "direct parent with fallback children"
  let plan ← ofExcept (FallbackList.«_pb$directPlanWithOptions»
    EncodeOptions.withDeterministic parent)
  let bytes ← ofExcept (FallbackList.encodeWithOptions
    EncodeOptions.withDeterministic parent)
  assertEq plan.size bytes.size "fallback child plan size"

def testImportedChildren : IO Unit := do
  let generated : ImportedGeneratedList := {
    children := #[{ id := 7, label := "generated" }, { id := 128, label := "跨模块" }]
  }
  assertGenerated
    (legacyEncodeWithOptions ImportedGeneratedList.toMessageWithOptions
      EncodeOptions.default generated)
    (ImportedGeneratedList.encode generated)
    "imported generated direct child"

  let legacy : ImportedLegacyList := {
    children := #[{ id := 9, label := "legacy" }, { id := 16384, label := "fallback" }]
  }
  assertGenerated
    (legacyEncodeWithOptions ImportedLegacyList.toMessageWithOptions
      EncodeOptions.default legacy)
    (ImportedLegacyList.encode legacy)
    "imported conventional child without direct hook"

def testHelperNameCollision : IO Unit := do
  let value : DirectHelperNameCollision :=
    { directPlanWithOptions := "one"
    , directPlan := "two"
    , encodeDirectWithOptions := "three"
    , encodeDirect := "four"
    }
  assertGenerated
    (legacyEncodeWithOptions DirectHelperNameCollision.toMessageWithOptions
      EncodeOptions.default value)
    (DirectHelperNameCollision.encode value)
    "direct helper name collision"

def testDirectEncode : IO Unit := do
  testWidgetCorpus
  testNestedLists
  testUnknownFields
  testFallbackSemantics
  testImportedChildren
  testHelperNameCollision

end DirectEncodeBazel

def main : IO Unit := DirectEncodeBazel.testDirectEncode
