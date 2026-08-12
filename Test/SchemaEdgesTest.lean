import Protobuf
import SchemaEdgesProto.schema_edges
import SchemaEdgesPeerProto.schema_edges_peer

open Protobuf Encoding

namespace SchemaEdgesTest

def ofExcept {α} (result : Except ProtoError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error err => throw (IO.userError err.toString)

def expect (condition : Bool) (failureMessage : String) : IO Unit := do
  if condition then pure () else throw (IO.userError failureMessage)

def expectEq [BEq α] (actual expected : α) (failureMessage : String) : IO Unit :=
  expect (actual == expected) failureMessage

def expectText
    (actual : Option _root_.test.edges.Envelope.payload_Type)
    (expected : Option String)
    (failureMessage : String) : IO Unit := do
  match actual, expected with
  | none, none => pure ()
  | some (.text actual), some expected => expectEq actual expected failureMessage
  | _, _ => throw (IO.userError failureMessage)

/-- A single-member oneof follows the same "last one wins" rule as any other:
an absent right-hand state keeps the left-hand one, a present one replaces it. -/
def testSingleMemberOneofMerge : IO Unit := do
  let text (value : String) : Option _root_.test.edges.Envelope.payload_Type :=
    some (.text value)
  let merge := _root_.test.edges.Envelope.payload_Type.merge
  expectText (merge (text "left") none) (some "left")
    "absent right-hand oneof state must keep the left-hand one"
  expectText (merge none (text "right")) (some "right")
    "present right-hand oneof state must replace an absent left-hand one"
  expectText (merge (text "left") (text "right")) (some "right")
    "present right-hand oneof state must replace the left-hand one"
  expectText (merge none none) none "two absent oneof states must merge to absent"

def testSingleMemberOneofRoundTrip : IO Unit := do
  let value : _root_.test.edges.Envelope := { id := "envelope", payload := some (.text "hi") }
  let encoded ← ofExcept (_root_.test.edges.Envelope.encode value)
  let decoded ← ofExcept (_root_.test.edges.Envelope.decode encoded)
  let some (.text decodedText) := decoded.payload
    | throw (IO.userError "single-member oneof did not round-trip")
  expectEq decodedText "hi" "single-member oneof payload did not round-trip"
  expectEq decoded.id "envelope" "message around a single-member oneof did not round-trip"

def testSingleMemberOneofGetters : IO Unit := do
  let set : _root_.test.edges.Envelope := { payload := some (.text "hi") }
  let unset : _root_.test.edges.Envelope := {}
  expect set.has_text "member presence must hold when the single member is set"
  expect (!unset.has_text) "member presence must fail when the oneof is absent"
  expectEq set.text "hi" "member getter must yield the payload when set"
  expectEq unset.text "" "member getter must yield the default when the oneof is absent"

/-- Messages whose Lean type names differ only in their proto scope each get
their own `Inhabited` instance, so both defaults are reachable. -/
def testScopeCollidingDefaults : IO Unit := do
  let leftItem : _root_.test.edges.Left.Item := default
  let rightItem : _root_.test.edges.Right.Item := default
  expect leftItem.right.isNone "Left.Item default must leave its message field absent"
  expect rightItem.left.isNone "Right.Item default must leave its message field absent"
  let value : _root_.test.edges.Left := { item := some { right := some { item := some rightItem } } }
  let encoded ← ofExcept (_root_.test.edges.Left.encode value)
  let decoded ← ofExcept (_root_.test.edges.Left.decode encoded)
  let some decodedItem := decoded.item
    | throw (IO.userError "scoped nested message did not round-trip")
  let some decodedRight := decodedItem.right
    | throw (IO.userError "cycle through the scoped nested messages did not round-trip")
  expect decodedRight.item.isSome
    "second scoped nested message did not round-trip"

def testEnumDefaults : IO Unit := do
  expectEq (default : _root_.test.edges.Mode) .MODE_UNSPECIFIED
    "enum default must be its zero value"
  expectEq (_root_.test.edges.Mode.fromInt32 2) .MODE_CURRENT
    "enum decoding must map its wire value"
  expectEq (default : _root_.test.edges.Left.State) .LEFT_STATE_UNSPECIFIED
    "first scoped enum default must be its zero value"
  expectEq (default : _root_.test.edges.Right.State) .RIGHT_STATE_UNSPECIFIED
    "second scoped enum default must be its zero value"

/-- Fully qualified helper names remain distinct when separately generated
modules defining the same short message and enum names are imported together. -/
def testCrossModuleInstanceNames : IO Unit := do
  let localCapabilities : _root_.test.edges.Capabilities := default
  let peerCapabilities : _root_.test.peer.Capabilities := default
  expectEq localCapabilities.name "" "local Capabilities default must be available"
  expectEq peerCapabilities.name "" "peer Capabilities default must be available"
  expectEq (default : _root_.test.edges.Status) .STATUS_UNSPECIFIED
    "local Status default must be available"
  expectEq (default : _root_.test.peer.Status) .STATUS_UNSPECIFIED
    "peer Status default must be available"

def testInstanceHelperNameIsolation : IO Unit := do
  let fieldValue : _root_.test.edges.InstanceNameCollision := {
    instInhabited := "field"
  }
  expectEq fieldValue.instInhabited "field"
    "message field named instInhabited must remain usable"
  expectEq (default : _root_.test.edges.InstanceValueCollision) .instInhabited
    "enum value named instInhabited must remain usable"
  let nested : _root_.test.edges.NestedTypeCollision.instInhabited := {
    value := "nested"
  }
  let outer : _root_.test.edges.NestedTypeCollision := { value := some nested }
  let some decodedNested := outer.value
    | throw (IO.userError "nested message named instInhabited must remain usable")
  expectEq decodedNested.value "nested"
    "nested message named instInhabited must retain its field"

-- Reading the deprecated field is what this check is about, so the deprecation
-- the generated module carries for it is expected here.
set_option linter.deprecated false in
def testDeprecatedFieldRoundTrip : IO Unit := do
  let value : _root_.test.edges.Envelope := { id := "envelope", legacy_id := "legacy" }
  let encoded ← ofExcept (_root_.test.edges.Envelope.encode value)
  let decoded ← ofExcept (_root_.test.edges.Envelope.decode encoded)
  expectEq decoded.legacy_id "legacy" "deprecated field must still round-trip"

end SchemaEdgesTest

def main : IO Unit := do
  SchemaEdgesTest.testSingleMemberOneofMerge
  SchemaEdgesTest.testSingleMemberOneofRoundTrip
  SchemaEdgesTest.testSingleMemberOneofGetters
  SchemaEdgesTest.testScopeCollidingDefaults
  SchemaEdgesTest.testEnumDefaults
  SchemaEdgesTest.testCrossModuleInstanceNames
  SchemaEdgesTest.testInstanceHelperNameIsolation
  SchemaEdgesTest.testDeprecatedFieldRoundTrip
  IO.println "protobuf schema edge-case tests passed"
