module

public import Protobuf.Encoding

public section

open Protobuf Encoding

namespace ImportedLegacy

/-- A conventional protobuf message implementation that predates PB-02 and
therefore intentionally has no `«_pb$directPlanWithOptions»` declaration. -/
structure LegacyChild where
  id : UInt64 := 0
  label : String := ""
  «Unknown.Fields» : Std.HashMap Nat (Array ProtoVal) := {}

instance : Inhabited LegacyChild := ⟨{}⟩

/- An unrelated declaration with PB-02's discarded prototype name must not be
mistaken for the generator's `$`-qualified cross-module hook. -/
def LegacyChild.directPlanWithOptions : Nat := 7

def LegacyChild.toMessageWithOptions (options : EncodeOptions)
    (value : LegacyChild) : Except ProtoError Message := do
  let msg :=
    if value.id == 0 then Message.empty
    else Message.set Message.empty 1 (.VARINT value.id.toNat)
  let msg :=
    if value.label.isEmpty then msg
    else Message.set msg 2 (.LEN value.label.toUTF8)
  let msg := Message.wire_mapWithOptions options msg value.«Unknown.Fields»
  msg.validate
  return msg

def LegacyChild.toMessage : LegacyChild → Except ProtoError Message :=
  LegacyChild.toMessageWithOptions EncodeOptions.default

def LegacyChild.builder (value : LegacyChild) : Except ProtoError ProtoVal := do
  ProtoVal.ofMessage (← value.toMessage)

def LegacyChild.fromMessageWithOptions (_options : DecodeOptions) (_depth : Nat)
    (msg : Message) : Except ProtoError LegacyChild := do
  let id := (← Message.getVarint_uint64? msg 1).getD 0
  let label := (← Message.getString? msg 2).getD ""
  return { id, label }

def LegacyChild.decoderRepWithOptions (options : DecodeOptions) (depth : Nat)
    (msg : Message) (fieldNumber : Nat) : Except ProtoError (Array LegacyChild) := do
  let children ← Message.getExpandedMessageWithOptions options (depth + 1) msg fieldNumber
  children.mapM (LegacyChild.fromMessageWithOptions options (depth + 1))

def LegacyChild.merge (left right : LegacyChild) : LegacyChild :=
  { id := if right.id == 0 then left.id else right.id
  , label := if right.label.isEmpty then left.label else right.label
  , «Unknown.Fields» := right.«Unknown.Fields»
  }

end ImportedLegacy
