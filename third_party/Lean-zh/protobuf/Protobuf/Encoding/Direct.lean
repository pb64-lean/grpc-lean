module

public import Protobuf.Encoding.Builder
import Std

public section

namespace Protobuf.Encoding.Direct

open Binary

/-- A sized wire action. Nested plans can write into their parent's active
output without first materializing a child `ByteArray`. -/
structure Plan where
  size : Nat
  put : Put
deriving Inhabited

namespace Plan

@[always_inline]
def empty : Plan := { size := 0, put := pure () }

@[always_inline]
def concat (plans : Array Plan) : Plan :=
  { size := plans.foldl (init := 0) fun total plan => total + plan.size
  , put := plans.forM fun plan => plan.put
  }

@[always_inline]
def run (plan : Plan) : ByteArray :=
  Binary.Put.run plan.put plan.size

end Plan

@[always_inline]
partial def varintSize (n : Nat) : Nat :=
  let rec go (v : UInt64) (count : Nat) : Nat :=
    if v < 0x80 then count else go (v >>> 7) (count + 1)
  go (UInt64.ofNat n) 1

@[always_inline]
def zigzagEncode (x : Int) : Nat :=
  if x < 0 then
    Int.toNat ((-x) * 2 - 1)
  else
    Int.toNat (x * 2)

@[always_inline]
def key (fieldNumber wireType : Nat) : Nat :=
  (fieldNumber <<< 3) ||| wireType

@[always_inline]
def keySize (fieldNumber wireType : Nat) : Nat :=
  varintSize (key fieldNumber wireType)

@[always_inline]
def putKey (fieldNumber wireType : Nat) : Put :=
  put_varint (key fieldNumber wireType)

@[always_inline]
def varintFieldSize (fieldNumber value : Nat) : Nat :=
  keySize fieldNumber 0 + varintSize value

@[always_inline]
def putVarintField (fieldNumber value : Nat) : Put := do
  putKey fieldNumber 0
  put_varint value

@[always_inline]
def i64FieldSize (fieldNumber : Nat) : Nat :=
  keySize fieldNumber 1 + 8

open Binary.Primitive.LE in
@[always_inline]
def putUInt64 (value : UInt64) : Put :=
  Binary.put value

@[always_inline]
def putI64Field (fieldNumber : Nat) (value : UInt64) : Put := do
  putKey fieldNumber 1
  putUInt64 value

@[always_inline]
def i32FieldSize (fieldNumber : Nat) : Nat :=
  keySize fieldNumber 5 + 4

open Binary.Primitive.LE in
@[always_inline]
def putUInt32 (value : UInt32) : Put :=
  Binary.put value

@[always_inline]
def putI32Field (fieldNumber : Nat) (value : UInt32) : Put := do
  putKey fieldNumber 5
  putUInt32 value

@[always_inline]
def lengthDelimitedFieldSize (fieldNumber payloadSize : Nat) : Nat :=
  keySize fieldNumber 2 + varintSize payloadSize + payloadSize

@[always_inline]
def putLengthDelimitedHeader (fieldNumber payloadSize : Nat) : Put := do
  putKey fieldNumber 2
  put_varint payloadSize

@[always_inline]
def bytesFieldSize (fieldNumber : Nat) (value : ByteArray) : Nat :=
  lengthDelimitedFieldSize fieldNumber value.size

@[always_inline]
def putBytesField (fieldNumber : Nat) (value : ByteArray) : Put := do
  putLengthDelimitedHeader fieldNumber value.size
  Binary.put_bytes value

@[always_inline]
def stringFieldSize (fieldNumber : Nat) (value : String) : Nat :=
  lengthDelimitedFieldSize fieldNumber value.utf8ByteSize

@[always_inline]
def putStringField (fieldNumber : Nat) (value : String) : Put := do
  putLengthDelimitedHeader fieldNumber value.utf8ByteSize
  Binary.put_bytes value.toUTF8

@[always_inline]
def messageFieldSize (fieldNumber : Nat) (plan : Plan) : Nat :=
  lengthDelimitedFieldSize fieldNumber plan.size

@[always_inline]
def putMessageField (fieldNumber : Nat) (plan : Plan) : Put := do
  putLengthDelimitedHeader fieldNumber plan.size
  plan.put

@[always_inline]
def groupFieldSize (fieldNumber : Nat) (plan : Plan) : Nat :=
  keySize fieldNumber 3 + plan.size + keySize fieldNumber 4

@[always_inline]
def putGroupField (fieldNumber : Nat) (plan : Plan) : Put := do
  putKey fieldNumber 3
  plan.put
  putKey fieldNumber 4

mutual

@[always_inline]
partial def Plan.ofValue (fieldNumber : Nat) : ProtoVal → Except ProtoError Plan
  | .VARINT value => do
      if value < UInt64.size then
        pure
          { size := varintFieldSize fieldNumber value
          , put := putVarintField fieldNumber value
          }
      else
        throw .invalidVarint
  | .I64 value =>
      pure
        { size := i64FieldSize fieldNumber
        , put := putI64Field fieldNumber (UInt64.ofBitVec value)
        }
  | .LEN value =>
      pure
        { size := bytesFieldSize fieldNumber value
        , put := putBytesField fieldNumber value
        }
  | .GROUPED message => do
      let child ← Plan.ofMessage message
      pure
        { size := groupFieldSize fieldNumber child
        , put := putGroupField fieldNumber child
        }
  | .I32 value =>
      pure
        { size := i32FieldSize fieldNumber
        , put := putI32Field fieldNumber (UInt32.ofBitVec value)
        }

@[always_inline]
partial def Plan.ofRecord (record : Record) : Except ProtoError Plan := do
  if !fieldNumberIsValid record.fieldNum then
    throw (.userError s!"protobuf: field number {record.fieldNum} is invalid")
  Plan.ofValue record.fieldNum record.value

@[always_inline]
partial def Plan.ofMessage (message : Message) : Except ProtoError Plan := do
  Plan.concat <$> message.records.mapM Plan.ofRecord

end

@[always_inline]
def Plan.ofUnknownFields (options : EncodeOptions)
    (fields : Std.HashMap Nat (Array ProtoVal)) : Except ProtoError Plan := do
  if fields.isEmpty then
    pure Plan.empty
  else
    let rawEntries := fields.toArray
    let entries :=
      if options.deterministic then
        (rawEntries.toList.mergeSort (fun a b => a.1 < b.1)).toArray
      else
        rawEntries
    let mut plans := Array.empty
    for (fieldNumber, values) in entries do
      for value in values do
        plans := plans.push (← Plan.ofRecord { fieldNum := fieldNumber, value })
    pure (Plan.concat plans)

end Protobuf.Encoding.Direct
