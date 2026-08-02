module

import Binary
public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
import Std

public section

namespace Protobuf.Encoding

open Binary

@[always_inline]
def Message.push (msg : Message) (r : Record) : Message := {msg with records := msg.records.push r }

@[always_inline]
def Message.set (msg : Message) (fieldNum : Nat) (value : ProtoVal) : Message := msg.push { fieldNum, value }

mutual

@[always_inline]
partial def ProtoVal.validate : ProtoVal → Except Protobuf.Encoding.ProtoError Unit
  | .VARINT n =>
      if n < UInt64.size then
        pure ()
      else
        throw .invalidVarint
  | .GROUPED msg => msg.validate
  | .I64 _ | .LEN _ | .I32 _ => pure ()

@[always_inline]
partial def Record.validate (r : Record) : Except Protobuf.Encoding.ProtoError Unit := do
  if !fieldNumberIsValid r.fieldNum then
    throw (.userError s!"protobuf: field number {r.fieldNum} is invalid")
  r.value.validate

@[always_inline]
partial def Message.validate (msg : Message) : Except Protobuf.Encoding.ProtoError Unit := do
  msg.records.forM Record.validate

end

@[always_inline]
def ProtoVal.ofMessage : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => do
  s.validate
  return ProtoVal.LEN (Put.run (put s))

@[always_inline]
def ProtoVal.ofGroup : Message → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => do
  s.validate
  return ProtoVal.GROUPED s

@[always_inline]
def ProtoVal.ofString : String → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => return ProtoVal.LEN s.toUTF8

@[always_inline]
def ProtoVal.ofBytes : ByteArray → Except Protobuf.Encoding.ProtoError ProtoVal := fun s => return ProtoVal.LEN s

@[always_inline]
def ProtoVal.ofBool : Bool → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT (if x then 1 else 0)

@[always_inline]
def ProtoVal.ofVarint_int32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  return ProtoVal.VARINT (Int64.ofInt x.toInt).toUInt64.toNat
@[always_inline]
def ProtoVal.ofVarint_uint32 : UInt32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toNat
@[always_inline]
def ProtoVal.ofVarint_int64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toUInt64.toNat
@[always_inline]
def ProtoVal.ofVarint_uint64 : UInt64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.VARINT x.toNat

@[always_inline]
private def zigzagEncode (x : Int) : Nat :=
  if x < 0 then
    Int.toNat ((-x) * 2 - 1)
  else
    Int.toNat (x * 2)

@[always_inline]
def ProtoVal.ofVarint_sint32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  return ProtoVal.VARINT (zigzagEncode x.toInt)
@[always_inline]
def ProtoVal.ofVarint_sint64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x =>
  return ProtoVal.VARINT (zigzagEncode x.toInt)

@[always_inline]
def ProtoVal.ofI64_double : Float → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I64 (x.toBits.toBitVec)
@[always_inline]
def ProtoVal.ofI64_fixed64 : UInt64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I64 (x.toBitVec)
@[always_inline]
def ProtoVal.ofI64_sfixed64 : Int64 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I64 (x.toBitVec)

@[always_inline]
def ProtoVal.ofI32_float : Float32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I32 (x.toBits.toBitVec)
@[always_inline]
def ProtoVal.ofI32_fixed32 : UInt32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I32 (x.toBitVec)
@[always_inline]
def ProtoVal.ofI32_sfixed32 : Int32 → Except Protobuf.Encoding.ProtoError ProtoVal := fun x => return ProtoVal.I32 (x.toBitVec)

@[always_inline]
def ProtoVal.canBePacked : ProtoVal → Bool
  | .VARINT ..
  | .I64 ..
  | .I32 .. => true
  | .GROUPED ..
  | .LEN .. => false

open Binary.Primitive.LE in
@[always_inline]
private def put_packed! : ProtoVal → Put
  | .VARINT x => put_varint x
  | .I64 x => put (UInt64.ofBitVec x)
  | .I32 x => put (UInt32.ofBitVec x)
  | _ => unreachable!

@[always_inline]
def ProtoVal.of_packed : Array ProtoVal → ProtoVal := fun xs =>
  assert! xs.all ProtoVal.canBePacked
  let data := Binary.Put.run do
    xs.forM put_packed!
  ProtoVal.LEN data

@[always_inline]
def Message.wire_mapWithOptions (options : EncodeOptions) (msg : Message) : Std.HashMap Nat (Array ProtoVal) → Message := fun m =>
  let xs :=
    if options.deterministic then
      (m.toArray.toList.mergeSort (fun a b => a.1 < b.1)).toArray
    else
      m.toArray
  let xs := xs.map fun (n, xs) => xs.map fun x => Record.mk n x
  {msg with records := msg.records.append xs.flatten}

@[always_inline]
def Message.wire_map (msg : Message) : Std.HashMap Nat (Array ProtoVal) → Message :=
  Message.wire_mapWithOptions EncodeOptions.default msg

def merge_map (a b : Std.HashMap Nat (Array ProtoVal)) : Std.HashMap Nat (Array ProtoVal) :=
  b.fold (init := a) (fun a n v => a.alter n (fun | .none => some v | .some arr => some (arr ++ v)))

end Protobuf.Encoding

namespace Protobuf.Notation

set_option quotPrecheck false

scoped notation n " <~ " val " # " msg => show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
  let v ← val
  pure (Protobuf.Encoding.Message.set msg n v)

scoped notation n " <~? " val " # " msg =>
  show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
    if let Option.some v ← val then
      pure (Protobuf.Encoding.Message.set msg n v)
    else
      pure msg

/-- flattened repeated -/
scoped notation n " <~f " vs " # " msg => show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
  let xs ← vs
  pure (Array.foldl (init := msg) (fun acc x => Protobuf.Encoding.Message.set acc n x) xs)

/-- packed repeated -/
scoped notation n " <~p " vs " # " msg => show Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message from do
  let xs ← vs
  pure (Protobuf.Encoding.Message.set msg n (Protobuf.Encoding.ProtoVal.of_packed xs))

set_option quotPrecheck true

end Notation
