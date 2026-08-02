module

public import Protobuf.Encoding.Basic
public import Protobuf.Encoding.Binary
public import Std

public section

namespace Protobuf.Encoding

@[specialize, always_inline]
def Message.filterRecords (f : Record → Bool) (msg : Message) : Array Record := msg.records.filter f

@[always_inline]
def Message.getRecordsOf (msg : Message) (fieldNum : Nat) : Array Record := msg.filterRecords (fun x => x.fieldNum == fieldNum)

@[always_inline]
def Message.getLastRecordOf? (msg : Message) (fieldNum : Nat) : Option Record := msg.records.reverse.find? (fun x => x.fieldNum == fieldNum)

@[always_inline]
def Message.getValuesOf (msg : Message) (fieldNum : Nat) : Array ProtoVal := msg.getRecordsOf fieldNum |>.map Record.value

@[always_inline]
def Message.getLastValueOf? (msg : Message) (fieldNum : Nat) : Option ProtoVal := msg.records.reverse.find? (fun x => x.fieldNum == fieldNum) |>.map Record.value

open Binary
open Primitive.LE

@[always_inline]
private def getVarintValue : Get Nat := get_varint

@[always_inline]
private def getI32Value : Get (BitVec 32) := do
  let v ← getThe UInt32
  return v.toBitVec

@[always_inline]
private def getI64Value : Get (BitVec 64) := do
  let v ← getThe UInt64
  return v.toBitVec

@[always_inline]
private partial def getPackedVarintValues : Get (Array Nat) := do
  let mut result := #[]
  repeat
    let r ← remaining
    if r == 0 then break
    result := result.push (← getVarintValue)
  return result

@[always_inline]
private partial def getPackedI32Values : Get (Array (BitVec 32)) := do
  let mut result := #[]
  repeat
    let r ← remaining
    if r == 0 then break
    result := result.push (← getI32Value)
  return result

@[always_inline]
private partial def getPackedI64Values : Get (Array (BitVec 64)) := do
  let mut result := #[]
  repeat
    let r ← remaining
    if r == 0 then break
    result := result.push (← getI64Value)
  return result

local macro "throwWireType! " err:term : term => ``(throw (ProtoError.invalidWireType s!"{decl_name%}: {$err}"))
local macro "throwUserError! " err:term : term => ``(throw (ProtoError.userError s!"{decl_name%}: {$err}"))
local macro "throwInvalidBuffer! " err:term : term => ``(throw (ProtoError.invalidBuffer s!"{decl_name%}: {$err}"))

def protoDecodeParseResultExcept : Except Binary.DecodeError α → Except ProtoError α
  | .ok r => pure r
  | .error .eoi => throw .truncated
  | .error (.userError e) =>
      if e == "protobuf: varint too long" || e == "protobuf: varint overflows uint64" then
        throw .invalidVarint
      else if let some (depth, maxDepth) := parseRecursionLimitBinaryError? e then
        throw (.recursionLimitExceeded depth maxDepth)
      else
        throwUserError! s!"error occured when parsing protobuf data: {e}"

@[always_inline]
private def decodePackedVarints (data : ByteArray) : Except ProtoError (Array Nat) := do
  protoDecodeParseResultExcept (Binary.Get.run getPackedVarintValues data).toExcept

@[always_inline]
private def decodePackedI32 (data : ByteArray) : Except ProtoError (Array (BitVec 32)) := do
  protoDecodeParseResultExcept (Binary.Get.run getPackedI32Values data).toExcept

@[always_inline]
private def decodePackedI64 (data : ByteArray) : Except ProtoError (Array (BitVec 64)) := do
  protoDecodeParseResultExcept (Binary.Get.run getPackedI64Values data).toExcept

@[always_inline]
private def Message.concatPackedWith {α : Type} (msg : Message) (fieldNum : Nat)
    (decode : ByteArray → Except ProtoError (Array α)) : Except ProtoError (Array α) := do
  let xs := msg.getValuesOf fieldNum
  if xs.any (fun x => !x.isLEN) then
    throwWireType! "packed data must be LEN"
  let xs := xs.map fun
    | .LEN data => data
    | _ => unreachable!
  let rs ← xs.mapM decode
  return rs.flatten

@[always_inline]
def Message.getString? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option String) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      let some str := String.fromUTF8? v | throwInvalidBuffer! "invalid UTF-8 data"
      return str
    throwWireType! "expected LEN"

@[always_inline]
def Message.getBytes? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option ByteArray) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    if let some v := x.isLEN? then
      return v
    throwWireType! "expected LEN"

@[always_inline]
private def decodeMessageWithOptions (options : DecodeOptions) (depth : Nat)
    (data : ByteArray) : Except ProtoError Message := do
  options.checkMessageSize data.size
  options.checkRecursionDepth depth
  let r := Binary.Get.run (getMessageWithOptions options depth) data
  protoDecodeParseResultExcept r.toExcept

@[always_inline]
private def decodeMessage (data : ByteArray) : Except ProtoError Message :=
  decodeMessageWithOptions DecodeOptions.default 0 data

@[always_inline]
def Message.getMessageWithOptions? (options : DecodeOptions) (depth : Nat)
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Message) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    match x with
    | .LEN data => decodeMessageWithOptions options depth data
    | .GROUPED sub =>
        options.checkRecursionDepth depth
        return sub
    | _ => throwWireType! "expected LEN or GROUPED"

@[always_inline]
def Message.getMessage? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Message) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    match x with
    | .LEN data => decodeMessage data
    | .GROUPED sub => return sub
    | _ => throwWireType! "expected LEN or GROUPED"

@[always_inline]
def Message.getLastValidWith? (msg : Message) (fieldNum : Nat)
    (decodeOne : Message → Nat → Except ProtoError (Option α)) : Except ProtoError (Option α) := do
  let mut out := none
  for record in msg.getRecordsOf fieldNum do
    let single := Message.mk #[record]
    match decodeOne single fieldNum with
    | .ok (some value) => out := some value
    | .ok none => pure ()
    | .error (.invalidWireType _) => pure ()
    | .error err => throw err
  return out

@[always_inline]
def Message.getMergedValidWith? (msg : Message) (fieldNum : Nat)
    (decodeOne : Message → Nat → Except ProtoError (Option α)) (merge : α → α → α) :
    Except ProtoError (Option α) := do
  let mut out := none
  for record in msg.getRecordsOf fieldNum do
    let single := Message.mk #[record]
    match decodeOne single fieldNum with
    | .ok (some value) =>
        out := match out with
          | some old => some (merge old value)
          | none => some value
    | .ok none => pure ()
    | .error (.invalidWireType _) => pure ()
    | .error err => throw err
  return out

@[always_inline]
def Message.getRepeatedValidWith (msg : Message) (fieldNum : Nat)
    (decodeMany : Message → Nat → Except ProtoError (Array α)) : Except ProtoError (Array α) := do
  let mut out := #[]
  for record in msg.getRecordsOf fieldNum do
    let single := Message.mk #[record]
    match decodeMany single fieldNum with
    | .ok values => out := out ++ values
    | .error (.invalidWireType _) => pure ()
    | .error err => throw err
  return out

@[always_inline]
def Message.getBool? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Bool) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x => do
    let some v := x.isVARINT? | throwWireType! "expected VARINT"
    return v != 0

@[always_inline]
def Message.getVarint? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Nat) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x =>
    match x.isVARINT? with
    | some v => return v
    | none => throwWireType! "expected VARINT"

@[always_inline]
def Message.getI64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option (BitVec 64)) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x =>
    match x.isI64? with
    | some v => return v
    | none => throwWireType! "expected I64"

@[always_inline]
def Message.getI32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option (BitVec 32)) := do
  let r := msg.getLastValueOf? fieldNum
  r.mapM fun x =>
    match x.isI32? with
    | some v => return v
    | none => throwWireType! "expected I32"

@[always_inline]
private def zigzagDecode32 (n : Nat) : Int32 :=
  let y : UInt32 := UInt32.ofNat n
  let mask : UInt32 := 0 - (y &&& 1)
  let z : UInt32 := (y >>> 1) ^^^ mask
  Int32.ofBitVec z.toBitVec

@[always_inline]
private def zigzagDecode64 (n : Nat) : Int64 :=
  let y : UInt64 := UInt64.ofNat n
  let mask : UInt64 := 0 - (y &&& 1)
  let z : UInt64 := (y >>> 1) ^^^ mask
  Int64.ofBitVec z.toBitVec

@[always_inline]
def Message.getVarint_int32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int32) := do
  let r ← msg.getVarint? fieldNum
  return r.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getVarint_uint32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt32) := do
  let r ← msg.getVarint? fieldNum
  return r.map UInt32.ofNat

@[always_inline]
def Message.getVarint_int64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int64) := do
  let r ← msg.getVarint? fieldNum
  return r.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getVarint_uint64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt64) := do
  let r ← msg.getVarint? fieldNum
  return r.map UInt64.ofNat

@[always_inline]
def Message.getVarint_sint32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int32) := do
  let r ← msg.getVarint? fieldNum
  return r.map zigzagDecode32

@[always_inline]
def Message.getVarint_sint64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int64) := do
  let r ← msg.getVarint? fieldNum
  return r.map zigzagDecode64

@[always_inline]
def Message.getI64_double? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Float) := do
  let r ← msg.getI64? fieldNum
  return r.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getI64_fixed64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt64) := do
  let r ← msg.getI64? fieldNum
  return r.map UInt64.ofBitVec

@[always_inline]
def Message.getI64_sfixed64? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int64) := do
  let r ← msg.getI64? fieldNum
  return r.map Int64.ofBitVec

@[always_inline]
def Message.getI32_float? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Float32) := do
  let r ← msg.getI32? fieldNum
  return r.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getI32_fixed32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option UInt32) := do
  let r ← msg.getI32? fieldNum
  return r.map UInt32.ofBitVec

@[always_inline]
def Message.getI32_sfixed32? (msg : Message) (fieldNum : Nat) : Except ProtoError (Option Int32) := do
  let r ← msg.getI32? fieldNum
  return r.map Int32.ofBitVec

@[always_inline]
private def Message.getPackedVarint (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Nat) := do
  msg.concatPackedWith fieldNum decodePackedVarints

@[always_inline]
private def Message.getPackedI64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 64)) := do
  msg.concatPackedWith fieldNum decodePackedI64

@[always_inline]
private def Message.getPackedI32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 32)) := do
  msg.concatPackedWith fieldNum decodePackedI32

@[always_inline]
def Message.getPackedBool (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Bool) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map (fun v => v != 0)

@[always_inline]
def Message.getPackedVarint_int32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getPackedVarint_uint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map UInt32.ofNat

@[always_inline]
def Message.getPackedVarint_int64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getPackedVarint_uint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map UInt64.ofNat

@[always_inline]
def Message.getPackedVarint_sint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map zigzagDecode32

@[always_inline]
def Message.getPackedVarint_sint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getPackedVarint fieldNum
  return xs.map zigzagDecode64

@[always_inline]
def Message.getPackedI64_double (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float) := do
  let xs ← msg.getPackedI64 fieldNum
  return xs.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getPackedI64_fixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getPackedI64 fieldNum
  return xs.map UInt64.ofBitVec

@[always_inline]
def Message.getPackedI64_sfixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getPackedI64 fieldNum
  return xs.map Int64.ofBitVec

@[always_inline]
def Message.getPackedI32_float (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float32) := do
  let xs ← msg.getPackedI32 fieldNum
  return xs.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getPackedI32_fixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getPackedI32 fieldNum
  return xs.map UInt32.ofBitVec

@[always_inline]
def Message.getPackedI32_sfixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getPackedI32 fieldNum
  return xs.map Int32.ofBitVec

@[always_inline]
private def Message.getExpandedVarint (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Nat) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x =>
    match x.isVARINT? with
    | some v => return v
    | none => throwWireType! "expected VARINT"

@[always_inline]
private def Message.getExpandedI64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 64)) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x =>
    match x.isI64? with
    | some v => return v
    | none => throwWireType! "expected I64"

@[always_inline]
private def Message.getExpandedI32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 32)) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x =>
    match x.isI32? with
    | some v => return v
    | none => throwWireType! "expected I32"

@[always_inline]
private def Message.getExpandedLen (msg : Message) (fieldNum : Nat) : Except ProtoError (Array ByteArray) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x =>
    match x.isLEN? with
    | some v => return v
    | none => throwWireType! "expected LEN"

@[always_inline]
def Message.getExpandedString (msg : Message) (fieldNum : Nat) : Except ProtoError (Array String) := do
  let xs ← msg.getExpandedLen fieldNum
  xs.mapM fun x => (String.fromUTF8? x).getDM (throwInvalidBuffer! "invalid UTF-8 data")

@[always_inline]
def Message.getExpandedBytes (msg : Message) (fieldNum : Nat) : Except ProtoError (Array ByteArray) := do
  msg.getExpandedLen fieldNum

@[always_inline]
def Message.getExpandedMessage (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Message) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    match x with
    | .LEN data => decodeMessage data
    | .GROUPED sub => return sub
    | _ => throwWireType! "expected LEN or GROUPED"

@[always_inline]
def Message.getExpandedMessageWithOptions (options : DecodeOptions) (depth : Nat)
    (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Message) := do
  let xs := msg.getValuesOf fieldNum
  xs.mapM fun x => do
    match x with
    | .LEN data => decodeMessageWithOptions options depth data
    | .GROUPED sub =>
        options.checkRecursionDepth depth
        return sub
    | _ => throwWireType! "expected LEN or GROUPED"

@[always_inline]
def Message.getExpandedBool (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Bool) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map (fun v => v != 0)

@[always_inline]
def Message.getExpandedVarint_int32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getExpandedVarint_uint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map UInt32.ofNat

@[always_inline]
def Message.getExpandedVarint_int64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getExpandedVarint_uint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map UInt64.ofNat

@[always_inline]
def Message.getExpandedVarint_sint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map zigzagDecode32

@[always_inline]
def Message.getExpandedVarint_sint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getExpandedVarint fieldNum
  return xs.map zigzagDecode64

@[always_inline]
def Message.getExpandedI64_double (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float) := do
  let xs ← msg.getExpandedI64 fieldNum
  return xs.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getExpandedI64_fixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getExpandedI64 fieldNum
  return xs.map UInt64.ofBitVec

@[always_inline]
def Message.getExpandedI64_sfixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getExpandedI64 fieldNum
  return xs.map Int64.ofBitVec

@[always_inline]
def Message.getExpandedI32_float (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float32) := do
  let xs ← msg.getExpandedI32 fieldNum
  return xs.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getExpandedI32_fixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getExpandedI32 fieldNum
  return xs.map UInt32.ofBitVec

@[always_inline]
def Message.getExpandedI32_sfixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getExpandedI32 fieldNum
  return xs.map Int32.ofBitVec

@[always_inline]
private def Message.getRepeatedVarint (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Nat) := do
  let rs := msg.getRecordsOf fieldNum
  let mut out := #[]
  for r in rs do
    match r.value with
    | .VARINT v => out := out.push v
    | .LEN data => out := out ++ (← decodePackedVarints data)
    | .GROUPED _ => throwWireType! "value of repeated field cannot be GROUPED"
    | _ => throwWireType! "expected VARINT or packed LEN"
  return out

@[always_inline]
private def Message.getRepeatedI64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 64)) := do
  let rs := msg.getRecordsOf fieldNum
  let mut out := #[]
  for r in rs do
    match r.value with
    | .I64 v => out := out.push v
    | .LEN data => out := out ++ (← decodePackedI64 data)
    | .GROUPED _ => throwWireType! "value of repeated field cannot be GROUPED"
    | _ => throwWireType! "expected I64 or packed LEN"
  return out

@[always_inline]
private def Message.getRepeatedI32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array (BitVec 32)) := do
  let rs := msg.getRecordsOf fieldNum
  let mut out := #[]
  for r in rs do
    match r.value with
    | .I32 v => out := out.push v
    | .LEN data => out := out ++ (← decodePackedI32 data)
    | .GROUPED _ => throwWireType! "value of repeated field cannot be GROUPED"
    | _ => throwWireType! "expected I32 or packed LEN"
  return out

@[always_inline]
def Message.getRepeatedBool (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Bool) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map (fun v => v != 0)

@[always_inline]
def Message.getRepeatedVarint_int32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map fun n => Int32.ofBitVec (UInt32.ofNat n).toBitVec

@[always_inline]
def Message.getRepeatedVarint_uint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map UInt32.ofNat

@[always_inline]
def Message.getRepeatedVarint_int64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map fun n => Int64.ofBitVec (UInt64.ofNat n).toBitVec

@[always_inline]
def Message.getRepeatedVarint_uint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map UInt64.ofNat

@[always_inline]
def Message.getRepeatedVarint_sint32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map zigzagDecode32

@[always_inline]
def Message.getRepeatedVarint_sint64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getRepeatedVarint fieldNum
  return xs.map zigzagDecode64

@[always_inline]
def Message.getRepeatedI64_double (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float) := do
  let xs ← msg.getRepeatedI64 fieldNum
  return xs.map fun n => Float.ofBits (UInt64.ofBitVec n)

@[always_inline]
def Message.getRepeatedI64_fixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt64) := do
  let xs ← msg.getRepeatedI64 fieldNum
  return xs.map UInt64.ofBitVec

@[always_inline]
def Message.getRepeatedI64_sfixed64 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int64) := do
  let xs ← msg.getRepeatedI64 fieldNum
  return xs.map Int64.ofBitVec

@[always_inline]
def Message.getRepeatedI32_float (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Float32) := do
  let xs ← msg.getRepeatedI32 fieldNum
  return xs.map fun n => Float32.ofBits (UInt32.ofBitVec n)

@[always_inline]
def Message.getRepeatedI32_fixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array UInt32) := do
  let xs ← msg.getRepeatedI32 fieldNum
  return xs.map UInt32.ofBitVec

@[always_inline]
def Message.getRepeatedI32_sfixed32 (msg : Message) (fieldNum : Nat) : Except ProtoError (Array Int32) := do
  let xs ← msg.getRepeatedI32 fieldNum
  return xs.map Int32.ofBitVec
