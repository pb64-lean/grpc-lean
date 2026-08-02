module

public import Binary
public import Protobuf.Encoding.Basic

public section

namespace Protobuf.Encoding

open Binary

inductive ProtoError where
  | truncated
  | invalidVarint
  | invalidWireType (err : String)
  | invalidBuffer (err : String)
  | missingRequiredField (err : String)
  | messageTooLarge (size maxSize : Nat)
  | recursionLimitExceeded (depth maxDepth : Nat)
  | userError (err : String)
deriving Repr

def ProtoError.toString : ProtoError → String
  | .truncated => "proto decode error: truncated input"
  | .invalidVarint => "proto decode error: invalid varint"
  | .invalidWireType err => s!"proto decode error: invalid wire type: {err}"
  | .invalidBuffer err => s!"proto decode error: invalid buffer: {err}"
  | .missingRequiredField err => s!"proto decode error: missing required field: {err}"
  | .messageTooLarge size maxSize => s!"proto decode error: message size {size} exceeds limit {maxSize}"
  | .recursionLimitExceeded depth maxDepth => s!"proto decode error: recursion depth {depth} exceeds limit {maxDepth}"
  | .userError err => s!"proto decode error: {err}"

instance : ToString ProtoError := ⟨ProtoError.toString⟩

structure DecodeOptions where
  maxMessageSize? : Option Nat := none
  maxRecursionDepth? : Option Nat := none
deriving Repr, Inhabited

structure EncodeOptions where
  deterministic : Bool := false
deriving Repr, Inhabited

namespace DecodeOptions

@[always_inline]
def default : DecodeOptions := {}

@[always_inline]
def withMaxMessageSize (maxSize : Nat) : DecodeOptions :=
  { default with maxMessageSize? := some maxSize }

@[always_inline]
def withMaxRecursionDepth (maxDepth : Nat) : DecodeOptions :=
  { default with maxRecursionDepth? := some maxDepth }

@[always_inline]
def withLimits (maxSize maxDepth : Nat) : DecodeOptions :=
  { maxMessageSize? := some maxSize, maxRecursionDepth? := some maxDepth }

@[always_inline]
def checkMessageSize (options : DecodeOptions) (size : Nat) : Except ProtoError Unit := do
  match options.maxMessageSize? with
  | some maxSize =>
      if size <= maxSize then
        pure ()
      else
        throw (.messageTooLarge size maxSize)
  | none => pure ()

@[always_inline]
def checkRecursionDepth (options : DecodeOptions) (depth : Nat) : Except ProtoError Unit := do
  match options.maxRecursionDepth? with
  | some maxDepth =>
      if depth <= maxDepth then
        pure ()
      else
        throw (.recursionLimitExceeded depth maxDepth)
  | none => pure ()

end DecodeOptions

namespace EncodeOptions

@[always_inline]
def default : EncodeOptions := {}

@[always_inline]
def withDeterministic : EncodeOptions :=
  { default with deterministic := true }

end EncodeOptions

@[always_inline]
def maxFieldNumber : Nat := (1 <<< 29) - 1

@[always_inline]
def firstReservedFieldNumber : Nat := 19000

@[always_inline]
def lastReservedFieldNumber : Nat := 19999

@[always_inline]
def fieldNumberIsValid (fieldNum : Nat) : Bool :=
  fieldNum != 0 && fieldNum <= maxFieldNumber

@[always_inline]
def fieldNumberIsReserved (fieldNum : Nat) : Bool :=
  firstReservedFieldNumber <= fieldNum && fieldNum <= lastReservedFieldNumber

@[always_inline]
def fieldNumberIsAllowedInSchema (fieldNum : Nat) : Bool :=
  fieldNumberIsValid fieldNum && !fieldNumberIsReserved fieldNum

@[always_inline]
def recursionLimitBinaryErrorPrefix : String := "protobuf: recursion limit exceeded:"

@[always_inline]
def recursionLimitBinaryError (depth maxDepth : Nat) : String :=
  s!"{recursionLimitBinaryErrorPrefix}{depth}:{maxDepth}"

def parseRecursionLimitBinaryError? (err : String) : Option (Nat × Nat) := do
  if !err.startsWith recursionLimitBinaryErrorPrefix then
    none
  let rest := (err.drop recursionLimitBinaryErrorPrefix.length).toString
  match rest.splitOn ":" with
  | [depth, maxDepth] => do
      let depth ← depth.toNat?
      let maxDepth ← maxDepth.toNat?
      some (depth, maxDepth)
  | _ => none

@[always_inline]
private def checkRecursionDepthInGet (options : DecodeOptions) (depth : Nat) : Get Unit := do
  match options.maxRecursionDepth? with
  | some maxDepth =>
      if depth <= maxDepth then
        pure ()
      else
        throw (.userError (recursionLimitBinaryError depth maxDepth))
  | none => pure ()

@[always_inline]
private partial def get_varint_bytes : Get ((bs : ByteArray) ×' bs.size > 0) := do
  let rec go (acc : ByteArray) : Get ((bs : ByteArray) ×' bs.size > 0) := do
    if acc.size ≥ 10 then
      throw (.userError "protobuf: varint too long")
    let b ← getThe UInt8
    let acc := acc.push b
    if !b.toBitVec.msb then
      return ⟨acc, by simp [acc, ByteArray.push]; unfold ByteArray.size; simp⟩
    go acc
  go (ByteArray.emptyWithCapacity 10)

@[always_inline]
partial def get_varint : Get Nat := do
  let ⟨bs, h⟩ ← get_varint_bytes
  let rec go (acc : Nat) (shift : Nat) (idx : USize) (h : idx.toNat < bs.size) : Nat :=
    let b := bs.uget idx h
    let j := idx + 1
    let acc := acc ||| ((b &&& 0x7F).toNat <<< shift)
    if h' : j.toNat < bs.size then
      go acc (shift + 7) j h'
    else
      acc
  let n := go 0 0 0 h
  if n < UInt64.size then
    return n
  else
    throw (.userError "protobuf: varint overflows uint64")

@[always_inline]
partial def put_varint (n : Nat) : Put := do
  let rec go (acc : ByteArray) (v : UInt64) : ByteArray :=
    let byte : UInt8 := UInt8.ofNat ((v &&& (0x7F : UInt64)).toNat)
    let v := v >>> 7
    if v = 0 then
      acc.push byte
    else
      go (acc.push (byte ||| (0x80 : UInt8))) v
  let bs := go (ByteArray.emptyWithCapacity 10) (UInt64.ofNat n)
  put_bytes bs

open Primitive.LE in
@[always_inline]
partial instance : Encode Record where
  put x := do
    let rec go (x : Record) : Put := do
      let wireType : ProtoVal → Nat
        | .VARINT .. => 0
        | .I64 .. => 1
        | .LEN .. => 2
        | .GROUPED .. => unreachable!
        | .I32 .. => 5
      match x.value with
      | .GROUPED sub =>
        put_varint <| (x.fieldNum <<< 3) ||| 3 -- SGROUP
        sub.records.forM go
        put_varint <| (x.fieldNum <<< 3) ||| 4 -- EGROUP
      | _ =>
        let v : Nat := (x.fieldNum <<< 3) ||| (wireType x.value)
        put_varint v
        match x.value with
        | .VARINT v => put_varint v
        | .I64 v => put (UInt64.ofBitVec v)
        | .I32 v => put (UInt32.ofBitVec v)
        | .GROUPED _ => unreachable!
        | .LEN data =>
          put_varint data.size
          put_bytes data
    go x

open Primitive.LE in
@[always_inline]
partial def getRecordWithOptions (options : DecodeOptions) (depth : Nat) : Get Record := do
    let rec go (depth : Nat) (endGroup? : Option Nat) : Get (Option Record) := do
      let key ← get_varint
      let wire_type := (key &&& 0b111)
      let num := (key >>> 3)
      if !fieldNumberIsValid num then
        throw (.userError s!"protobuf: field number {num} is invalid")
      match wire_type with
      | 0 =>
        let v ← get_varint
        return some ⟨num, .VARINT v⟩
      | 1 =>
        let v ← getThe UInt64
        return some ⟨num, .I64 v.toBitVec⟩
      | 2 =>
        let size ← get_varint
        let bytes ← get_bytes size
        return some ⟨num, .LEN bytes⟩
      | 3 =>
        let groupDepth := depth + 1
        checkRecursionDepthInGet options groupDepth
        let mut rs := #[]
        repeat
          let some x ← go groupDepth (some num) | break
          rs := rs.push x
        return some ⟨num, .GROUPED ⟨rs⟩⟩
      | 4 =>
        match endGroup? with
        | some expected =>
          if num == expected then
            return none
          else
            throw (.userError s!"protobuf: mismatched EGROUP for field {num}, expected {expected}")
        | none => return none
      | 5 =>
        let v ← getThe UInt32
        return some ⟨num, .I32 v.toBitVec⟩
      | _ => throw (.userError "protobuf: invalid wire type encountered")
    checkRecursionDepthInGet options depth
    let some r ← go depth none | throw (.userError "protobuf: unexpected EGROUP")
    return r

@[always_inline]
partial def getMessageWithOptions (options : DecodeOptions) (depth : Nat) : Get Message := do
  checkRecursionDepthInGet options depth
  let rec go (acc : Array Record) : Get (Array Record) := do
    if (← remaining) = 0 then
      return acc
    let r ← getRecordWithOptions options depth
    go (acc.push r)
  Message.mk <$> go (Array.emptyWithCapacity 32)

open Primitive.LE in
@[always_inline]
partial instance : Decode Record where
  get := getRecordWithOptions DecodeOptions.default 0

@[always_inline]
instance : Encode Message where
  put x := x.records.forM put

@[always_inline]
partial instance : Decode Message where
  get := getMessageWithOptions DecodeOptions.default 0
