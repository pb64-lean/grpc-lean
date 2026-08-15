module

public meta import Protobuf.Encoding
public import Protobuf.Base64
import Protobuf.Encoding.Builder
import Protobuf.Encoding.Unwire
import Protobuf.Utils
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Enum
public import Lean
import Protobuf.Notation.Syntax

public meta section

namespace Protobuf.Notation

open Encoding Notation

open Lean Meta Elab Term Command

initialize protoOneOfAttr : TagAttribute ←
  registerTagAttribute `proto_oneof "mark inductive type to be a protobuf oneof sum type"

public def getProtoOneOfs [Monad m] [MonadEnv m] : m NameSet := do
  let env ← getEnv
  return protoOneOfAttr.ext.getState env

public def isProtoOneOf [Monad m] [MonadEnv m] (x : Name) : m Bool := do
  let env ← getEnv
  return protoOneOfAttr.hasTag env x

private def resolveInternalType [Monad m] [MonadQuotation m] : TSyntax `ident → m (TSyntax `ident) := fun stx =>
  match stx with
  | `(string) => ``(String)
  | `(bytes) => ``(ByteArray)
  | `(bool) => ``(Bool)
  | `(int32) => ``(Int32)
  | `(uint32) => ``(UInt32)
  | `(int64) => ``(Int64)
  | `(uint64) => ``(UInt64)
  | `(sint32) => ``(Int32)
  | `(sint64) => ``(Int64)

  | `(double) => ``(Float)
  | `(float) => ``(Float32)
  | `(fixed64) => ``(UInt64)
  | `(sfixed64) => ``(Int64)
  | `(fixed32) => ``(UInt32)
  | `(sfixed32) => ``(Int32)
  | x => pure x

inductive Modifier where
  /-- singular scalar fields are encoded as plain scalar type with default value -/
  | default
  /-- all optional -/
  | optional
  | repeated
  | required
deriving Inhabited, BEq

instance : ToString Modifier where
  toString
    | .default => "default"
    | .optional => "optional"
    | .repeated => "repeated"
    | .required => "required"

inductive InternalType where
  | string
  | bytes
  | bool
  | int32
  | uint32
  | int64
  | uint64
  | sint32
  | sint64

  | double
  | fixed64
  | sfixed64
  | float
  | fixed32
  | sfixed32
deriving Inhabited, BEq

private def InternalType.isMapKeyAllowed : InternalType → Bool
  | .string
  | .bool
  | .int32
  | .uint32
  | .int64
  | .uint64
  | .sint32
  | .sint64
  | .fixed32
  | .fixed64
  | .sfixed32
  | .sfixed64 => true
  | .bytes
  | .double
  | .float => false

private def getInternalType? : TSyntax `ident → Option InternalType
  | `(string) => some .string
  | `(bool) => some .bool
  | `(bytes) => some .bytes
  | `(int32) => some .int32
  | `(uint32) => some .uint32
  | `(int64) => some .int64
  | `(uint64) => some .uint64
  | `(sint32) => some .sint32
  | `(sint64) => some .sint64

  | `(double) => some .double
  | `(float) => some .float
  | `(fixed64) => some .fixed64
  | `(sfixed64) => some .sfixed64
  | `(fixed32) => some .fixed32
  | `(sfixed32) => some .sfixed32
  | _ => none

/-- (is_scalar, internal_type?, enum_type?, oneof_type?) -/
@[specialize]
private def getProtoTypeMData [Monad m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) : TSyntax `ident → m (Bool × Option InternalType × Option Name × Option Name) := fun x => do
  let internal_type? := getInternalType? x
  if let some x := internal_type? then
    if x != InternalType.string && x != InternalType.bytes then
      return (true, internal_type?, none, none)
    else
      return (false, internal_type?, none, none)
  if mutEnums.contains x.getId then
    return (true, none, some x.getId, none)
  if mutOneofs.contains x.getId then
    return (false, none, none, some x.getId)
  if messages.contains x.getId then
    return (false, none, none, none)
  let ns ← try resolveGlobalConst x
    catch _ => throwErrorAt x "Type {x} is not one of mutual declarations but cannot be resolved.\n  Note: if a mutual declaration has qualified name, then it must also be qualified when used in the same mutual block."
      -- return (false, internal_type?, none, none)
  if ns.length > 1 then
    throwErrorAt x "{x} is ambiguous"
  if ← isProtoEnum ns[0]! then
    return (true, internal_type?, some ns[0]!, none)
  else if ← isProtoOneOf ns[0]! then
    return (false, internal_type?, none, some ns[0]!)
  else
    return (false, internal_type?, none, none)

private def InternalType.builder [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string =>  ``(Encoding.ProtoVal.ofString)
  | .bytes =>   ``(Encoding.ProtoVal.ofBytes)
  | .bool =>    ``(Encoding.ProtoVal.ofBool)
  | .int32 =>   ``(Encoding.ProtoVal.ofVarint_int32)
  | .uint32 =>  ``(Encoding.ProtoVal.ofVarint_uint32)
  | .int64 =>   ``(Encoding.ProtoVal.ofVarint_int64)
  | .uint64 =>  ``(Encoding.ProtoVal.ofVarint_uint64)
  | .sint32 =>  ``(Encoding.ProtoVal.ofVarint_sint32)
  | .sint64 =>  ``(Encoding.ProtoVal.ofVarint_sint64)

  | .double =>    ``(Encoding.ProtoVal.ofI64_double)
  | .fixed64 =>   ``(Encoding.ProtoVal.ofI64_fixed64)
  | .sfixed64 =>  ``(Encoding.ProtoVal.ofI64_sfixed64)
  | .float =>     ``(Encoding.ProtoVal.ofI32_float)
  | .fixed32 =>   ``(Encoding.ProtoVal.ofI32_fixed32)
  | .sfixed32 =>  ``(Encoding.ProtoVal.ofI32_sfixed32)

private def InternalType.decoder? [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string =>  ``(Encoding.Message.getString?)
  | .bytes =>   ``(Encoding.Message.getBytes?)
  | .bool =>    ``(Encoding.Message.getBool?)
  | .int32 =>   ``(Encoding.Message.getVarint_int32?)
  | .uint32 =>  ``(Encoding.Message.getVarint_uint32?)
  | .int64 =>   ``(Encoding.Message.getVarint_int64?)
  | .uint64 =>  ``(Encoding.Message.getVarint_uint64?)
  | .sint32 =>  ``(Encoding.Message.getVarint_sint32?)
  | .sint64 =>  ``(Encoding.Message.getVarint_sint64?)

  | .double =>    ``(Encoding.Message.getI64_double?)
  | .fixed64 =>   ``(Encoding.Message.getI64_fixed64?)
  | .sfixed64 =>  ``(Encoding.Message.getI64_sfixed64?)
  | .float =>     ``(Encoding.Message.getI32_float?)
  | .fixed32 =>   ``(Encoding.Message.getI32_fixed32?)
  | .sfixed32 =>  ``(Encoding.Message.getI32_sfixed32?)

private def InternalType.decoder_rep_packed [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string
  | .bytes =>   panic! "only scalar type is allowed to be packed"
  | .bool =>    ``(Encoding.Message.getPackedBool)
  | .int32 =>   ``(Encoding.Message.getPackedVarint_int32)
  | .uint32 =>  ``(Encoding.Message.getPackedVarint_uint32)
  | .int64 =>   ``(Encoding.Message.getPackedVarint_int64)
  | .uint64 =>  ``(Encoding.Message.getPackedVarint_uint64)
  | .sint32 =>  ``(Encoding.Message.getPackedVarint_sint32)
  | .sint64 =>  ``(Encoding.Message.getPackedVarint_sint64)

  | .double =>    ``(Encoding.Message.getPackedI64_double)
  | .fixed64 =>   ``(Encoding.Message.getPackedI64_fixed64)
  | .sfixed64 =>  ``(Encoding.Message.getPackedI64_sfixed64)
  | .float =>     ``(Encoding.Message.getPackedI32_float)
  | .fixed32 =>   ``(Encoding.Message.getPackedI32_fixed32)
  | .sfixed32 =>  ``(Encoding.Message.getPackedI32_sfixed32)

private def InternalType.decoder_rep [Monad m] [MonadQuotation m] : InternalType → m Ident
  | .string =>  ``(Encoding.Message.getExpandedString)
  | .bytes =>   ``(Encoding.Message.getExpandedBytes)
  | .bool =>    ``(Encoding.Message.getRepeatedBool)
  | .int32 =>   ``(Encoding.Message.getRepeatedVarint_int32)
  | .uint32 =>  ``(Encoding.Message.getRepeatedVarint_uint32)
  | .int64 =>   ``(Encoding.Message.getRepeatedVarint_int64)
  | .uint64 =>  ``(Encoding.Message.getRepeatedVarint_uint64)
  | .sint32 =>  ``(Encoding.Message.getRepeatedVarint_sint32)
  | .sint64 =>  ``(Encoding.Message.getRepeatedVarint_sint64)

  | .double =>    ``(Encoding.Message.getRepeatedI64_double)
  | .fixed64 =>   ``(Encoding.Message.getRepeatedI64_fixed64)
  | .sfixed64 =>  ``(Encoding.Message.getRepeatedI64_sfixed64)
  | .float =>     ``(Encoding.Message.getRepeatedI32_float)
  | .fixed32 =>   ``(Encoding.Message.getRepeatedI32_fixed32)
  | .sfixed32 =>  ``(Encoding.Message.getRepeatedI32_sfixed32)

inductive LeanShape where
  | strict
  | option
  | array
  | map
deriving Inhabited, BEq

structure MapFieldMData where
  key_proto_type : Ident
  value_proto_type : Ident
  key_lean_type : Ident
  value_lean_type : Ident
  key_builder : Ident
  value_builder : Ident
  key_decoder? : Ident
  value_decoder? : Ident
  value_decoder_with_options? : Option Ident
  value_closed_enum : Bool
  key_default : Term
  value_default : Term
  insert : Ident
  union : Ident
deriving Inhabited

structure ProtoFieldMData where
  mod : Modifier
  proto_type : Ident
  lean_type_inner : Ident
  lean_type : Term
  field_name : Ident
  field_proj : Ident
  field_num : TSyntax `num
  options : Options
  lean_shape : LeanShape
  map_info? : Option MapFieldMData
  is_scalar : Bool
  internal_type? : Option InternalType
  /-- the `«Default.Value»` of the type -/
  default_lean_value : Term
  /-- the default value term in constructor so that use-site `{...}` won't need to initialize everything -/
  default_ctor_value : Term
  /-- the code to test whether this fields should not be serialized to the wire -/
  test_unset : Term
  enum_type? : Option Name
  oneof_type? : Option Name
  builder? : Option Ident
  toMessage? : Option Ident
  fromMessage? : Option Ident
  fromMessage?? : Option Ident
  decoder?? : Option Ident
  decoder_rep? : Option Ident
  decoder_rep_packed? : Option Ident
deriving Inhabited

private def optionsValueToNumericTerm [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (v : TSyntax `options_value) : m Term := do
  match v with
  | `(options_value| $x:scientific) => `($x:scientific)
  | `(options_value| -$x:scientific) => `(-$x:scientific)
  | `(options_value| +$x:scientific) => `($x:scientific)
  | `(options_value| $x:num) => `($x:num)
  | `(options_value| -$x:num) => `(-$x:num)
  | `(options_value| +$x:num) => `($x:num)
  | _ => throwErrorAt field_name "default option expects a numeric literal"

private def optionsValueToTerm [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (_lean_shape : LeanShape) (_proto_type : Ident) (internal_type : InternalType) (v : TSyntax `options_value) : m Term := do
  match internal_type with
  | .bool =>
      match v with
      | `(options_value| true) => `(true)
      | `(options_value| false) => `(false)
      | _ => throwErrorAt field_name "default option expects a boolean literal"
  | .string =>
      match v with
      | `(options_value| $s:str) => `($s:str)
      | _ => throwErrorAt field_name "default option expects a string literal"
  | .bytes =>
      match v with
      | `(options_value| $s:str) => `(($s:str).toUTF8)
      | _ => throwErrorAt field_name "default option expects a string literal"
  | .double | .float =>
      match v with
      | `(options_value| $x:ident) => `($x:ident)
      | _ => optionsValueToNumericTerm field_name v
  | _ => optionsValueToNumericTerm field_name v

private def optionsBase64ValueToTerm [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (internal_type : InternalType) (v : TSyntax `options_value) : m Term := do
  match internal_type with
  | .string =>
      match v with
      | `(options_value| $s:str) =>
          match Protobuf.Base64.decodeBase64String s.getString with
          | .ok decoded =>
              let lit : TSyntax `str := ⟨Lean.Syntax.mkStrLit decoded⟩
              `($lit:str)
          | .error err => throwErrorAt field_name err
      | _ => throwErrorAt field_name "default_base64 option expects a string literal"
  | .bytes =>
      match v with
      | `(options_value| $s:str) =>
          match Protobuf.Base64.decode s.getString with
          | .ok decoded =>
              let mut byteTerms := #[]
              for h : i in [:decoded.size] do
                let byte : UInt8 := decoded[i]
                let n := quote byte.toNat
                byteTerms := byteTerms.push (← `(UInt8.ofNat $n))
              `(ByteArray.mk #[$byteTerms,*])
          | .error err => throwErrorAt field_name err
      | _ => throwErrorAt field_name "default_base64 option expects a string literal"
  | _ => throwErrorAt field_name "default_base64 option is only supported for string or bytes fields"

private def defaultOverride? [Monad m] [MonadQuotation m] [MonadError m] [MonadRef m] [AddMessageContext m]
    (field_name : Ident) (lean_shape : LeanShape) (proto_type : Ident) (internal_type? : Option InternalType) (enum_type? : Option Name)
    (options : Options) : m (Option Term) := do
  match options.default?, options.defaultBase64? with
  | some _, some _ =>
      throwErrorAt field_name "default and default_base64 options cannot both be set"
  | none, none => return none
  | some v, none =>
      if let some internal_type := internal_type? then
        some <$> optionsValueToTerm field_name lean_shape proto_type internal_type v
      else if enum_type?.isSome then
        match v with
        | `(options_value| $x:ident) =>
            let term := mkIdentFrom proto_type (proto_type.getId.append x.getId)
            return some term
        | _ => throwErrorAt field_name "default option expects an enum value identifier"
      else
        throwErrorAt field_name "default option is only supported for scalar or enum fields"
  | none, some v =>
      if let some internal_type := internal_type? then
        some <$> optionsBase64ValueToTerm field_name internal_type v
      else
        throwErrorAt field_name "default_base64 option is only supported for string or bytes fields"

def computeMData.map [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (_name : Ident)
    (key_proto_type : Ident) (value_proto_type : Ident) (mod? : Modifier)
    (_proto_type : TSyntax `Protobuf.Notation.message_field_type)
    (field_name : Ident)
    (field_proj : Ident)
    (field_num : TSyntax `num)
    (options : Options) : m ProtoFieldMData := do
  if !(mod? matches .default) then
    throwErrorAt field_name "map fields cannot have cardinality modifiers"
  if options.packed?.isEqSome true then
    throwErrorAt field_name "packed option is only valid for repeated scalar or enum fields"
  let key_lean_type ← resolveInternalType key_proto_type
  let value_lean_type ← resolveInternalType value_proto_type
  let (_, key_internal_type?, _, key_oneof_type?) ← getProtoTypeMData mutEnums mutOneofs messages key_proto_type
  if key_oneof_type?.isSome then
    throwErrorAt key_proto_type "map key type cannot be a oneof"
  let some key_internal_type := key_internal_type?
    | throwErrorAt key_proto_type "map key type must be a scalar type"
  if !InternalType.isMapKeyAllowed key_internal_type then
    throwErrorAt key_proto_type "map key type must be an integral type, bool, or string"
  let (value_is_scalar, value_internal_type?, value_enum_type?, value_oneof_type?) ←
    getProtoTypeMData mutEnums mutOneofs messages value_proto_type
  if value_oneof_type?.isSome then
    throwErrorAt value_proto_type "map value type cannot be a oneof"
  let key_builder ← InternalType.builder key_internal_type
  let key_decoder? ← InternalType.decoder? key_internal_type
  let value_builder ←
    if let some value_internal_type := value_internal_type? then
      InternalType.builder value_internal_type
    else
      pure (mkIdentFrom value_proto_type (value_proto_type.getId.str "builder"))
  let value_decoder? ←
    if let some value_internal_type := value_internal_type? then
      InternalType.decoder? value_internal_type
    else
      pure (mkIdentFrom value_proto_type (value_proto_type.getId.str "decoder?"))
  let value_decoder_with_options? :=
    if value_internal_type?.isNone && value_enum_type?.isNone && !value_is_scalar then
      some (mkIdentFrom value_proto_type (value_proto_type.getId.str "decoderWithOptions?"))
    else
      none
  let value_closed_enum := value_enum_type?.isSome && options.closed_enum?.isEqSome true
  let key_default : Term ← match key_internal_type with
    | .bool => `(false)
    | .string => `("")
    | .bytes => `({})
    | _ => `(0)
  let value_default : Term ← match value_internal_type? with
    | some itype =>
      match itype with
      | .bool => `(false)
      | .string => `("")
      | .bytes => `({})
      | _ => `(0)
    | none =>
      if value_enum_type?.isSome || !value_is_scalar then
        pure (mkIdentFrom value_proto_type (value_proto_type.getId.str "Default.Value"))
      else
        throwErrorAt value_proto_type "map value type must be scalar, enum, or message"
  /-
  `Std.HashMap` is not strictly positive when its value belongs to this
  recursive declaration group: the map's internal well-formedness proof keeps
  a reference to the pre-transformation value type.  Use the array-backed
  representation only for that case; ordinary maps retain `Std.HashMap`.
  -/
  let is_recursive := messages.contains value_proto_type.getId
  let map_type := if is_recursive then mkIdent `Protobuf.RecursiveMap else mkIdent `Std.HashMap
  let map_insert := if is_recursive then mkIdent `Protobuf.RecursiveMap.insert else mkIdent `Std.HashMap.insert
  let map_union := if is_recursive then mkIdent `Protobuf.RecursiveMap.union else mkIdent `Std.HashMap.union
  let map_is_empty := if is_recursive then mkIdent `Protobuf.RecursiveMap.isEmpty else mkIdent `Std.HashMap.isEmpty
  let map_info := {
    key_proto_type,
    value_proto_type,
    key_lean_type,
    value_lean_type,
    key_builder,
    value_builder,
    key_decoder?,
    value_decoder?,
    value_decoder_with_options?,
    value_closed_enum,
    key_default,
    value_default,
    insert := map_insert,
    union := map_union
  }
  let lean_type ← `($map_type:ident $key_lean_type $value_lean_type)
  let default_map := (← `({}))
  return {
    mod := .default,
    proto_type := map_type,
    lean_type_inner := map_type,
    lean_type,
    field_name,
    field_proj,
    field_num,
    options,
    lean_shape := .map,
    map_info? := some map_info,
    is_scalar := false,
    internal_type? := none,
    default_lean_value := default_map,
    default_ctor_value := default_map,
    test_unset := map_is_empty,
    enum_type? := none,
    oneof_type? := none,
    builder? := none,
    toMessage? := none,
    decoder?? := none,
    fromMessage? := none,
    fromMessage?? := none,
    decoder_rep_packed? := none,
    decoder_rep? := none,
    : ProtoFieldMData
  }

def computeMData.ordinary.computeShape [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mod? : Modifier) (internal_type? : Option InternalType) (enum_type? : Option Name) (lean_type_inner : Ident) : m (TSyntax `term × LeanShape) := do
  match mod? with
    | .default | .required =>
      if internal_type?.isSome || enum_type?.isSome then
        pure (← `($lean_type_inner), LeanShape.strict)
      else
        pure (← `(Option $lean_type_inner), LeanShape.option)
    | .optional => pure (← `(Option $lean_type_inner), LeanShape.option)
    | .repeated => pure (← `(Array $lean_type_inner), LeanShape.array)

def computeMData.ordinary.computeCtorValue [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (name : Ident) (internal_type? : Option InternalType) (lean_shape : LeanShape) (enum_type? : Option Name) (proto_type : Ident) : m Term := do
  match lean_shape with
    | .strict =>
      if let some itype := internal_type? then
        match itype with
        | .bool => `(false)
        | .string => `("")
        | .bytes => `({})
        | _ => `(0)
      else if enum_type?.isSome then
        pure (mkIdentFrom proto_type (proto_type.getId.str "Default.Value"))
      else throwErrorAt name "{decl_name%}: internal error: strict non-scalar type"
    | .option => `(Option.none) -- oneofs always go here
    | .array => `(#[])
    | .map => unreachable!

def computeMData.ordinary.computeTestUnset [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (name : Ident) (internal_type? : Option InternalType) (lean_shape : LeanShape) (enum_type? : Option Name) (proto_type : Ident) : m Term := do
  match lean_shape with
    | .strict =>
      if let some itype := internal_type? then
        match itype with
        | .bool => `((· == false))
        | .string => `(String.isEmpty)
        | .bytes => `(ByteArray.isEmpty)
        | _ => `((· == 0))
      else if enum_type?.isSome then
        let x := mkIdentFrom proto_type (proto_type.getId.str "Default.Value")
        `((· == $x)) -- TODO: maybe make `Enum.«Default.Value»` a `@[match_pattern]`?
      else throwErrorAt name "{decl_name%}: internal error: strict non-scalar type"
    | .option => `(Option.isNone) -- oneofs always go here
    | .array => `(Array.isEmpty)
    | .map => unreachable!

def computeMData.ordinary [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (name : Ident)
    (mod? : Modifier)
    (proto_type : Ident)
    (field_name : Ident)
    (field_proj : Ident)
    (field_num : TSyntax `num)
    (options : Options) : m ProtoFieldMData := do
  let lean_type_inner ← resolveInternalType proto_type
  let (is_scalar, internal_type?, enum_type?, oneof_type?) ← getProtoTypeMData mutEnums mutOneofs messages proto_type
  if oneof_type?.isSome && !(mod? matches .default) then
    throwErrorAt name "oneof field cannot have cardinality modifier: {oneof_type?.get!}"
  let (lean_type, lean_shape) ← computeMData.ordinary.computeShape mod? internal_type? enum_type? lean_type_inner
  if options.packed?.isEqSome true then
    if mod? != Modifier.repeated then
      throwErrorAt field_name "packed option is only valid for repeated scalar or enum fields"
    if !is_scalar then
      throwErrorAt field_name "packed option is only valid for repeated scalar or enum fields"
  let builder? ← internal_type?.mapM InternalType.builder
  let builder? := if oneof_type?.isNone then some (builder?.getD (mkIdentFrom proto_type (proto_type.getId.str "builder"))) else none
  let toMessage? := if is_scalar then none else some (mkIdentFrom proto_type (proto_type.getId.str "toMessage"))
  let fromMessage? := if is_scalar then none else some (mkIdentFrom proto_type (proto_type.getId.str "fromMessage"))
  let fromMessage?? := if oneof_type?.isSome then some (mkIdentFrom proto_type (proto_type.getId.str "fromMessage?")) else none
  let decoder?? ← internal_type?.mapM InternalType.decoder?
  let decoder?? := if oneof_type?.isNone then some (decoder??.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder?"))) else none
  let decoder_rep_packed? ← match internal_type? with
    | some .string => pure none
    | some .bytes => pure none
    | some itype => some <$> InternalType.decoder_rep_packed itype
    | none => pure none
  let decoder_rep_packed? :=
    if is_scalar then (decoder_rep_packed? <|> some (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep_packed")))
    else none
  let decoder_rep? ← internal_type?.mapM InternalType.decoder_rep
  let decoder_rep? := if oneof_type?.isSome then none else some <| decoder_rep?.getD (mkIdentFrom proto_type (proto_type.getId.str "decoder_rep"))
  let default_override? ← defaultOverride? field_name lean_shape proto_type internal_type? enum_type? options
  if default_override?.isSome && mod? == Modifier.repeated then
    throwErrorAt field_name "default option is not allowed for repeated fields"
  let default_lean_value_base ← match lean_shape with
    | .strict =>
      if internal_type?.isSome then `(Inhabited.default)
      else pure (mkIdentFrom proto_type (proto_type.getId.str "Default.Value"))
    | .option => `(Option.none) -- oneofs always go here
    | .array => `(#[])
    | .map => unreachable!
  let default_ctor_value_base ← computeMData.ordinary.computeCtorValue name internal_type? lean_shape enum_type? proto_type
  let test_unset_base ← computeMData.ordinary.computeTestUnset name internal_type? lean_shape enum_type? proto_type
  let (default_lean_value, default_ctor_value, test_unset) ← do
    match default_override? with
    | some default_term =>
        match lean_shape with
        | .strict =>
          let test_unset_override ← `((· == $default_term))
          pure (default_term, default_term, test_unset_override)
        | .option =>
          pure (default_lean_value_base, default_ctor_value_base, test_unset_base)
        | _ =>
          pure (default_lean_value_base, default_ctor_value_base, test_unset_base)
    | none =>
        pure (default_lean_value_base, default_ctor_value_base, test_unset_base)
  return {
    mod := mod?,
    proto_type,
    lean_type_inner,
    lean_type,
    field_name,
    field_proj,
    field_num,
    options,
    lean_shape,
    map_info? := none,
    default_lean_value,
    default_ctor_value,
    test_unset,
    is_scalar,
    internal_type?,
    enum_type?,
    oneof_type?,
    builder?,
    toMessage?,
    decoder??,
    fromMessage?,
    fromMessage??,
    decoder_rep_packed?,
    decoder_rep?,
    : ProtoFieldMData
  }

def computeMData [Monad m] [MonadQuotation m] [MonadError m] [MonadEnv m] [MonadOptions m] [MonadLog m] [MonadRef m] [AddMessageContext m] [MonadResolveName m]
    (mutEnums mutOneofs messages : NameSet) (name : Ident)
    (mod : Array (Option (TSyntax `Protobuf.Notation.message_entry_modifier)))
    (t' : Array (TSyntax `Protobuf.Notation.message_field_type)) (n : Array Ident) (fidx : Array (TSyntax `num)) (optionsStx : Array (Option (TSyntax `Protobuf.Notation.options))) : m (Array ProtoFieldMData) := do
  let ms ← mod.mapM fun mod? => do
    let some mod := mod? | return Modifier.default
    match mod with
    | `(message_entry_modifier| optional) => return Modifier.optional
    | `(message_entry_modifier| repeated) => return Modifier.repeated
    | `(message_entry_modifier| required) => return Modifier.required
    | _ => unreachable!
  let dots ← n.mapM fun (x : Ident) => return mkIdentFrom x (name.getId.append x.getId)
  let options := optionsStx.map Options.parseD
  let mut out := #[]
  for mod? in ms, proto_type in t', field_name in n, field_proj in dots, field_num in fidx, options in options do
    let r ← match proto_type with
    | `(message_field_type| $s:message_field_type_map) => do
      let `(message_field_type_map| map<$key_proto_type:ident, $value_proto_type:ident>) := s | throwUnsupportedSyntax
      computeMData.map mutEnums mutOneofs messages name key_proto_type value_proto_type mod? proto_type field_name field_proj field_num options
    | `(message_field_type| $proto_type:ident) => do
      computeMData.ordinary mutEnums mutOneofs messages name mod? proto_type field_name field_proj field_num options
    | _ => throwUnsupportedSyntax
    if r.oneof_type?.isNone then
      let fieldNum := field_num.getNat
      if !Encoding.fieldNumberIsAllowedInSchema fieldNum then
        if !Encoding.fieldNumberIsValid fieldNum then
          throwErrorAt field_num "protobuf field number {fieldNum} is outside the valid schema range 1..{Encoding.maxFieldNumber}"
        else
          throwErrorAt field_num "protobuf field number {fieldNum} is reserved for implementation use"
    out := out.push r
  return out

public meta section

public def elabOneofDecCore (mutEnums mutOneofs messages : NameSet) : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(oneofDec| oneof $name { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData mutEnums mutOneofs messages name mod t' n fidx optionsStx
  mdata.forM fun x =>
    match x.mod with
    | .default => pure ()
    | _ => throwErrorAt x.field_name "Fields in oneofs must not have cardinality modifier"
  mdata.forM fun x => do
    if x.map_info?.isSome then
      throwErrorAt x.field_name "map fields cannot appear in oneofs"
  let ts := mdata.map fun x => x.lean_type_inner
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let ind ← `(@[proto_oneof] inductive $name where
    $[| $n:ident : $ts:term → $(ts.map (fun _ => name)):ident]*
    )
  let builder ← mdata.mapM fun m =>
    m.builder?.getDM (throwError "{decl_name%}: builder is absent") -- NOTE: builder is absent when type is a oneof, while nested oneof is forbidden by protobuf
  let decoder? ← mdata.mapM fun m =>
    m.decoder??.getDM (throwError "{decl_name%}: decoder? is absent")
  let encodeOptions := mkIdent `options
  let toMessageAlts ← (mdata.zip builder).mapM fun (x, b) => do
    let value := mkIdent `x
    let protoVal ←
      if x.internal_type?.isNone && x.enum_type?.isNone then
        let toMessageWithOptions := mkIdentFrom x.proto_type (x.proto_type.getId.str "toMessageWithOptions")
        if x.options.wired_as_group?.isEqSome true then
          `(do
            let m ← $toMessageWithOptions:ident $encodeOptions:ident $value:ident
            Encoding.ProtoVal.ofGroup m)
        else
          `(do
            let m ← $toMessageWithOptions:ident $encodeOptions:ident $value:ident
            Encoding.ProtoVal.ofMessage m)
      else
        `($b:ident $value:ident)
    `(Parser.Term.matchAltExpr|
      | $(x.field_proj) $value:ident =>
          (fun v => Protobuf.Encoding.Message.mk #[Protobuf.Encoding.Record.mk $(x.field_num):num v]) <$> $protoVal:term)
  let toMessageWithOptionsId := push_name "toMessageWithOptions"
  let toMessageWithOptions ← `(partial def $toMessageWithOptionsId:ident : Protobuf.Encoding.EncodeOptions → $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun $encodeOptions val =>
    match val with
    $toMessageAlts:matchAlt*
    )
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message :=
    $toMessageWithOptionsId:ident Protobuf.Encoding.EncodeOptions.default)
  let msg ← mkIdent <$> mkFreshUserName `msg
  let recVar := mkIdent `r
  let recMsg := mkIdent `recordMsg
  let state := mkIdent `st
  let state' := mkIdent `st'
  let options := mkIdent `options
  let depth := mkIdent `depth
  let ds ← mdata.zip decoder? |>.mapM fun (x, d) => do
    let knownCheck? :=
      if x.enum_type?.isSome && x.options.closed_enum?.isEqSome true then
        some (mkIdentFrom x.proto_type (x.proto_type.getId.str "isKnown"))
      else
        none
    let decode ←
      if x.internal_type?.isSome || x.enum_type?.isSome then
        match knownCheck? with
        | some isKnown =>
            `(do
              let Option.some v ← ($d:ident $recMsg:ident $(x.field_num):num) | throw (Protobuf.Encoding.ProtoError.userError "")
              if !$isKnown:ident v then
                throw (Protobuf.Encoding.ProtoError.invalidWireType "closed enum value is unknown")
              pure (Option.some ($(x.field_proj) v)))
        | none =>
            `(do
              let Option.some v ← ($d:ident $recMsg:ident $(x.field_num):num) | throw (Protobuf.Encoding.ProtoError.userError "")
              pure (Option.some ($(x.field_proj) v)))
      else
        let merger := mkIdentFrom x.proto_type (x.proto_type.getId.append `merge)
        let decoderWithOptions? := mkIdentFrom x.proto_type (x.proto_type.getId.str "decoderWithOptions?")
        let val := mkIdent `val
        let merged := mkIdent `merged
        `(do
          let Option.some $val:ident ← ($decoderWithOptions?:ident $options:ident $depth:ident $recMsg:ident $(x.field_num):num) | throw (Protobuf.Encoding.ProtoError.userError "")
          let $merged:ident := match $state:ident with
            | Option.some ($(x.field_proj) old) => Option.some ($(x.field_proj) ($merger old $val:ident))
            | _ => Option.some ($(x.field_proj) $val:ident)
          pure $merged:ident)
    pure (x.field_num.getNat, decode)
  let rec mkDispatch (cases : List (Nat × Term)) : CommandElabM Term := do
    match cases with
    | [] => `(pure $state:ident)
    | (fieldNum, body) :: rest =>
      let restTerm ← mkDispatch rest
      `(if ($recVar:ident).fieldNum == $(quote fieldNum) then
          $body:term
        else
          $restTerm:term)
  let dispatch ← mkDispatch ds.toList
  let validateRecordId := push_name "validateRecord"
  let record := mkIdent `record
  let validateRecMsg := mkIdent `recordMsg
  let dsValidate ← mdata.zip decoder? |>.mapM fun (x, d) => do
    let knownCheck? :=
      if x.enum_type?.isSome && x.options.closed_enum?.isEqSome true then
        some (mkIdentFrom x.proto_type (x.proto_type.getId.str "isKnown"))
      else
        none
    let body ←
      if x.internal_type?.isSome || x.enum_type?.isSome then
        match knownCheck? with
        | some isKnown =>
            `(do
              let value? ← ($d:ident $validateRecMsg:ident $(x.field_num):num)
              match value? with
              | some value =>
                  if !$isKnown:ident value then
                    throw (Protobuf.Encoding.ProtoError.invalidWireType "closed enum value is unknown")
                  pure true
              | none => pure true)
        | none =>
            `(do
              let _ ← ($d:ident $validateRecMsg:ident $(x.field_num):num)
              pure true)
      else
        let decoderWithOptions? := mkIdentFrom x.proto_type (x.proto_type.getId.str "decoderWithOptions?")
        `(do
          let _ ← ($decoderWithOptions?:ident $options:ident $depth:ident $validateRecMsg:ident $(x.field_num):num)
          pure true)
    pure (x.field_num.getNat, body)
  let rec mkValidateDispatch (cases : List (Nat × Term)) : CommandElabM Term := do
    match cases with
    | [] => `(pure false)
    | (fieldNum, body) :: rest =>
      let restTerm ← mkValidateDispatch rest
      `(if ($record:ident).fieldNum == $(quote fieldNum) then
          $body:term
        else
          $restTerm:term)
  let validateDispatch ← mkValidateDispatch dsValidate.toList
  let validateRecordWithOptionsId := push_name "validateRecordWithOptions"
  let validateRecordWithOptions ← `(partial def $validateRecordWithOptionsId:ident : Protobuf.Encoding.DecodeOptions → Nat → Protobuf.Encoding.Record → Except Protobuf.Encoding.ProtoError Bool := fun $options $depth $record => do
    let $validateRecMsg:ident := Protobuf.Encoding.Message.mk #[$record:ident]
    $validateDispatch:term)
  let validateRecord ← `(partial def $validateRecordId:ident : Protobuf.Encoding.Record → Except Protobuf.Encoding.ProtoError Bool :=
    $validateRecordWithOptionsId:ident Protobuf.Encoding.DecodeOptions.default 0)
  let fromMessageWithOptions?Id := push_name "fromMessageWithOptions?"
  let fromMessageWithOptions? ← `(
    partial def $fromMessageWithOptions?Id:ident : Protobuf.Encoding.DecodeOptions → Nat → Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError (Option $name) := fun $options $depth $msg => do
      ($msg).records.foldlM (init := (Option.none : Option $name)) (fun $state:ident $recVar:ident => do
        let $recMsg:ident := Protobuf.Encoding.Message.mk #[$recVar:ident]
        let $state':ident ←
          match (show Except Protobuf.Encoding.ProtoError (Option $name) from $dispatch:term) with
          | .ok decoded => pure decoded
          | .error (.invalidWireType _) => pure $state:ident
          | .error err => throw err
        pure $state':ident))
  let fromMessage?Id := push_name "fromMessage?"
  let fromMessage? ← `(
    /--
    Decode a standalone oneof payload using protobuf's wire-level "last one wins" rule.

    Parsing must respect wire order. When a later record belongs to a different member, it clears the
    previous case; when it belongs to the same message-valued member, it merges into the value already
    accumulated for that case.
    -/
    partial def $fromMessage?Id:ident : Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError (Option $name) :=
      $fromMessageWithOptions?Id:ident Protobuf.Encoding.DecodeOptions.default 0)
  let mergeId := push_name "merge"
  let old := mkIdent `old
  let new := mkIdent `new
  let mergeAlts ← mdata.mapM fun x => do
    if x.internal_type?.isNone && x.enum_type?.isNone then
      let merger := mkIdentFrom x.proto_type (x.proto_type.getId.append `merge)
      `(Parser.Term.matchAltExpr|
        | Option.some ($(x.field_proj) $old:ident), Option.some ($(x.field_proj) $new:ident) =>
            Option.some ($(x.field_proj) ($merger:ident $old:ident $new:ident)))
    else
      `(Parser.Term.matchAltExpr|
        | Option.some ($(x.field_proj) _), Option.some ($(x.field_proj) $new:ident) =>
            Option.some ($(x.field_proj) $new:ident))
  let merge ← `(
    /--
    Merge oneof state. A present right-hand case replaces a different left-hand case; if both sides
    hold the same message-valued case, protobuf merge semantics merge the nested messages.
    -/
    partial def $mergeId:ident : Option $name → Option $name → Option $name
      $mergeAlts:matchAlt*
      | old, Option.none => old
      | _, Option.some new => Option.some new)
  return { decls := #[ind], functions := #[toMessageWithOptions, toMessage, validateRecordWithOptions, validateRecord, fromMessageWithOptions?, fromMessage?, merge] }

@[scoped command_elab oneofDec]
public def elabOneofDec : CommandElab := fun stx => do
  let r ← elabOneofDecCore {} {} {} stx
  r.elaborate

end

private def construct_toMessage (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) :
    CommandElabM (Ident × Command × Ident × Command) := do
  let options ← mkIdent <$> mkFreshUserName `options
  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let toMessageBody ← fields.mapM fun {mod, proto_type, field_proj, field_num, options := fieldOptions, internal_type?, builder?, enum_type?, oneof_type?, toMessage?, test_unset, map_info?, ..} => do
    if let some map_info := map_info? then
      let entries ← mkIdent <$> mkFreshUserName `entries
      let rawEntries ← mkIdent <$> mkFreshUserName `rawEntries
      let submsg ← mkIdent <$> mkFreshUserName `submsg
      let entry_key := mkIdent `entry_key
      let entry_val := mkIdent `entry_val
      let key_builder := map_info.key_builder
      let value_builder := map_info.value_builder
      let rawEntriesList ← mkIdent <$> mkFreshUserName `rawEntriesList
      let value_to_proto_val ←
        if map_info.value_decoder_with_options?.isSome then
          let toMessageWithOptions := mkIdentFrom map_info.value_proto_type (map_info.value_proto_type.getId.str "toMessageWithOptions")
          `(do
            let m ← $toMessageWithOptions:ident $options:ident $entry_val:ident
            Encoding.ProtoVal.ofMessage m)
        else
          `($value_builder:ident $entry_val:ident)
      `(Parser.Term.doSeqItem|
        let $msg:ident ← do
          if $test_unset ($field_proj $val) then
            pure $msg
          else
            let $rawEntries:ident := ($field_proj $val).toArray
            let $rawEntriesList:ident := Array.toList $rawEntries:ident
            let $rawEntries:ident :=
              if Protobuf.Encoding.EncodeOptions.deterministic ($options:ident) then
                (List.mergeSort $rawEntriesList:ident (fun a b => compare a.1 b.1 == Ordering.lt)).toArray
              else
                $rawEntries:ident
            let stableEntries := $rawEntries:ident
            let $entries:ident ← stableEntries.mapM (fun ($entry_key:ident, $entry_val:ident) => do
              let $submsg:ident := Protobuf.Encoding.Message.emptyWithCapacity 2
              let $submsg:ident ← (1 : Nat) <~ ($key_builder $entry_key) # $submsg
              let $submsg:ident ← (2 : Nat) <~ $value_to_proto_val:term # $submsg
              Encoding.ProtoVal.ofMessage $submsg
              )
            $field_num:num <~f (pure $entries) # $msg
        )
    else if oneof_type?.isSome then
      assert! toMessage?.isSome
      let toMessageWithOptions := mkIdentFrom proto_type (proto_type.getId.str "toMessageWithOptions")
      `(Parser.Term.doSeqItem|
        let $msg:ident ← (do
          let sub? ← (Option.mapM ($toMessageWithOptions:ident $options:ident) ($field_proj $val))
          let combined := Option.getD (Option.map (fun sub => Protobuf.Encoding.Message.combine $msg sub) sub?) $msg
          pure combined)
      )
    else
      assert! builder?.isSome
      let builder := builder?.get!
      let value_to_proto_val ←
        if internal_type?.isNone && enum_type?.isNone then
          let toMessageWithOptions := mkIdentFrom proto_type (proto_type.getId.str "toMessageWithOptions")
          let fieldValue := mkIdent `fieldValue
          if fieldOptions.wired_as_group?.isEqSome true then
            `(fun $fieldValue:ident => do
              let m ← $toMessageWithOptions:ident $options:ident $fieldValue:ident
              Encoding.ProtoVal.ofGroup m)
          else
            `(fun $fieldValue:ident => do
              let m ← $toMessageWithOptions:ident $options:ident $fieldValue:ident
              Encoding.ProtoVal.ofMessage m)
        else
          `($builder:ident)
      match mod with
      | .default =>
        if internal_type?.isSome || enum_type?.isSome then
          `(Parser.Term.doSeqItem| let $msg ← do
            if $test_unset ($field_proj $val) then
              pure $msg
            else
              $field_num:num <~ ($value_to_proto_val:term ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $value_to_proto_val:term ($field_proj $val)) # $msg)
      | .required =>
        if internal_type?.isSome || enum_type?.isSome then
          `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~ ($value_to_proto_val:term ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if let Option.some v := ($field_proj $val) then
                $field_num:num <~ ($value_to_proto_val:term v) # $msg
              else
                throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote field_proj.getId.toString)}` is missing when building the message")
              )
      | .optional =>
        `(Parser.Term.doSeqItem| let $msg ← $field_num:num <~? (Option.mapM $value_to_proto_val:term ($field_proj $val)) # $msg)
      | .repeated =>
        if fieldOptions.packed?.isEqSome true then
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if $test_unset ($field_proj $val) then
                pure $msg
              else
                $field_num:num <~p (Array.mapM $value_to_proto_val:term ($field_proj $val)) # $msg)
        else
          `(Parser.Term.doSeqItem|
            let $msg ← do
              if $test_unset ($field_proj $val) then
                pure $msg
              else
                $field_num:num <~f (Array.mapM $value_to_proto_val:term ($field_proj $val)) # $msg)
  let toMessageWithOptionsId := push_name "toMessageWithOptions"
  let toMessageWithOptions ← `(partial def $toMessageWithOptionsId:ident : Protobuf.Encoding.EncodeOptions → $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message := fun $options $val => do
    let $msg:ident := Protobuf.Encoding.Message.emptyWithCapacity $(quote fields.size)
    $toMessageBody*
    let $msg := Protobuf.Encoding.Message.wire_mapWithOptions $options $msg ($(push_name "Unknown.Fields") $val)
    Protobuf.Encoding.Message.validate $msg
    return $msg
    )
  let toMessageId := push_name "toMessage"
  let toMessage ← `(partial def $toMessageId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Message :=
    $toMessageWithOptionsId:ident Protobuf.Encoding.EncodeOptions.default)
  return (toMessageId, toMessage, toMessageWithOptionsId, toMessageWithOptions)

private def construct_builder (name : Ident) (push_name : String → Ident) (toMessage : Ident) : CommandElabM (Ident × Command) := do
  let val ← mkIdent <$> mkFreshUserName `val
  let builderId := push_name "builder"
  let builder ← `(partial def $builderId:ident : $name → Except Protobuf.Encoding.ProtoError Protobuf.Encoding.ProtoVal := fun $val => do
    let m ← $toMessage:ident $val
    Encoding.ProtoVal.ofMessage m
    )
  return (builderId, builder)

private def construct_fromMessage (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) :
    CommandElabM (Ident × Command × Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let options := mkIdent `options
  let depth := mkIdent `depth
  let recVar := mkIdent `r
  let recMsg := mkIdent `recordMsg
  let acc := mkIdent `acc
  let state := mkIdent `st
  let seen := mkIdent `seen
  let state' := mkIdent `st'
  let seen' := mkIdent `seen'
  let unknownField := mkIdent `«Unknown.Fields»
  let unknownProj := mkIdentFrom name (name.getId.append unknownField.getId)
  let oneofFields := fields.filter (fun x => x.oneof_type?.isSome)
  let regularFields := fields.filter (fun x => x.oneof_type?.isNone)
  let requiredStrictFields := regularFields.filter (fun x =>
    x.mod == .required && (x.internal_type?.isSome || x.enum_type?.isSome))
  let requiredMessageFields := regularFields.filter (fun x =>
    x.mod == .required && !(x.internal_type?.isSome || x.enum_type?.isSome))
  let requiredStrictMeta := requiredStrictFields.zipIdx.map fun (x, i) => (x.field_name.getId, i)
  /-
  We decode the message in a single left-to-right pass over wire records.

  `state` stores the partially decoded Lean value; `seen` tracks only required strict fields
  (scalar / enum fields represented directly in the structure) because their default Lean values are
  indistinguishable from "not present". Required submessages keep presence in `Option`, so they can
  be checked after the fold without an auxiliary bitmap.
  -/
  let stateTy ← `(($name × Array Bool))
  let mkStatePair : Term → Term → CommandElabM Term := fun st sn => do
    `((($st, $sn) : $stateTy))
  let mkSeenUpdate : ProtoFieldMData → CommandElabM Term := fun x => do
    match requiredStrictMeta.findSome? (fun (fieldName, i) =>
      if fieldName == x.field_name.getId then some i else none) with
    | some i => `(($seen).set! $(quote i) true)
    | none => `($seen)
  let branchCases ← regularFields.mapM (β := Nat × Term) fun x => do
    let seenUpdate ← mkSeenUpdate x
    if let some map_info := x.map_info? then
      let key_decoder? := map_info.key_decoder?
      let value_decoder? := map_info.value_decoder?
      let value_decoder_with_options? := map_info.value_decoder_with_options?
      let key_default := map_info.key_default
      let value_default := map_info.value_default
      let value_merge := mkIdentFrom map_info.value_proto_type (map_info.value_proto_type.getId.append `merge)
      let map_insert := map_info.insert
      let entry := mkIdent `entry
      let map := mkIdent `map
      let field_num_stx := x.field_num
      let field := x.field_name
      let body ← match value_decoder_with_options? with
        | some d =>
            `(do
              let entries ← Encoding.Message.getExpandedMessageWithOptions $options:ident ($depth:ident + 1) $recMsg:ident $field_num_stx:num
              let $map:ident ← entries.foldlM (init := $(x.field_proj) $state:ident) (fun $map:ident $entry:ident => do
                let key? ← Encoding.Message.getLastValidWith? $entry 1 $key_decoder?:ident
                let value? ← Encoding.Message.getMergedValidWith? $entry 2
                  (fun msg fieldNum => $d:ident $options:ident ($depth:ident + 1) msg fieldNum)
                  $value_merge:ident
                let key := Option.getD key? $key_default
                let value := Option.getD value? $value_default
                pure ($map_insert:ident $map key value))
              let $state':ident : $name := { $state:ident with $field:ident := $map:ident }
              let $seen':ident := $seenUpdate:term
              pure (($state':ident, $seen':ident) : $stateTy))
        | none =>
            if map_info.value_closed_enum then
              let isKnown := mkIdentFrom map_info.value_proto_type (map_info.value_proto_type.getId.str "isKnown")
              let mapState := mkIdent `mapState
              let mapAcc := mkIdent `mapAcc
              let unknownEntries := mkIdent `unknownEntries
              let unknownFields := mkIdent `unknownFields
              `(do
                let entries ← Encoding.Message.getExpandedMessageWithOptions $options:ident ($depth:ident + 1) $recMsg:ident $field_num_stx:num
                let $mapState:ident ← entries.foldlM
                  (init := ($(x.field_proj) $state:ident, (#[] : Array Protobuf.Encoding.ProtoVal)))
                  (fun $mapAcc:ident $entry:ident => do
                    let key? ← Encoding.Message.getLastValidWith? $entry 1 $key_decoder?:ident
                    let value? ← Encoding.Message.getLastValidWith? $entry 2 $value_decoder?:ident
                    let key := Option.getD key? $key_default
                    match value? with
                    | Option.some value =>
                        if $isKnown:ident value then
                          pure ($map_insert:ident ($mapAcc:ident).1 key value, ($mapAcc:ident).2)
                        else
                          pure (($mapAcc:ident).1, (($mapAcc:ident).2).push $(recVar).value)
                    | Option.none =>
                        let value := $value_default
                        pure ($map_insert:ident ($mapAcc:ident).1 key value, ($mapAcc:ident).2))
                let $map:ident := ($mapState:ident).1
                let $unknownEntries:ident := ($mapState:ident).2
                let $unknownFields:ident :=
                  if Array.isEmpty $unknownEntries:ident then
                    $unknownProj:ident $state:ident
                  else
                    ($unknownProj:ident $state:ident).alter $field_num_stx:num (fun
                      | Option.none => Option.some $unknownEntries:ident
                      | Option.some vals => Option.some (vals ++ $unknownEntries:ident))
                let $state':ident : $name := {
                  $state:ident with
                  $field:ident := $map:ident,
                  $unknownField:ident := $unknownFields:ident
                }
                let $seen':ident := $seenUpdate:term
                pure (($state':ident, $seen':ident) : $stateTy))
            else
              `(do
                let entries ← Encoding.Message.getExpandedMessageWithOptions $options:ident ($depth:ident + 1) $recMsg:ident $field_num_stx:num
                let $map:ident ← entries.foldlM (init := $(x.field_proj) $state:ident) (fun $map:ident $entry:ident => do
                  let key? ← Encoding.Message.getLastValidWith? $entry 1 $key_decoder?:ident
                  let value? ← Encoding.Message.getLastValidWith? $entry 2 $value_decoder?:ident
                  let key := Option.getD key? $key_default
                  let value := Option.getD value? $value_default
                  pure ($map_insert:ident $map key value))
                let $state':ident : $name := { $state:ident with $field:ident := $map:ident }
                let $seen':ident := $seenUpdate:term
                pure (($state':ident, $seen':ident) : $stateTy))
      pure (x.field_num.getNat, body)
    else
      match x.mod with
      | .repeated =>
        let field_num_stx := x.field_num
        let field := x.field_name
        /-
        Repeated scalar parsers must accept both packed and unpacked wire records. The internal
        `packed` option controls how we *serialize* this field, but decoding stays liberal so that a
        field can round-trip data produced by older/newer schemas and other protobuf implementations.
        -/
        let decoder_rep := x.decoder_rep?.get!
        let decoder_rep_with_options := mkIdentFrom x.proto_type (x.proto_type.getId.str "decoderRepWithOptions")
        let xs := mkIdent `xs
        let body ←
          if x.internal_type?.isNone && x.enum_type?.isNone then
            `(do
              let $xs:ident ← $decoder_rep_with_options:ident $options:ident $depth:ident $recMsg:ident $field_num_stx:num
              let $state':ident : $name := { $state:ident with $field:ident := $(x.field_proj) $state:ident ++ $xs:ident }
              let $seen':ident := $seenUpdate:term
              pure (($state':ident, $seen':ident) : $stateTy))
          else
            let isKnown? :=
              if x.enum_type?.isSome && x.options.closed_enum?.isEqSome true then
                some (mkIdentFrom x.proto_type (x.proto_type.getId.str "isKnown"))
              else
                none
            match isKnown? with
            | some isKnown =>
                let builder := x.builder?.get!
                let knownValues := mkIdent `knownValues
                let unknownValues := mkIdent `unknownValues
                let unknownProtoVals := mkIdent `unknownProtoVals
                let unknownFields := mkIdent `unknownFields
                `(do
                  let $xs:ident ← $decoder_rep:ident $recMsg:ident $field_num_stx:num
                  let $knownValues:ident := Array.filter (fun value => $isKnown:ident value) $xs:ident
                  let $unknownValues:ident := Array.filter (fun value => !$isKnown:ident value) $xs:ident
                  let $unknownProtoVals:ident ← Array.mapM $builder:ident $unknownValues:ident
                  let $unknownFields:ident :=
                    if Array.isEmpty $unknownProtoVals:ident then
                      $unknownProj:ident $state:ident
                    else
                      ($unknownProj:ident $state:ident).alter $field_num_stx:num (fun
                        | Option.none => Option.some $unknownProtoVals:ident
                        | Option.some vals => Option.some (vals ++ $unknownProtoVals:ident))
                  let $state':ident : $name := {
                    $state:ident with
                    $field:ident := $(x.field_proj) $state:ident ++ $knownValues:ident,
                    $unknownField:ident := $unknownFields:ident
                  }
                  let $seen':ident := $seenUpdate:term
                  pure (($state':ident, $seen':ident) : $stateTy))
            | none =>
                `(do
                  let $xs:ident ← $decoder_rep:ident $recMsg:ident $field_num_stx:num
                  let $state':ident : $name := { $state:ident with $field:ident := $(x.field_proj) $state:ident ++ $xs:ident }
                  let $seen':ident := $seenUpdate:term
                  pure (($state':ident, $seen':ident) : $stateTy))
        pure (x.field_num.getNat, body)
      | .default | .required | .optional =>
        if x.internal_type?.isSome || x.enum_type?.isSome then
          let field_num_stx := x.field_num
          let field := x.field_name
          let decoder? := x.decoder??.get!
          let isKnown? :=
            if x.enum_type?.isSome && x.options.closed_enum?.isEqSome true then
              some (mkIdentFrom x.proto_type (x.proto_type.getId.str "isKnown"))
            else
              none
          let value? := mkIdent `value?
          let value := mkIdent `value
          match x.mod with
          | .optional =>
            let pureSeenUnchanged ← mkStatePair state' seen
            let body ← match isKnown? with
              | some isKnown =>
                  `(do
                    let $value?:ident ← $decoder?:ident $recMsg:ident $field_num_stx:num
                    match $value?:ident with
                    | some $value:ident =>
                        if !$isKnown:ident $value:ident then
                          throw (Protobuf.Encoding.ProtoError.invalidWireType "closed enum value is unknown")
                    | none => pure ()
                    let $state':ident : $name := { $state:ident with $field:ident := $value?:ident }
                    pure $pureSeenUnchanged:term)
              | none =>
                  `(do
                    let $value?:ident ← $decoder?:ident $recMsg:ident $field_num_stx:num
                    let $state':ident : $name := { $state:ident with $field:ident := $value?:ident }
                    pure $pureSeenUnchanged:term)
            pure (x.field_num.getNat, body)
          | .default | .required =>
            let pureState ← mkStatePair state seen
            let pureSeenUpdated ← mkStatePair state' seen'
            let body ← match isKnown? with
              | some isKnown =>
                  `(do
                    let $value?:ident ← $decoder?:ident $recMsg:ident $field_num_stx:num
                    match $value?:ident with
                    | Option.some $value:ident =>
                        if !$isKnown:ident $value:ident then
                          throw (Protobuf.Encoding.ProtoError.invalidWireType "closed enum value is unknown")
                        let $state':ident : $name := { $state:ident with $field:ident := $value:ident }
                        let $seen':ident := $seenUpdate:term
                        pure $pureSeenUpdated:term
                    | Option.none =>
                        pure $pureState:term)
              | none =>
                  `(do
                    let $value?:ident ← $decoder?:ident $recMsg:ident $field_num_stx:num
                    match $value?:ident with
                    | Option.some $value:ident =>
                        let $state':ident : $name := { $state:ident with $field:ident := $value:ident }
                        let $seen':ident := $seenUpdate:term
                        pure $pureSeenUpdated:term
                    | Option.none =>
                        pure $pureState:term)
            pure (x.field_num.getNat, body)
          | .repeated => unreachable!
        else
          let field_num_stx := x.field_num
          let field := x.field_name
          let fieldProj : Term := x.field_proj
          let decoderWithOptions? := mkIdentFrom x.proto_type (x.proto_type.getId.str "decoderWithOptions?")
          let merger := mkIdentFrom x.proto_type (x.proto_type.getId.append `merge)
          let value := mkIdent `value
          let merged := mkIdent `merged
          let pureSeenUpdated ← mkStatePair state' seen'
          let body ← `(do
            let $value:ident ← $decoderWithOptions?:ident $options:ident $depth:ident $recMsg:ident $field_num_stx:num
            let $merged:ident := match $fieldProj:term $state:ident, $value:ident with
              | Option.some old, Option.some new => Option.some ($merger old new)
              | Option.none, Option.some new => Option.some new
              | Option.some old, Option.none => Option.some old
              | Option.none, Option.none => Option.none
            let $state':ident : $name := { $state:ident with $field:ident := $merged:ident }
            let $seen':ident := $seenUpdate:term
            pure $pureSeenUpdated:term)
          pure (x.field_num.getNat, body)
  let stateInit ← `(Parser.Term.doSeqItem| let $state:ident : $name := default)
  let seenInit ← `(Parser.Term.doSeqItem| let $seen:ident : Array Bool := Array.replicate $(quote requiredStrictFields.size) false)
  let foldAcc := mkIdent `acc
  let unknownPair ← mkStatePair state' seen
  let unknownBody ← `(do
    let $state':ident : $name := {
      $state:ident with
      $unknownField:ident := ($unknownProj:ident $state:ident).alter $(recVar).fieldNum (fun
        | Option.none => Option.some #[$(recVar).value]
        | Option.some vals => Option.some (vals.push $(recVar).value))
    }
    pure $unknownPair:term)
  let oneofDeferredPair ← mkStatePair state seen
  let rec mkOneofDispatch (fields : List ProtoFieldMData) : CommandElabM Term := do
    match fields with
    | [] => pure unknownBody
    | x :: rest =>
      let restTerm ← mkOneofDispatch rest
      let validateRecord := mkIdentFrom x.proto_type (x.proto_type.getId.str "validateRecordWithOptions")
      `(match ($validateRecord:ident $options:ident $depth:ident $(recVar)) with
        | .ok true => pure $oneofDeferredPair:term
        | .ok false => $restTerm:term
        | .error (.invalidWireType _) => $unknownBody:term
        | .error err => throw err)
  let oneofDispatchBody ← mkOneofDispatch oneofFields.toList
  let rec mkDispatch (cases : List (Nat × Term)) : CommandElabM Term := do
    match cases with
    | [] => pure oneofDispatchBody
    | (fieldNum, body) :: rest =>
      let restTerm ← mkDispatch rest
      `(if $(recVar).fieldNum == $(quote fieldNum) then
          match (show Except Protobuf.Encoding.ProtoError $stateTy:term from $body:term) with
          | .ok decoded => pure decoded
          | .error (.invalidWireType _) => $unknownBody:term
          | .error err => throw err
        else
          $restTerm:term)
  let dispatchBody ← mkDispatch branchCases.toList
  let foldExpr ← `((Protobuf.Encoding.Message.records $msg).foldlM
      (init := ((($state:ident, $seen:ident) : $stateTy)))
      (fun ($acc:ident : $stateTy) $recVar:ident => do
        let $state:ident := ($acc:ident).1
        let $seen:ident := ($acc:ident).2
        let $recMsg:ident := Protobuf.Encoding.Message.mk #[$recVar:ident]
        $dispatchBody:term))
  let foldBody ← `(Parser.Term.doSeqItem| let $foldAcc:ident : $stateTy ← $foldExpr:term)
  let stateAfterFold := mkIdent `st
  let seenAfterFold := mkIdent `seen
  let foldStateBind ← `(Parser.Term.doSeqItem| let $stateAfterFold:ident : $name := ($foldAcc:ident).1)
  let foldSeenBind ← `(Parser.Term.doSeqItem| let $seenAfterFold:ident : Array Bool := ($foldAcc:ident).2)
  let requiredChecks ← requiredStrictFields.zipIdx.mapM (β := TSyntax ``Parser.Term.doSeqItem) fun (x, i) => do
    let err ← `(throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote x.field_proj.getId.toString)}` is missing when decoding the message"))
    `(Parser.Term.doSeqItem|
      if !$seenAfterFold:ident[$(quote i)]! then
        $err:term
      else
        pure ()
      )
  let requiredMessageChecks ← requiredMessageFields.mapM (β := TSyntax ``Parser.Term.doSeqItem) fun x => do
    let err ← `(throw (Protobuf.Encoding.ProtoError.missingRequiredField s!"required field `{$(quote x.field_proj.getId.toString)}` is missing when decoding the message"))
    `(Parser.Term.doSeqItem|
      if ($(x.field_proj) $stateAfterFold:ident).isNone then
        $err:term
      else
        pure ()
      )
  let oneofStatePairs ← oneofFields.foldlM
    (init := (#[], stateAfterFold))
    (fun (accState : Array (TSyntax ``Parser.Term.doSeqItem) × Ident) x => do
      let (items, currentState) := accState
      let field := x.field_name
      let fromMessage? := mkIdentFrom x.proto_type (x.proto_type.getId.str "fromMessageWithOptions?")
      let oneofVal ← mkIdent <$> mkFreshUserName (x.field_name.getId)
      let nextState ← mkIdent <$> mkFreshUserName `st
      let item1 ← `(Parser.Term.doSeqItem| let $oneofVal:ident ← $fromMessage?:ident $options:ident $depth:ident $msg)
      let item2 ← `(Parser.Term.doSeqItem| let $nextState:ident : $name := { $currentState:ident with $field:ident := $oneofVal:ident })
      pure (items.push item1 |>.push item2, nextState))
  let oneofDecodes := oneofStatePairs.1
  let finalState := oneofStatePairs.2
  let ret ← `(Parser.Term.doSeqItem| pure $finalState:ident)
  let fromMessageWithOptionsId := push_name "fromMessageWithOptions"
  let fromMessageWithOptions ← `(partial def $fromMessageWithOptionsId:ident : Protobuf.Encoding.DecodeOptions → Nat → Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError $name := fun $options $depth $msg => do
    $stateInit
    $seenInit
    $foldBody
    $foldStateBind
    $foldSeenBind
    $requiredChecks*
    $requiredMessageChecks*
    $oneofDecodes*
    $ret
    )
  let fromMessageId := push_name "fromMessage"
  let fromMessage ← `(partial def $fromMessageId:ident : Protobuf.Encoding.Message → Except Protobuf.Encoding.ProtoError $name :=
    $fromMessageWithOptionsId:ident Protobuf.Encoding.DecodeOptions.default 0)
  return (fromMessageId, fromMessage, fromMessageWithOptionsId, fromMessageWithOptions)

private def construct_decoder_rep (name : Ident) (push_name : String → Ident) (fromMessage fromMessageWithOptions : Ident) :
    CommandElabM (Ident × Command × Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let options := mkIdent `options
  let depth := mkIdent `depth
  let decoderRepWithOptionsId := push_name "decoderRepWithOptions"
  let decoderRepWithOptions ← `(partial def $decoderRepWithOptionsId:ident : Protobuf.Encoding.DecodeOptions → Nat → Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $options $depth $msg field_num => do
    let xs ← Encoding.Message.getExpandedMessageWithOptions $options ($depth + 1) $msg field_num
    xs.mapM ($fromMessageWithOptions:ident $options ($depth + 1))
    )
  let decoderRepId := push_name "decoder_rep"
  let decoderRep ← `(partial def $decoderRepId:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Array $name) := fun $msg field_num => do
    let xs ← Encoding.Message.getExpandedMessage $msg field_num
    xs.mapM $fromMessage:ident
    )
  return (decoderRepId, decoderRep, decoderRepWithOptionsId, decoderRepWithOptions)

private def construct_merge (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let a ← mkIdent <$> mkFreshUserName `a
  let b ← mkIdent <$> mkFreshUserName `b
  let mergeBody ← fields.mapM (β := (Ident × TSyntax ``Parser.Term.doSeqItem)) fun {mod, proto_type, field_name, field_proj, internal_type?, enum_type?, oneof_type?, map_info?, test_unset, ..} => do
    let var ← mkIdent <$> mkFreshUserName (field_name.getId)
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let merger := mkIdentFrom proto_type (proto_type.getId.append `merge)
    if let some map_info := map_info? then
      let map_union := map_info.union
      let stx ← `(Parser.Term.doSeqItem| let $var := $map_union:ident $va $vb)
      return (var, stx)
    else if oneof_type?.isSome then
      let stx ← `(Parser.Term.doSeqItem| let $var := $merger:ident $va $vb)
      return (var, stx)
    else
      let stx ← match mod with
        | .default =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := if $test_unset $vb then $va else $vb)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .required =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := $vb)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .optional =>
          if internal_type?.isSome || enum_type?.isSome then
            `(Parser.Term.doSeqItem| let $var := $vb <|> $va)
          else
            `(Parser.Term.doSeqItem| let $var := match $va:term, $vb:term with
              | Option.some x, Option.some y => Option.some ($merger x y)
              | Option.some x, _ => Option.some x
              | _, Option.some y => Option.some y
              | _, _ => Option.none)
        | .repeated => `(Parser.Term.doSeqItem| let $var := $va ++ $vb) -- concatenate
      return (var, stx)
  let u := mkIdent `«Unknown.Fields»
  let mergeBody := mergeBody.push (← do
    let field_proj := push_name "Unknown.Fields"
    let va ← `($field_proj $a)
    let vb ← `($field_proj $b)
    let s ← `(Parser.Term.doSeqItem| let $u:ident := Protobuf.Encoding.merge_map $va $vb)
    pure (u, s))
  let ps := fields.map ProtoFieldMData.field_name |>.push u
  let (vs, mergeBody) := mergeBody.unzip
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let ret ← `(Parser.Term.doSeqItem| return $structInst)
  let mergeId := push_name "merge"
  let merge ← `(partial def $mergeId:ident : $name → $name → $name := fun $a $b => Id.run do
    $mergeBody*
    $ret
    )
  return (mergeId, merge)

private def construct_decoder? (name : Ident) (push_name : String → Ident) (fromMessageWithOptions merge : Ident) :
    CommandElabM (Ident × Command × Ident × Command) := do
  let msg ← mkIdent <$> mkFreshUserName `msg
  let options := mkIdent `options
  let depth := mkIdent `depth
  let decoderWithOptions?Id := push_name "decoderWithOptions?"
  let decoderWithOptions? ← `(partial def $decoderWithOptions?Id:ident : Protobuf.Encoding.DecodeOptions → Nat → Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Option $name) := fun $options $depth $msg field_num => do
    let xs? ← Encoding.Message.getExpandedMessageWithOptions $options ($depth + 1) $msg field_num
    let ms ← xs?.mapM ($fromMessageWithOptions:ident $options ($depth + 1))
    if let m :: ms := ms.toList then
      if ms.isEmpty then
        return some m
      else
        return some <| ms.foldl (init := m) $merge
    else
      return none
    )
  let decoder?Id := push_name "decoder?"
  let decoder? ← `(partial def $decoder?Id:ident : Protobuf.Encoding.Message → Nat → Except Protobuf.Encoding.ProtoError (Option $name) :=
    $decoderWithOptions?Id:ident Protobuf.Encoding.DecodeOptions.default 0)
  return (decoder?Id, decoder?, decoderWithOptions?Id, decoderWithOptions?)

private def construct_default (name : Ident) (push_name : String → Ident) (fields : Array ProtoFieldMData) : CommandElabM (Ident × Command) := do
  let u := mkIdent `«Unknown.Fields»
  let ps := fields.map ProtoFieldMData.field_name |>.push u
  let vs := fields.map (fun x => x.default_lean_value) |>.push (← ``(Std.HashMap.emptyWithCapacity 8))
  let structInst ← `({ $[$ps:ident := $vs]* : $name })
  let defaultId := push_name "Default.Value"
  let default ← `(partial def $defaultId:ident : $name := $structInst)
  return (defaultId, default)

/-- Value-or-default getters (`<field>D`, following core's `getD` naming) for
explicit-presence fields: the value when set, the type's default otherwise.
These give CEL-style field traversal (an unset message field reads as the
default instance) a dot-notation spelling — `m.subD.x` — without giving up
the `Option` in the structure itself. Oneof pseudo-fields are skipped (CEL
has no group-level value). -/
private def construct_defaulted_getters (name : Ident) (push_name : String → Ident)
    (fields : Array ProtoFieldMData) : CommandElabM (Array Command) := do
  fields.filterMapM fun x => do
    match x.lean_shape, x.oneof_type? with
    | LeanShape.option, none =>
      let getterId := push_name (x.field_name.getId.toString ++ "D")
      -- partial: generated functions may land in a `mutual` block (recursive
      -- messages), where partial and non-partial definitions cannot mix.
      let getter ← `(partial def $getterId:ident (m : $name) : $(x.lean_type_inner) :=
        ($(x.field_proj) m).getD default)
      return some getter
    | _, _ => return none

/-- Presence predicates (`has_<field>`), mirroring CEL's per-category `has()`
semantics: `isSome` for explicit-presence fields, non-empty for
repeated/map, non-default for implicit-presence scalars. Oneof pseudo-fields
are skipped (CEL addresses members, not groups; member predicates are
generated alongside the member getters). -/
private def construct_presence_getters (name : Ident) (push_name : String → Ident)
    (fields : Array ProtoFieldMData) : CommandElabM (Array Command) := do
  fields.filterMapM fun x => do
    if x.oneof_type?.isSome then
      return none
    let getterId := push_name ("has_" ++ x.field_name.getId.toString)
    let getter ←
      match x.lean_shape with
      | LeanShape.option =>
        `(def $getterId:ident (m : $name) : Bool := ($(x.field_proj) m).isSome)
      | LeanShape.array | LeanShape.map =>
        `(def $getterId:ident (m : $name) : Bool := !($(x.field_proj) m).isEmpty)
      | LeanShape.strict =>
        `(def $getterId:ident (m : $name) : Bool := ($(x.field_proj) m) != default)
    return some getter

/-- Value-or-default getters for oneof members, on the *message* (CEL treats
members as fields of the enclosing message): `m.email` / `m.emailD` yield the
payload when that case is active and the payload type's default otherwise.
Constructor names are read from the already-elaborated oneof inductive, so
oneofs declared inside the same `mutual` block are skipped (their sum is not
in the environment yet). -/
private def construct_member_getters (name : Ident) (push_name : String → Ident)
    (fields : Array ProtoFieldMData) : CommandElabM (Array Command) := do
  let env ← getEnv
  let mut out : Array Command := #[]
  for x in fields do
    if let some oneofName := x.oneof_type? then
      if let some (.inductInfo iv) := env.find? oneofName then
        for ctor in iv.ctors do
          if let .str _ memberStr := ctor then
            let getterId := push_name memberStr
            let getterDId := push_name (memberStr ++ "D")
            let hasId := push_name ("has_" ++ memberStr)
            let ctorId := mkIdent ctor
            let getter ← `(def $getterId:ident (m : $name) :=
              match $(x.field_proj):ident m with
              | some ($ctorId:ident v) => v
              | _ => default)
            let getterD ← `(def $getterDId:ident (m : $name) := $getterId m)
            -- A single-member oneof makes the member test vacuous: any
            -- present state holds this member. It also makes the `matches`
            -- fallback below a redundant alternative, which Lean rejects, so
            -- this is not merely a simplification.
            let hasGetter ←
              if iv.ctors.length == 1 then
                `(def $hasId:ident (m : $name) : Bool := ($(x.field_proj) m).isSome)
              else
                `(def $hasId:ident (m : $name) : Bool :=
                  ($(x.field_proj) m).any (fun c => c matches $ctorId:ident _))
            out := out.push getter
            out := out.push getterD
            out := out.push hasGetter
  return out

/-- PB-02's bounded direct-encoding subset. Every message still gets an internal
direct-plan hook, but schemas outside this subset use the generic validated
fallback. Its generated name component contains `$`, which cannot occur in a
protobuf identifier, so legal field projections cannot collide with the hook.
Keeping this predicate structural avoids message-name-specific
codecs while allowing the Widget/ListWidgetsResponse shape to bypass the
intermediate `Message`/`Record`/nested `ByteArray` graph. -/
private def directTypedFieldSupported (x : ProtoFieldMData) : Bool :=
  if x.map_info?.isSome || x.oneof_type?.isSome then
    false
  else
    match x.mod with
    | .default =>
        match x.internal_type? with
        | some .string | some .uint32 | some .uint64 => true
        | _ => false
    | .repeated =>
        x.internal_type?.isNone && x.enum_type?.isNone &&
          !x.options.wired_as_group?.isEqSome true
    | .optional | .required => false

/-- Build one generated `Put` state transformer rather than a runtime array of
per-field plans. Each known-field action threads the same output buffer, then
the generic unknown-field plan writes last. -/
private partial def constructDirectPutBody (putTerms : List Term)
    (out unknownPlan : Ident) : CommandElabM Term := do
  match putTerms with
  | [] => `(($unknownPlan:ident).put $out:ident)
  | putTerm :: rest =>
      let nextOut ← mkIdent <$> mkFreshUserName `out
      let tail ← constructDirectPutBody rest nextOut unknownPlan
      `(let (_, $nextOut:ident) := ($putTerm:term) $out:ident
        $tail:term)

private def construct_direct_plan (name : Ident) (push_name : String → Ident)
    (fields : Array ProtoFieldMData) (toMessageWithOptions : Ident)
    (mutMessages : NameSet) :
    CommandElabM (Array Command) := do
  let directPlanWithOptionsId := push_name "_pb$directPlanWithOptions"
  let options ← mkIdent <$> mkFreshUserName `options
  let val ← mkIdent <$> mkFreshUserName `val
  let msg ← mkIdent <$> mkFreshUserName `msg

  let directPlanWithOptions ←
    if fields.all directTypedFieldSupported then
      let mut childSetups : Array (Ident × Term × Ident) := #[]
      let mut sizeTerms : Array Term := #[]
      let mut putTerms : Array Term := #[]
      for x in fields do
        match x.mod, x.internal_type? with
        | .default, some internalType =>
            let value ← `($(x.field_proj):ident $val:ident)
            let (fieldSize, fieldPut) ←
              match internalType with
              | .string =>
                  pure (← `(Protobuf.Encoding.Direct.stringFieldSize $(x.field_num):num $value:term),
                    ← `(Protobuf.Encoding.Direct.putStringField $(x.field_num):num $value:term))
              | .uint32 =>
                  pure (← `(Protobuf.Encoding.Direct.varintFieldSize $(x.field_num):num ($value:term).toNat),
                    ← `(Protobuf.Encoding.Direct.putVarintField $(x.field_num):num ($value:term).toNat))
              | .uint64 =>
                  pure (← `(Protobuf.Encoding.Direct.varintFieldSize $(x.field_num):num ($value:term).toNat),
                    ← `(Protobuf.Encoding.Direct.putVarintField $(x.field_num):num ($value:term).toNat))
              | _ => unreachable!
            sizeTerms := sizeTerms.push
              (← `(if $(x.test_unset):term $value:term then 0 else $fieldSize:term))
            putTerms := putTerms.push
              (← `(if $(x.test_unset):term $value:term then
                (pure () : Binary.Put)
              else
                $fieldPut:term))
        | .repeated, none =>
            let childPlans ← mkIdent <$> mkFreshUserName `childPlans
            let childDirectPlanWithOptionsId :=
              mkIdentFrom x.proto_type
                (x.proto_type.getId.str "_pb$directPlanWithOptions")
            let childHasDirectPlan : Bool ←
              if mutMessages.contains x.proto_type.getId then
                pure true
              else
                try
                  let resolved ← resolveGlobalConst childDirectPlanWithOptionsId
                  pure !resolved.isEmpty
                catch _ =>
                  pure false
            let childPlanner ←
              if childHasDirectPlan then
                `($childDirectPlanWithOptionsId:ident)
              else
                let childToMessageWithOptions :=
                  mkIdentFrom x.proto_type (x.proto_type.getId.str "toMessageWithOptions")
                let childOptions ← mkIdent <$> mkFreshUserName `options
                let childValue ← mkIdent <$> mkFreshUserName `value
                `(fun $childOptions:ident $childValue:ident =>
                  $childToMessageWithOptions:ident $childOptions:ident $childValue:ident >>=
                    Protobuf.Encoding.Direct.Plan.ofMessage)
            childSetups := childSetups.push
              (childPlans, childPlanner, x.field_proj)
            sizeTerms := sizeTerms.push
              (← `(($childPlans:ident).foldl (init := 0) fun total child =>
                total + Protobuf.Encoding.Direct.messageFieldSize $(x.field_num):num child))
            putTerms := putTerms.push
              (← `(($childPlans:ident).forM fun child =>
                Protobuf.Encoding.Direct.putMessageField $(x.field_num):num child))
        | _, _ => unreachable!
      let knownSize ← sizeTerms.foldlM (init := ← `(0)) fun total fieldSize =>
        `($total:term + $fieldSize:term)
      let unknownPlan ← mkIdent <$> mkFreshUserName `unknownPlan
      let unknownProj := push_name "Unknown.Fields"
      let out ← mkIdent <$> mkFreshUserName `out
      let putBody ← constructDirectPutBody putTerms.toList out unknownPlan
      let mut body ← `(Protobuf.Encoding.Direct.Plan.ofUnknownFields
        $options:ident ($unknownProj:ident $val:ident) >>= fun $unknownPlan:ident =>
          pure
            { size := $knownSize:term + ($unknownPlan:ident).size
            , put := fun $out:ident => $putBody:term
            })
      for (childPlans, childPlanner, fieldProj) in childSetups.reverse do
        body ← `(Array.mapM
            ($childPlanner:term $options:ident)
            ($fieldProj:ident $val:ident) >>= fun $childPlans:ident =>
          $body:term)
      `(partial def $directPlanWithOptionsId:ident :
          Protobuf.Encoding.EncodeOptions → $name →
            Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Direct.Plan :=
        fun $options:ident $val:ident => $body:term)
    else
      `(partial def $directPlanWithOptionsId:ident :
          Protobuf.Encoding.EncodeOptions → $name →
            Except Protobuf.Encoding.ProtoError Protobuf.Encoding.Direct.Plan :=
        fun $options:ident $val:ident => do
          let $msg:ident := (← $toMessageWithOptions:ident $options:ident $val:ident)
          Protobuf.Encoding.Direct.Plan.ofMessage $msg:ident)

  return #[directPlanWithOptions]

private def construct_encode (name : Ident) (push_name : String → Ident)
    (toMessageWithOptions : Ident) (directPlanWithOptions? : Option Ident) :
    CommandElabM (Ident × Command × Ident × Command) := do
  let encodeWithOptionsId := push_name "encodeWithOptions"
  let sWithOptions ←
    match directPlanWithOptions? with
    | some directPlanWithOptions =>
        `(partial def $encodeWithOptionsId:ident : Encoding.EncodeOptions → $name → Except Encoding.ProtoError ByteArray := fun options x => do
          let plan ← $directPlanWithOptions:ident options x
          return Protobuf.Encoding.Direct.Plan.run plan)
    | none =>
        `(partial def $encodeWithOptionsId:ident : Encoding.EncodeOptions → $name → Except Encoding.ProtoError ByteArray := fun options x => do
          return Binary.Put.run (Binary.put (← $toMessageWithOptions:ident options x)))
  let encodeId := push_name "encode"
  let s ← `(partial def $encodeId:ident : $name → Except Encoding.ProtoError ByteArray :=
    $encodeWithOptionsId:ident Encoding.EncodeOptions.default)
  return (encodeId, s, encodeWithOptionsId, sWithOptions)

private def construct_decode (name : Ident) (push_name : String → Ident) (fromMessageWithOptions : Ident) : CommandElabM (Array Command) := do
  let decodeWithOptionsId := push_name "decodeWithOptions"
  let sWithOptions ← `(partial def $decodeWithOptionsId:ident : Encoding.DecodeOptions → ByteArray → Except Encoding.ProtoError $name := fun options bs => do
    options.checkMessageSize bs.size
    let msg := Binary.Get.run (Encoding.getMessageWithOptions options 0) bs |>.toExcept
    let msg ← Encoding.protoDecodeParseResultExcept msg
    $fromMessageWithOptions:ident options 0 msg)
  let decodeId := push_name "decode"
  let s ← `(partial def $decodeId:ident : ByteArray → Except Encoding.ProtoError $name :=
    $decodeWithOptionsId:ident Encoding.DecodeOptions.default)
  return #[sWithOptions, s]

public def elabMessageDecCore (mutEnums mutOneofs messages : NameSet) : Syntax → CommandElabM ProtobufDeclBlock := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData mutEnums mutOneofs messages name mod t' n fidx optionsStx
  mdata.forM fun x => do
    if x.oneof_type?.isSome then
      if x.field_num.getNat != 0 then
        throwErrorAt x.field_num "oneof field can only have dummy field number 0, but got {x.field_num.getNat}"
  let defs := mdata.map fun x => x.default_ctor_value
  let struct ← `(structure $name where
    $[$n:ident : $(mdata.map fun x => x.lean_type) := $defs]*
    «Unknown.Fields» : Std.HashMap Nat (Array Encoding.ProtoVal) := {})
  let push_name (component : String) := mkIdentFrom name (name.getId.str component)
  let (default', default) ← construct_default name push_name mdata
  -- Auto-generated instance names use only the type's final component and can
  -- collide inside recursive blocks or when same-named scoped messages from
  -- different modules are imported together. Qualify the helper by the full
  -- type name; `?` cannot occur in a protobuf identifier, so schema
  -- declarations cannot steal this name.
  let inhabitedId := push_name "instInhabited?"
  let inhInst ← `(instance $inhabitedId:ident : Inhabited $name := ⟨$default'⟩)
  let (toMessage', toMessage, toMessageWithOptions', toMessageWithOptions) ← construct_toMessage name push_name mdata
  let (_, builder) ← construct_builder name push_name toMessage'
  let (fromMessage', fromMessage, fromMessageWithOptions', fromMessageWithOptions) ← construct_fromMessage name push_name mdata
  let (merge', merge) ← construct_merge name push_name mdata
  let (_, decoder?, _, decoderWithOptions?) ← construct_decoder? name push_name fromMessageWithOptions' merge'
  let (_, decoder_rep, _, decoderRepWithOptions) ← construct_decoder_rep name push_name fromMessage' fromMessageWithOptions'
  let directPlanForEncode? :=
    if mdata.all directTypedFieldSupported then
      some (push_name "_pb$directPlanWithOptions")
    else
      none
  let (_, encode, _, encodeWithOptions) ←
    construct_encode name push_name toMessageWithOptions' directPlanForEncode?
  let directEncoding ← construct_direct_plan name push_name mdata toMessageWithOptions' messages
  let decodes ← construct_decode name push_name fromMessageWithOptions'
  let defaultedGetters ← construct_defaulted_getters name push_name mdata
  let memberGetters ← construct_member_getters name push_name mdata
  let presenceGetters ← construct_presence_getters name push_name mdata
  return {
    decls := #[struct],
    inhabitedFunctions := #[default],
    inhabitedInsts := #[inhInst],
    functions := #[toMessageWithOptions, toMessage, builder, fromMessageWithOptions, fromMessage, merge, decoderWithOptions?, decoder?, decoderRepWithOptions, decoder_rep] ++ directEncoding ++ #[encodeWithOptions, encode] ++ decodes ++ defaultedGetters,
    postFunctions := memberGetters ++ presenceGetters
  }

@[scoped command_elab messageDec]
public def elabMessageDec : CommandElab := fun stx => do
  let `(messageDec| message $name $[$msgOptions?]? { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let r ← elabMessageDecCore {} {} {name.getId} stx
  r.elaborate
