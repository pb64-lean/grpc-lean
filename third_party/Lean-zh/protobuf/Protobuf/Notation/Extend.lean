module

public import Lean
public meta import Protobuf.Notation.Basic
public import Protobuf.Notation.Message
import Protobuf.Notation.Syntax

set_option hygiene false

public meta section

namespace Protobuf.Notation

open Lean Meta Elab Term Command

private def ensureExtendFieldSupported (x : ProtoFieldMData) : CommandElabM Unit := do
  if x.map_info?.isSome then
    throwErrorAt x.field_name "map fields are not supported in extend"
  if x.oneof_type?.isSome then
    throwErrorAt x.field_name "oneof fields are not supported in extend"

private def elabExtendField (extendee : Ident) (x : ProtoFieldMData) : CommandElabM (Array Command) := do
  ensureExtendFieldSupported x
  let fieldNameStr := x.field_name.getId.toString
  let extendeeId := extendee
  let fieldNumTerm := x.field_num
  let isRepeated := x.mod == Modifier.repeated
  let leanType := x.lean_type_inner
  let builder ← x.builder?.getDM (throwErrorAt x.field_name "builder is absent for extension field")
  let decoder? ← x.decoder??.getDM (throwErrorAt x.field_name "decoder? is absent for extension field")
  let decoderRep ← x.decoder_rep?.getDM (throwErrorAt x.field_name "decoder_rep is absent for extension field")
  let packed := x.options.packed?.isEqSome true
  let closedEnum := x.enum_type?.isSome && x.options.closed_enum?.isEqSome true
  let enumIsKnown := mkIdentFrom x.proto_type (x.proto_type.getId.str "isKnown")
  if packed && x.decoder_rep_packed?.isNone then
    throwErrorAt x.field_name "packed is not supported for this field type"
  let unknownAccessor := mkIdentFrom extendee (extendee.getId.str "Unknown.Fields")
  let unknownFieldId := mkIdent `«Unknown.Fields»
  let getId := mkIdentFrom extendee (extendee.getId.str s!"get_{fieldNameStr}?")
  let setId := mkIdentFrom extendee (extendee.getId.str s!"set_{fieldNameStr}")
  let hasId := mkIdentFrom extendee (extendee.getId.str s!"has_{fieldNameStr}")
  let msg ← mkIdent <$> mkFreshUserName `msg
  let val ← mkIdent <$> mkFreshUserName `val
  let map ← mkIdent <$> mkFreshUserName `map
  let wire ← mkIdent <$> mkFreshUserName `wire
  let vals ← mkIdent <$> mkFreshUserName `vals
  let getCmd ←
    if isRepeated then
      if closedEnum then
        `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Array $leanType) := fun $msg => do
          let $wire:ident := Protobuf.Encoding.Message.wire_map Protobuf.Encoding.Message.empty ($unknownAccessor $msg)
          Protobuf.Encoding.Message.getRepeatedValidWith $wire $fieldNumTerm (fun msg fieldNum => do
            let values ← $decoderRep:ident msg fieldNum
            return values.filter (fun value => $enumIsKnown:ident value))
          )
      else
        `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Array $leanType) := fun $msg => do
          let $wire:ident := Protobuf.Encoding.Message.wire_map Protobuf.Encoding.Message.empty ($unknownAccessor $msg)
          Protobuf.Encoding.Message.getRepeatedValidWith $wire $fieldNumTerm $decoderRep:ident
          )
    else if x.internal_type?.isNone && x.enum_type?.isNone then
      let merge := mkIdentFrom x.proto_type (x.proto_type.getId.append `merge)
      `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Option $leanType) := fun $msg => do
        let $wire:ident := Protobuf.Encoding.Message.wire_map Protobuf.Encoding.Message.empty ($unknownAccessor $msg)
        Protobuf.Encoding.Message.getMergedValidWith? $wire $fieldNumTerm $decoder?:ident $merge:ident
        )
    else if closedEnum then
      `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Option $leanType) := fun $msg => do
        let $wire:ident := Protobuf.Encoding.Message.wire_map Protobuf.Encoding.Message.empty ($unknownAccessor $msg)
        Protobuf.Encoding.Message.getLastValidWith? $wire $fieldNumTerm (fun msg fieldNum => do
          let value? ← $decoder?:ident msg fieldNum
          match value? with
          | Option.some value =>
              if $enumIsKnown:ident value then
                pure (Option.some value)
              else
                throw (Protobuf.Encoding.ProtoError.invalidWireType "closed enum value is unknown")
          | Option.none => pure Option.none)
        )
    else
      `(partial def $getId:ident : $extendeeId → Except Protobuf.Encoding.ProtoError (Option $leanType) := fun $msg => do
        let $wire:ident := Protobuf.Encoding.Message.wire_map Protobuf.Encoding.Message.empty ($unknownAccessor $msg)
        Protobuf.Encoding.Message.getLastValidWith? $wire $fieldNumTerm $decoder?:ident
        )
  let setCmd ←
    if isRepeated then
      if packed then
        `(partial def $setId:ident : $extendeeId → Array $leanType → Except Protobuf.Encoding.ProtoError $extendeeId := fun $msg $vals => do
          let $vals:ident ← Array.mapM $builder $vals
          let $vals:ident := #[Protobuf.Encoding.ProtoVal.of_packed $vals]
          let $map:ident := ($unknownAccessor $msg).insert $fieldNumTerm $vals
          return { $msg with $unknownFieldId:ident := $map }
          )
      else
        `(partial def $setId:ident : $extendeeId → Array $leanType → Except Protobuf.Encoding.ProtoError $extendeeId := fun $msg $vals => do
          let $vals:ident ← Array.mapM $builder $vals
          let $map:ident := ($unknownAccessor $msg).insert $fieldNumTerm $vals
          return { $msg with $unknownFieldId:ident := $map }
          )
    else
      `(partial def $setId:ident : $extendeeId → $leanType → Except Protobuf.Encoding.ProtoError $extendeeId := fun $msg $val => do
        let $val:ident ← $builder:ident $val
        let $map:ident := ($unknownAccessor $msg).insert $fieldNumTerm #[$val]
        return { $msg with $unknownFieldId:ident := $map }
        )
  let hasCmd ←
    if isRepeated then
      `(partial def $hasId:ident : $extendeeId → Bool := fun $msg =>
        match $getId:ident $msg with
        | .ok vals => !vals.isEmpty
        | .error _ => false)
    else
      `(partial def $hasId:ident : $extendeeId → Bool := fun $msg =>
        match $getId:ident $msg with
        | .ok (some _) => true
        | _ => false)
  return #[getCmd, setCmd, hasCmd]

@[scoped command_elab extendDec]
public def elabExtendDec : CommandElab := fun stx => do
  let `(extendDec| extend $extendee { $[$[$mod]? $t' $n = $fidx $[$optionsStx]? ;]* }) := stx | throwUnsupportedSyntax
  let mdata ← computeMData {} {} {} extendee mod t' n fidx optionsStx
  let cmds ← mdata.mapM (elabExtendField extendee)
  for cmd in cmds.flatten do
    elabCommand cmd

end Protobuf.Notation
