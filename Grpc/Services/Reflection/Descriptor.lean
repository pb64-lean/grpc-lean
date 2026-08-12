module

public section

namespace Grpc
namespace Services
namespace Reflection

structure ExtensionDescriptor where
  containingType : String
  extensionNumber : Int32
  deriving Inhabited, Repr, DecidableEq

/-- One protobuf file and the lookup metadata needed by gRPC server reflection. -/
structure FileDescriptor where
  name : String
  package : String := ""
  symbols : Array String := #[]
  dependencies : Array String := #[]
  fileDescriptorProto : ByteArray
  extensions : Array ExtensionDescriptor := #[]
  extensionNumbers : Array (String × Array Int32) := #[]
  deriving Inhabited, DecidableEq

/-- A descriptor-set merge was conflicting, incomplete, or ambiguous. -/
inductive DescriptorSetMergeError where
  | conflictingFile (name : String)
  | missingDependency (file dependency : String)
  | conflictingSymbol (symbol firstFile secondFile : String)
  | conflictingExtension (containingType : String) (extensionNumber : Int32)
      (firstFile secondFile : String)
  deriving Inhabited, Repr, DecidableEq

namespace DescriptorSetMergeError

def message : DescriptorSetMergeError → String
  | .conflictingFile name => s!"conflicting reflection descriptors for {name}"
  | .missingDependency file dependency =>
      s!"reflection descriptor {file} depends on missing file {dependency}"
  | .conflictingSymbol symbol firstFile secondFile =>
      s!"reflection symbol {symbol} is defined by both {firstFile} and {secondFile}"
  | .conflictingExtension containingType extensionNumber firstFile secondFile =>
      s!"reflection extension {containingType}/{extensionNumber} is defined by both " ++
        s!"{firstFile} and {secondFile}"

instance : ToString DescriptorSetMergeError where
  toString := message

end DescriptorSetMergeError

/--
Flatten descriptor sets in caller order and retain the first occurrence of
each filename. Repeated identical descriptors are removed; a repeated filename
with different bytes or lookup metadata is rejected instead of silently making
reflection depend on input order.
-/
def mergeDescriptorSets (sets : Array (Array FileDescriptor)) :
    Except DescriptorSetMergeError (Array FileDescriptor) := do
  let mut merged : Array FileDescriptor := #[]
  for set in sets do
    for descriptor in set do
      match merged.find? (fun existing => existing.name == descriptor.name) with
      | none => merged := merged.push descriptor
      | some existing =>
          if existing == descriptor then
            pure ()
          else
            throw (.conflictingFile descriptor.name)
  for descriptor in merged do
    for dependency in descriptor.dependencies do
      unless merged.any (fun candidate => candidate.name == dependency) do
        throw (.missingDependency descriptor.name dependency)
  for i in [:merged.size] do
    let descriptor := merged[i]!
    for j in [i + 1:merged.size] do
      let other := merged[j]!
      for symbol in descriptor.symbols do
        if other.symbols.contains symbol then
          throw (.conflictingSymbol symbol descriptor.name other.name)
      for extension in descriptor.extensions do
        if other.extensions.contains extension then
          throw (.conflictingExtension extension.containingType extension.extensionNumber
            descriptor.name other.name)
  pure merged

end Reflection
end Services
end Grpc
