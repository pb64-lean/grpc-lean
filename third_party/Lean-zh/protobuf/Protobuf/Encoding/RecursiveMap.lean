module

public section

namespace Protobuf

/--
An insertion-ordered protobuf map representation used when a map value is part
of the same recursive message group as the containing message.

`Std.HashMap` cannot occur in such a Lean mutual inductive group: its internal
well-formedness proof refers to the pre-transformation value type, which the
kernel rejects when Lean compiles nested recursion.  This small array-backed
map keeps the recursive occurrence strictly positive while preserving protobuf
map semantics.  Generated non-recursive maps continue to use `Std.HashMap`.
-/
structure RecursiveMap (κ : Type u) (ν : Type v) where
  entries : Array (κ × ν) := #[]

namespace RecursiveMap

@[inline]
def empty : RecursiveMap κ ν := {}

instance : Inhabited (RecursiveMap κ ν) := ⟨empty⟩

@[inline]
def toArray (map : RecursiveMap κ ν) : Array (κ × ν) := map.entries

@[inline]
def toList (map : RecursiveMap κ ν) : List (κ × ν) := map.entries.toList

@[inline]
def isEmpty (map : RecursiveMap κ ν) : Bool := map.entries.isEmpty

@[inline]
def size (map : RecursiveMap κ ν) : Nat := map.entries.size

def get? [BEq κ] (map : RecursiveMap κ ν) (key : κ) : Option ν :=
  map.entries.findSome? fun (entryKey, value) =>
    if entryKey == key then some value else none

@[inline]
def contains [BEq κ] (map : RecursiveMap κ ν) (key : κ) : Bool :=
  (map.get? key).isSome

/-- Insert a key/value pair, replacing an existing value for the key. -/
def insert [BEq κ] (map : RecursiveMap κ ν) (key : κ) (value : ν) : RecursiveMap κ ν :=
  if map.contains key then
    { entries := map.entries.map fun (entryKey, entryValue) =>
        if entryKey == key then (key, value) else (entryKey, entryValue) }
  else
    { entries := map.entries.push (key, value) }

def erase [BEq κ] (map : RecursiveMap κ ν) (key : κ) : RecursiveMap κ ν :=
  { entries := map.entries.filter fun (entryKey, _) => entryKey != key }

/--
Combine two protobuf maps.  As with `Std.HashMap.union`, values from the right
argument replace values from the left argument when their keys match.
-/
def union [BEq κ] (left right : RecursiveMap κ ν) : RecursiveMap κ ν :=
  right.entries.foldl (fun map (key, value) => map.insert key value) left

end RecursiveMap

end Protobuf
