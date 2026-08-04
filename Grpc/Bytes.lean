module

public section

/-!
# Shared `ByteArray` proof lemmas

Small structural facts about `ByteArray.push`/`extract` that the codec proofs
in `Grpc.Protocol`, `Grpc.Metadata` and `Grpc.Http2.Hpack` all need. They are
proof-only glue for core-library gaps (there is no `push`/`append` bridge and
no single-element `extract` lemma in core), not part of the runtime API.
-/

namespace Grpc
namespace Bytes

/-- `push` is `append` of a singleton. The core library states this for `Array`
(`Array.push_eq_append`) but not for `ByteArray`. -/
theorem byteArray_push_eq_append (a : ByteArray) (x : UInt8) :
    a.push x = a ++ ByteArray.empty.push x := by
  have hdata : (a.push x).data = (a ++ ByteArray.empty.push x).data := by
    rw [ByteArray.data_push, ByteArray.data_append]
    exact Array.push_eq_append
  cases ha : a.push x
  cases hb : a ++ ByteArray.empty.push x
  simp_all

/-- Appending onto a `push` is a `push` onto the append. -/
theorem append_push (a b : ByteArray) (x : UInt8) :
    a ++ b.push x = (a ++ b).push x := by
  have hdata : (a ++ b.push x).data = ((a ++ b).push x).data := by
    rw [ByteArray.data_append, ByteArray.data_push, ByteArray.data_push,
      ByteArray.data_append, Array.push_eq_append, Array.push_eq_append,
      Array.append_assoc]
  cases ha : a ++ b.push x
  cases hb : (a ++ b).push x
  simp_all

/-- A one-element slice is the singleton holding that element. -/
theorem extract_singleton {bytes : ByteArray} {i : Nat} (h : i < bytes.size) :
    bytes.extract i (i + 1) = ByteArray.empty.push bytes[i] := by
  apply ByteArray.ext_getElem
  · rw [ByteArray.size_extract]
    show min (i + 1) bytes.size - i = 1
    omega
  · intro j hj hj'
    rw [ByteArray.getElem_extract]
    have hj0 : j = 0 := by
      rw [ByteArray.size_extract] at hj
      omega
    subst hj0
    rfl

/-- Moving one decoded byte from the accumulator into the residual slice: the
step lemma every `decodeLoop`/`encodeLoop` induction in this repo turns on. -/
theorem push_extract_step {bytes : ByteArray} {i : Nat} (h : i < bytes.size)
    (out : ByteArray) :
    out.push bytes[i] ++ bytes.extract (i + 1) bytes.size
      = out ++ bytes.extract i bytes.size := by
  rw [byteArray_push_eq_append, ByteArray.append_assoc,
    show ByteArray.empty.push bytes[i] = bytes.extract i (i + 1) from (extract_singleton h).symm,
    ByteArray.extract_append_extract,
    show min i (i + 1) = i from by omega,
    show max (i + 1) bytes.size = bytes.size from by omega]

/-- A slice that starts at or past the end is empty. -/
theorem extract_eq_empty {bytes : ByteArray} {i : Nat} (h : bytes.size ≤ i) :
    bytes.extract i bytes.size = ByteArray.empty :=
  ByteArray.extract_eq_empty_iff.mpr (by omega)

end Bytes
end Grpc
