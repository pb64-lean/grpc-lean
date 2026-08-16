module

public import Grpc.Bytes
public import Grpc.Status

public section

open Grpc.Bytes

namespace Grpc

structure Header where
  name : String
  value : String
  deriving Inhabited, Repr, DecidableEq

abbrev Metadata := Array Header

namespace Header

@[inline] private def isAsciiNonUpperByte (byte : UInt8) : Bool :=
  byte < 128 && !(65 <= byte && byte <= 90)

private def isAsciiWithoutUpperFrom (name : String) (index : Nat) : Bool :=
  if h : index < name.utf8ByteSize then
    let byte := name.getUTF8Byte ⟨index⟩ (by
      simpa only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using h)
    if isAsciiNonUpperByte byte then
      isAsciiWithoutUpperFrom name (index + 1)
    else
      false
  else
    true
termination_by name.utf8ByteSize - index

/-- Executable header-name normalization. Common already-normalized ASCII names
retain their original String object; ASCII uppercase and every non-ASCII input
fall back to the exact existing `String.toLower` behavior. -/
def normalizeNameByteIndexed (name : String) : String :=
  if isAsciiWithoutUpperFrom name 0 then name else name.toLower

/-- Logical header-name normalization. Generated code first uses the
differential-tested byte scan to reuse already-normalized ASCII names. -/
@[implemented_by normalizeNameByteIndexed]
def normalizeName (name : String) : String :=
  name.toLower

@[expose] def of (name value : String) : Header :=
  { name := normalizeName name, value := value }

def isBinary (header : Header) : Bool :=
  header.name.endsWith "-bin"

end Header

namespace Metadata

def empty : Metadata := #[]

def insert (metadata : Metadata) (name value : String) : Metadata :=
  metadata.push (Header.of name value)

def singleton (name value : String) : Metadata :=
  empty.insert name value

@[expose] def getAll (metadata : Metadata) (name : String) : Array String :=
  let key := Header.normalizeName name
  metadata.filterMap fun header =>
    if header.name == key then some header.value else none

@[expose] def get? (metadata : Metadata) (name : String) : Option String :=
  (getAll metadata name)[0]?

def contains (metadata : Metadata) (name value : String) : Bool :=
  (getAll metadata name).contains value

def append (left right : Metadata) : Metadata :=
  right.foldl (fun acc header => acc.push header) left

def headerListEntrySize (header : Header) : Nat :=
  header.name.toUTF8.size + header.value.toUTF8.size + 32

def headerListSize (metadata : Metadata) : Nat :=
  metadata.foldl (fun total header => total + headerListEntrySize header) 0

def validateHeaderListSize (maxSize? : Option Nat) (metadata : Metadata) : Except Status Unit := do
  match maxSize? with
  | none => pure ()
  | some maxSize =>
      let actual := headerListSize metadata
      if actual > maxSize then
        throw (Status.resourceExhausted s!"HTTP/2 header list exceeds configured size limit {maxSize}")
      else
        pure ()

end Metadata

namespace Ascii

def isLowercaseHeaderNameChar (c : Char) : Bool :=
  c.isLower || c.isDigit || c == '-' || c == '_' || c == '.'

/-- Byte-level form of `isLowercaseHeaderNameChar`.  Every accepted character
is one-byte ASCII, while every byte in a non-ASCII UTF-8 encoding is rejected. -/
@[inline] private def isLowercaseHeaderNameByte (byte : UInt8) : Bool :=
  (97 <= byte && byte <= 122) || (48 <= byte && byte <= 57) ||
    byte == 45 || byte == 95 || byte == 46

private def validHeaderNameBytesFrom (name : String) (index : Nat) : Bool :=
  if h : index < name.utf8ByteSize then
    let byte := name.getUTF8Byte ⟨index⟩ (by
      simpa only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using h)
    if isLowercaseHeaderNameByte byte then
      validHeaderNameBytesFrom name (index + 1)
    else
      false
  else
    true
termination_by name.utf8ByteSize - index

/-- Allocation-free executable header-name validation over cached UTF-8
bytes.  Empty names remain invalid. -/
def validHeaderNameByteIndexed (name : String) : Bool :=
  !name.isEmpty && validHeaderNameBytesFrom name 0

/-- The character-level specification remains the logical definition used by
proofs; generated code uses the differential-tested byte-indexed scan. -/
@[implemented_by validHeaderNameByteIndexed]
def validHeaderName (name : String) : Bool :=
  !name.isEmpty && name.all isLowercaseHeaderNameChar

def isVisible (c : Char) : Bool :=
  let n := c.toNat
  0x20 <= n && n <= 0x7e

private def visibleStringBytesFrom (value : String) (index : Nat) : Bool :=
  if h : index < value.utf8ByteSize then
    let byte := value.getUTF8Byte ⟨index⟩ (by
      simpa only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using h)
    if 0x20 <= byte && byte <= 0x7e then
      visibleStringBytesFrom value (index + 1)
    else
      false
  else
    true
termination_by value.utf8ByteSize - index

/-- Allocation-free executable visible-ASCII validation over cached UTF-8
bytes.  The empty string remains valid. -/
def isVisibleStringByteIndexed (value : String) : Bool :=
  visibleStringBytesFrom value 0

/-- Character-level visible-ASCII specification.  Generated code uses the
differential-tested byte-indexed scan. -/
@[implemented_by isVisibleStringByteIndexed]
def isVisibleString (value : String) : Bool :=
  value.all isVisible

end Ascii

namespace Base64

private def alphabet : Array UInt8 :=
  #[
    65, 66, 67, 68, 69, 70, 71, 72,
    73, 74, 75, 76, 77, 78, 79, 80,
    81, 82, 83, 84, 85, 86, 87, 88,
    89, 90, 97, 98, 99, 100, 101, 102,
    103, 104, 105, 106, 107, 108, 109, 110,
    111, 112, 113, 114, 115, 116, 117, 118,
    119, 120, 121, 122, 48, 49, 50, 51,
    52, 53, 54, 55, 56, 57, 43, 47
  ]

private def alphabetByte (i : Nat) : UInt8 :=
  alphabet[i]!

private def alphabetChar (i : Nat) : Char :=
  Char.ofNat (alphabetByte i).toNat

private def decodeChar? (c : Char) : Option Nat :=
  if 'A' <= c && c <= 'Z' then
    some (c.toNat - 'A'.toNat)
  else if 'a' <= c && c <= 'z' then
    some (26 + (c.toNat - 'a'.toNat))
  else if '0' <= c && c <= '9' then
    some (52 + (c.toNat - '0'.toNat))
  else if c == '+' then
    some 62
  else if c == '/' then
    some 63
  else
    none

private def encodeLoop (bytes : ByteArray) (i : Nat) : List Char :=
  if h : i < bytes.size then
    if h1 : i + 1 < bytes.size then
      if h2 : i + 2 < bytes.size then
        alphabetChar (bytes[i].toNat / 4)
          :: alphabetChar (((bytes[i].toNat % 4) * 16) + (bytes[i + 1].toNat / 16))
          :: alphabetChar (((bytes[i + 1].toNat % 16) * 4) + (bytes[i + 2].toNat / 64))
          :: alphabetChar (bytes[i + 2].toNat % 64)
          :: encodeLoop bytes (i + 3)
      else
        [alphabetChar (bytes[i].toNat / 4),
          alphabetChar (((bytes[i].toNat % 4) * 16) + (bytes[i + 1].toNat / 16)),
          alphabetChar ((bytes[i + 1].toNat % 16) * 4), '=']
    else
      [alphabetChar (bytes[i].toNat / 4), alphabetChar ((bytes[i].toNat % 4) * 16), '=', '=']
  else
    []
  termination_by bytes.size - i
  decreasing_by omega

def encodeBytes (bytes : ByteArray) : String :=
  String.ofList (encodeLoop bytes 0)

private def dropLeadingPadding : List Char -> List Char
  | '=' :: rest => dropLeadingPadding rest
  | chars => chars

def encodeBytesUnpadded (bytes : ByteArray) : String :=
  String.ofList ((dropLeadingPadding (encodeBytes bytes).toList.reverse).reverse)

private def decodeQuad (a b : Nat) (c d : Option Nat) : ByteArray :=
  let byte0 := UInt8.ofNat ((a * 4) + (b / 16))
  match c with
  | none => ByteArray.empty.push byte0
  | some c =>
      let byte1 := UInt8.ofNat (((b % 16) * 16) + (c / 4))
      match d with
      | none => ByteArray.empty.push byte0 |>.push byte1
      | some d =>
          let byte2 := UInt8.ofNat (((c % 4) * 64) + d)
          ByteArray.empty.push byte0 |>.push byte1 |>.push byte2

private def decodeLoop (chars : List Char) (out : ByteArray) : Except String ByteArray :=
  match chars with
  | [] => .ok out
  | a :: b :: c :: d :: rest =>
      match decodeChar? a, decodeChar? b with
      | some va, some vb =>
          let vc? := if c == '=' then none else decodeChar? c
          let vd? := if d == '=' then none else decodeChar? d
          if c == '=' && d != '=' then
            .error "invalid base64 padding"
          else if c != '=' && vc?.isNone then
            .error "invalid base64 character"
          else if d != '=' && vd?.isNone then
            .error "invalid base64 character"
          else if (c == '=' || d == '=') && !rest.isEmpty then
            .error "base64 padding before end"
          else
            decodeLoop rest (out ++ decodeQuad va vb vc? vd?)
      | _, _ => .error "invalid base64 character"
  | _ => .error "base64 length is not a multiple of 4"

private def paddedInput (value : String) : Except String String :=
  match value.toList.length % 4 with
  | 0 => .ok value
  | 2 => .ok (value ++ "==")
  | 3 => .ok (value ++ "=")
  | _ => .error "base64 length is invalid"

def decodeBytes (value : String) : Except String ByteArray := do
  let value ← paddedInput value
  decodeLoop value.toList ByteArray.empty

/-!
### Codec laws

`decodeBytes_encodeBytes` and `decodeBytes_encodeBytesUnpadded`: base64
decoding inverts both the padded and the unpadded encoder, so `-bin`
metadata values survive a wire roundtrip.
-/

set_option maxRecDepth 8192 in
private theorem decodeChar?_alphabetChar {n : Nat} (h : n < 64) :
    decodeChar? (alphabetChar n) = some n :=
  (by decide : ∀ i : Fin 64, decodeChar? (alphabetChar i.val) = some i.val) ⟨n, h⟩

set_option maxRecDepth 8192 in
private theorem alphabetChar_beq_pad {n : Nat} (h : n < 64) :
    (alphabetChar n == '=') = false :=
  (by decide : ∀ i : Fin 64, (alphabetChar i.val == '=') = false) ⟨n, h⟩

private theorem alphabetChar_ne_pad {n : Nat} (h : n < 64) : alphabetChar n ≠ '=' := by
  have := alphabetChar_beq_pad h
  simpa using this

private theorem ofNat_toNat_of_eq {x : UInt8} {n : Nat} (h : n = x.toNat) :
    UInt8.ofNat n = x := by
  rw [h, UInt8.ofNat_toNat]

/-- Three decoded bytes moved from the accumulator into the residual slice. -/
private theorem push3_extract_step {bytes : ByteArray} {i : Nat} (h2 : i + 2 < bytes.size)
    (out : ByteArray) :
    ((out.push bytes[i]).push bytes[i + 1]).push bytes[i + 2]
        ++ bytes.extract (i + 3) bytes.size
      = out ++ bytes.extract i bytes.size := by
  have h1 : i + 1 < bytes.size := by omega
  have h : i < bytes.size := by omega
  rw [show i + 3 = i + 2 + 1 from by omega, push_extract_step h2,
    show i + 2 = i + 1 + 1 from by omega, push_extract_step h1, push_extract_step h]

/-- Base64 decoding recovers every byte an encoding pass emitted, appended to
whatever the accumulator already held. -/
private theorem decodeLoop_encodeLoop (bytes : ByteArray) (i : Nat) :
    ∀ out, decodeLoop (encodeLoop bytes i) out = .ok (out ++ bytes.extract i bytes.size) := by
  fun_induction encodeLoop bytes i
  next i h h1 h2 ih =>
    intro out
    have b0 : bytes[i].toNat < 256 := UInt8.toNat_lt bytes[i]
    have b1 : bytes[i + 1].toNat < 256 := UInt8.toNat_lt bytes[i + 1]
    have b2 : bytes[i + 2].toNat < 256 := UInt8.toNat_lt bytes[i + 2]
    rw [decodeLoop]
    simp only [decodeChar?_alphabetChar (show bytes[i].toNat / 4 < 64 by omega),
      decodeChar?_alphabetChar
        (show bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16 < 64 by omega),
      decodeChar?_alphabetChar
        (show bytes[i + 1].toNat % 16 * 4 + bytes[i + 2].toNat / 64 < 64 by omega),
      decodeChar?_alphabetChar (show bytes[i + 2].toNat % 64 < 64 by omega),
      alphabetChar_beq_pad
        (show bytes[i + 1].toNat % 16 * 4 + bytes[i + 2].toNat / 64 < 64 by omega),
      alphabetChar_beq_pad (show bytes[i + 2].toNat % 64 < 64 by omega),
      Bool.false_eq_true, Bool.false_and, Bool.and_false, Bool.false_or, if_false,
      Option.isNone_some, Bool.and_true, decodeQuad, append_push, ByteArray.append_empty]
    rw [ih]
    rw [ofNat_toNat_of_eq
        (show bytes[i].toNat / 4 * 4 + (bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16) / 16
          = bytes[i].toNat by omega),
      ofNat_toNat_of_eq
        (show (bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16) % 16 * 16
            + (bytes[i + 1].toNat % 16 * 4 + bytes[i + 2].toNat / 64) / 4
          = bytes[i + 1].toNat by omega),
      ofNat_toNat_of_eq
        (show (bytes[i + 1].toNat % 16 * 4 + bytes[i + 2].toNat / 64) % 4 * 64
            + bytes[i + 2].toNat % 64
          = bytes[i + 2].toNat by omega),
      push3_extract_step h2]
  next i h h1 h2 =>
    intro out
    have b0 : bytes[i].toNat < 256 := UInt8.toNat_lt bytes[i]
    have b1 : bytes[i + 1].toNat < 256 := UInt8.toNat_lt bytes[i + 1]
    rw [decodeLoop]
    simp only [decodeChar?_alphabetChar (show bytes[i].toNat / 4 < 64 by omega),
      decodeChar?_alphabetChar
        (show bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16 < 64 by omega),
      decodeChar?_alphabetChar (show bytes[i + 1].toNat % 16 * 4 < 64 by omega),
      alphabetChar_beq_pad (show bytes[i + 1].toNat % 16 * 4 < 64 by omega),
      Bool.false_eq_true, Bool.false_and, Bool.and_false, Bool.false_or, if_false,
      Option.isNone_some, Bool.and_true, Bool.not_true, Bool.true_and, Bool.and_self,
      List.isEmpty_nil, if_true, beq_self_eq_true, bne_self_eq_false, Option.isNone_none,
      decodeLoop, decodeQuad, append_push, ByteArray.append_empty]
    rw [ofNat_toNat_of_eq
        (show bytes[i].toNat / 4 * 4 + (bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16) / 16
          = bytes[i].toNat by omega),
      ofNat_toNat_of_eq
        (show (bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16) % 16 * 16
            + bytes[i + 1].toNat % 16 * 4 / 4
          = bytes[i + 1].toNat by omega)]
    rw [← push_extract_step h out, ← push_extract_step h1 (out.push bytes[i]),
      extract_eq_empty (show bytes.size ≤ i + 1 + 1 by omega), ByteArray.append_empty]
  next i h h1 =>
    intro out
    have b0 : bytes[i].toNat < 256 := UInt8.toNat_lt bytes[i]
    rw [decodeLoop]
    simp only [decodeChar?_alphabetChar (show bytes[i].toNat / 4 < 64 by omega),
      decodeChar?_alphabetChar (show bytes[i].toNat % 4 * 16 < 64 by omega),
      Bool.false_eq_true, Bool.false_and, Bool.and_false, Bool.false_or, if_false,
      Option.isNone_some, Bool.and_true, Bool.not_true, Bool.true_and, Bool.and_self,
      List.isEmpty_nil, if_true, beq_self_eq_true, bne_self_eq_false, Option.isNone_none,
      decodeLoop, decodeQuad, append_push, ByteArray.append_empty]
    rw [← push_extract_step h out, extract_eq_empty (show bytes.size ≤ i + 1 by omega),
      ByteArray.append_empty,
      ofNat_toNat_of_eq
        (show bytes[i].toNat / 4 * 4 + bytes[i].toNat % 4 * 16 / 16 = bytes[i].toNat by omega)]
  next i h =>
    intro out
    rw [decodeLoop, extract_eq_empty (by omega), ByteArray.append_empty]

private theorem encodeLoop_length_mod (bytes : ByteArray) (i : Nat) :
    (encodeLoop bytes i).length % 4 = 0 := by
  fun_induction encodeLoop bytes i <;> simp_all <;> omega

/-- Base64 decoding inverts the padded encoder. -/
theorem decodeBytes_encodeBytes (bytes : ByteArray) :
    decodeBytes (encodeBytes bytes) = .ok bytes := by
  have hpad : paddedInput (encodeBytes bytes) = .ok (encodeBytes bytes) := by
    unfold paddedInput encodeBytes
    rw [String.toList_ofList, encodeLoop_length_mod]
    rfl
  unfold decodeBytes
  simp only [bind, Except.bind, hpad]
  rw [encodeBytes, String.toList_ofList, decodeLoop_encodeLoop, ByteArray.extract_zero_size,
    ByteArray.empty_append]

private theorem dropLeadingPadding_cons_ne {c : Char} (hc : c ≠ '=') (l : List Char) :
    dropLeadingPadding (c :: l) = c :: l := by
  rw [dropLeadingPadding.eq_def]
  split <;> simp_all

private theorem dropLeadingPadding_replicate_append (k : Nat) (l : List Char)
    (h : ∀ c ∈ l, c ≠ '=') : dropLeadingPadding (List.replicate k '=' ++ l) = l := by
  induction k with
  | zero =>
      cases l with
      | nil => rfl
      | cons c rest => exact dropLeadingPadding_cons_ne (h c (by simp)) rest
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, dropLeadingPadding]
      exact ih

/-- An encoding pass emits a padding-free body followed by at most two `=`
padding characters, and the two together are a multiple of four long. -/
private theorem encodeLoop_split (bytes : ByteArray) (i : Nat) :
    ∃ front k, encodeLoop bytes i = front ++ List.replicate k '=' ∧ k ≤ 2
      ∧ (∀ c ∈ front, c ≠ '=') ∧ (front.length + k) % 4 = 0 := by
  fun_induction encodeLoop bytes i
  next i h h1 h2 ih =>
    obtain ⟨front, k, heq, hk, hne, hlen⟩ := ih
    have b0 : bytes[i].toNat < 256 := UInt8.toNat_lt bytes[i]
    have b1 : bytes[i + 1].toNat < 256 := UInt8.toNat_lt bytes[i + 1]
    have b2 : bytes[i + 2].toNat < 256 := UInt8.toNat_lt bytes[i + 2]
    refine ⟨alphabetChar (bytes[i].toNat / 4)
        :: alphabetChar (bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16)
        :: alphabetChar (bytes[i + 1].toNat % 16 * 4 + bytes[i + 2].toNat / 64)
        :: alphabetChar (bytes[i + 2].toNat % 64) :: front, k, by rw [heq]; rfl, hk, ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | rfl | rfl | rfl | hc
      · exact alphabetChar_ne_pad (by omega)
      · exact alphabetChar_ne_pad (by omega)
      · exact alphabetChar_ne_pad (by omega)
      · exact alphabetChar_ne_pad (by omega)
      · exact hne c hc
    · simp only [List.length_cons]
      omega
  next i h h1 h2 =>
    have b0 : bytes[i].toNat < 256 := UInt8.toNat_lt bytes[i]
    have b1 : bytes[i + 1].toNat < 256 := UInt8.toNat_lt bytes[i + 1]
    refine ⟨[alphabetChar (bytes[i].toNat / 4),
        alphabetChar (bytes[i].toNat % 4 * 16 + bytes[i + 1].toNat / 16),
        alphabetChar (bytes[i + 1].toNat % 16 * 4)], 1, rfl, by omega, ?_, by simp⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact alphabetChar_ne_pad (by omega)
    · exact alphabetChar_ne_pad (by omega)
    · exact alphabetChar_ne_pad (by omega)
  next i h h1 =>
    have b0 : bytes[i].toNat < 256 := UInt8.toNat_lt bytes[i]
    refine ⟨[alphabetChar (bytes[i].toNat / 4), alphabetChar (bytes[i].toNat % 4 * 16)], 2,
      rfl, by omega, ?_, by simp⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact alphabetChar_ne_pad (by omega)
    · exact alphabetChar_ne_pad (by omega)
  next i h =>
    exact ⟨[], 0, rfl, by omega, by simp, by simp⟩

/-- Base64 decoding inverts the unpadded encoder used for `-bin` metadata:
the decoder restores the stripped `=` padding before decoding. -/
theorem decodeBytes_encodeBytesUnpadded (bytes : ByteArray) :
    decodeBytes (encodeBytesUnpadded bytes) = .ok bytes := by
  obtain ⟨front, k, heq, hk, hne, hlen⟩ := encodeLoop_split bytes 0
  have hunpadded : encodeBytesUnpadded bytes = String.ofList front := by
    unfold encodeBytesUnpadded encodeBytes
    rw [String.toList_ofList, heq, List.reverse_append, List.reverse_replicate,
      dropLeadingPadding_replicate_append k front.reverse
        (fun c hc => hne c (List.mem_reverse.mp hc)),
      List.reverse_reverse]
  have hpad : ∃ s, paddedInput (encodeBytesUnpadded bytes) = .ok s
      ∧ s.toList = encodeLoop bytes 0 := by
    rw [hunpadded]
    unfold paddedInput
    rw [String.toList_ofList]
    match k, hk, hlen with
    | 0, _, hlen =>
        refine ⟨String.ofList front, ?_, ?_⟩
        · rw [show front.length % 4 = 0 from by omega]
          rfl
        · rw [String.toList_ofList, heq, List.replicate_zero, List.append_nil]
    | 1, _, hlen =>
        refine ⟨String.ofList front ++ "=", ?_, ?_⟩
        · rw [show front.length % 4 = 3 from by omega]
          rfl
        · rw [String.toList_append, String.toList_ofList, heq]
          rfl
    | 2, _, hlen =>
        refine ⟨String.ofList front ++ "==", ?_, ?_⟩
        · rw [show front.length % 4 = 2 from by omega]
          rfl
        · rw [String.toList_append, String.toList_ofList, heq]
          rfl
  obtain ⟨s, hs, hlist⟩ := hpad
  unfold decodeBytes
  simp only [bind, Except.bind, hs]
  rw [hlist, decodeLoop_encodeLoop, ByteArray.extract_zero_size, ByteArray.empty_append]

end Base64

namespace Metadata

private def binaryKey (name : String) : String :=
  let key := Header.normalizeName name
  if key.endsWith "-bin" then key else key ++ "-bin"

def insertBinary (metadata : Metadata) (name : String) (bytes : ByteArray) : Metadata :=
  metadata.insert (binaryKey name) (Base64.encodeBytesUnpadded bytes)

private def binaryValues (value : String) : List String :=
  value.splitOn ","

private def decodeBinaryValue (name value : String) : Except String ByteArray :=
  match Base64.decodeBytes value with
  | .ok bytes => .ok bytes
  | .error err => .error s!"invalid binary gRPC metadata {name}: {err}"

private def decodeBinaryHeaderValue (name value : String) : Except String (Array ByteArray) :=
  (binaryValues value).foldlM (init := #[]) fun values part => do
    pure (values.push (← decodeBinaryValue name part))

def getBinaryAll (metadata : Metadata) (name : String) : Except String (Array ByteArray) :=
  let key := binaryKey name
  (metadata.getAll key).foldlM (init := #[]) fun values value => do
    pure (values.append (← decodeBinaryHeaderValue key value))

def getBinary? (metadata : Metadata) (name : String) : Except String (Option ByteArray) := do
  pure (← metadata.getBinaryAll name)[0]?

private def knownPseudoHeader (name : String) : Bool :=
  name == ":method"
    || name == ":scheme"
    || name == ":path"
    || name == ":authority"
    || name == ":status"

def validHeaderName (name : String) : Bool :=
  if name.startsWith ":" then
    knownPseudoHeader name
  else
    Ascii.validHeaderName name

private def forbiddenHttp2HeaderName (name : String) : Bool :=
  name == "connection"
    || name == "keep-alive"
    || name == "proxy-connection"
    || name == "transfer-encoding"
    || name == "upgrade"

private def validatePseudoHeaders (metadata : Metadata) : Except Status Unit := do
  let _ ← metadata.foldlM (init := (false, (#[] : Array String))) fun state header => do
    let (seenRegular, seenPseudo) := state
    let name := header.name
    if name.startsWith ":" then
      if seenRegular then
        throw (Status.invalidArgument s!"HTTP/2 pseudo-header {name} appeared after regular metadata")
      else if seenPseudo.contains name then
        throw (Status.invalidArgument s!"duplicate HTTP/2 pseudo-header {name}")
      else
        pure (seenRegular, seenPseudo.push name)
    else
      pure (true, seenPseudo)
  pure ()

def validateHeader (header : Header) : Except Status Unit := do
  if !validHeaderName header.name then
    throw (Status.invalidArgument s!"invalid gRPC metadata name {header.name}")
  if forbiddenHttp2HeaderName header.name then
    throw (Status.invalidArgument s!"HTTP/2 connection-specific metadata is forbidden: {header.name}")
  if header.isBinary then
    match decodeBinaryHeaderValue header.name header.value with
    | .ok _ => pure ()
    | .error err => throw (Status.invalidArgument err)
  else if Ascii.isVisibleString header.value then
    pure ()
  else
    throw (Status.invalidArgument s!"invalid ASCII gRPC metadata value for {header.name}")

def validate (metadata : Metadata) : Except Status Unit := do
  validatePseudoHeaders metadata
  metadata.forM validateHeader

end Metadata

end Grpc
