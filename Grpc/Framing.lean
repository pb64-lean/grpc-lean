module

public import Grpc.Status
import Zlib.Gzip

public section

namespace Grpc

inductive CompressionFlag where
  | identity
  | compressed
  deriving Inhabited, Repr, DecidableEq

namespace CompressionFlag

def toUInt8 : CompressionFlag -> UInt8
  | .identity => 0
  | .compressed => 1

def ofUInt8? : UInt8 -> Option CompressionFlag
  | 0 => some .identity
  | 1 => some .compressed
  | _ => none

theorem ofUInt8?_toUInt8 (flag : CompressionFlag) : ofUInt8? flag.toUInt8 = some flag := by
  cases flag <;> rfl

end CompressionFlag

structure Message where
  compressed : CompressionFlag := .identity
  data : ByteArray
  deriving Inhabited, DecidableEq

namespace Message

def maxWireLength : Nat := 4294967295

/-- Length of the per-message wire prefix: 1 compressed-flag byte + 4 length bytes. -/
@[expose] def prefixLength : Nat := 5

private def uint32BE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat (n % 256)]

private def readUInt32BE (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 16777216
    + bytes[offset + 1]!.toNat * 65536
    + bytes[offset + 2]!.toNat * 256
    + bytes[offset + 3]!.toNat

def encode (message : Message) : Except Status ByteArray :=
  let len := message.data.size
  if len > maxWireLength then
    .error (Status.internal "gRPC message exceeds 32-bit wire length")
  else
    .ok <| ByteArray.empty
      |>.push message.compressed.toUInt8
      |>.append (uint32BE len)
      |>.append message.data

structure DecodeState where
  buffered : ByteArray := ByteArray.empty
  messages : Array Message := #[]
  deriving Inhabited

private def checkDataSize (maxDataSize? : Option Nat) (len : Nat) : Except Status Unit :=
  match maxDataSize? with
  | none => .ok ()
  | some maxDataSize =>
      if len > maxDataSize then
        .error (Status.resourceExhausted s!"gRPC message exceeds configured size limit {maxDataSize}")
      else
        .ok ()

/-- Parse one length-prefixed message from the front of `buffered`: `none`
when more bytes are needed, otherwise the message and the residual bytes. -/
private def parseFrame? (maxDataSize? : Option Nat) (buffered : ByteArray) :
    Except Status (Option (Message × ByteArray)) :=
  if buffered.size < 5 then
    .ok none
  else
    match CompressionFlag.ofUInt8? buffered[0]! with
    | none => .error (Status.internal s!"invalid gRPC compression flag {buffered[0]!.toNat}")
    | some flag =>
        match checkDataSize maxDataSize? (readUInt32BE buffered 1) with
        | .error status => .error status
        | .ok () =>
            if buffered.size < 5 + readUInt32BE buffered 1 then
              .ok none
            else
              .ok (some ({
                compressed := flag,
                data := buffered.extract 5 (5 + readUInt32BE buffered 1)
              }, buffered.extract (5 + readUInt32BE buffered 1) buffered.size))

private theorem parseFrame?_rest_size {maxDataSize? : Option Nat} {buffered : ByteArray}
    {message : Message} {rest : ByteArray}
    (h : parseFrame? maxDataSize? buffered = .ok (some (message, rest))) :
    rest.size < buffered.size := by
  unfold parseFrame? at h
  split at h
  next => cases h
  next h5 =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next =>
        split at h
        next => cases h
        next =>
          cases h
          simp only [ByteArray.size_extract]
          omega

private def parseBuffered (maxDataSize? : Option Nat) (buffered : ByteArray)
    (messages : Array Message) :
    Except Status DecodeState :=
  match h : parseFrame? maxDataSize? buffered with
  | .error status => .error status
  | .ok none => .ok { buffered := buffered, messages := messages }
  | .ok (some (message, rest)) => parseBuffered maxDataSize? rest (messages.push message)
  termination_by buffered.size
  decreasing_by exact parseFrame?_rest_size h

def decodeChunkWithLimit (maxDataSize? : Option Nat) (state : DecodeState) (chunk : ByteArray) :
    Except Status DecodeState :=
  parseBuffered maxDataSize? (state.buffered.append chunk) #[]

def decodeChunk (state : DecodeState) (chunk : ByteArray) : Except Status DecodeState :=
  decodeChunkWithLimit none state chunk

def decodeAllWithLimit (maxDataSize? : Option Nat) (bytes : ByteArray) :
    Except Status (Array Message) := do
  let state ← parseBuffered maxDataSize? bytes #[]
  if state.buffered.isEmpty then
    pure state.messages
  else
    throw (Status.internal "incomplete gRPC message")

def decodeAll (bytes : ByteArray) : Except Status (Array Message) := do
  decodeAllWithLimit none bytes

/-!
### Codec laws

`encode`/`decodeAll` inversion with residual bytes, and the size-limit
guarantee for `decodeAllWithLimit`:

* `decodeAllWithLimit_encode_append` / `decodeAll_encode_append` — decoding
  `encode x ++ rest` yields `x` followed by whatever `rest` decodes to;
* `decodeAll_encode` — a single encoded message decodes to exactly that
  message;
* `decodeAllWithLimit_size_le` — a successful size-limited decode never
  returns a message whose payload exceeds the limit.
-/

private theorem append_eq (a b : ByteArray) : a.append b = a ++ b := rfl

private theorem throw_eq (e : Status) {α : Type} :
    (throw e : Except Status α) = .error e := rfl

private theorem map_error {α β : Type} (f : α -> β) (e : Status) :
    (Except.error e : Except Status α).map f = .error e := rfl

private theorem map_ok {α β : Type} (f : α -> β) (v : α) :
    (Except.ok v : Except Status α).map f = .ok (f v) := rfl

private theorem encode_ok {x : Message} {bs : ByteArray} (h : encode x = .ok bs) :
    x.data.size ≤ maxWireLength
      ∧ bs = ByteArray.empty.push x.compressed.toUInt8 ++ uint32BE x.data.size ++ x.data := by
  simp only [encode] at h
  split at h
  next => cases h
  next hle => cases h; exact ⟨by omega, rfl⟩

private theorem get!_encodeFlag (f : UInt8) (u data rest : ByteArray) :
    (ByteArray.empty.push f ++ u ++ data ++ rest)[0]! = f := by
  have hp : (ByteArray.empty.push f).size = 1 := rfl
  have h1 : 0 < (ByteArray.empty.push f ++ u).size := by
    simp only [ByteArray.size_append, hp]; omega
  have h2 : 0 < (ByteArray.empty.push f ++ u ++ data).size := by
    simp only [ByteArray.size_append, hp]; omega
  have h3 : 0 < (ByteArray.empty.push f ++ u ++ data ++ rest).size := by
    simp only [ByteArray.size_append, hp]; omega
  rw [getElem!_pos (ByteArray.empty.push f ++ u ++ data ++ rest) 0 h3,
    ByteArray.getElem_append_left h2, ByteArray.getElem_append_left h1,
    ByteArray.getElem_append_left (by omega)]
  rfl

private theorem get!_encodePrefix (f : UInt8) (u data rest : ByteArray) {i j : Nat}
    (hij : i = 1 + j) (hj : j < u.size) :
    (ByteArray.empty.push f ++ u ++ data ++ rest)[i]! = u[j] := by
  subst hij
  have hp : (ByteArray.empty.push f).size = 1 := rfl
  have h1 : 1 + j < (ByteArray.empty.push f ++ u).size := by
    simp only [ByteArray.size_append, hp]; omega
  have h2 : 1 + j < (ByteArray.empty.push f ++ u ++ data).size := by
    simp only [ByteArray.size_append, hp]; omega
  have h3 : 1 + j < (ByteArray.empty.push f ++ u ++ data ++ rest).size := by
    simp only [ByteArray.size_append, hp]; omega
  rw [getElem!_pos (ByteArray.empty.push f ++ u ++ data ++ rest) (1 + j) h3,
    ByteArray.getElem_append_left h2, ByteArray.getElem_append_left h1,
    ByteArray.getElem_append_right (by omega)]
  simp only [hp, Nat.add_sub_cancel_left]

private theorem uint32BE_getElem_zero (n : Nat) {h : 0 < (uint32BE n).size} :
    (uint32BE n)[0] = UInt8.ofNat ((n / 16777216) % 256) := rfl

private theorem uint32BE_getElem_one (n : Nat) {h : 1 < (uint32BE n).size} :
    (uint32BE n)[1] = UInt8.ofNat ((n / 65536) % 256) := rfl

private theorem uint32BE_getElem_two (n : Nat) {h : 2 < (uint32BE n).size} :
    (uint32BE n)[2] = UInt8.ofNat ((n / 256) % 256) := rfl

private theorem uint32BE_getElem_three (n : Nat) {h : 3 < (uint32BE n).size} :
    (uint32BE n)[3] = UInt8.ofNat (n % 256) := rfl

private theorem readUInt32BE_encode (f : UInt8) (len : Nat) (hlen : len ≤ maxWireLength)
    (data rest : ByteArray) :
    readUInt32BE (ByteArray.empty.push f ++ uint32BE len ++ data ++ rest) 1 = len := by
  have hu : (uint32BE len).size = 4 := rfl
  unfold readUInt32BE
  rw [get!_encodePrefix f (uint32BE len) data rest (i := 1) (j := 0) rfl (by omega),
    get!_encodePrefix f (uint32BE len) data rest (i := 1 + 1) (j := 1) rfl (by omega),
    get!_encodePrefix f (uint32BE len) data rest (i := 1 + 2) (j := 2) rfl (by omega),
    get!_encodePrefix f (uint32BE len) data rest (i := 1 + 3) (j := 3) rfl (by omega)]
  rw [uint32BE_getElem_zero, uint32BE_getElem_one, uint32BE_getElem_two,
    uint32BE_getElem_three]
  simp only [UInt8.toNat_ofNat', Nat.reducePow]
  simp only [maxWireLength] at hlen
  omega

private theorem checkDataSize_le {maxDataSize? : Option Nat} {len : Nat}
    (hlim : ∀ maxDataSize, maxDataSize? = some maxDataSize -> len ≤ maxDataSize) :
    checkDataSize maxDataSize? len = .ok () := by
  cases maxDataSize? with
  | none => rfl
  | some maxDataSize =>
      have hle := hlim maxDataSize rfl
      simp only [checkDataSize]
      rw [if_neg (by omega)]

private theorem checkDataSize_ok {maxDataSize len : Nat}
    (h : checkDataSize (some maxDataSize) len = .ok ()) : len ≤ maxDataSize := by
  simp only [checkDataSize] at h
  split at h
  next => cases h
  next hcond => omega

/-- Parsing one frame from `encode x ++ rest` recovers `x` and leaves exactly
`rest`. -/
private theorem parseFrame?_encode {x : Message} {bs : ByteArray}
    (henc : encode x = .ok bs) {maxDataSize? : Option Nat}
    (hchk : checkDataSize maxDataSize? x.data.size = .ok ())
    (rest : ByteArray) :
    parseFrame? maxDataSize? (bs ++ rest) = .ok (some (x, rest)) := by
  obtain ⟨hlen, rfl⟩ := encode_ok henc
  have hp : (ByteArray.empty.push x.compressed.toUInt8).size = 1 := rfl
  have hu : (uint32BE x.data.size).size = 4 := rfl
  have hsz : (ByteArray.empty.push x.compressed.toUInt8 ++ uint32BE x.data.size
      ++ x.data ++ rest).size = 5 + x.data.size + rest.size := by
    simp only [ByteArray.size_append, hp, hu]
  have hA : (ByteArray.empty.push x.compressed.toUInt8 ++ uint32BE x.data.size
      ++ x.data).size = 5 + x.data.size := by
    simp only [ByteArray.size_append, hp, hu]
  have hflag := get!_encodeFlag x.compressed.toUInt8 (uint32BE x.data.size) x.data rest
  have hread := readUInt32BE_encode x.compressed.toUInt8 x.data.size hlen x.data rest
  have hdata : (ByteArray.empty.push x.compressed.toUInt8 ++ uint32BE x.data.size
      ++ x.data ++ rest).extract 5 (5 + x.data.size) = x.data := by
    rw [ByteArray.extract_append, hA]
    rw [show (5 : Nat) - (5 + x.data.size) = 0 from by omega, Nat.sub_self]
    rw [show rest.extract 0 0 = ByteArray.empty from by simp, ByteArray.append_empty]
    exact ByteArray.extract_append_eq_right
      (by simp only [ByteArray.size_append, hp, hu])
      (by simp only [ByteArray.size_append, hp, hu])
  have hrest : (ByteArray.empty.push x.compressed.toUInt8 ++ uint32BE x.data.size
      ++ x.data ++ rest).extract (5 + x.data.size)
        (ByteArray.empty.push x.compressed.toUInt8 ++ uint32BE x.data.size
          ++ x.data ++ rest).size = rest := by
    rw [hsz]
    exact ByteArray.extract_append_eq_right hA.symm (by rw [hA])
  unfold parseFrame?
  rw [if_neg (by omega)]
  rw [hflag, CompressionFlag.ofUInt8?_toUInt8]
  simp only [hread, hchk]
  rw [if_neg (by omega)]
  rw [hdata, hrest]

private theorem parseFrame?_checkDataSize {maxDataSize? : Option Nat} {buffered : ByteArray}
    {message : Message} {rest : ByteArray}
    (h : parseFrame? maxDataSize? buffered = .ok (some (message, rest))) :
    checkDataSize maxDataSize? (readUInt32BE buffered 1) = .ok ()
      ∧ message.data = buffered.extract 5 (5 + readUInt32BE buffered 1) := by
  unfold parseFrame? at h
  split at h
  next => cases h
  next h5 =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next hchk =>
        split at h
        next => cases h
        next =>
          cases h
          exact ⟨hchk, rfl⟩

private theorem parseFrame?_size_le {maxDataSize : Nat} {buffered : ByteArray}
    {message : Message} {rest : ByteArray}
    (h : parseFrame? (some maxDataSize) buffered = .ok (some (message, rest))) :
    message.data.size ≤ maxDataSize := by
  obtain ⟨hchk, hdata⟩ := parseFrame?_checkDataSize h
  have hle := checkDataSize_ok hchk
  rw [hdata]
  simp only [ByteArray.size_extract]
  omega

/-- Non-dependent one-step unfolding of `parseBuffered`. -/
private theorem parseBuffered_step (maxDataSize? : Option Nat) (buffered : ByteArray)
    (messages : Array Message) :
    parseBuffered maxDataSize? buffered messages
      = match parseFrame? maxDataSize? buffered with
        | .error status => .error status
        | .ok none => .ok { buffered := buffered, messages := messages }
        | .ok (some (message, rest)) => parseBuffered maxDataSize? rest (messages.push message) := by
  conv => lhs; rw [parseBuffered.eq_def]
  split <;> rename_i heq <;> rw [heq]

/-- One `encode`d message at the front of the buffer parses off in a single
`parseBuffered` step, leaving the residual bytes. -/
private theorem parseBuffered_encode_append {x : Message} {bs : ByteArray}
    (henc : encode x = .ok bs) {maxDataSize? : Option Nat}
    (hchk : checkDataSize maxDataSize? x.data.size = .ok ())
    (rest : ByteArray) (messages : Array Message) :
    parseBuffered maxDataSize? (bs ++ rest) messages
      = parseBuffered maxDataSize? rest (messages.push x) := by
  rw [parseBuffered_step, parseFrame?_encode henc hchk rest]

/-- The message accumulator only prepends: parsing with accumulator
`prefixMessages ++ extra` is parsing with `extra` and prepending. -/
private theorem parseBuffered_append_acc (maxDataSize? : Option Nat) (buffered : ByteArray)
    (prefixMessages extra : Array Message) :
    parseBuffered maxDataSize? buffered (prefixMessages ++ extra)
      = (parseBuffered maxDataSize? buffered extra).map
          (fun state => { state with messages := prefixMessages ++ state.messages }) := by
  fun_induction parseBuffered maxDataSize? buffered extra
  next hcase =>
    rw [parseBuffered_step]
    simp only [hcase, map_error]
  next hcase =>
    rw [parseBuffered_step]
    simp only [hcase, map_ok]
  next message rest hcase ih =>
    rw [parseBuffered_step]
    simp only [hcase]
    rw [Array.push_append]
    exact ih

private theorem parseBuffered_acc (maxDataSize? : Option Nat) (buffered : ByteArray)
    (messages : Array Message) :
    parseBuffered maxDataSize? buffered messages
      = (parseBuffered maxDataSize? buffered #[]).map
          (fun state => { state with messages := messages ++ state.messages }) := by
  have h := parseBuffered_append_acc maxDataSize? buffered messages #[]
  rw [Array.append_empty] at h
  exact h

private theorem parseBuffered_size_le {maxDataSize : Nat} {buffered : ByteArray}
    {messages : Array Message} {state : DecodeState}
    (h : parseBuffered (some maxDataSize) buffered messages = .ok state)
    (hacc : ∀ message ∈ messages, message.data.size ≤ maxDataSize) :
    ∀ message ∈ state.messages, message.data.size ≤ maxDataSize := by
  revert h hacc
  fun_induction parseBuffered (some maxDataSize) buffered messages
  next => exact fun h _ => nomatch h
  next => exact fun h hacc => by cases h; exact hacc
  next message rest hcase ih =>
    intro h hacc
    refine ih h ?_
    intro m hm
    cases Array.mem_push.mp hm with
    | inl hmem => exact hacc m hmem
    | inr heq => exact heq ▸ parseFrame?_size_le hcase

private theorem decodeChunkWithLimit_empty (maxDataSize? : Option Nat) (bytes : ByteArray) :
    decodeChunkWithLimit maxDataSize? {} bytes = parseBuffered maxDataSize? bytes #[] := by
  unfold decodeChunkWithLimit
  rw [show ({} : DecodeState).buffered.append bytes = bytes from ByteArray.empty_append]

theorem decodeAll_empty : decodeAll ByteArray.empty = .ok #[] := by
  unfold decodeAll decodeAllWithLimit
  simp only [bind, Except.bind, pure, Except.pure]
  rw [parseBuffered.eq_def]
  rfl

/-- Residual-byte inversion: decoding `encode x ++ rest` under a limit that
admits `x` yields `x` followed by whatever `rest` decodes to. -/
theorem decodeAllWithLimit_encode_append {x : Message} {bs : ByteArray}
    (henc : encode x = .ok bs) {maxDataSize? : Option Nat}
    (hlim : ∀ maxDataSize, maxDataSize? = some maxDataSize -> x.data.size ≤ maxDataSize)
    (rest : ByteArray) :
    decodeAllWithLimit maxDataSize? (bs ++ rest)
      = (decodeAllWithLimit maxDataSize? rest).map (fun messages => #[x] ++ messages) := by
  have hchk := checkDataSize_le hlim
  unfold decodeAllWithLimit
  simp only [bind, Except.bind, pure, Except.pure, throw_eq]
  rw [parseBuffered_encode_append henc hchk rest #[]]
  rw [show (#[] : Array Message).push x = #[x] from rfl]
  rw [parseBuffered_acc maxDataSize? rest #[x]]
  cases hres : parseBuffered maxDataSize? rest #[] with
  | error status => simp only [map_error]
  | ok state =>
      simp only [map_ok]
      cases hbuf : state.buffered.isEmpty <;> simp [map_ok, map_error]

/-- Residual-byte inversion for the unlimited decoder. -/
theorem decodeAll_encode_append {x : Message} {bs : ByteArray}
    (henc : encode x = .ok bs) (rest : ByteArray) :
    decodeAll (bs ++ rest) = (decodeAll rest).map (fun messages => #[x] ++ messages) := by
  unfold decodeAll
  exact decodeAllWithLimit_encode_append (maxDataSize? := none) henc
    (fun _ h => nomatch h) rest

/-- A single encoded message decodes to exactly that message. -/
theorem decodeAll_encode {x : Message} {bs : ByteArray} (henc : encode x = .ok bs) :
    decodeAll bs = .ok #[x] := by
  have h := decodeAll_encode_append henc ByteArray.empty
  rw [ByteArray.append_empty] at h
  simp only [h, decodeAll_empty, map_ok, Array.append_empty]

/-- A successful size-limited decode never returns an oversized message. -/
theorem decodeAllWithLimit_size_le {maxDataSize : Nat} {bytes : ByteArray}
    {messages : Array Message}
    (h : decodeAllWithLimit (some maxDataSize) bytes = .ok messages) :
    ∀ message ∈ messages, message.data.size ≤ maxDataSize := by
  unfold decodeAllWithLimit at h
  simp only [bind, Except.bind, pure, Except.pure, throw_eq] at h
  split at h
  next => cases h
  next state hstate =>
    split at h
    next =>
        cases h
        exact parseBuffered_size_le hstate (fun m hm => by simp at hm)
    next => cases h

/-! ### Wire-byte conservation

The HTTP/2 receive window is charged in wire bytes, but stream flow-control
credit is only returned once a whole gRPC message has been decoded and
consumed.  The lemmas below are what make that accounting exact: every byte
handed to the decoder is either accounted for by a completed message (its
`wireSize`) or is still sitting in the decoder's buffer.  `Grpc.Http2.Connection`
turns this into the credit-on-consume conservation law. -/

/-- Wire bytes one message occupies: the 5-byte length prefix plus its data. -/
def wireSize (message : Message) : Nat := prefixLength + message.data.size

/-- Total wire bytes of a batch of decoded messages. -/
def messagesWireSize (messages : Array Message) : Nat :=
  messages.foldl (fun total message => total + wireSize message) 0

@[simp] theorem messagesWireSize_empty : messagesWireSize #[] = 0 := by rfl

theorem messagesWireSize_eq_foldl (messages : Array Message) :
    messagesWireSize messages
      = messages.foldl (fun total message => total + (prefixLength + message.data.size)) 0 := by
  rfl

theorem messagesWireSize_push (messages : Array Message) (message : Message) :
    messagesWireSize (messages.push message)
      = messagesWireSize messages + wireSize message := by
  simp only [messagesWireSize, Array.foldl_push]

/-- Parsing one message off the front of the buffer consumes exactly that
message's wire size. -/
private theorem parseFrame?_conserves {maxDataSize? : Option Nat} {buffered : ByteArray}
    {message : Message} {rest : ByteArray}
    (h : parseFrame? maxDataSize? buffered = .ok (some (message, rest))) :
    rest.size + wireSize message = buffered.size := by
  unfold parseFrame? at h
  split at h
  next => cases h
  next h5 =>
    split at h
    next => cases h
    next =>
      split at h
      next => cases h
      next =>
        split at h
        next => cases h
        next hfit =>
          cases h
          simp only [wireSize, prefixLength, ByteArray.size_extract]
          omega

/-- Whatever the decoder does with a buffer, no byte is lost: the residual
buffer plus the wire size of every message it produced is exactly the input. -/
private theorem parseBuffered_conserves {maxDataSize? : Option Nat} {buffered : ByteArray}
    {messages : Array Message} {state : DecodeState}
    (h : parseBuffered maxDataSize? buffered messages = .ok state) :
    state.buffered.size + messagesWireSize state.messages
      = buffered.size + messagesWireSize messages := by
  revert h
  fun_induction parseBuffered maxDataSize? buffered messages
  next => exact fun h => nomatch h
  next =>
    intro h
    injection h with h
    subst h
    rfl
  next hcase ih =>
    intro h
    have hstep := parseFrame?_conserves hcase
    have hih := ih h
    rw [messagesWireSize_push] at hih
    omega

/-- Feeding a chunk to the message decoder conserves bytes: the bytes still
buffered plus the wire size of the messages just completed equal the bytes that
were buffered plus the chunk. -/
theorem decodeChunkWithLimit_conserves {maxDataSize? : Option Nat} {state : DecodeState}
    {chunk : ByteArray} {state' : DecodeState}
    (h : decodeChunkWithLimit maxDataSize? state chunk = .ok state') :
    state'.buffered.size + messagesWireSize state'.messages
      = state.buffered.size + chunk.size := by
  unfold decodeChunkWithLimit at h
  have := parseBuffered_conserves h
  rw [messagesWireSize_empty, Nat.add_zero, append_eq, ByteArray.size_append] at this
  exact this

/-- Default cap on the inflated size of a single gzip-compressed message. -/
@[expose] def defaultMaxDecompressedSize : Nat := 4194304

/-- Messages at or above this size are gzip-compressed when response
compression is negotiated; smaller messages keep the identity flag. -/
def gzipCompressThreshold : Nat := 1024

private def clampUInt32 (n : Nat) : UInt32 :=
  if n < 4294967296 then UInt32.ofNat n else 4294967295

/-- Resolve a message's per-message compression flag. `usesGzip` records
whether the request declared `grpc-encoding: gzip`. A compressed flag without
a matching encoding is an `INTERNAL` error per the gRPC spec. -/
def decompress (usesGzip : Bool) (maxSize : Nat) (message : Message) :
    Except Status Message := do
  match message.compressed with
  | .identity => pure message
  | .compressed =>
      if !usesGzip then
        throw (Status.internal
          "gRPC message has the compressed flag set without a message encoding")
      else
        match Zlib.Gzip.decompress message.data (clampUInt32 maxSize) with
        | some data => pure { compressed := .identity, data := data }
        | none => throw (Status.internal "failed to decompress gzip gRPC message")

/-- Build a message for `data`, gzip-compressing it when it meets the size
threshold; smaller payloads keep the identity flag (allowed per-message). -/
def gzipped (data : ByteArray) : Message :=
  if data.size >= gzipCompressThreshold then
    { compressed := .compressed, data := Zlib.Gzip.compress data }
  else
    { data := data }

/-- Decode a length-prefixed request body, decompress any gzip-compressed
messages, and re-encode with identity flags so downstream handlers see plain
payloads. Bodies with no compressed messages pass through unchanged. -/
def decompressBody (usesGzip : Bool) (maxDataSize? : Option Nat) (body : ByteArray) :
    Except Status ByteArray := do
  let messages ← decodeAllWithLimit maxDataSize? body
  if messages.all (fun message => message.compressed == .identity) then
    pure body
  else
    let maxSize := maxDataSize?.getD defaultMaxDecompressedSize
    messages.foldlM (init := ByteArray.empty) fun out message => do
      let message ← decompress usesGzip maxSize message
      let encoded ← encode message
      pure (out.append encoded)

end Message

end Grpc
