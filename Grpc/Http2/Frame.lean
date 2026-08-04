module

public import Grpc.Status

public section

namespace Grpc
namespace Http2

def connectionPrefaceString : String :=
  "PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n"

def connectionPreface : ByteArray :=
  connectionPrefaceString.toUTF8

def frameHeaderSize : Nat := 9

def maxFramePayloadLength : Nat := 16777215

def defaultMaxFramePayloadLength : Nat := 16384

@[expose] def maxStreamId : Nat := 2147483647

inductive FrameType where
  | data
  | headers
  | priority
  | rstStream
  | settings
  | pushPromise
  | ping
  | goAway
  | windowUpdate
  | continuation
  | unknown (value : UInt8)
  deriving Inhabited, Repr, DecidableEq

namespace FrameType

def toUInt8 : FrameType -> UInt8
  | .data => 0
  | .headers => 1
  | .priority => 2
  | .rstStream => 3
  | .settings => 4
  | .pushPromise => 5
  | .ping => 6
  | .goAway => 7
  | .windowUpdate => 8
  | .continuation => 9
  | .unknown value => value

def ofUInt8 : UInt8 -> FrameType
  | 0 => .data
  | 1 => .headers
  | 2 => .priority
  | 3 => .rstStream
  | 4 => .settings
  | 5 => .pushPromise
  | 6 => .ping
  | 7 => .goAway
  | 8 => .windowUpdate
  | 9 => .continuation
  | value => .unknown value

end FrameType

inductive ErrorCode where
  | noError
  | protocolError
  | internalError
  | flowControlError
  | settingsTimeout
  | streamClosed
  | frameSizeError
  | refusedStream
  | cancel
  | compressionError
  | connectError
  | enhanceYourCalm
  | inadequateSecurity
  | http11Required
  | unknown (value : Nat)
  deriving Inhabited, Repr, DecidableEq

namespace ErrorCode

def toNat : ErrorCode -> Nat
  | .noError => 0
  | .protocolError => 1
  | .internalError => 2
  | .flowControlError => 3
  | .settingsTimeout => 4
  | .streamClosed => 5
  | .frameSizeError => 6
  | .refusedStream => 7
  | .cancel => 8
  | .compressionError => 9
  | .connectError => 10
  | .enhanceYourCalm => 11
  | .inadequateSecurity => 12
  | .http11Required => 13
  | .unknown value => value

def ofNat : Nat -> ErrorCode
  | 0 => .noError
  | 1 => .protocolError
  | 2 => .internalError
  | 3 => .flowControlError
  | 4 => .settingsTimeout
  | 5 => .streamClosed
  | 6 => .frameSizeError
  | 7 => .refusedStream
  | 8 => .cancel
  | 9 => .compressionError
  | 10 => .connectError
  | 11 => .enhanceYourCalm
  | 12 => .inadequateSecurity
  | 13 => .http11Required
  | value => .unknown value

end ErrorCode

structure FrameHeader where
  length : Nat
  frameType : FrameType
  flags : UInt8 := 0
  streamId : Nat := 0
  deriving Inhabited, Repr, DecidableEq

structure Frame where
  header : FrameHeader
  payload : ByteArray := ByteArray.empty
  deriving Inhabited, DecidableEq

namespace FrameFlag

def endStream : UInt8 := 0x1
def endHeaders : UInt8 := 0x4
def padded : UInt8 := 0x8
def priority : UInt8 := 0x20

def has (flags flag : UInt8) : Bool :=
  flag.toNat != 0 && ((flags.toNat / flag.toNat) % 2 == 1)

def combine (flags : Array UInt8) : UInt8 :=
  UInt8.ofNat (flags.foldl (fun acc flag => acc + flag.toNat) 0)

end FrameFlag

namespace Frame

private def u24BE (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

private def u31BE (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (UInt8.ofNat ((n / 16777216) % 128))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

private def u16BE (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

private def u32BE (n : Nat) : ByteArray :=
  ByteArray.empty
    |>.push (UInt8.ofNat ((n / 16777216) % 256))
    |>.push (UInt8.ofNat ((n / 65536) % 256))
    |>.push (UInt8.ofNat ((n / 256) % 256))
    |>.push (UInt8.ofNat (n % 256))

private def readUInt16BE (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 256 + bytes[offset + 1]!.toNat

private def readUInt24BE (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 65536
    + bytes[offset + 1]!.toNat * 256
    + bytes[offset + 2]!.toNat

private def readUInt32BE (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 16777216
    + bytes[offset + 1]!.toNat * 65536
    + bytes[offset + 2]!.toNat * 256
    + bytes[offset + 3]!.toNat

/-- The 9 header bytes: 24-bit length, type, flags, 31-bit stream id
(big-endian). Kept as a single literal so byte-level proofs reduce by `rfl`. -/
private def headerBytes (header : FrameHeader) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((header.length / 65536) % 256),
    UInt8.ofNat ((header.length / 256) % 256),
    UInt8.ofNat (header.length % 256),
    header.frameType.toUInt8,
    header.flags,
    UInt8.ofNat ((header.streamId / 16777216) % 128),
    UInt8.ofNat ((header.streamId / 65536) % 256),
    UInt8.ofNat ((header.streamId / 256) % 256),
    UInt8.ofNat (header.streamId % 256)]

def encodeHeader (header : FrameHeader) : Except Status ByteArray := do
  if header.length > maxFramePayloadLength then
    throw (Status.internal "HTTP/2 frame payload exceeds 24-bit length")
  if header.streamId > maxStreamId then
    throw (Status.internal "HTTP/2 stream id exceeds 31-bit length")
  pure (headerBytes header)

def decodeHeader (bytes : ByteArray) : Except Status FrameHeader := do
  if bytes.size < frameHeaderSize then
    throw (Status.internal "incomplete HTTP/2 frame header")
  pure {
    length := readUInt24BE bytes 0,
    frameType := FrameType.ofUInt8 bytes[3]!,
    flags := bytes[4]!,
    streamId := readUInt32BE bytes 5 % (maxStreamId + 1)
  }

def encode (frame : Frame) : Except Status ByteArray := do
  if frame.header.length != frame.payload.size then
    throw (Status.internal "HTTP/2 frame header length does not match payload size")
  let header ← encodeHeader frame.header
  pure (header.append frame.payload)

structure DecodeState where
  buffered : ByteArray := ByteArray.empty
  frames : Array Frame := #[]
  deriving Inhabited

/-- Parse one frame from the front of `buffered`: `none` when more bytes are
needed, otherwise the frame and the residual bytes. -/
private def parseFrame? (buffered : ByteArray) :
    Except Status (Option (Frame × ByteArray)) :=
  if buffered.size < frameHeaderSize then
    .ok none
  else
    match decodeHeader (buffered.extract 0 frameHeaderSize) with
    | .error status => .error status
    | .ok header =>
        if buffered.size < frameHeaderSize + header.length then
          .ok none
        else
          .ok (some ({
            header := header,
            payload := buffered.extract frameHeaderSize (frameHeaderSize + header.length)
          }, buffered.extract (frameHeaderSize + header.length) buffered.size))

private theorem parseFrame?_rest_size {buffered : ByteArray} {frame : Frame}
    {rest : ByteArray} (h : parseFrame? buffered = .ok (some (frame, rest))) :
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
        cases h
        simp only [ByteArray.size_extract, frameHeaderSize] at *
        omega

private def parseBuffered (buffered : ByteArray) (frames : Array Frame) :
    Except Status DecodeState :=
  match h : parseFrame? buffered with
  | .error status => .error status
  | .ok none => .ok { buffered := buffered, frames := frames }
  | .ok (some (frame, rest)) => parseBuffered rest (frames.push frame)
  termination_by buffered.size
  decreasing_by exact parseFrame?_rest_size h

def decodeChunk (state : DecodeState) (chunk : ByteArray) : Except Status DecodeState :=
  parseBuffered (state.buffered.append chunk) #[]

def decodeAll (bytes : ByteArray) : Except Status (Array Frame) := do
  let state ← decodeChunk {} bytes
  if state.buffered.isEmpty then
    pure state.frames
  else
    throw (Status.internal "incomplete HTTP/2 frame")

/-!
### Codec laws

Frame-header and whole-frame encode/decode inversion with residual bytes:

* `decodeHeader_encodeHeader_append` — decoding `encodeHeader h ++ rest` reads
  exactly the 9 header bytes and recovers `h`;
* `decodeAll_encode_append` / `decodeAll_encode` — decoding `encode f ++ rest`
  yields `f` followed by whatever `rest` decodes to.

All laws take a canonical-frame-type hypothesis `FrameType.ofUInt8
h.frameType.toUInt8 = h.frameType`, discharged by
`FrameType.ofUInt8_toUInt8` (named constructors) or
`FrameType.ofUInt8_toUInt8_unknown` (`unknown` values `≥ 10`), because e.g.
`FrameType.unknown 0` re-decodes as `.data`.
-/

private theorem map_error {α β : Type} (f : α -> β) (e : Status) :
    (Except.error e : Except Status α).map f = .error e := rfl

private theorem map_ok {α β : Type} (f : α -> β) (v : α) :
    (Except.ok v : Except Status α).map f = .ok (f v) := rfl

private theorem get!_append_left {bytes rest : ByteArray} {i : Nat} (hi : i < bytes.size) :
    (bytes ++ rest)[i]! = bytes[i] := by
  have h : i < (bytes ++ rest).size := by rw [ByteArray.size_append]; omega
  rw [getElem!_pos (bytes ++ rest) i h, ByteArray.getElem_append_left hi]

private theorem headerBytes_size (header : FrameHeader) : (headerBytes header).size = 9 := rfl

private theorem headerBytes_zero (header : FrameHeader) {h : 0 < (headerBytes header).size} :
    (headerBytes header)[0] = UInt8.ofNat ((header.length / 65536) % 256) := rfl

private theorem headerBytes_one (header : FrameHeader) {h : 1 < (headerBytes header).size} :
    (headerBytes header)[1] = UInt8.ofNat ((header.length / 256) % 256) := rfl

private theorem headerBytes_two (header : FrameHeader) {h : 2 < (headerBytes header).size} :
    (headerBytes header)[2] = UInt8.ofNat (header.length % 256) := rfl

private theorem headerBytes_three (header : FrameHeader) {h : 3 < (headerBytes header).size} :
    (headerBytes header)[3] = header.frameType.toUInt8 := rfl

private theorem headerBytes_four (header : FrameHeader) {h : 4 < (headerBytes header).size} :
    (headerBytes header)[4] = header.flags := rfl

private theorem headerBytes_five (header : FrameHeader) {h : 5 < (headerBytes header).size} :
    (headerBytes header)[5] = UInt8.ofNat ((header.streamId / 16777216) % 128) := rfl

private theorem headerBytes_six (header : FrameHeader) {h : 6 < (headerBytes header).size} :
    (headerBytes header)[6] = UInt8.ofNat ((header.streamId / 65536) % 256) := rfl

private theorem headerBytes_seven (header : FrameHeader) {h : 7 < (headerBytes header).size} :
    (headerBytes header)[7] = UInt8.ofNat ((header.streamId / 256) % 256) := rfl

private theorem headerBytes_eight (header : FrameHeader) {h : 8 < (headerBytes header).size} :
    (headerBytes header)[8] = UInt8.ofNat (header.streamId % 256) := rfl

private theorem readUInt24BE_headerBytes (header : FrameHeader) (rest : ByteArray)
    (hlen : header.length ≤ maxFramePayloadLength) :
    readUInt24BE (headerBytes header ++ rest) 0 = header.length := by
  unfold readUInt24BE
  simp only [Nat.reduceAdd]
  rw [get!_append_left (i := 0) (by rw [headerBytes_size]; omega),
    get!_append_left (i := 1) (by rw [headerBytes_size]; omega),
    get!_append_left (i := 2) (by rw [headerBytes_size]; omega)]
  rw [headerBytes_zero, headerBytes_one, headerBytes_two]
  simp only [UInt8.toNat_ofNat', Nat.reducePow]
  simp only [maxFramePayloadLength] at hlen
  omega

private theorem readUInt32BE_headerBytes (header : FrameHeader) (rest : ByteArray)
    (hsid : header.streamId ≤ maxStreamId) :
    readUInt32BE (headerBytes header ++ rest) 5 = header.streamId := by
  unfold readUInt32BE
  simp only [Nat.reduceAdd]
  rw [get!_append_left (i := 5) (by rw [headerBytes_size]; omega),
    get!_append_left (i := 6) (by rw [headerBytes_size]; omega),
    get!_append_left (i := 7) (by rw [headerBytes_size]; omega),
    get!_append_left (i := 8) (by rw [headerBytes_size]; omega)]
  rw [headerBytes_five, headerBytes_six, headerBytes_seven, headerBytes_eight]
  simp only [UInt8.toNat_ofNat', Nat.reducePow]
  simp only [maxStreamId] at hsid
  omega

private theorem encodeHeader_ok {header : FrameHeader} {bs : ByteArray}
    (h : encodeHeader header = .ok bs) :
    header.length ≤ maxFramePayloadLength ∧ header.streamId ≤ maxStreamId
      ∧ bs = headerBytes header := by
  simp only [encodeHeader, bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next h1 =>
    split at h
    next => cases h
    next h2 => cases h; exact ⟨by omega, by omega, rfl⟩

/-- Decoding an encoded frame header with any residual bytes appended reads
exactly the 9 header bytes and recovers the header. -/
theorem decodeHeader_encodeHeader_append {header : FrameHeader} {bs : ByteArray}
    (henc : encodeHeader header = .ok bs)
    (hft : FrameType.ofUInt8 header.frameType.toUInt8 = header.frameType)
    (rest : ByteArray) :
    decodeHeader (bs ++ rest) = .ok header := by
  obtain ⟨hlen, hsid, rfl⟩ := encodeHeader_ok henc
  have hsz : (headerBytes header ++ rest).size = 9 + rest.size := by
    rw [ByteArray.size_append, headerBytes_size]
  simp only [decodeHeader, bind, Except.bind, pure, Except.pure]
  rw [if_neg (by simp only [frameHeaderSize]; omega)]
  rw [readUInt24BE_headerBytes header rest hlen,
    readUInt32BE_headerBytes header rest hsid]
  rw [get!_append_left (i := 3) (by rw [headerBytes_size]; omega),
    get!_append_left (i := 4) (by rw [headerBytes_size]; omega)]
  rw [headerBytes_three, headerBytes_four, hft]
  rw [Nat.mod_eq_of_lt (by simp only [maxStreamId] at *; omega)]

end Frame

namespace FrameType

/-- Round-trip for the named frame types; `unknown` values below 10 re-decode
as the corresponding named type, so they are excluded here. -/
theorem ofUInt8_toUInt8 {frameType : FrameType}
    (h : ∀ value, frameType ≠ .unknown value) :
    ofUInt8 frameType.toUInt8 = frameType := by
  cases frameType <;> first | rfl | exact absurd rfl (h _)

/-- Round-trip for `unknown` frame types with values outside the named
range. -/
theorem ofUInt8_toUInt8_unknown {value : UInt8} (h : 10 ≤ value.toNat) :
    ofUInt8 (FrameType.unknown value).toUInt8 = .unknown value := by
  have hall : ∀ i : Fin 256, 10 ≤ i.val ->
      ofUInt8 (UInt8.ofNat i.val) = .unknown (UInt8.ofNat i.val) := by
    set_option maxRecDepth 4096 in decide
  have := hall ⟨value.toNat, value.toNat_lt⟩ h
  simpa [UInt8.ofNat_toNat] using this

end FrameType

namespace Frame

private theorem throw_eq (e : Status) {α : Type} :
    (throw e : Except Status α) = .error e := rfl

private theorem encode_ok {frame : Frame} {bs : ByteArray} (h : encode frame = .ok bs) :
    frame.header.length = frame.payload.size
      ∧ encodeHeader frame.header = .ok (headerBytes frame.header)
      ∧ bs = headerBytes frame.header ++ frame.payload := by
  simp only [encode, bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next hlen =>
    split at h
    next => cases h
    next hb hhb =>
      obtain ⟨h1, h2, rfl⟩ := encodeHeader_ok hhb
      cases h
      refine ⟨?_, hhb, rfl⟩
      simpa using hlen

private theorem parseFrame?_encode {frame : Frame} {bs : ByteArray}
    (henc : encode frame = .ok bs)
    (hft : FrameType.ofUInt8 frame.header.frameType.toUInt8 = frame.header.frameType)
    (rest : ByteArray) :
    parseFrame? (bs ++ rest) = .ok (some (frame, rest)) := by
  obtain ⟨hlen, hhb, rfl⟩ := encode_ok henc
  have hAsz : (headerBytes frame.header ++ frame.payload).size
      = 9 + frame.payload.size := by
    simp only [ByteArray.size_append, headerBytes_size]
  have hsz : ((headerBytes frame.header ++ frame.payload) ++ rest).size
      = 9 + frame.payload.size + rest.size := by
    simp only [ByteArray.size_append, headerBytes_size]
  have hextract9 : ((headerBytes frame.header ++ frame.payload) ++ rest).extract 0
      frameHeaderSize = headerBytes frame.header := by
    simp only [frameHeaderSize]
    rw [ByteArray.extract_append, hAsz]
    rw [show (0 : Nat) - (9 + frame.payload.size) = 0 from by omega,
      show (9 : Nat) - (9 + frame.payload.size) = 0 from by omega]
    rw [show rest.extract 0 0 = ByteArray.empty from by simp, ByteArray.append_empty]
    exact ByteArray.extract_append_eq_left (by rw [headerBytes_size])
  have hdec : decodeHeader (headerBytes frame.header) = .ok frame.header := by
    have h := decodeHeader_encodeHeader_append hhb hft ByteArray.empty
    rwa [ByteArray.append_empty] at h
  have hpayload : ((headerBytes frame.header ++ frame.payload) ++ rest).extract
      frameHeaderSize (frameHeaderSize + frame.header.length) = frame.payload := by
    simp only [frameHeaderSize, hlen]
    rw [ByteArray.extract_append, hAsz]
    rw [show (9 : Nat) - (9 + frame.payload.size) = 0 from by omega, Nat.sub_self]
    rw [show rest.extract 0 0 = ByteArray.empty from by simp, ByteArray.append_empty]
    exact ByteArray.extract_append_eq_right (by rw [headerBytes_size])
      (by rw [headerBytes_size])
  have hrest : ((headerBytes frame.header ++ frame.payload) ++ rest).extract
      (frameHeaderSize + frame.header.length)
      ((headerBytes frame.header ++ frame.payload) ++ rest).size = rest := by
    simp only [frameHeaderSize, hlen]
    rw [hsz]
    exact ByteArray.extract_append_eq_right hAsz.symm (by rw [hAsz])
  unfold parseFrame?
  rw [if_neg (by simp only [frameHeaderSize, hsz]; omega)]
  simp only [hextract9, hdec]
  rw [if_neg (by simp only [frameHeaderSize, hsz, hlen]; omega)]
  rw [hpayload, hrest]

/-- Non-dependent one-step unfolding of `parseBuffered`. -/
private theorem parseBuffered_step (buffered : ByteArray) (frames : Array Frame) :
    parseBuffered buffered frames
      = match parseFrame? buffered with
        | .error status => .error status
        | .ok none => .ok { buffered := buffered, frames := frames }
        | .ok (some (frame, rest)) => parseBuffered rest (frames.push frame) := by
  conv => lhs; rw [parseBuffered.eq_def]
  split <;> rename_i heq <;> rw [heq]

/-- One encoded frame at the front of the buffer parses off in a single
`parseBuffered` step, leaving the residual bytes. -/
private theorem parseBuffered_encode_append {frame : Frame} {bs : ByteArray}
    (henc : encode frame = .ok bs)
    (hft : FrameType.ofUInt8 frame.header.frameType.toUInt8 = frame.header.frameType)
    (rest : ByteArray) (frames : Array Frame) :
    parseBuffered (bs ++ rest) frames = parseBuffered rest (frames.push frame) := by
  rw [parseBuffered_step, parseFrame?_encode henc hft rest]

/-- The frame accumulator only prepends. -/
private theorem parseBuffered_append_acc (buffered : ByteArray)
    (prefixFrames extra : Array Frame) :
    parseBuffered buffered (prefixFrames ++ extra)
      = (parseBuffered buffered extra).map
          (fun state => { state with frames := prefixFrames ++ state.frames }) := by
  fun_induction parseBuffered buffered extra
  next hcase =>
    rw [parseBuffered_step]
    simp only [hcase, map_error]
  next hcase =>
    rw [parseBuffered_step]
    simp only [hcase, map_ok]
  next frame rest hcase ih =>
    rw [parseBuffered_step]
    simp only [hcase]
    rw [Array.push_append]
    exact ih

private theorem parseBuffered_acc (buffered : ByteArray) (frames : Array Frame) :
    parseBuffered buffered frames
      = (parseBuffered buffered #[]).map
          (fun state => { state with frames := frames ++ state.frames }) := by
  have h := parseBuffered_append_acc buffered frames #[]
  rw [Array.append_empty] at h
  exact h

private theorem decodeChunk_empty (bytes : ByteArray) :
    decodeChunk {} bytes = parseBuffered bytes #[] := by
  unfold decodeChunk
  rw [show ({} : DecodeState).buffered.append bytes = bytes from ByteArray.empty_append]

theorem decodeAll_empty : decodeAll ByteArray.empty = .ok #[] := by
  unfold decodeAll
  simp only [bind, Except.bind, pure, Except.pure, throw_eq]
  rw [decodeChunk_empty, parseBuffered.eq_def]
  rfl

/-- Residual-byte inversion: decoding `encode frame ++ rest` yields `frame`
followed by whatever `rest` decodes to. -/
theorem decodeAll_encode_append {frame : Frame} {bs : ByteArray}
    (henc : encode frame = .ok bs)
    (hft : FrameType.ofUInt8 frame.header.frameType.toUInt8 = frame.header.frameType)
    (rest : ByteArray) :
    decodeAll (bs ++ rest) = (decodeAll rest).map (fun frames => #[frame] ++ frames) := by
  unfold decodeAll
  simp only [bind, Except.bind, pure, Except.pure, throw_eq]
  rw [decodeChunk_empty, decodeChunk_empty]
  rw [parseBuffered_encode_append henc hft rest #[]]
  rw [show (#[] : Array Frame).push frame = #[frame] from rfl]
  rw [parseBuffered_acc rest #[frame]]
  cases hres : parseBuffered rest #[] with
  | error status => simp only [map_error]
  | ok state =>
      simp only [map_ok]
      cases hbuf : state.buffered.isEmpty <;> simp [map_ok, map_error]

/-- A single encoded frame decodes to exactly that frame. -/
theorem decodeAll_encode {frame : Frame} {bs : ByteArray}
    (henc : encode frame = .ok bs)
    (hft : FrameType.ofUInt8 frame.header.frameType.toUInt8 = frame.header.frameType) :
    decodeAll bs = .ok #[frame] := by
  have h := decodeAll_encode_append henc hft ByteArray.empty
  rw [ByteArray.append_empty] at h
  simp only [h, decodeAll_empty, map_ok, Array.append_empty]

end Frame

namespace Priority

structure Value where
  exclusive : Bool
  streamDependency : Nat
  weight : UInt8
  deriving Inhabited, Repr, DecidableEq

def decode (frame : Frame) : Except Status Value := do
  if frame.header.frameType != FrameType.priority then
    throw (Status.internal "expected HTTP/2 PRIORITY frame")
  if frame.header.streamId == 0 then
    throw (Status.internal "HTTP/2 PRIORITY frame must use a stream id")
  if frame.payload.size != 5 then
    throw (Status.internal "HTTP/2 PRIORITY payload must be exactly 5 bytes")
  let rawDependency := Frame.readUInt32BE frame.payload 0
  let streamDependency := rawDependency % (maxStreamId + 1)
  if streamDependency == frame.header.streamId then
    throw (Status.internal "HTTP/2 PRIORITY dependency cannot reference the same stream")
  pure {
    exclusive := rawDependency >= (maxStreamId + 1),
    streamDependency := streamDependency,
    weight := frame.payload[4]!
  }

end Priority

namespace Ping

def ackFlag : UInt8 := 0x1

def isAck (frame : Frame) : Bool :=
  frame.header.frameType == FrameType.ping && FrameFlag.has frame.header.flags ackFlag

def frame (payload : ByteArray) (ack : Bool := false) : Except Status Frame := do
  if payload.size != 8 then
    throw (Status.internal "HTTP/2 PING payload must be exactly 8 bytes")
  pure {
    header := {
      length := payload.size,
      frameType := FrameType.ping,
      flags := if ack then ackFlag else 0,
      streamId := 0
    },
    payload := payload
  }

def decode (frame : Frame) : Except Status ByteArray := do
  if frame.header.frameType != FrameType.ping then
    throw (Status.internal "expected HTTP/2 PING frame")
  if frame.header.streamId != 0 then
    throw (Status.internal "HTTP/2 PING frame must use stream 0")
  if frame.payload.size != 8 then
    throw (Status.internal "HTTP/2 PING payload must be exactly 8 bytes")
  pure frame.payload

end Ping

namespace RstStream

def frame (streamId : Nat) (errorCode : ErrorCode) : Except Status Frame := do
  if streamId == 0 then
    throw (Status.internal "HTTP/2 RST_STREAM frame must use a stream id")
  if streamId > maxStreamId then
    throw (Status.internal "HTTP/2 RST_STREAM stream id exceeds 31-bit length")
  let payload := Frame.u32BE errorCode.toNat
  pure {
    header := {
      length := payload.size,
      frameType := FrameType.rstStream,
      flags := 0,
      streamId := streamId
    },
    payload := payload
  }

/-- A built RST_STREAM frame is an RST_STREAM frame. -/
theorem frame_frameType {streamId : Nat} {code : ErrorCode} {out : Frame}
    (h : frame streamId code = .ok out) : out.header.frameType = FrameType.rstStream := by
  unfold frame at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next => cases h; rfl

/-- A built RST_STREAM frame names the stream it was built for: a stream error
never touches another stream (RFC 9113 §5.4.2). -/
theorem frame_streamId {streamId : Nat} {code : ErrorCode} {out : Frame}
    (h : frame streamId code = .ok out) : out.header.streamId = streamId := by
  unfold frame at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  next => cases h
  next =>
    split at h
    next => cases h
    next => cases h; rfl

def decode (frame : Frame) : Except Status ErrorCode := do
  if frame.header.frameType != FrameType.rstStream then
    throw (Status.internal "expected HTTP/2 RST_STREAM frame")
  if frame.header.streamId == 0 then
    throw (Status.internal "HTTP/2 RST_STREAM frame must use a stream id")
  if frame.payload.size != 4 then
    throw (Status.internal "HTTP/2 RST_STREAM payload must be exactly 4 bytes")
  pure (ErrorCode.ofNat (Frame.readUInt32BE frame.payload 0))

end RstStream

namespace GoAway

structure Decoded where
  lastStreamId : Nat
  errorCode : ErrorCode
  debugData : ByteArray
  deriving Inhabited, DecidableEq

def frame (lastStreamId : Nat) (errorCode : ErrorCode)
    (debugData : ByteArray := ByteArray.empty) : Except Status Frame := do
  if lastStreamId > maxStreamId then
    throw (Status.internal "HTTP/2 GOAWAY last stream id exceeds 31-bit length")
  let payload := ByteArray.empty
    |>.append (Frame.u31BE lastStreamId)
    |>.append (Frame.u32BE errorCode.toNat)
    |>.append debugData
  pure {
    header := {
      length := payload.size,
      frameType := FrameType.goAway,
      flags := 0,
      streamId := 0
    },
    payload := payload
  }

def decode (frame : Frame) : Except Status Decoded := do
  if frame.header.frameType != FrameType.goAway then
    throw (Status.internal "expected HTTP/2 GOAWAY frame")
  if frame.header.streamId != 0 then
    throw (Status.internal "HTTP/2 GOAWAY frame must use stream 0")
  if frame.payload.size < 8 then
    throw (Status.internal "HTTP/2 GOAWAY payload must be at least 8 bytes")
  pure {
    lastStreamId := Frame.readUInt32BE frame.payload 0 % (maxStreamId + 1),
    errorCode := ErrorCode.ofNat (Frame.readUInt32BE frame.payload 4),
    debugData := frame.payload.extract 8 frame.payload.size
  }

end GoAway

namespace WindowUpdate

def frame (streamId increment : Nat) : Except Status Frame := do
  if streamId > maxStreamId then
    throw (Status.internal "HTTP/2 WINDOW_UPDATE stream id exceeds 31-bit length")
  if increment == 0 then
    throw (Status.internal "HTTP/2 WINDOW_UPDATE increment must be positive")
  if increment > maxStreamId then
    throw (Status.internal "HTTP/2 WINDOW_UPDATE increment exceeds 31-bit length")
  let payload := Frame.u31BE increment
  pure {
    header := {
      length := payload.size,
      frameType := FrameType.windowUpdate,
      flags := 0,
      streamId := streamId
    },
    payload := payload
  }

def decode (frame : Frame) : Except Status Nat := do
  if frame.header.frameType != FrameType.windowUpdate then
    throw (Status.internal "expected HTTP/2 WINDOW_UPDATE frame")
  if frame.payload.size != 4 then
    throw (Status.internal "HTTP/2 WINDOW_UPDATE payload must be exactly 4 bytes")
  let increment := Frame.readUInt32BE frame.payload 0 % (maxStreamId + 1)
  if increment == 0 then
    throw (Status.internal "HTTP/2 WINDOW_UPDATE increment must be positive")
  pure increment

end WindowUpdate

inductive SettingId where
  | headerTableSize
  | enablePush
  | maxConcurrentStreams
  | initialWindowSize
  | maxFrameSize
  | maxHeaderListSize
  | unknown (value : Nat)
  deriving Inhabited, Repr, DecidableEq

namespace SettingId

def toNat : SettingId -> Nat
  | .headerTableSize => 1
  | .enablePush => 2
  | .maxConcurrentStreams => 3
  | .initialWindowSize => 4
  | .maxFrameSize => 5
  | .maxHeaderListSize => 6
  | .unknown value => value

def ofNat : Nat -> SettingId
  | 1 => .headerTableSize
  | 2 => .enablePush
  | 3 => .maxConcurrentStreams
  | 4 => .initialWindowSize
  | 5 => .maxFrameSize
  | 6 => .maxHeaderListSize
  | value => .unknown value

end SettingId

structure Setting where
  id : SettingId
  value : Nat
  deriving Inhabited, Repr, DecidableEq

namespace Settings

def ackFlag : UInt8 := 0x1

def isAck (frame : Frame) : Bool :=
  frame.header.frameType == FrameType.settings && FrameFlag.has frame.header.flags ackFlag

private def encodePayload (settings : Array Setting) : Except Status ByteArray := do
  settings.foldlM (init := ByteArray.empty) fun out setting => do
    let id := setting.id.toNat
    if id > 65535 then
      throw (Status.internal "HTTP/2 setting id exceeds 16-bit length")
    pure <| out
      |>.append (Frame.u16BE id)
      |>.append (Frame.u32BE setting.value)

def frame (settings : Array Setting) (ack : Bool := false) : Except Status Frame := do
  if ack && !settings.isEmpty then
    throw (Status.internal "HTTP/2 SETTINGS ack frame must have empty payload")
  let payload ← encodePayload settings
  pure {
    header := {
      length := payload.size,
      frameType := FrameType.settings,
      flags := if ack then ackFlag else 0,
      streamId := 0
    },
    payload := payload
  }

def decode (frame : Frame) : Except Status (Array Setting) := do
  if frame.header.frameType != FrameType.settings then
    throw (Status.internal "expected HTTP/2 SETTINGS frame")
  if frame.header.streamId != 0 then
    throw (Status.internal "HTTP/2 SETTINGS frame must use stream 0")
  if isAck frame then
    if frame.payload.isEmpty then
      pure #[]
    else
      throw (Status.internal "HTTP/2 SETTINGS ack frame must have empty payload")
  else if frame.payload.size % 6 != 0 then
    throw (Status.internal "HTTP/2 SETTINGS payload length must be a multiple of 6")
  else
    let rec loop (i : Nat) (out : Array Setting) : Array Setting :=
      if i < frame.payload.size then
        let id := Frame.readUInt16BE frame.payload i
        let value := Frame.readUInt32BE frame.payload (i + 2)
        loop (i + 6) (out.push { id := SettingId.ofNat id, value := value })
      else
        out
    pure (loop 0 #[])

end Settings

end Http2
end Grpc
