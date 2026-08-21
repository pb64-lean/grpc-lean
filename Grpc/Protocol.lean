module

public import Std.Sync.Channel
public import Grpc.Bytes
public import Grpc.Framing
public import Grpc.Metadata

public section

open Grpc.Bytes

namespace Grpc

structure MethodName where
  service : String
  method : String
  deriving Repr, DecidableEq

namespace MethodName

def path (method : MethodName) : String :=
  "/" ++ method.service ++ "/" ++ method.method

def parsePath? (path : String) : Option MethodName :=
  match path.splitToList (· == '/') with
  | "" :: service :: method :: [] =>
      if service.isEmpty || method.isEmpty then none else some { service, method }
  | _ => none

end MethodName

inductive TimeoutUnit where
  | hour
  | minute
  | second
  | millisecond
  | microsecond
  | nanosecond
  deriving Repr, DecidableEq

namespace TimeoutUnit

def ofChar? : Char -> Option TimeoutUnit
  | 'H' => some .hour
  | 'M' => some .minute
  | 'S' => some .second
  | 'm' => some .millisecond
  | 'u' => some .microsecond
  | 'n' => some .nanosecond
  | _ => none

def nanoseconds : TimeoutUnit -> Nat
  | .hour => 3600000000000
  | .minute => 60000000000
  | .second => 1000000000
  | .millisecond => 1000000
  | .microsecond => 1000
  | .nanosecond => 1

def toChar : TimeoutUnit -> Char
  | .hour => 'H'
  | .minute => 'M'
  | .second => 'S'
  | .millisecond => 'm'
  | .microsecond => 'u'
  | .nanosecond => 'n'

theorem ofChar?_toChar (unit : TimeoutUnit) : ofChar? unit.toChar = some unit := by
  cases unit <;> rfl

end TimeoutUnit

structure Timeout where
  value : Nat
  unit : TimeoutUnit
  deriving Repr, DecidableEq

namespace Timeout

private def digit? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else
    none

private def parseDigits (chars : List Char) (value : Nat) : Option Nat :=
  match chars with
  | [] => some value
  | c :: rest =>
      match digit? c with
      | some digit => parseDigits rest (value * 10 + digit)
      | none => none

/-! The list parser is the proof-facing specification.  Executable request
handling uses the byte-indexed implementation below, and the focused timeout
test keeps both definitions differential-tested. -/
def parseReference? (raw : String) : Option Timeout :=
  match raw.toList.reverse with
  | [] => none
  | unitChar :: reversedDigits =>
      let digits := reversedDigits.reverse
      if digits.isEmpty || digits.length > 8 then
        none
      else
        match TimeoutUnit.ofChar? unitChar, parseDigits digits 0 with
        | some unit, some value =>
            if value == 0 then none else some { value := value, unit := unit }
        | _, _ => none

private def parseByteIndexedDigits (raw : String) (stop : Nat)
    (hstop : stop < raw.utf8ByteSize) (i value : Nat) : Option Nat :=
  if hi : i < stop then
    let byte := raw.getUTF8Byte ⟨i⟩ (by
      simp only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos]
      exact Nat.lt_trans hi hstop)
    if 48 ≤ byte && byte ≤ 57 then
      parseByteIndexedDigits raw stop hstop (i + 1)
        (value * 10 + (byte - 48).toNat)
    else
      none
  else
    some value
termination_by stop - i

/-- Allocation-reduced `grpc-timeout` parser.  Valid timeout values are ASCII,
so their character count equals their cached UTF-8 byte count.  Indexing those
bytes avoids materializing and reversing character lists. -/
def parseByteIndexed? (raw : String) : Option Timeout :=
  if hsize : 2 ≤ raw.utf8ByteSize ∧ raw.utf8ByteSize ≤ 9 then
    let stop := raw.utf8ByteSize - 1
    have hstop : stop < raw.utf8ByteSize := by omega
    let unitByte := raw.getUTF8Byte ⟨stop⟩ (by
      simpa only [String.Pos.Raw.lt_iff, String.byteIdx_rawEndPos] using hstop)
    match TimeoutUnit.ofChar? (Char.ofNat unitByte.toNat),
        parseByteIndexedDigits raw stop hstop 0 0 with
    | some unit, some value =>
        if value == 0 then none else some { value := value, unit := unit }
    | _, _ => none
  else
    none

/-- Parse the decimal digits and unit in a `grpc-timeout` header.  The logical
definition remains the list specification used by the codec proofs; generated
code uses the differential-tested byte-indexed implementation. -/
@[implemented_by parseByteIndexed?]
def parse? (raw : String) : Option Timeout :=
  parseReference? raw

def toNanoseconds (timeout : Timeout) : Nat :=
  timeout.value * timeout.unit.nanoseconds

def toMillisecondsCeil (timeout : Timeout) : Nat :=
  (timeout.toNanoseconds + 999999) / 1000000

private def digitChar (n : Nat) : Char :=
  Char.ofNat ('0'.toNat + n)

private def renderDigits (n : Nat) : List Char :=
  if n < 10 then
    [digitChar n]
  else
    renderDigits (n / 10) ++ [digitChar (n % 10)]
  termination_by n
  decreasing_by omega

/-- Render a timeout as its `grpc-timeout` header value (decimal digits
followed by the unit character, e.g. `"250m"`). -/
def render (timeout : Timeout) : String :=
  String.ofList (renderDigits timeout.value ++ [timeout.unit.toChar])

/-- The largest value `grpc-timeout` can carry: the wire format allows at most
eight decimal digits. -/
def maxRenderedValue : Nat := 99999999

/-- Units a duration may be rendered in, finest first. -/
private def renderUnits : List TimeoutUnit :=
  [.nanosecond, .microsecond, .millisecond, .second, .minute, .hour]

private def ceilDiv (n divisor : Nat) : Nat := (n + divisor - 1) / divisor

private def ofNanosecondsIn (nanoseconds : Nat) : List TimeoutUnit -> Timeout
  | [] => { value := maxRenderedValue, unit := .hour }
  | unit :: rest =>
      if ceilDiv nanoseconds unit.nanoseconds ≤ maxRenderedValue then
        { value := ceilDiv nanoseconds unit.nanoseconds, unit := unit }
      else
        ofNanosecondsIn nanoseconds rest

/-- Express a duration in nanoseconds as a `grpc-timeout` value: the finest
unit whose value still fits the eight-digit wire limit.

Rounding is *up*, and a zero duration renders as the smallest representable
one, because `grpc-timeout` has no encoding for zero — `parse?` rejects it, so
a value rounded down to zero would be dropped and read by the peer as "no
deadline at all", which is the opposite of what a propagated deadline means.
Rounding up can overshoot by at most one unit, which cannot outlive the caller:
the caller enforces its own deadline independently (`runWithDeadlineUntil`), so
the downstream call is cut off at the caller's deadline regardless. -/
def ofNanoseconds (nanoseconds : Nat) : Timeout :=
  ofNanosecondsIn (Nat.max nanoseconds 1) renderUnits

/-!
### Codec laws

`parse?_render`: rendering a timeout whose value is nonzero and fits the
8-digit wire limit parses back to exactly that timeout.
-/

private theorem digit?_digitChar {n : Nat} (h : n < 10) : digit? (digitChar n) = some n :=
  (by decide : ∀ i : Fin 10, digit? (digitChar i.val) = some i.val) ⟨n, h⟩

private theorem parseDigits_append (l₁ l₂ : List Char) (value : Nat) :
    parseDigits (l₁ ++ l₂) value
      = match parseDigits l₁ value with
        | some v => parseDigits l₂ v
        | none => none := by
  induction l₁ generalizing value with
  | nil => rfl
  | cons c rest ih =>
      cases hd : digit? c with
      | none => simp only [List.cons_append, parseDigits, hd]
      | some d =>
          simp only [List.cons_append, parseDigits, hd]
          exact ih _

/-- `10 ^ (number of decimal digits of n)`. -/
private def pow10 (n : Nat) : Nat :=
  if n < 10 then 10 else 10 * pow10 (n / 10)
  termination_by n
  decreasing_by omega

private theorem parseDigits_renderDigits (n : Nat) :
    ∀ value, parseDigits (renderDigits n) value = some (value * pow10 n + n) := by
  fun_induction renderDigits n
  next n h =>
    intro value
    simp only [parseDigits, digit?_digitChar h]
    rw [pow10, if_pos h]
  next n h ih =>
    intro value
    rw [parseDigits_append]
    simp only [ih, parseDigits, digit?_digitChar (Nat.mod_lt n (by omega))]
    conv => rhs; rw [pow10, if_neg h]
    have hmul : value * (10 * pow10 (n / 10)) = value * pow10 (n / 10) * 10 := by
      rw [Nat.mul_comm 10 (pow10 (n / 10)), ← Nat.mul_assoc]
    rw [hmul]
    exact congrArg some (by omega)

private theorem renderDigits_ne_nil (n : Nat) : renderDigits n ≠ [] := by
  rw [renderDigits]
  split <;> simp

private theorem renderDigits_length_le (k : Nat) :
    ∀ {n : Nat}, n < 10 ^ (k + 1) -> (renderDigits n).length ≤ k + 1 := by
  induction k with
  | zero =>
      intro n h
      rw [renderDigits, if_pos (by omega)]
      simp
  | succ k ih =>
      intro n h
      rw [renderDigits]
      split
      next => simp
      next h10 =>
        rw [List.length_append]
        have hdiv : n / 10 < 10 ^ (k + 1) := by
          rw [Nat.pow_succ, Nat.mul_comm] at h
          exact Nat.div_lt_of_lt_mul h
        have := ih hdiv
        simp only [List.length_cons, List.length_nil]
        omega

/-- Rendering roundtrip: a nonzero timeout value that fits the 8-digit wire
limit parses back to exactly the same timeout. -/
theorem parse?_render (timeout : Timeout) (hpos : timeout.value ≠ 0)
    (hle : timeout.value ≤ 99999999) :
    parse? timeout.render = some timeout := by
  unfold parse? parseReference? render
  rw [String.toList_ofList, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.reverse_reverse]
  rw [if_neg (by
    simp only [Bool.or_eq_true, not_or]
    refine ⟨?_, ?_⟩
    · simp [List.isEmpty_iff, renderDigits_ne_nil]
    · have := renderDigits_length_le 7 (n := timeout.value) (by omega)
      simp only [decide_eq_true_eq]
      omega)]
  rw [TimeoutUnit.ofChar?_toChar]
  simp only [parseDigits_renderDigits, Nat.zero_mul, Nat.zero_add]
  rw [if_neg (by simpa using hpos)]

private theorem nanoseconds_pos (unit : TimeoutUnit) : 0 < unit.nanoseconds := by
  cases unit <;> decide

private theorem ceilDiv_pos {n divisor : Nat} (hn : 1 ≤ n) (hd : 0 < divisor) :
    1 ≤ ceilDiv n divisor := by
  unfold ceilDiv
  rw [Nat.le_div_iff_mul_le hd]
  omega

/-- Every duration renders to a value the wire format can carry: nonzero and
at most eight digits.  This is what `parse?_render` needs, so `ofNanoseconds`
always produces a header value that parses back. -/
theorem ofNanoseconds_bounds (nanoseconds : Nat) :
    (ofNanoseconds nanoseconds).value ≠ 0
      ∧ (ofNanoseconds nanoseconds).value ≤ maxRenderedValue := by
  unfold ofNanoseconds
  have hn : 1 ≤ Nat.max nanoseconds 1 := Nat.le_max_right _ _
  generalize Nat.max nanoseconds 1 = n at hn
  induction renderUnits with
  | nil =>
      refine ⟨?_, Nat.le_refl _⟩
      show maxRenderedValue ≠ 0
      decide
  | cons unit rest ih =>
      rw [ofNanosecondsIn]
      by_cases hle : ceilDiv n unit.nanoseconds ≤ maxRenderedValue
      · rw [if_pos hle]
        refine ⟨?_, hle⟩
        have h1 := ceilDiv_pos hn (nanoseconds_pos unit)
        show ceilDiv n unit.nanoseconds ≠ 0
        omega
      · rw [if_neg hle]
        exact ih

/-- A duration always renders to a `grpc-timeout` value that parses back to
the same timeout. -/
theorem parse?_render_ofNanoseconds (nanoseconds : Nat) :
    parse? (ofNanoseconds nanoseconds).render = some (ofNanoseconds nanoseconds) :=
  parse?_render _ (ofNanoseconds_bounds nanoseconds).1 (ofNanoseconds_bounds nanoseconds).2

end Timeout

structure MessageStream (α : Type) where
  recv? : GrpcM (Option α)
  cancel : GrpcM Unit := pure ()

namespace MessageStream

inductive Event (α : Type) where
  | item : α -> Event α
  | error : Status -> Event α

structure Producer (α : Type) where
  stream : MessageStream α
  send : α -> GrpcM Unit
  fail : Status -> GrpcM Unit
  close : GrpcM Unit
  cancel : GrpcM Unit

def ofArray (items : Array α) : GrpcM (MessageStream α) := do
  let cursor ← IO.mkRef 0
  pure {
    recv? := do
      let i ← cursor.get
      match items[i]? with
      | none => pure none
      | some item =>
          cursor.set (i + 1)
          pure (some item)
    cancel := pure ()
  }

def mapM (stream : MessageStream α) (f : α -> GrpcM β) : MessageStream β :=
  {
    recv? := do
      match ← stream.recv? with
      | none => pure none
      | some item => pure (some (← f item))
    cancel := stream.cancel
  }

partial def collect (stream : MessageStream α) (out : Array α := #[]) : GrpcM (Array α) := do
  match ← stream.recv? with
  | none => pure out
  | some item => collect stream (out.push item)

def empty : GrpcM (MessageStream α) :=
  ofArray #[]

private def channelClosedStatus : Status :=
  Status.cancelled "gRPC message stream is closed"

private def channelErrorStatus : Std.CloseableChannel.Error -> Status
  | .closed => channelClosedStatus
  | .alreadyClosed => channelClosedStatus

private def sendEvent (ch : Std.CloseableChannel.Sync (Event α)) (event : Event α) : GrpcM Unit := do
  -- Run the synchronous channel action in the current task. Spawning a second
  -- task and immediately waiting for it can exhaust the default task pool when
  -- several producers run concurrently (and is unnecessary for an unbounded
  -- channel, whose underlying send always returns an already-resolved task).
  let result ← (Std.CloseableChannel.Sync.send ch event).toBaseIO
  GrpcM.ofExcept <| result.mapError channelErrorStatus

private def closeChannel (ch : Std.CloseableChannel.Sync (Event α)) : GrpcM Unit := do
  let result ← (Std.CloseableChannel.Sync.close ch).toBaseIO
  match result with
  | Except.ok () => pure ()
  | .error .alreadyClosed => pure ()
  | .error err => GrpcM.ofExcept (.error (channelErrorStatus err))

def pipe (capacity : Option Nat := some 16) : GrpcM (Producer α) := do
  let ch ← Std.CloseableChannel.Sync.new (α := Event α) capacity
  let stream : MessageStream α := {
    recv? := do
      match ← Std.CloseableChannel.Sync.recv ch with
      | none => pure none
      | some (.item item) => pure (some item)
      | some (.error status) => throw status
    cancel := closeChannel ch
  }
  pure {
    stream := stream,
    send := fun item => sendEvent ch (.item item),
    fail := fun status => do
      sendEvent ch (.error status)
      closeChannel ch,
    close := closeChannel ch,
    cancel := closeChannel ch
  }

end MessageStream

/-! ### Deadlines

A request's `grpc-timeout` is a *duration*, so on its own it cannot answer the
question a handler making a downstream call has to answer: how much of it is
left?  The server turns it into an absolute instant on `IO.monoNanosNow`'s
monotonic clock as soon as the request headers are decoded, and hands that
instant to the handler as `request.deadline`.  `Deadline.remaining?` turns the
instant back into a duration at the moment of the downstream call. -/

/-- What is left of a request's deadline. -/
inductive Deadline.Remaining where
  /-- The request carried no `grpc-timeout`: a downstream call inherits no
  deadline. -/
  | unbounded
  /-- Time is left; this is what to send as the downstream `grpc-timeout`. -/
  | remaining (timeout : Timeout)
  /-- The deadline has already passed. -/
  | exceeded
  deriving Repr, DecidableEq, Inhabited

namespace Deadline

/-- Convert a validated `grpc-timeout` duration into an absolute instant,
anchored at `startedAt?` when the transport recorded END_HEADERS or at the
current monotonic time for standalone callers. -/
def fromTimeoutAt? (timeout? : Option Timeout) (startedAt? : Option Nat) :
    IO (Option Nat) := do
  match timeout? with
  | none => pure none
  | some timeout =>
      let startedAt ← match startedAt? with
        | some startedAt => pure startedAt
        | none => IO.monoNanosNow
      pure (some (startedAt + timeout.toNanoseconds))

/-- Convert a validated `grpc-timeout` duration into an absolute instant on
`IO.monoNanosNow`'s monotonic clock. -/
def fromTimeout? (timeout? : Option Timeout) : IO (Option Nat) :=
  fromTimeoutAt? timeout? none

/-- Time left before `deadline?` (an absolute `IO.monoNanosNow` reading, as
carried by `UnaryRequest.deadline` and friends), rendered as a `grpc-timeout`
duration for a downstream call.

`Timeout.ofNanoseconds` rounds up, so a strictly positive remainder never
collapses to "no deadline"; a remainder of zero is reported as `.exceeded`
rather than as a timeout, since the call cannot succeed. -/
def remaining? (deadline? : Option Nat) : IO Remaining := do
  match deadline? with
  | none => pure .unbounded
  | some deadline =>
      let now ← IO.monoNanosNow
      if deadline ≤ now then
        pure .exceeded
      else
        pure (.remaining (Timeout.ofNanoseconds (deadline - now)))

/-- The `Status` a handler should fail with when its deadline is already
spent. -/
def exceededStatus : Status :=
  Status.deadlineExceeded "gRPC deadline exceeded"

/-- The remaining deadline as a `grpc-timeout` header value: `none` when the
request carried no deadline, an error when it has already expired. -/
def remainingHeaderValue? (deadline? : Option Nat) : IO (Except Status (Option String)) := do
  match ← remaining? deadline? with
  | .unbounded => pure (.ok none)
  | .remaining timeout => pure (.ok (some timeout.render))
  | .exceeded => pure (.error exceededStatus)

end Deadline

structure UnaryRequest where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  /-- Absolute deadline on `IO.monoNanosNow`'s clock, set when the request
  carried a `grpc-timeout`.  Pass it to `Deadline.remaining?` (or
  `Grpc.Client.CallOptions.propagating`) to give a downstream call the time
  that is actually left. -/
  deadline : Option Nat := none
  data : ByteArray

structure ClientStreamingRequest where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  /-- Absolute deadline on `IO.monoNanosNow`'s clock; see
  `UnaryRequest.deadline`. -/
  deadline : Option Nat := none
  messages : Array ByteArray := #[]

structure ClientStreamingStreamRequest where
  method : MethodName
  metadata : Metadata
  timeout : Option Timeout := none
  /-- Absolute deadline on `IO.monoNanosNow`'s clock; see
  `UnaryRequest.deadline`. -/
  deadline : Option Nat := none
  messages : MessageStream ByteArray

structure UnaryResponse where
  metadata : Metadata := Metadata.empty
  data : ByteArray := ByteArray.empty
  status : Status := Status.ok
  trailers : Metadata := Metadata.empty

structure ServerStreamingResponse where
  metadata : Metadata := Metadata.empty
  messages : Array ByteArray := #[]
  status : Status := Status.ok
  trailers : Metadata := Metadata.empty

structure ServerStreamingStreamResponse where
  metadata : Metadata := Metadata.empty
  messages : MessageStream ByteArray
  status : Status := Status.ok
  trailers : Metadata := Metadata.empty

namespace Percent

private def hexDigit (n : Nat) : Char :=
  if n < 10 then
    Char.ofNat ('0'.toNat + n)
  else
    Char.ofNat ('A'.toNat + (n - 10))

private def fromHex? (c : Char) : Option Nat :=
  if '0' <= c && c <= '9' then
    some (c.toNat - '0'.toNat)
  else if 'A' <= c && c <= 'F' then
    some (10 + c.toNat - 'A'.toNat)
  else if 'a' <= c && c <= 'f' then
    some (10 + c.toNat - 'a'.toNat)
  else
    none

private def unreserved (byte : UInt8) : Bool :=
  let n := byte.toNat
  (0x30 <= n && n <= 0x39)
    || (0x41 <= n && n <= 0x5a)
    || (0x61 <= n && n <= 0x7a)
    || n == 0x2d || n == 0x2e || n == 0x5f || n == 0x7e || n == 0x20

private def encodeByte (byte : UInt8) : List Char :=
  if unreserved byte then
    [Char.ofNat byte.toNat]
  else
    ['%', hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]

private def encodeFrom (bytes : ByteArray) (i : Nat) : List Char :=
  if h : i < bytes.size then
    encodeByte bytes[i] ++ encodeFrom bytes (i + 1)
  else
    []
  termination_by bytes.size - i
  decreasing_by omega

def encode (message : String) : String :=
  String.ofList (encodeFrom message.toByteArray 0)

private def decodeLoop (chars : List Char) (out : ByteArray) : Except String ByteArray :=
  match chars with
  | [] => .ok out
  | '%' :: a :: b :: rest =>
      match fromHex? a, fromHex? b with
      | some hi, some lo => decodeLoop rest (out.push (UInt8.ofNat (hi * 16 + lo)))
      | _, _ => .error "invalid percent escape"
  | '%' :: _ => .error "truncated percent escape"
  | c :: rest => decodeLoop rest (out.push c.toUInt8)

def decode (message : String) : Except String String := do
  let bytes ← decodeLoop message.toList ByteArray.empty
  match String.fromUTF8? bytes with
  | some value => pure value
  | none => throw "percent-decoded grpc-message is not valid UTF-8"

/-!
### Codec laws

`decode_encode`: percent-decoding inverts percent-encoding for every string.
-/

set_option maxRecDepth 4096 in
private theorem toUInt8_char_unreserved {byte : UInt8} (h : unreserved byte = true) :
    (Char.ofNat byte.toNat).toUInt8 = byte := by
  have := (by decide : ∀ i : Fin 256, unreserved (UInt8.ofNat i.val) = true →
      (Char.ofNat (UInt8.ofNat i.val).toNat).toUInt8 = UInt8.ofNat i.val)
    ⟨byte.toNat, by have := UInt8.toNat_lt byte; omega⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h

set_option maxRecDepth 4096 in
private theorem char_ne_percent_unreserved {byte : UInt8} (h : unreserved byte = true) :
    Char.ofNat byte.toNat ≠ '%' := by
  have := (by decide : ∀ i : Fin 256, unreserved (UInt8.ofNat i.val) = true →
      Char.ofNat (UInt8.ofNat i.val).toNat ≠ '%')
    ⟨byte.toNat, by have := UInt8.toNat_lt byte; omega⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h

private theorem fromHex?_hexDigit {n : Nat} (h : n < 16) : fromHex? (hexDigit n) = some n :=
  (by decide : ∀ i : Fin 16, fromHex? (hexDigit i.val) = some i.val) ⟨n, h⟩

private theorem decodeLoop_cons_ne {c : Char} (hc : c ≠ '%') (l : List Char) (out : ByteArray) :
    decodeLoop (c :: l) out = decodeLoop l (out.push c.toUInt8) := by
  rw [decodeLoop.eq_def]
  split <;> simp_all

private theorem decodeLoop_encodeFrom (bytes : ByteArray) (i : Nat) :
    ∀ out, decodeLoop (encodeFrom bytes i) out = .ok (out ++ bytes.extract i bytes.size) := by
  fun_induction encodeFrom bytes i
  next i h ih =>
    intro out
    have hlt := UInt8.toNat_lt bytes[i]
    by_cases hu : unreserved bytes[i] = true
    · rw [show encodeByte bytes[i] = [Char.ofNat bytes[i].toNat] from by
        rw [encodeByte, if_pos hu]]
      rw [List.singleton_append, decodeLoop_cons_ne (char_ne_percent_unreserved hu),
        toUInt8_char_unreserved hu, ih, push_extract_step h]
    · rw [show encodeByte bytes[i]
          = '%' :: hexDigit (bytes[i].toNat / 16) :: hexDigit (bytes[i].toNat % 16) :: [] from by
        rw [encodeByte, if_neg hu]]
      simp only [List.cons_append, List.nil_append, decodeLoop,
        fromHex?_hexDigit (show bytes[i].toNat / 16 < 16 by omega),
        fromHex?_hexDigit (show bytes[i].toNat % 16 < 16 by omega)]
      rw [show UInt8.ofNat (bytes[i].toNat / 16 * 16 + bytes[i].toNat % 16) = bytes[i] from by
        rw [show bytes[i].toNat / 16 * 16 + bytes[i].toNat % 16 = bytes[i].toNat from by omega,
          UInt8.ofNat_toNat]]
      rw [ih, push_extract_step h]
  next i h =>
    intro out
    rw [show bytes.extract i bytes.size = ByteArray.empty from
        ByteArray.extract_eq_empty_iff.mpr (by omega),
      ByteArray.append_empty]
    rfl

private theorem fromUTF8?_toByteArray (s : String) :
    String.fromUTF8? s.toByteArray = some s := by
  have hv : s.toByteArray.IsValidUTF8 := ⟨s.toList, String.utf8Encode_toList.symm⟩
  unfold String.fromUTF8?
  split
  next h => rfl
  next h => exact absurd hv h

/-- Percent-decoding inverts percent-encoding. -/
theorem decode_encode (message : String) : decode (encode message) = .ok message := by
  unfold decode encode
  simp only [bind, Except.bind]
  rw [String.toList_ofList, decodeLoop_encodeFrom message.toByteArray 0 ByteArray.empty]
  simp only [ByteArray.extract_zero_size, ByteArray.empty_append, fromUTF8?_toByteArray,
    pure, Except.pure]

end Percent

namespace Headers

def contentType (metadata : Metadata) : Option String :=
  metadata.get? "content-type"

def isGrpcContentType (value : String) : Bool :=
  value == "application/grpc" || value == "application/grpc+proto"

private def singletonValues? (name : String) (values : Array String) :
    Except Status (Option String) := do
  if values.size > 1 then
    throw (Status.invalidArgument s!"duplicate {Header.normalizeName name} header")
  else
    pure values[0]?

private def singletonHeader? (metadata : Metadata) (name : String) : Except Status (Option String) :=
  singletonValues? name (metadata.getAll name)

def timeout? (metadata : Metadata) : Except Status (Option Timeout) := do
  match ← singletonHeader? metadata "grpc-timeout" with
  | none => pure none
  | some value =>
      match Timeout.parse? value with
      | some timeout => pure (some timeout)
      | none => throw (Status.invalidArgument s!"invalid grpc-timeout header {value}")

def contentLength? (metadata : Metadata) : Except Status (Option Nat) := do
  match ← singletonHeader? metadata "content-length" with
  | none => pure none
  | some value =>
      match value.toNat? with
      | some length => pure (some length)
      | none => throw (Status.invalidArgument s!"invalid content-length header {value}")

def validateContentLengthValue (contentLength : Option Nat) (actual : Nat) :
    Except Status Unit := do
  match contentLength with
  | none => pure ()
  | some expected =>
      if expected == actual then
        pure ()
      else
        throw (Status.invalidArgument s!"content-length {expected} does not match request body size {actual}")

def validateContentLength (metadata : Metadata) (actual : Nat) : Except Status Unit := do
  validateContentLengthValue (← contentLength? metadata) actual

def identityEncoding : String := "identity"

def gzipEncoding : String := "gzip"

def acceptedEncodings : String := s!"{identityEncoding},{gzipEncoding}"

/-- The validated `grpc-encoding` of a request: `none`/`identity` mean no
compression, `gzip` means gzip-compressed messages. Other encodings reject
with `UNIMPLEMENTED` per the gRPC spec. Returns whether gzip is in use. -/
def requestUsesGzip (metadata : Metadata) : Except Status Bool := do
  match ← singletonHeader? metadata "grpc-encoding" with
  | none => pure false
  | some value =>
      if value == identityEncoding then
        pure false
      else if value == gzipEncoding then
        pure true
      else
        throw (Status.unimplemented s!"unsupported grpc-encoding {value}")

def validateRequestEncoding (metadata : Metadata) : Except Status Unit := do
  discard <| requestUsesGzip metadata

/-- Whether one `grpc-accept-encoding` value advertises gzip. -/
private def valueAcceptsGzip (value : String) : Bool :=
  value.splitOn "," |>.any fun token => token.trim == gzipEncoding

/-- Whether the client's `grpc-accept-encoding` header advertises gzip. -/
def clientAcceptsGzip (metadata : Metadata) : Bool :=
  metadata.getAll "grpc-accept-encoding" |>.any valueAcceptsGzip

/-! Parsed facts retained by a managed HTTP/2 connection after the request
header block has passed the complete gRPC validation sequence. -/
structure RequestPreflight where
  method : MethodName
  timeout : Option Timeout
  contentLength : Option Nat
  requestUsesGzip : Bool
  clientAcceptsGzip : Bool
  deriving Repr, DecidableEq

/-! The managed HTTP/2 preflight needs the first value of four pseudo headers,
singleton/count information for five ordinary headers, and every raw
accepted-encoding value.  On accepted requests, its historical implementation
obtains those facts with ten complete metadata scans after `Metadata.validate`.
The executable scanner below collects the same raw facts in one pass. It
recognizes the two prefix-stable outcomes while scanning, while timeout,
length, encoding, and accept-encoding token parsing remain deferred so
established error precedence is unchanged. -/

private structure HeaderOccurrence where
  first? : Option String := none
  count : Nat := 0

@[inline] private def HeaderOccurrence.add (occurrence : HeaderOccurrence)
    (value : String) : HeaderOccurrence :=
  {
    first? := match occurrence.first? with
      | none => some value
      | some first => some first
    count := occurrence.count + 1
  }

private structure RequestHeaderSummary where
  method? : Option String := none
  scheme? : Option String := none
  status? : Option String := none
  path? : Option String := none
  contentType : HeaderOccurrence := {}
  te : HeaderOccurrence := {}
  timeout : HeaderOccurrence := {}
  contentLength : HeaderOccurrence := {}
  requestEncoding : HeaderOccurrence := {}
  clientAcceptEncodingValues : Array String := #[]

@[inline] private def rememberFirst (current : Option String) (value : String) :
    Option String :=
  match current with
  | none => some value
  | some first => some first

@[inline] private def summarizeRequestHeader (summary : RequestHeaderSummary)
    (header : Header) : RequestHeaderSummary :=
  let nameLength := header.name.utf8ByteSize
  match nameLength with
  | 2 =>
      if header.name == "te" then
        { summary with te := summary.te.add header.value }
      else
        summary
  | 5 =>
      if header.name == ":path" then
        { summary with path? := rememberFirst summary.path? header.value }
      else
        summary
  | 7 =>
      if header.name == ":method" then
        { summary with method? := rememberFirst summary.method? header.value }
      else if header.name == ":scheme" then
        { summary with scheme? := rememberFirst summary.scheme? header.value }
      else if header.name == ":status" then
        { summary with status? := rememberFirst summary.status? header.value }
      else
        summary
  | 12 =>
      if header.name == "content-type" then
        { summary with contentType := summary.contentType.add header.value }
      else if header.name == "grpc-timeout" then
        { summary with timeout := summary.timeout.add header.value }
      else
        summary
  | 13 =>
      if header.name == "grpc-encoding" then
        { summary with requestEncoding := summary.requestEncoding.add header.value }
      else
        summary
  | 14 =>
      if header.name == "content-length" then
        { summary with contentLength := summary.contentLength.add header.value }
      else
        summary
  | 20 =>
      if header.name == "grpc-accept-encoding" then
        { summary with clientAcceptEncodingValues :=
            summary.clientAcceptEncodingValues.push header.value }
      else
        summary
  | _ => summary

private inductive RequestHeaderScanStop where
  | unsupportedContentType
  | reject (status : Status)

private inductive RequestHeaderScanState where
  | summarize (summary : RequestHeaderSummary)
  | pendingReject (status : Status)

private def invalidMethodStatus : Status :=
  Status.invalidArgument "gRPC requests must use POST"

@[inline] private def scanRequestHeader (state : RequestHeaderScanState)
    (header : Header) : Except RequestHeaderScanStop RequestHeaderScanState :=
  let nameLength := header.name.utf8ByteSize
  match state with
  | .pendingReject status =>
      match nameLength with
      | 12 =>
          if header.name == "content-type" then
            if isGrpcContentType header.value then
              .error (.reject status)
            else
              .error .unsupportedContentType
          else
            .ok state
      | _ => .ok state
  | .summarize summary =>
      match nameLength with
      | 2 =>
          if header.name == "te" then
            .ok (.summarize
              { summary with te := summary.te.add header.value })
          else
            .ok state
      | 5 =>
          if header.name == ":path" then
            .ok (.summarize
              { summary with path? := rememberFirst summary.path? header.value })
          else
            .ok state
      | 7 =>
          if header.name == ":method" then
            match summary.method? with
            | some _ => .ok state
            | none =>
                if header.value == "POST" then
                  .ok (.summarize { summary with method? := some header.value })
                else
                  match summary.contentType.first? with
                  | some _ => .error (.reject invalidMethodStatus)
                  | none => .ok (.pendingReject invalidMethodStatus)
          else if header.name == ":scheme" then
            .ok (.summarize
              { summary with scheme? := rememberFirst summary.scheme? header.value })
          else if header.name == ":status" then
            .ok (.summarize
              { summary with status? := rememberFirst summary.status? header.value })
          else
            .ok state
      | 12 =>
          if header.name == "content-type" then
            match summary.contentType.first? with
            | some _ =>
                .ok (.summarize
                  { summary with contentType := summary.contentType.add header.value })
            | none =>
                if isGrpcContentType header.value then
                  .ok (.summarize
                    { summary with contentType := summary.contentType.add header.value })
                else
                  .error .unsupportedContentType
          else if header.name == "grpc-timeout" then
            .ok (.summarize
              { summary with timeout := summary.timeout.add header.value })
          else
            .ok state
      | 13 =>
          if header.name == "grpc-encoding" then
            .ok (.summarize
              { summary with requestEncoding := summary.requestEncoding.add header.value })
          else
            .ok state
      | 14 =>
          if header.name == "content-length" then
            .ok (.summarize
              { summary with contentLength := summary.contentLength.add header.value })
          else
            .ok state
      | 20 =>
          if header.name == "grpc-accept-encoding" then
            .ok (.summarize
              { summary with clientAcceptEncodingValues :=
                  summary.clientAcceptEncodingValues.push header.value })
          else
            .ok state
      | _ => .ok state

/-- Proof-facing fold specification for the direct scanner below. -/
private def scanRequestHeadersCandidate (metadata : Metadata) :
    Except RequestHeaderScanStop RequestHeaderScanState :=
  metadata.foldlM scanRequestHeader (.summarize {})

private def summarizeRequestHeadersCandidate (metadata : Metadata) :
    RequestHeaderSummary :=
  metadata.foldl summarizeRequestHeader {}

private def occurrenceReference (metadata : Metadata) (name : String) :
    HeaderOccurrence :=
  let values := metadata.getAll name
  { first? := values[0]?, count := values.size }

private def summarizeRequestHeadersReference (metadata : Metadata) :
    RequestHeaderSummary :=
  {
    method? := metadata.get? ":method"
    scheme? := metadata.get? ":scheme"
    status? := metadata.get? ":status"
    path? := metadata.get? ":path"
    contentType := occurrenceReference metadata "content-type"
    te := occurrenceReference metadata "te"
    timeout := occurrenceReference metadata "grpc-timeout"
    contentLength := occurrenceReference metadata "content-length"
    requestEncoding := occurrenceReference metadata "grpc-encoding"
    clientAcceptEncodingValues := metadata.getAll "grpc-accept-encoding"
  }

private theorem normalizeName_eq_self_of_map (name : String)
    (h : name.toList.map Char.toLower = name.toList) :
    Header.normalizeName name = name := by
  apply Header.normalizeName_eq_self
  unfold String.toLower
  rw [← String.toList_inj, String.toList_map]
  exact h

private theorem normalizeName_method : Header.normalizeName ":method" = ":method" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_scheme : Header.normalizeName ":scheme" = ":scheme" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_status : Header.normalizeName ":status" = ":status" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_path : Header.normalizeName ":path" = ":path" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_contentType :
    Header.normalizeName "content-type" = "content-type" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_te : Header.normalizeName "te" = "te" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_timeout :
    Header.normalizeName "grpc-timeout" = "grpc-timeout" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_contentLength :
    Header.normalizeName "content-length" = "content-length" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_requestEncoding :
    Header.normalizeName "grpc-encoding" = "grpc-encoding" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

private theorem normalizeName_acceptEncoding :
    Header.normalizeName "grpc-accept-encoding" = "grpc-accept-encoding" := by
  apply normalizeName_eq_self_of_map
  simp [Char.toLower]

@[simp] private theorem utf8ByteSize_te : "te".utf8ByteSize = 2 := by decide
@[simp] private theorem utf8ByteSize_path : ":path".utf8ByteSize = 5 := by decide
@[simp] private theorem utf8ByteSize_method : ":method".utf8ByteSize = 7 := by decide
@[simp] private theorem utf8ByteSize_scheme : ":scheme".utf8ByteSize = 7 := by decide
@[simp] private theorem utf8ByteSize_status : ":status".utf8ByteSize = 7 := by decide
@[simp] private theorem utf8ByteSize_contentType :
    "content-type".utf8ByteSize = 12 := by decide
@[simp] private theorem utf8ByteSize_timeout :
    "grpc-timeout".utf8ByteSize = 12 := by decide
@[simp] private theorem utf8ByteSize_requestEncoding :
    "grpc-encoding".utf8ByteSize = 13 := by decide
@[simp] private theorem utf8ByteSize_contentLength :
    "content-length".utf8ByteSize = 14 := by decide
@[simp] private theorem utf8ByteSize_acceptEncoding :
    "grpc-accept-encoding".utf8ByteSize = 20 := by decide

private theorem summarizeRequestHeader_contentType_first?_of_some
    (summary : RequestHeaderSummary) (header : Header) (value : String)
    (hfirst : summary.contentType.first? = some value) :
    (summarizeRequestHeader summary header).contentType.first? = some value := by
  grind [summarizeRequestHeader, HeaderOccurrence.add]

private theorem summarizeRequestHeader_method?_of_some
    (summary : RequestHeaderSummary) (header : Header) (value : String)
    (hfirst : summary.method? = some value) :
    (summarizeRequestHeader summary header).method? = some value := by
  grind [summarizeRequestHeader, rememberFirst]

private theorem summarizeRequestHeader_contentType_first?_of_none
    (summary : RequestHeaderSummary) (header : Header)
    (hfirst : summary.contentType.first? = none) :
    (summarizeRequestHeader summary header).contentType.first? =
      if header.name == "content-type" then some header.value else none := by
  by_cases hname : header.name = "content-type"
  · simp_all [summarizeRequestHeader, HeaderOccurrence.add]
  · grind [summarizeRequestHeader, HeaderOccurrence.add]

private theorem summarizeRequestHeader_method?_of_none
    (summary : RequestHeaderSummary) (header : Header)
    (hfirst : summary.method? = none) :
    (summarizeRequestHeader summary header).method? =
      if header.name == ":method" then some header.value else none := by
  by_cases hname : header.name = ":method"
  · simp_all [summarizeRequestHeader, rememberFirst]
  · grind [summarizeRequestHeader, rememberFirst]

private theorem getAll_push (metadata : Metadata) (header : Header) (name : String) :
    Metadata.getAll (metadata.push header) name =
      if header.name == Header.normalizeName name then
        (Metadata.getAll metadata name).push header.value
      else
        Metadata.getAll metadata name := by
  simp only [Metadata.getAll]
  split <;> simp_all

private theorem first?_push (values : Array String) (value : String) :
    (values.push value)[0]? = rememberFirst values[0]? value := by
  cases values with
  | mk values => cases values <;> simp [rememberFirst]

private theorem get?_push (metadata : Metadata) (header : Header) (name : String) :
    Metadata.get? (metadata.push header) name =
      if header.name == Header.normalizeName name then
        rememberFirst (Metadata.get? metadata name) header.value
      else
        Metadata.get? metadata name := by
  unfold Metadata.get?
  rw [getAll_push]
  split
  next => rw [first?_push]
  next => rfl

private theorem occurrenceOfValues_push (values : Array String) (value : String) :
    ({
      first? := (values.push value)[0]?
      count := (values.push value).size
    } : HeaderOccurrence) = ({
      first? := values[0]?
      count := values.size
    } : HeaderOccurrence).add value := by
  cases values with
  | mk values => cases values <;> simp [HeaderOccurrence.add]

private theorem occurrenceReference_push (metadata : Metadata) (header : Header)
    (name : String) :
    occurrenceReference (metadata.push header) name =
      if header.name == Header.normalizeName name then
        (occurrenceReference metadata name).add header.value
      else
        occurrenceReference metadata name := by
  unfold occurrenceReference
  rw [getAll_push]
  split
  next => exact occurrenceOfValues_push _ _
  next => rfl

private theorem summarizeRequestHeadersReference_push (metadata : Metadata)
    (header : Header) :
    summarizeRequestHeadersReference (metadata.push header) =
      summarizeRequestHeader (summarizeRequestHeadersReference metadata) header := by
  unfold summarizeRequestHeadersReference summarizeRequestHeader
  simp only [get?_push, occurrenceReference_push, getAll_push,
    normalizeName_method, normalizeName_scheme, normalizeName_status,
    normalizeName_path, normalizeName_contentType, normalizeName_te,
    normalizeName_timeout, normalizeName_contentLength,
    normalizeName_requestEncoding, normalizeName_acceptEncoding]
  by_cases hmethod : header.name = ":method"
  · simp_all
  by_cases hscheme : header.name = ":scheme"
  · simp_all
  by_cases hstatus : header.name = ":status"
  · simp_all
  by_cases hpath : header.name = ":path"
  · simp_all
  by_cases hcontentType : header.name = "content-type"
  · simp_all
  by_cases hte : header.name = "te"
  · simp_all
  by_cases htimeout : header.name = "grpc-timeout"
  · simp_all
  by_cases hcontentLength : header.name = "content-length"
  · simp_all
  by_cases hrequestEncoding : header.name = "grpc-encoding"
  · simp_all
  by_cases hacceptEncoding : header.name = "grpc-accept-encoding"
  · simp_all
  grind

private theorem array_push_induction {α : Type} {motive : Array α → Prop}
    (empty : motive #[])
    (push : ∀ (values : Array α) (value : α),
      motive values → motive (values.push value))
    (values : Array α) : motive values := by
  suffices h : ∀ reverse : List α, motive reverse.reverse.toArray by
    simpa using h values.toList.reverse
  intro reverse
  induction reverse with
  | nil => simpa using empty
  | cons value rest ih =>
      rw [List.reverse_cons]
      have harray : (rest.reverse ++ [value]).toArray =
          rest.reverse.toArray.push value := by
        rw [← Array.toList_inj]
        simp
      rw [harray]
      exact push _ _ ih

private theorem summarizeRequestHeadersCandidate_eq_reference (metadata : Metadata) :
    summarizeRequestHeadersCandidate metadata =
      summarizeRequestHeadersReference metadata := by
  apply array_push_induction (values := metadata)
  · simp [summarizeRequestHeadersCandidate, summarizeRequestHeadersReference,
      occurrenceReference, Metadata.get?, Metadata.getAll]
  · intro values value ih
    rw [summarizeRequestHeadersReference_push]
    unfold summarizeRequestHeadersCandidate at ih ⊢
    rw [Array.foldl_push, ih]

private structure ValidatedRequestCore where
  method : MethodName
  timeout : Option Timeout
  contentLength : Option Nat
  requestUsesGzip : Bool

/-- Fallible request validation shared by the legacy method-only API and the
managed preflight. The managed wrapper alone scans response gzip acceptance. -/
private def validateUnaryRequestCoreAfterMetadata (metadata : Metadata)
    (contentTypes : Array String) : Except Status ValidatedRequestCore := do

  match metadata.get? ":method" with
  | some "POST" => pure ()
  | some _ => throw (Status.invalidArgument "gRPC requests must use POST")
  | none => throw (Status.invalidArgument "missing :method header")

  match metadata.get? ":scheme" with
  | some "http" => pure ()
  | some "https" => pure ()
  | some value => throw (Status.invalidArgument s!"unsupported gRPC scheme {value}")
  | none => throw (Status.invalidArgument "missing :scheme header")

  match metadata.get? ":status" with
  | some _ => throw (Status.invalidArgument "gRPC requests must not include :status")
  | none => pure ()

  let path ← match metadata.get? ":path" with
    | some path => pure path
    | none => throw (Status.invalidArgument "missing :path header")

  let method ← match MethodName.parsePath? path with
    | some method => pure method
    | none => throw (Status.invalidArgument s!"invalid gRPC method path {path}")

  match ← singletonValues? "content-type" contentTypes with
  | some value =>
      if isGrpcContentType value then pure () else
        throw (Status.invalidArgument s!"unsupported content-type {value}")
  | none => throw (Status.invalidArgument "missing content-type header")

  match ← singletonHeader? metadata "te" with
  | some "trailers" => pure ()
  | some _ => throw (Status.invalidArgument "gRPC requests must send te: trailers")
  | none => throw (Status.invalidArgument "missing te header")

  let timeout ← timeout? metadata
  let contentLength ← contentLength? metadata
  let requestUsesGzip ← requestUsesGzip metadata

  pure {
    method := method,
    timeout := timeout,
    contentLength := contentLength,
    requestUsesGzip := requestUsesGzip
  }

/-- Complete request validation after `Metadata.validate` has already
succeeded. `contentTypes` is supplied by the early HTTP-status preflight so
that its first-value check and the full singleton check share one scan. -/
def validateUnaryRequestPreflightAfterMetadata (metadata : Metadata)
    (contentTypes : Array String) : Except Status RequestPreflight := do
  let core ← validateUnaryRequestCoreAfterMetadata metadata contentTypes
  pure {
    method := core.method
    timeout := core.timeout
    contentLength := core.contentLength
    requestUsesGzip := core.requestUsesGzip
    clientAcceptsGzip := clientAcceptsGzip metadata
  }

private def singletonOccurrence? (name : String) (occurrence : HeaderOccurrence) :
    Except Status (Option String) := do
  if occurrence.count > 1 then
    throw (Status.invalidArgument s!"duplicate {Header.normalizeName name} header")
  else
    pure occurrence.first?

private def timeoutOccurrence? (occurrence : HeaderOccurrence) :
    Except Status (Option Timeout) := do
  match ← singletonOccurrence? "grpc-timeout" occurrence with
  | none => pure none
  | some value =>
      match Timeout.parse? value with
      | some timeout => pure (some timeout)
      | none => throw (Status.invalidArgument s!"invalid grpc-timeout header {value}")

private def contentLengthOccurrence? (occurrence : HeaderOccurrence) :
    Except Status (Option Nat) := do
  match ← singletonOccurrence? "content-length" occurrence with
  | none => pure none
  | some value =>
      match value.toNat? with
      | some length => pure (some length)
      | none => throw (Status.invalidArgument s!"invalid content-length header {value}")

private def requestUsesGzipOccurrence (occurrence : HeaderOccurrence) :
    Except Status Bool := do
  match ← singletonOccurrence? "grpc-encoding" occurrence with
  | none => pure false
  | some value =>
      if value == identityEncoding then
        pure false
      else if value == gzipEncoding then
        pure true
      else
        throw (Status.unimplemented s!"unsupported grpc-encoding {value}")

private def validateUnaryRequestSummaryCore (summary : RequestHeaderSummary) :
    Except Status ValidatedRequestCore := do
  match summary.method? with
  | some "POST" => pure ()
  | some _ => throw (Status.invalidArgument "gRPC requests must use POST")
  | none => throw (Status.invalidArgument "missing :method header")

  match summary.scheme? with
  | some "http" => pure ()
  | some "https" => pure ()
  | some value => throw (Status.invalidArgument s!"unsupported gRPC scheme {value}")
  | none => throw (Status.invalidArgument "missing :scheme header")

  match summary.status? with
  | some _ => throw (Status.invalidArgument "gRPC requests must not include :status")
  | none => pure ()

  let path ← match summary.path? with
    | some path => pure path
    | none => throw (Status.invalidArgument "missing :path header")

  let method ← match MethodName.parsePath? path with
    | some method => pure method
    | none => throw (Status.invalidArgument s!"invalid gRPC method path {path}")

  match ← singletonOccurrence? "content-type" summary.contentType with
  | some value =>
      if isGrpcContentType value then pure () else
        throw (Status.invalidArgument s!"unsupported content-type {value}")
  | none => throw (Status.invalidArgument "missing content-type header")

  match ← singletonOccurrence? "te" summary.te with
  | some "trailers" => pure ()
  | some _ => throw (Status.invalidArgument "gRPC requests must send te: trailers")
  | none => throw (Status.invalidArgument "missing te header")

  let timeout ← timeoutOccurrence? summary.timeout
  let contentLength ← contentLengthOccurrence? summary.contentLength
  let requestUsesGzip ← requestUsesGzipOccurrence summary.requestEncoding

  pure {
    method := method
    timeout := timeout
    contentLength := contentLength
    requestUsesGzip := requestUsesGzip
  }

private def validateUnaryRequestSummary (summary : RequestHeaderSummary) :
    Except Status RequestPreflight := do
  let core ← validateUnaryRequestSummaryCore summary
  pure {
    method := core.method
    timeout := core.timeout
    contentLength := core.contentLength
    requestUsesGzip := core.requestUsesGzip
    clientAcceptsGzip := summary.clientAcceptEncodingValues.any valueAcceptsGzip
  }

private theorem singletonOccurrence_reference (metadata : Metadata) (name : String) :
    singletonOccurrence? name (occurrenceReference metadata name) =
      singletonHeader? metadata name := by
  unfold singletonOccurrence? occurrenceReference singletonHeader? singletonValues?
  rfl

private theorem singletonOccurrence_values_reference (metadata : Metadata)
    (name : String) :
    singletonOccurrence? name (occurrenceReference metadata name) =
      singletonValues? name (metadata.getAll name) := by
  unfold singletonOccurrence? occurrenceReference singletonValues?
  rfl

private theorem timeoutOccurrence_reference (metadata : Metadata) :
    timeoutOccurrence? (occurrenceReference metadata "grpc-timeout") =
      timeout? metadata := by
  unfold timeoutOccurrence? timeout?
  rw [singletonOccurrence_reference]

private theorem contentLengthOccurrence_reference (metadata : Metadata) :
    contentLengthOccurrence? (occurrenceReference metadata "content-length") =
      contentLength? metadata := by
  unfold contentLengthOccurrence? contentLength?
  rw [singletonOccurrence_reference]

private theorem requestUsesGzipOccurrence_reference (metadata : Metadata) :
    requestUsesGzipOccurrence (occurrenceReference metadata "grpc-encoding") =
      requestUsesGzip metadata := by
  unfold requestUsesGzipOccurrence requestUsesGzip
  rw [singletonOccurrence_reference]

private theorem validateUnaryRequestSummaryCore_reference (metadata : Metadata) :
    validateUnaryRequestSummaryCore (summarizeRequestHeadersReference metadata) =
      validateUnaryRequestCoreAfterMetadata metadata
        (metadata.getAll "content-type") := by
  unfold validateUnaryRequestSummaryCore summarizeRequestHeadersReference
    validateUnaryRequestCoreAfterMetadata
  simp only [singletonOccurrence_values_reference, singletonHeader?,
    timeoutOccurrence_reference, contentLengthOccurrence_reference,
    requestUsesGzipOccurrence_reference]

private theorem validateUnaryRequestSummary_reference (metadata : Metadata) :
    validateUnaryRequestSummary (summarizeRequestHeadersReference metadata) =
      validateUnaryRequestPreflightAfterMetadata metadata
        (metadata.getAll "content-type") := by
  unfold validateUnaryRequestSummary validateUnaryRequestPreflightAfterMetadata
  rw [validateUnaryRequestSummaryCore_reference]
  unfold summarizeRequestHeadersReference clientAcceptsGzip
  rfl

/-- Pure classification used after `Metadata.validate` and before response
encoding or registry lookup. `unsupportedContentType` retains the historical
HTTP 415 path, while `reject` carries the exact gRPC validation status. -/
inductive RequestHeaderPreflightResult where
  | unsupportedContentType
  | reject (status : Status)
  | accept (preflight : RequestPreflight)
  deriving Repr, DecidableEq

private def requestHeaderPreflightValidatedSummary (summary : RequestHeaderSummary) :
    RequestHeaderPreflightResult :=
  match validateUnaryRequestSummary summary with
  | .error status => .reject status
  | .ok preflight => .accept preflight

private def requestHeaderPreflightReference (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  let contentTypes := metadata.getAll "content-type"
  match contentTypes[0]? with
  | some value =>
      if !isGrpcContentType value then
        .unsupportedContentType
      else
        match validateUnaryRequestPreflightAfterMetadata metadata contentTypes with
        | .error status => .reject status
        | .ok preflight => .accept preflight
  | none =>
      match validateUnaryRequestPreflightAfterMetadata metadata contentTypes with
      | .error status => .reject status
      | .ok preflight => .accept preflight

private def requestHeaderPreflightSummary (summary : RequestHeaderSummary) :
    RequestHeaderPreflightResult :=
  match summary.contentType.first? with
  | some value =>
      if !isGrpcContentType value then
        .unsupportedContentType
      else
        requestHeaderPreflightValidatedSummary summary
  | none => requestHeaderPreflightValidatedSummary summary

private def requestHeaderPreflightCandidateLogical (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  requestHeaderPreflightSummary (summarizeRequestHeadersCandidate metadata)

private def requestHeaderScanStopResult (stop : RequestHeaderScanStop) :
    RequestHeaderPreflightResult :=
  match stop with
  | .unsupportedContentType => .unsupportedContentType
  | .reject status => .reject status

private def finishRequestHeaderScan
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState) :
    RequestHeaderPreflightResult :=
  match outcome with
  | .error stop => requestHeaderScanStopResult stop
  | .ok (.pendingReject status) => .reject status
  | .ok (.summarize summary) => requestHeaderPreflightValidatedSummary summary

private def firstContentTypeSupported (summary : RequestHeaderSummary) : Prop :=
  match summary.contentType.first? with
  | none => True
  | some value => isGrpcContentType value = true

private def firstMethodAccepted (summary : RequestHeaderSummary) : Prop :=
  match summary.method? with
  | none => True
  | some value => value = "POST"

private def RequestHeaderScanMatches
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState)
    (summary : RequestHeaderSummary) : Prop :=
  match outcome with
  | .ok (.summarize scanned) =>
      scanned = summary ∧ firstContentTypeSupported summary ∧
        firstMethodAccepted summary
  | .ok (.pendingReject status) =>
      status = invalidMethodStatus ∧ summary.contentType.first? = none ∧
        ∃ value, summary.method? = some value ∧ value ≠ "POST"
  | .error .unsupportedContentType =>
      ∃ value, summary.contentType.first? = some value ∧
        isGrpcContentType value = false
  | .error (.reject status) =>
      status = invalidMethodStatus ∧
        (∃ contentType, summary.contentType.first? = some contentType ∧
          isGrpcContentType contentType = true) ∧
        ∃ value, summary.method? = some value ∧ value ≠ "POST"

private theorem scanRequestHeader_regular (summary : RequestHeaderSummary)
    (header : Header) (hmethod : header.name ≠ ":method")
    (hcontentType : header.name ≠ "content-type") :
    scanRequestHeader (.summarize summary) header =
      .ok (.summarize (summarizeRequestHeader summary header)) := by
  grind [scanRequestHeader, summarizeRequestHeader,
    utf8ByteSize_te, utf8ByteSize_path, utf8ByteSize_method,
    utf8ByteSize_scheme, utf8ByteSize_status, utf8ByteSize_contentType,
    utf8ByteSize_timeout, utf8ByteSize_requestEncoding,
    utf8ByteSize_contentLength, utf8ByteSize_acceptEncoding, Except.pure]

private theorem firstContentTypeSupported_regular
    (summary : RequestHeaderSummary) (header : Header)
    (hcontentType : header.name ≠ "content-type")
    (hsupported : firstContentTypeSupported summary) :
    firstContentTypeSupported (summarizeRequestHeader summary header) := by
  unfold firstContentTypeSupported at hsupported ⊢
  cases hfirst : summary.contentType.first? with
  | none =>
      rw [summarizeRequestHeader_contentType_first?_of_none _ _ hfirst]
      simp [hcontentType]
  | some value =>
      rw [summarizeRequestHeader_contentType_first?_of_some _ _ _ hfirst]
      simpa [hfirst] using hsupported

private theorem firstMethodAccepted_regular (summary : RequestHeaderSummary)
    (header : Header) (hmethod : header.name ≠ ":method")
    (haccepted : firstMethodAccepted summary) :
    firstMethodAccepted (summarizeRequestHeader summary header) := by
  unfold firstMethodAccepted at haccepted ⊢
  cases hfirst : summary.method? with
  | none =>
      rw [summarizeRequestHeader_method?_of_none _ _ hfirst]
      simp [hmethod]
  | some value =>
      rw [summarizeRequestHeader_method?_of_some _ _ _ hfirst]
      simpa [hfirst] using haccepted

private theorem scanRequestHeader_summarize_matches
    (summary : RequestHeaderSummary) (header : Header)
    (hcontentType : firstContentTypeSupported summary)
    (hmethod : firstMethodAccepted summary) :
    RequestHeaderScanMatches (scanRequestHeader (.summarize summary) header)
      (summarizeRequestHeader summary header) := by
  by_cases hmethodName : header.name = ":method"
  · cases hmethodFirst : summary.method? with
    | none =>
        cases hcontentFirst : summary.contentType.first? with
        | none =>
            by_cases hpost : header.value = "POST"
            · simp_all [scanRequestHeader, summarizeRequestHeader,
                RequestHeaderScanMatches, firstContentTypeSupported,
                firstMethodAccepted, rememberFirst]
            · simp_all [scanRequestHeader, summarizeRequestHeader,
                RequestHeaderScanMatches, firstContentTypeSupported,
                firstMethodAccepted, rememberFirst]
        | some contentType =>
            by_cases hpost : header.value = "POST"
            · simp_all [scanRequestHeader, summarizeRequestHeader,
                RequestHeaderScanMatches, firstContentTypeSupported,
                firstMethodAccepted, rememberFirst]
            · simp_all [scanRequestHeader, summarizeRequestHeader,
                RequestHeaderScanMatches, firstContentTypeSupported,
                firstMethodAccepted, rememberFirst]
    | some method =>
        simp [firstMethodAccepted, hmethodFirst] at hmethod
        subst method
        cases summary
        simp_all [scanRequestHeader, summarizeRequestHeader,
          RequestHeaderScanMatches, firstContentTypeSupported,
          firstMethodAccepted, rememberFirst]
  · by_cases hcontentTypeName : header.name = "content-type"
    · cases hcontentFirst : summary.contentType.first? with
      | none =>
          cases hsupported : isGrpcContentType header.value <;>
            simp_all [scanRequestHeader, summarizeRequestHeader,
              RequestHeaderScanMatches, firstContentTypeSupported,
              firstMethodAccepted, HeaderOccurrence.add]
      | some contentType =>
          simp [firstContentTypeSupported, hcontentFirst] at hcontentType
          simp_all [scanRequestHeader, summarizeRequestHeader,
            RequestHeaderScanMatches, firstContentTypeSupported,
            firstMethodAccepted, HeaderOccurrence.add]
    · rw [scanRequestHeader_regular summary header hmethodName hcontentTypeName]
      simp [RequestHeaderScanMatches,
        firstContentTypeSupported_regular summary header hcontentTypeName hcontentType,
        firstMethodAccepted_regular summary header hmethodName hmethod]

private theorem scanRequestHeader_pending_matches (status : Status)
    (summary : RequestHeaderSummary) (header : Header)
    (hstatus : status = invalidMethodStatus)
    (hcontentType : summary.contentType.first? = none)
    (hmethod : ∃ value, summary.method? = some value ∧ value ≠ "POST") :
    RequestHeaderScanMatches (scanRequestHeader (.pendingReject status) header)
      (summarizeRequestHeader summary header) := by
  rcases hmethod with ⟨method, hmethodFirst, hmethodValue⟩
  by_cases hcontentTypeName : header.name = "content-type"
  · cases hsupported : isGrpcContentType header.value <;>
      simp_all [scanRequestHeader, summarizeRequestHeader,
        RequestHeaderScanMatches, HeaderOccurrence.add]
  · have hcontentTypeNext :=
      summarizeRequestHeader_contentType_first?_of_none summary header hcontentType
    have hmethodNext :=
      summarizeRequestHeader_method?_of_some summary header method hmethodFirst
    simp [hcontentTypeName] at hcontentTypeNext
    grind [scanRequestHeader, RequestHeaderScanMatches,
      utf8ByteSize_contentType]

private theorem scanRequestHeadersCandidate_matches (metadata : Metadata) :
    RequestHeaderScanMatches (scanRequestHeadersCandidate metadata)
      (summarizeRequestHeadersCandidate metadata) := by
  apply array_push_induction (values := metadata)
  · simp [scanRequestHeadersCandidate, summarizeRequestHeadersCandidate,
      RequestHeaderScanMatches, firstContentTypeSupported, firstMethodAccepted,
      pure, Except.pure]
  · intro values header ih
    unfold scanRequestHeadersCandidate summarizeRequestHeadersCandidate at ih ⊢
    rw [Array.foldlM_push, Array.foldl_push]
    cases hscan : Array.foldlM scanRequestHeader (.summarize {}) values with
    | error stop =>
        change RequestHeaderScanMatches (.error stop)
          (summarizeRequestHeader
            (Array.foldl summarizeRequestHeader {} values) header)
        rw [hscan] at ih
        cases stop with
        | unsupportedContentType =>
            rcases ih with ⟨contentType, hcontentType, hsupported⟩
            exact ⟨contentType,
              summarizeRequestHeader_contentType_first?_of_some
                _ _ _ hcontentType,
              hsupported⟩
        | reject status =>
            rcases ih with
              ⟨hstatus, ⟨contentType, hcontentType, hsupported⟩,
                method, hmethod, hmethodValue⟩
            exact ⟨hstatus,
              ⟨contentType,
                summarizeRequestHeader_contentType_first?_of_some
                  _ _ _ hcontentType,
                hsupported⟩,
              method,
              summarizeRequestHeader_method?_of_some _ _ _ hmethod,
              hmethodValue⟩
    | ok state =>
        change RequestHeaderScanMatches (scanRequestHeader state header)
          (summarizeRequestHeader
            (Array.foldl summarizeRequestHeader {} values) header)
        rw [hscan] at ih
        cases state with
        | summarize summary =>
            rcases ih with ⟨rfl, hcontentType, hmethod⟩
            exact scanRequestHeader_summarize_matches _ _ hcontentType hmethod
        | pendingReject status =>
            rcases ih with ⟨hstatus, hcontentType, hmethod⟩
            exact scanRequestHeader_pending_matches _ _ _ hstatus hcontentType hmethod

private theorem requestHeaderPreflightValidatedSummary_invalidMethod
    (summary : RequestHeaderSummary) (method : String)
    (hmethod : summary.method? = some method) (hmethodValue : method ≠ "POST") :
    requestHeaderPreflightValidatedSummary summary =
      .reject invalidMethodStatus := by
  have hcore : validateUnaryRequestSummaryCore summary =
      .error (Status.invalidArgument "gRPC requests must use POST") := by
    unfold validateUnaryRequestSummaryCore
    rw [hmethod]
    simp [bind, Except.bind, throw, throwThe,
      MonadExceptOf.throw]
  unfold requestHeaderPreflightValidatedSummary validateUnaryRequestSummary
    invalidMethodStatus
  rw [hcore]
  rfl

private theorem finishRequestHeaderScan_matches
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState)
    (summary : RequestHeaderSummary)
    (hmatches : RequestHeaderScanMatches outcome summary) :
    finishRequestHeaderScan outcome = requestHeaderPreflightSummary summary := by
  cases outcome with
  | error stop =>
      cases stop with
      | unsupportedContentType =>
          rcases hmatches with ⟨contentType, hcontentType, hsupported⟩
          simp [finishRequestHeaderScan, requestHeaderScanStopResult,
            requestHeaderPreflightSummary, hcontentType, hsupported]
      | reject status =>
          rcases hmatches with
            ⟨hstatus, ⟨contentType, hcontentType, hsupported⟩,
              method, hmethod, hmethodValue⟩
          subst status
          have hvalidated := requestHeaderPreflightValidatedSummary_invalidMethod
            summary method hmethod hmethodValue
          simp [finishRequestHeaderScan, requestHeaderScanStopResult,
            requestHeaderPreflightSummary, hcontentType, hsupported, hvalidated]
  | ok state =>
      cases state with
      | summarize scanned =>
          rcases hmatches with ⟨rfl, hcontentType, _⟩
          cases hfirst : scanned.contentType.first? with
          | none =>
              simp [finishRequestHeaderScan, requestHeaderPreflightSummary,
                hfirst]
          | some contentType =>
              simp [firstContentTypeSupported, hfirst] at hcontentType
              simp [finishRequestHeaderScan, requestHeaderPreflightSummary,
                hfirst, hcontentType]
      | pendingReject status =>
          rcases hmatches with
            ⟨hstatus, hcontentType, method, hmethod, hmethodValue⟩
          subst status
          have hvalidated := requestHeaderPreflightValidatedSummary_invalidMethod
            summary method hmethod hmethodValue
          simp [finishRequestHeaderScan, requestHeaderPreflightSummary,
            hcontentType, hvalidated]

private theorem finishRequestHeaderScan_eq_logical (metadata : Metadata) :
    finishRequestHeaderScan (scanRequestHeadersCandidate metadata) =
      requestHeaderPreflightCandidateLogical metadata := by
  unfold requestHeaderPreflightCandidateLogical
  exact finishRequestHeaderScan_matches _ _
    (scanRequestHeadersCandidate_matches metadata)

private def requestHeaderPreflightPendingMethodDirect
    (metadata : Metadata) (index : Nat) (status : Status) :
    RequestHeaderPreflightResult :=
  if h : index < metadata.size then
    let header := metadata[index]
    let next := index + 1
    match header.name.utf8ByteSize with
    | 12 =>
        if header.name == "content-type" then
          if isGrpcContentType header.value then
            .reject status
          else
            .unsupportedContentType
        else
          requestHeaderPreflightPendingMethodDirect metadata next status
    | _ => requestHeaderPreflightPendingMethodDirect metadata next status
  else
    .reject status
termination_by metadata.size - index
decreasing_by all_goals omega

private def requestHeaderPreflightCandidateDirectLoop (metadata : Metadata)
    (index : Nat) (summary : RequestHeaderSummary) :
    RequestHeaderPreflightResult :=
  if h : index < metadata.size then
    let header := metadata[index]
    let next := index + 1
    match header.name.utf8ByteSize with
    | 2 =>
        if header.name == "te" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with te := summary.te.add header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | 5 =>
        if header.name == ":path" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with path? := rememberFirst summary.path? header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | 7 =>
        if header.name == ":method" then
          match summary.method? with
          | some _ => requestHeaderPreflightCandidateDirectLoop metadata next summary
          | none =>
              if header.value == "POST" then
                requestHeaderPreflightCandidateDirectLoop metadata next
                  { summary with method? := some header.value }
              else
                match summary.contentType.first? with
                | some _ => .reject invalidMethodStatus
                | none =>
                    requestHeaderPreflightPendingMethodDirect metadata next
                      invalidMethodStatus
        else if header.name == ":scheme" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with scheme? := rememberFirst summary.scheme? header.value }
        else if header.name == ":status" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with status? := rememberFirst summary.status? header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | 12 =>
        if header.name == "content-type" then
          match summary.contentType.first? with
          | some _ =>
              requestHeaderPreflightCandidateDirectLoop metadata next
                { summary with contentType := summary.contentType.add header.value }
          | none =>
              if isGrpcContentType header.value then
                requestHeaderPreflightCandidateDirectLoop metadata next
                  { summary with contentType := summary.contentType.add header.value }
              else
                .unsupportedContentType
        else if header.name == "grpc-timeout" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with timeout := summary.timeout.add header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | 13 =>
        if header.name == "grpc-encoding" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with requestEncoding := summary.requestEncoding.add header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | 14 =>
        if header.name == "content-length" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with contentLength := summary.contentLength.add header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | 20 =>
        if header.name == "grpc-accept-encoding" then
          requestHeaderPreflightCandidateDirectLoop metadata next
            { summary with clientAcceptEncodingValues :=
                summary.clientAcceptEncodingValues.push header.value }
        else
          requestHeaderPreflightCandidateDirectLoop metadata next summary
    | _ => requestHeaderPreflightCandidateDirectLoop metadata next summary
  else
    requestHeaderPreflightValidatedSummary summary
termination_by metadata.size - index
decreasing_by all_goals omega

private def requestHeaderPreflightCandidateDirect (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  requestHeaderPreflightCandidateDirectLoop metadata 0 {}

private theorem requestHeaderPreflightPendingMethodDirect_eq_foldlM
    (metadata : Metadata) (index : Nat) (status : Status) :
    requestHeaderPreflightPendingMethodDirect metadata index status =
      finishRequestHeaderScan
        ((metadata.toList.drop index).foldlM scanRequestHeader
          (.pendingReject status)) := by
  fun_induction requestHeaderPreflightPendingMethodDirect metadata index status <;>
    simp_all +zetaDelta [List.drop_eq_getElem_cons, List.drop_of_length_le,
      scanRequestHeader,
      finishRequestHeaderScan, requestHeaderScanStopResult, bind, Except.bind,
      pure, Except.pure]

private theorem requestHeaderPreflightCandidateDirectLoop_eq_foldlM
    (metadata : Metadata) (index : Nat) (summary : RequestHeaderSummary) :
    requestHeaderPreflightCandidateDirectLoop metadata index summary =
      finishRequestHeaderScan
        ((metadata.toList.drop index).foldlM scanRequestHeader
          (.summarize summary)) := by
  fun_induction requestHeaderPreflightCandidateDirectLoop metadata index summary <;>
    simp_all +zetaDelta [List.drop_eq_getElem_cons, List.drop_of_length_le,
      scanRequestHeader, requestHeaderPreflightPendingMethodDirect_eq_foldlM,
      finishRequestHeaderScan, requestHeaderScanStopResult, bind, Except.bind,
      pure, Except.pure]

private theorem requestHeaderPreflightCandidateDirect_eq_logical
    (metadata : Metadata) :
    requestHeaderPreflightCandidateDirect metadata =
      requestHeaderPreflightCandidateLogical metadata := by
  unfold requestHeaderPreflightCandidateDirect
  rw [requestHeaderPreflightCandidateDirectLoop_eq_foldlM]
  simp only [List.drop_zero, Array.foldlM_toList]
  exact finishRequestHeaderScan_eq_logical metadata

private def requestHeaderPreflightCandidate (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  requestHeaderPreflightCandidateDirect metadata

private theorem requestHeaderPreflightCandidate_eq_logical (metadata : Metadata) :
    requestHeaderPreflightCandidate metadata =
      requestHeaderPreflightReference metadata := by
  unfold requestHeaderPreflightCandidate
  rw [requestHeaderPreflightCandidateDirect_eq_logical]
  unfold requestHeaderPreflightReference requestHeaderPreflightCandidateLogical
    requestHeaderPreflightSummary requestHeaderPreflightValidatedSummary
  rw [summarizeRequestHeadersCandidate_eq_reference]
  simp only [validateUnaryRequestSummary_reference]
  unfold summarizeRequestHeadersReference occurrenceReference
  rfl

/-- Classify already validated request metadata. The logical body retains the
former repeated getters; generated code uses the proved direct index scan and
its prefix-stable short-circuit outcomes. -/
@[implemented_by requestHeaderPreflightCandidate]
def requestHeaderPreflight (metadata : Metadata) : RequestHeaderPreflightResult :=
  requestHeaderPreflightReference metadata

namespace TestSupport

/-- Exact former repeated-scan classifier retained for differential tests. -/
@[noinline] def requestHeaderPreflightReferenceForBenchmark (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  requestHeaderPreflightReference metadata

/-- Executable direct one-pass classifier retained for differential tests. -/
@[noinline] def requestHeaderPreflightCandidateForBenchmark (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  requestHeaderPreflightCandidate metadata

end TestSupport

/-- The executable one-pass classifier has exactly the result of the logical
repeated-scan definition for every metadata array. -/
theorem requestHeaderPreflightCandidate_eq_requestHeaderPreflight
    (metadata : Metadata) :
    TestSupport.requestHeaderPreflightCandidateForBenchmark metadata =
      requestHeaderPreflight metadata := by
  unfold TestSupport.requestHeaderPreflightCandidateForBenchmark
    requestHeaderPreflight
  exact requestHeaderPreflightCandidate_eq_logical metadata

/-- The independent benchmark seams agree for every metadata array. -/
theorem requestHeaderPreflightCandidate_eq_reference (metadata : Metadata) :
    TestSupport.requestHeaderPreflightCandidateForBenchmark metadata =
      TestSupport.requestHeaderPreflightReferenceForBenchmark metadata := by
  unfold TestSupport.requestHeaderPreflightCandidateForBenchmark
    TestSupport.requestHeaderPreflightReferenceForBenchmark
  exact requestHeaderPreflightCandidate_eq_logical metadata

/-! The managed transport historically runs `Metadata.validate` and then the
request classifier above.  The executor below keeps pseudo-header validation
as the unchanged first pass, but fuses ordinary name/value validation with the
classifier scan.  An already determined classifier outcome is retained while
the loop continues validating later headers, so metadata errors still outrank
HTTP 415 and every gRPC semantic rejection. -/

@[inline] private def advanceValidatedRequestHeaderScan
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState)
    (header : Header) : Except RequestHeaderScanStop RequestHeaderScanState :=
  outcome.bind fun state => scanRequestHeader state header

@[inline] private def validateAndScanRequestHeader
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState)
    (header : Header) :
    Except Status (Except RequestHeaderScanStop RequestHeaderScanState) := do
  Metadata.validateHeader header
  pure (advanceValidatedRequestHeaderScan outcome header)

private theorem validateAndScanRequestHeadersList_eq_separate
    (headers : List Header)
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState) :
    headers.foldlM validateAndScanRequestHeader outcome =
      match headers.foldlM (fun _ header => Metadata.validateHeader header)
          PUnit.unit with
      | .error status => .error status
      | .ok _ =>
          .ok (headers.foldl advanceValidatedRequestHeaderScan outcome) := by
  induction headers generalizing outcome with
  | nil => rfl
  | cons header headers ih =>
      simp only [List.foldlM_cons, List.foldl_cons]
      cases hvalidate : Metadata.validateHeader header with
      | error status =>
          simp [validateAndScanRequestHeader, hvalidate, bind, Except.bind]
      | ok result =>
          cases result
          simp only [validateAndScanRequestHeader, hvalidate, bind, Except.bind,
            pure, Except.pure]
          rw [ih]

private theorem validateAndScanRequestHeaders_eq_separate
    (metadata : Metadata)
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState) :
    metadata.foldlM validateAndScanRequestHeader outcome =
      match metadata.forM Metadata.validateHeader with
      | .error status => .error status
      | .ok _ =>
          .ok (metadata.foldl advanceValidatedRequestHeaderScan outcome) := by
  change metadata.foldlM validateAndScanRequestHeader outcome =
    match metadata.foldlM (fun _ header => Metadata.validateHeader header)
        PUnit.unit with
    | .error status => .error status
    | .ok _ =>
        .ok (metadata.foldl advanceValidatedRequestHeaderScan outcome)
  rw [← Array.foldlM_toList, ← Array.foldlM_toList,
    ← Array.foldl_toList]
  exact validateAndScanRequestHeadersList_eq_separate metadata.toList outcome

private theorem advanceValidatedRequestHeaderScanList_eq_foldlM
    (headers : List Header)
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState) :
    headers.foldl advanceValidatedRequestHeaderScan outcome =
      match outcome with
      | .error stop => .error stop
      | .ok state => headers.foldlM scanRequestHeader state := by
  induction headers generalizing outcome with
  | nil => cases outcome <;> rfl
  | cons header headers ih =>
      simp only [List.foldl_cons]
      rw [ih]
      cases outcome with
      | error stop => rfl
      | ok state =>
          simp only [advanceValidatedRequestHeaderScan, bind, Except.bind,
            List.foldlM_cons]
          cases scanRequestHeader state header <;> rfl

private theorem advanceValidatedRequestHeaderScan_eq_foldlM
    (metadata : Metadata)
    (outcome : Except RequestHeaderScanStop RequestHeaderScanState) :
    metadata.foldl advanceValidatedRequestHeaderScan outcome =
      match outcome with
      | .error stop => .error stop
      | .ok state => metadata.foldlM scanRequestHeader state := by
  rw [← Array.foldl_toList]
  cases outcome with
  | error stop =>
      exact advanceValidatedRequestHeaderScanList_eq_foldlM
        metadata.toList (.error stop)
  | ok state =>
      simp only
      rw [← Array.foldlM_toList]
      exact advanceValidatedRequestHeaderScanList_eq_foldlM
        metadata.toList (.ok state)

private def validateRequestHeaderPreflightReference (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  match Metadata.validate metadata with
  | .error status => .reject status
  | .ok () => requestHeaderPreflightReference metadata

private def validateRequestHeaderPreflightCandidateFold (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  match Metadata.validatePseudoHeaders metadata with
  | .error status => .reject status
  | .ok () =>
      match metadata.foldlM validateAndScanRequestHeader
          (.ok (.summarize {})) with
      | .error status => .reject status
      | .ok outcome => finishRequestHeaderScan outcome

private theorem finishRequestHeaderScan_eq_reference (metadata : Metadata) :
    finishRequestHeaderScan (scanRequestHeadersCandidate metadata) =
      requestHeaderPreflightReference metadata := by
  calc
    finishRequestHeaderScan (scanRequestHeadersCandidate metadata) =
        requestHeaderPreflightCandidateLogical metadata :=
      finishRequestHeaderScan_eq_logical metadata
    _ = requestHeaderPreflightReference metadata := by
      have h := requestHeaderPreflightCandidate_eq_logical metadata
      unfold requestHeaderPreflightCandidate at h
      rw [requestHeaderPreflightCandidateDirect_eq_logical] at h
      exact h

private theorem validateRequestHeaderPreflightCandidateFold_eq_reference
    (metadata : Metadata) :
    validateRequestHeaderPreflightCandidateFold metadata =
      validateRequestHeaderPreflightReference metadata := by
  unfold validateRequestHeaderPreflightCandidateFold
    validateRequestHeaderPreflightReference
  rw [Metadata.validate_eq_stages]
  cases hpseudo : Metadata.validatePseudoHeaders metadata with
  | error status => simp [bind, Except.bind]
  | ok result =>
      cases result
      simp only [bind, Except.bind]
      rw [validateAndScanRequestHeaders_eq_separate]
      cases hheaders : metadata.forM Metadata.validateHeader with
      | error status => simp
      | ok result =>
          cases result
          simp only
          rw [advanceValidatedRequestHeaderScan_eq_foldlM]
          exact finishRequestHeaderScan_eq_reference metadata

/-! Allocation-light specialized executor. Accepted requests carry the raw
summary rather than nested `Except` scan state. Once a prefix-stable semantic
result is known, a small continuation validates the suffix without doing more
classifier work. -/

@[inline] private def validateKnownVisibleRequestHeader (header : Header) :
    Except Status Unit :=
  if Ascii.isVisibleString header.value then
    .ok ()
  else
    .error (Status.invalidArgument
      s!"invalid ASCII gRPC metadata value for {header.name}")

@[inline] private def validateNonExtensionRequestHeaderFast (header : Header) :
    Except Status Unit :=
  match header.name.utf8ByteSize with
  | 2 =>
      if header.name == "te" then validateKnownVisibleRequestHeader header
      else Metadata.validateHeader header
  | 5 =>
      if header.name == ":path" then validateKnownVisibleRequestHeader header
      else Metadata.validateHeader header
  | 7 =>
      if header.name == ":method" || header.name == ":scheme" ||
          header.name == ":status" then
        validateKnownVisibleRequestHeader header
      else
        Metadata.validateHeader header
  | 10 =>
      if header.name == ":authority" then validateKnownVisibleRequestHeader header
      else Metadata.validateHeader header
  | 12 =>
      if header.name == "content-type" || header.name == "grpc-timeout" ||
          header.name == "x-request-id" then
        validateKnownVisibleRequestHeader header
      else
        Metadata.validateHeader header
  | 13 =>
      if header.name == "grpc-encoding" || header.name == "authorization" then
        validateKnownVisibleRequestHeader header
      else
        Metadata.validateHeader header
  | 14 =>
      if header.name == "content-length" then validateKnownVisibleRequestHeader header
      else Metadata.validateHeader header
  | 20 =>
      if header.name == "grpc-accept-encoding" then
        validateKnownVisibleRequestHeader header
      else
        Metadata.validateHeader header
  | _ => Metadata.validateHeader header

private theorem validateKnownVisibleRequestHeader_eq_validateHeader
    (header : Header)
    (hname :
      header.name = "te" ∨
      header.name = ":path" ∨
      header.name = ":method" ∨
      header.name = ":scheme" ∨
      header.name = ":status" ∨
      header.name = ":authority" ∨
      header.name = "content-type" ∨
      header.name = "grpc-timeout" ∨
      header.name = "x-request-id" ∨
      header.name = "grpc-encoding" ∨
      header.name = "authorization" ∨
      header.name = "content-length" ∨
      header.name = "grpc-accept-encoding") :
    validateKnownVisibleRequestHeader header =
      Metadata.validateHeader header := by
  rw [Metadata.validateHeader_eq_visible_of_fixedRequestName header hname]
  unfold validateKnownVisibleRequestHeader
  split <;> rfl

private theorem validateNonExtensionRequestHeaderFast_eq_validateHeader
    (header : Header) :
    validateNonExtensionRequestHeaderFast header =
      Metadata.validateHeader header := by
  unfold validateNonExtensionRequestHeaderFast
  split <;> simp_all
  all_goals intro hname
  all_goals apply validateKnownVisibleRequestHeader_eq_validateHeader
  all_goals grind

private def validateRemainingRequestHeadersDirect (metadata : Metadata)
    (index : Nat) (result : RequestHeaderPreflightResult) :
    RequestHeaderPreflightResult :=
  if h : index < metadata.size then
    let header := metadata[index]
    let next := index + 1
    match validateNonExtensionRequestHeaderFast header with
    | .error status => .reject status
    | .ok () => validateRemainingRequestHeadersDirect metadata next result
  else
    result
termination_by metadata.size - index
decreasing_by all_goals omega

private def validatePendingInvalidMethodDirect (metadata : Metadata)
    (index : Nat) (status : Status) : RequestHeaderPreflightResult :=
  if h : index < metadata.size then
    let header := metadata[index]
    let next := index + 1
    match validateNonExtensionRequestHeaderFast header with
    | .error status => .reject status
    | .ok () =>
        match header.name.utf8ByteSize with
        | 12 =>
            if header.name == "content-type" then
              if isGrpcContentType header.value then
                validateRemainingRequestHeadersDirect metadata next (.reject status)
              else
                validateRemainingRequestHeadersDirect metadata next
                  .unsupportedContentType
            else
              validatePendingInvalidMethodDirect metadata next status
        | _ => validatePendingInvalidMethodDirect metadata next status
  else
    .reject status
termination_by metadata.size - index
decreasing_by all_goals omega

private def validateRequestHeaderPreflightFusedDirectLoop (metadata : Metadata)
    (index : Nat) (summary : RequestHeaderSummary) :
    RequestHeaderPreflightResult :=
  if h : index < metadata.size then
    let header := metadata[index]
    let next := index + 1
    match header.name.utf8ByteSize with
    | 2 =>
        if header.name == "te" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with te := summary.te.add header.value }
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 5 =>
        if header.name == ":path" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with path? := rememberFirst summary.path? header.value }
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 7 =>
        if header.name == ":method" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              match summary.method? with
              | some _ =>
                  validateRequestHeaderPreflightFusedDirectLoop metadata next summary
              | none =>
                  if header.value == "POST" then
                    validateRequestHeaderPreflightFusedDirectLoop metadata next
                      { summary with method? := some header.value }
                  else
                    match summary.contentType.first? with
                    | some _ =>
                        validateRemainingRequestHeadersDirect metadata next
                          (.reject invalidMethodStatus)
                    | none =>
                        validatePendingInvalidMethodDirect metadata next
                          invalidMethodStatus
        else if header.name == ":scheme" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with scheme? := rememberFirst summary.scheme? header.value }
        else if header.name == ":status" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with status? := rememberFirst summary.status? header.value }
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 10 =>
        if header.name == ":authority" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 12 =>
        if header.name == "content-type" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              match summary.contentType.first? with
              | some _ =>
                  validateRequestHeaderPreflightFusedDirectLoop metadata next
                    { summary with contentType := summary.contentType.add header.value }
              | none =>
                  if isGrpcContentType header.value then
                    validateRequestHeaderPreflightFusedDirectLoop metadata next
                      { summary with contentType := summary.contentType.add header.value }
                  else
                    validateRemainingRequestHeadersDirect metadata next
                      .unsupportedContentType
        else if header.name == "grpc-timeout" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with timeout := summary.timeout.add header.value }
        else if header.name == "x-request-id" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 13 =>
        if header.name == "grpc-encoding" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with requestEncoding :=
                    summary.requestEncoding.add header.value }
        else if header.name == "authorization" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 14 =>
        if header.name == "content-length" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with contentLength := summary.contentLength.add header.value }
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | 20 =>
        if header.name == "grpc-accept-encoding" then
          match validateKnownVisibleRequestHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next
                { summary with clientAcceptEncodingValues :=
                    summary.clientAcceptEncodingValues.push header.value }
        else
          match Metadata.validateHeader header with
          | .error status => .reject status
          | .ok () =>
              validateRequestHeaderPreflightFusedDirectLoop metadata next summary
    | _ =>
        match Metadata.validateHeader header with
        | .error status => .reject status
        | .ok () =>
            validateRequestHeaderPreflightFusedDirectLoop metadata next summary
  else
    requestHeaderPreflightValidatedSummary summary
termination_by metadata.size - index
decreasing_by all_goals omega

private def validateRequestHeaderPreflightFusedDirect (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  match Metadata.validatePseudoHeaders metadata with
  | .error status => .reject status
  | .ok () => validateRequestHeaderPreflightFusedDirectLoop metadata 0 {}

@[inline] private def finishValidatedRequestHeaderScan
    (outcome : Except Status
      (Except RequestHeaderScanStop RequestHeaderScanState)) :
    RequestHeaderPreflightResult :=
  match outcome with
  | .error status => .reject status
  | .ok outcome => finishRequestHeaderScan outcome

private theorem validateRemainingRequestHeadersDirect_eq_foldlM
    (metadata : Metadata) (index : Nat) (stop : RequestHeaderScanStop) :
    validateRemainingRequestHeadersDirect metadata index
        (requestHeaderScanStopResult stop) =
      finishValidatedRequestHeaderScan
        ((metadata.toList.drop index).foldlM validateAndScanRequestHeader
          (.error stop)) := by
  fun_induction validateRemainingRequestHeadersDirect metadata index
    (requestHeaderScanStopResult stop) <;>
    simp_all +zetaDelta [List.drop_eq_getElem_cons, List.drop_of_length_le,
      validateAndScanRequestHeader, advanceValidatedRequestHeaderScan,
      validateNonExtensionRequestHeaderFast_eq_validateHeader,
      finishValidatedRequestHeaderScan, finishRequestHeaderScan,
      requestHeaderScanStopResult, bind, Except.bind, pure, Except.pure]

private theorem validateRemainingRequestHeadersDirect_reject_eq_foldlM
    (metadata : Metadata) (index : Nat) (status : Status) :
    validateRemainingRequestHeadersDirect metadata index (.reject status) =
      finishValidatedRequestHeaderScan
        ((metadata.toList.drop index).foldlM validateAndScanRequestHeader
          (.error (.reject status))) :=
  validateRemainingRequestHeadersDirect_eq_foldlM metadata index (.reject status)

private theorem validateRemainingRequestHeadersDirect_unsupported_eq_foldlM
    (metadata : Metadata) (index : Nat) :
    validateRemainingRequestHeadersDirect metadata index .unsupportedContentType =
      finishValidatedRequestHeaderScan
        ((metadata.toList.drop index).foldlM validateAndScanRequestHeader
          (.error .unsupportedContentType)) :=
  validateRemainingRequestHeadersDirect_eq_foldlM metadata index
    .unsupportedContentType

private theorem validatePendingInvalidMethodDirect_eq_foldlM
    (metadata : Metadata) (index : Nat) (status : Status) :
    validatePendingInvalidMethodDirect metadata index status =
      finishValidatedRequestHeaderScan
        ((metadata.toList.drop index).foldlM validateAndScanRequestHeader
          (.ok (.pendingReject status))) := by
  fun_induction validatePendingInvalidMethodDirect metadata index status <;>
    simp_all +zetaDelta [List.drop_eq_getElem_cons, List.drop_of_length_le,
      validateAndScanRequestHeader, advanceValidatedRequestHeaderScan,
      validateNonExtensionRequestHeaderFast_eq_validateHeader,
      finishValidatedRequestHeaderScan, finishRequestHeaderScan,
      scanRequestHeader, requestHeaderScanStopResult,
      validateRemainingRequestHeadersDirect_reject_eq_foldlM,
      validateRemainingRequestHeadersDirect_unsupported_eq_foldlM,
      bind, Except.bind, pure, Except.pure]

private theorem validateRequestHeaderPreflightFusedDirectLoop_eq_foldlM
    (metadata : Metadata) (index : Nat) (summary : RequestHeaderSummary) :
    validateRequestHeaderPreflightFusedDirectLoop metadata index summary =
      finishValidatedRequestHeaderScan
        ((metadata.toList.drop index).foldlM validateAndScanRequestHeader
          (.ok (.summarize summary))) := by
  fun_induction validateRequestHeaderPreflightFusedDirectLoop metadata index summary <;>
    simp_all +zetaDelta [List.drop_eq_getElem_cons, List.drop_of_length_le,
      validateAndScanRequestHeader, advanceValidatedRequestHeaderScan,
      validateKnownVisibleRequestHeader_eq_validateHeader,
      finishValidatedRequestHeaderScan, finishRequestHeaderScan,
      scanRequestHeader, requestHeaderScanStopResult,
      validateRemainingRequestHeadersDirect_reject_eq_foldlM,
      validateRemainingRequestHeadersDirect_unsupported_eq_foldlM,
      validatePendingInvalidMethodDirect_eq_foldlM,
      bind, Except.bind, pure, Except.pure]

private theorem validateRequestHeaderPreflightFusedDirect_eq_fold
    (metadata : Metadata) :
    validateRequestHeaderPreflightFusedDirect metadata =
      validateRequestHeaderPreflightCandidateFold metadata := by
  unfold validateRequestHeaderPreflightFusedDirect
    validateRequestHeaderPreflightCandidateFold
  cases hpseudo : Metadata.validatePseudoHeaders metadata with
  | error status => rfl
  | ok result =>
      cases result
      rw [validateRequestHeaderPreflightFusedDirectLoop_eq_foldlM]
      simp only [List.drop_zero, Array.foldlM_toList]
      rfl

private def validateRequestHeaderPreflightCandidate (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  validateRequestHeaderPreflightFusedDirect metadata

private theorem validateRequestHeaderPreflightCandidate_eq_reference
    (metadata : Metadata) :
  validateRequestHeaderPreflightCandidate metadata =
      validateRequestHeaderPreflightReference metadata := by
  unfold validateRequestHeaderPreflightCandidate
  rw [validateRequestHeaderPreflightFusedDirect_eq_fold]
  exact validateRequestHeaderPreflightCandidateFold_eq_reference metadata

/-- Validate and classify managed request metadata.  The logical definition is
the former three-pass sequence; generated code uses the proved two-pass direct
executor while retaining exact metadata and gRPC rejection precedence. -/
@[implemented_by validateRequestHeaderPreflightCandidate]
def validateRequestHeaderPreflight (metadata : Metadata) :
    RequestHeaderPreflightResult :=
  validateRequestHeaderPreflightReference metadata

namespace TestSupport

/-- Exact separate validation/classification sequence retained for tests and
incremental benchmarks. -/
@[noinline] def validateRequestHeaderPreflightReferenceForBenchmark
    (metadata : Metadata) : RequestHeaderPreflightResult :=
  validateRequestHeaderPreflightReference metadata

/-- Executable fused validation/classification sequence retained for tests and
incremental benchmarks. -/
@[noinline] def validateRequestHeaderPreflightCandidateForBenchmark
    (metadata : Metadata) : RequestHeaderPreflightResult :=
  validateRequestHeaderPreflightCandidate metadata

end TestSupport

/-- The executable fused validator has exactly the result of the former
separate production sequence for every metadata array. -/
theorem validateRequestHeaderPreflightCandidate_eq_validateRequestHeaderPreflight
    (metadata : Metadata) :
    TestSupport.validateRequestHeaderPreflightCandidateForBenchmark metadata =
      validateRequestHeaderPreflight metadata := by
  unfold TestSupport.validateRequestHeaderPreflightCandidateForBenchmark
    validateRequestHeaderPreflight
  exact validateRequestHeaderPreflightCandidate_eq_reference metadata

/-- The independent fused and separate benchmark seams agree for every
metadata array. -/
theorem validateRequestHeaderPreflightCandidate_eq_referenceForBenchmark
    (metadata : Metadata) :
    TestSupport.validateRequestHeaderPreflightCandidateForBenchmark metadata =
      TestSupport.validateRequestHeaderPreflightReferenceForBenchmark metadata := by
  unfold TestSupport.validateRequestHeaderPreflightCandidateForBenchmark
    TestSupport.validateRequestHeaderPreflightReferenceForBenchmark
  exact validateRequestHeaderPreflightCandidate_eq_reference metadata

def validateUnaryRequestPreflight (metadata : Metadata) : Except Status RequestPreflight := do
  Metadata.validate metadata
  validateUnaryRequestPreflightAfterMetadata metadata (metadata.getAll "content-type")

def validateUnaryRequestHeaders (metadata : Metadata) : Except Status MethodName := do
  Metadata.validate metadata
  pure (← validateUnaryRequestCoreAfterMetadata metadata
    (metadata.getAll "content-type")).method

def responseHeaders : Metadata :=
  Metadata.empty
    |>.insert ":status" "200"
    |>.insert "content-type" "application/grpc"
    |>.insert "grpc-accept-encoding" acceptedEncodings

private def reservedResponseMetadataName (name : String) : Bool :=
  name.startsWith ":"
    || name == "content-type"
    || name == "grpc-status"
    || name == "grpc-message"
    || name == "grpc-status-details-bin"
    || name == "grpc-accept-encoding"

private def reservedResponseTrailerName (name : String) : Bool :=
  name.startsWith ":"
    || name == "content-type"
    || name == "grpc-status"
    || name == "grpc-message"
    || name == "grpc-accept-encoding"

private def validateOutboundHeader (kind : String) (reserved : String -> Bool)
    (header : Header) : Except Status Unit := do
  let name := Header.normalizeName header.name
  if reserved name then
    throw (Status.internal s!"reserved gRPC {kind} metadata name {name}")
  match Metadata.validateHeader { header with name := name } with
  | .ok _ => pure ()
  | .error status => throw (Status.internal status.messageD)

def validateResponseMetadata (metadata : Metadata) : Except Status Unit :=
  metadata.forM (validateOutboundHeader "response" reservedResponseMetadataName)

def validateResponseTrailers (metadata : Metadata) : Except Status Unit :=
  metadata.forM (validateOutboundHeader "trailer" reservedResponseTrailerName)

def trailers (status : Status) (extra : Metadata := Metadata.empty) : Metadata :=
  let base := Metadata.empty.insert "grpc-status" status.code.toHeaderValue
  let base := match status.message with
    | none => base
    | some message => base.insert "grpc-message" (Percent.encode message)
  base.append extra

def statusFromTrailers (metadata : Metadata) : Except Status Status := do
  Metadata.validate metadata
  let codeValue ← match ← singletonHeader? metadata "grpc-status" with
    | some value => pure value
    | none => throw (Status.unknown "missing grpc-status trailer")
  let code ← match Code.ofString? codeValue with
    | some code => pure code
    | none => throw (Status.unknown s!"invalid grpc-status trailer {codeValue}")
  let message? ← match ← singletonHeader? metadata "grpc-message" with
    | none => pure none
    | some value =>
        match Percent.decode value with
        | .ok message => pure (some message)
        | .error err => throw (Status.unknown s!"invalid grpc-message trailer: {err}")
  pure { code := code, message := message? }

end Headers

end Grpc
