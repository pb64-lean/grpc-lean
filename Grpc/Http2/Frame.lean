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

def maxStreamId : Nat := 2147483647

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

def encodeHeader (header : FrameHeader) : Except Status ByteArray := do
  if header.length > maxFramePayloadLength then
    throw (Status.internal "HTTP/2 frame payload exceeds 24-bit length")
  if header.streamId > maxStreamId then
    throw (Status.internal "HTTP/2 stream id exceeds 31-bit length")
  pure <| ByteArray.empty
    |>.append (u24BE header.length)
    |>.push header.frameType.toUInt8
    |>.push header.flags
    |>.append (u31BE header.streamId)

def decodeHeader (bytes : ByteArray) : Except Status FrameHeader := do
  if bytes.size < frameHeaderSize then
    throw (Status.internal "incomplete HTTP/2 frame header")
  let rawStreamId := readUInt32BE bytes 5
  pure {
    length := readUInt24BE bytes 0,
    frameType := FrameType.ofUInt8 bytes[3]!,
    flags := bytes[4]!,
    streamId := rawStreamId % (maxStreamId + 1)
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

private partial def parseBuffered (buffered : ByteArray) (frames : Array Frame) :
    Except Status DecodeState := do
  if buffered.size < frameHeaderSize then
    pure { buffered := buffered, frames := frames }
  else
    let headerBytes := buffered.extract 0 frameHeaderSize
    let header ← decodeHeader headerBytes
    let endPos := frameHeaderSize + header.length
    if buffered.size < endPos then
      pure { buffered := buffered, frames := frames }
    else
      let payload := buffered.extract frameHeaderSize endPos
      let rest := buffered.extract endPos buffered.size
      parseBuffered rest (frames.push { header := header, payload := payload })

def decodeChunk (state : DecodeState) (chunk : ByteArray) : Except Status DecodeState :=
  parseBuffered (state.buffered.append chunk) #[]

def decodeAll (bytes : ByteArray) : Except Status (Array Frame) := do
  let state ← decodeChunk {} bytes
  if state.buffered.isEmpty then
    pure state.frames
  else
    throw (Status.internal "incomplete HTTP/2 frame")

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
