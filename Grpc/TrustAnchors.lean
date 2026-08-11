module

public import Grpc.Posix
public import TLS13.X509.Chain

public section

/-!
# System trust-anchor loading

Environment precedence and default-path selection are explicit. Reads are
bounded before UTF-8 and strict PEM validation, and an explicitly configured
path is authoritative: a bad explicit file is never hidden by a system
fallback. Linux reads own one descriptor through a consuming close; Darwin
still uses Lean's finalizer-backed file handle and is not claimed as the same
descriptor-custody proof boundary.
-/

namespace Grpc.TrustAnchors

def maximumBundleBytes : Nat := 16 * 1024 * 1024

def sslCertFileVariable : String := "SSL_CERT_FILE"
def nixSslCertFileVariable : String := "NIX_SSL_CERT_FILE"

inductive Platform where
  | linux
  | macos
deriving BEq, DecidableEq, Repr

def defaultPaths : Platform → List System.FilePath
  | .linux => [
      "/etc/ssl/certs/ca-certificates.crt",
      "/etc/pki/tls/certs/ca-bundle.crt",
      "/etc/ssl/ca-bundle.pem",
      "/etc/pki/ca-trust/extracted/pem/tls-ca-bundle.pem",
      "/etc/ssl/cert.pem"
    ]
  | .macos => [
      "/etc/ssl/cert.pem"
    ]

inductive Source where
  | sslCertFile
  | nixSslCertFile
  | system
deriving BEq, DecidableEq, Repr

/--
A size-bounded, UTF-8 certificate PEM bundle containing only X.509 anchors
which the pinned TLS implementation can parse.

System bundles commonly contain roots using algorithms that the deliberately
small TLS implementation does not support.  Loading filters those roots and
re-encodes the usable subset; malformed PEM framing still rejects the entire
file.  The private constructor prevents downstream TLS configuration from
accepting unchecked file contents.
-/
structure Bundle where
  private mk ::
  source : Source
  path : System.FilePath
  pem : String

inductive ValidationError where
  | empty
  | invalidUtf8
  | invalidPem (detail : String)
deriving BEq, DecidableEq, Repr

inductive DescriptorOperation where
  | open
  | read
deriving BEq, DecidableEq, Repr

inductive ReadFailure where
  | io (error : IO.Error)
  | descriptor (operation : DescriptorOperation)
      (error : Grpc.Posix.Errno)
  /-- Linux consumed the descriptor, but `close(2)` reported delayed failure. -/
  | closeDiagnostic (error : Grpc.Posix.Errno)
  | tooLarge (limit : Nat)

inductive Error where
  | emptyExplicitPath (environmentName : String)
  | explicitPathContainsNul (environmentName : String)
  | probe (path : System.FilePath) (error : IO.Error)
  | read (path : System.FilePath) (error : IO.Error)
  | descriptor (path : System.FilePath) (operation : DescriptorOperation)
      (error : Grpc.Posix.Errno)
  | closeDiagnostic (path : System.FilePath)
      (error : Grpc.Posix.Errno)
  | tooLarge (path : System.FilePath) (limit : Nat)
  | validation (path : System.FilePath) (error : ValidationError)
  | noSystemBundle (attempted : List System.FilePath)

namespace Error

def render : Error → String
  | .emptyExplicitPath environmentName =>
      s!"{environmentName} is set to an empty path"
  | .explicitPathContainsNul environmentName =>
      s!"{environmentName} contains NUL"
  | .probe path error =>
      s!"could not inspect trust-anchor path {path}: {error}"
  | .read path error =>
      s!"could not read trust-anchor path {path}: {error}"
  | .descriptor path operation error =>
      let action := match operation with
        | .open => "open"
        | .read => "read"
      s!"could not {action} trust-anchor path {path}: " ++
        Grpc.Posix.strerror error
  | .closeDiagnostic path error =>
      s!"closing trust-anchor path {path} reported: " ++
        Grpc.Posix.strerror error
  | .tooLarge path limit =>
      s!"trust-anchor file {path} exceeds {limit} bytes"
  | .validation path .empty =>
      s!"trust-anchor file {path} is empty"
  | .validation path .invalidUtf8 =>
      s!"trust-anchor file {path} is not UTF-8"
  | .validation path (.invalidPem detail) =>
      s!"trust-anchor file {path} is not a certificate PEM bundle: {detail}"
  | .noSystemBundle attempted =>
      let paths := String.intercalate ", " (attempted.map toString)
      s!"no system trust-anchor bundle exists at: {paths}"

end Error

instance : ToString Error := ⟨Error.render⟩

structure Backend where
  platform : Platform
  getEnvironment : String → IO (Option String)
  probe : System.FilePath → IO (Except IO.Error Bool)
  read : System.FilePath → IO (Except ReadFailure ByteArray)

private def containsNul (value : String) : Bool :=
  value.toList.any (· == Char.ofNat 0)

private def asciiWhitespace (byte : UInt8) : Bool :=
  byte == 0x09 || byte == 0x0a || byte == 0x0b ||
    byte == 0x0c || byte == 0x0d || byte == 0x20

private def base64Alphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/" |>.toList.toArray

@[always_inline]
private def base64Character (index : Nat) : Char :=
  base64Alphabet[index]!

private def encodeBase64 (bytes : ByteArray) : String := Id.run do
  let mut encoded := #[]
  let mut offset := 0
  while offset < bytes.size do
    let first := bytes[offset]!.toNat
    let second := if offset + 1 < bytes.size then bytes[offset + 1]!.toNat else 0
    let third := if offset + 2 < bytes.size then bytes[offset + 2]!.toNat else 0
    let bits := (first <<< 16) ||| (second <<< 8) ||| third
    encoded := encoded.push (base64Character ((bits >>> 18) &&& 0x3f))
    encoded := encoded.push (base64Character ((bits >>> 12) &&& 0x3f))
    encoded := encoded.push <|
      if offset + 1 < bytes.size then
        base64Character ((bits >>> 6) &&& 0x3f)
      else
        '='
    encoded := encoded.push <|
      if offset + 2 < bytes.size then
        base64Character (bits &&& 0x3f)
      else
        '='
    offset := offset + 3
  String.ofList encoded.toList

private def wrapBase64 (encoded : String) : Array String := Id.run do
  let bytes := encoded.toUTF8
  let mut lines := #[]
  let mut offset := 0
  while offset < bytes.size do
    let stop := min (offset + 64) bytes.size
    lines := lines.push (String.fromUTF8! (bytes.extract offset stop))
    offset := stop
  lines

private def encodeCertificate (der : ByteArray) : String :=
  String.intercalate "\n" <| (
    #["-----BEGIN CERTIFICATE-----"] ++
      wrapBase64 (encodeBase64 der) ++
      #["-----END CERTIFICATE-----"]
  ).toList ++ [""]

/--
Validate UTF-8 and strict RFC 7468 framing, then retain exactly the certificate
blocks understood by the pinned X.509 implementation.

Ignoring an unsupported individual root only narrows trust; it cannot add a
trust anchor.  A bundle with no usable certificate is rejected.
-/
def validateBundle (bytes : ByteArray) : Except ValidationError String := do
  if bytes.isEmpty || bytes.data.all asciiWhitespace then
    .error .empty
  let text ← match String.fromUTF8? bytes with
    | some text => pure text
    | none => .error .invalidUtf8
  let blocks ← match TLS13.X509.PEM.decodeBlocks text with
    | .ok blocks => pure blocks
    | .error detail => .error (.invalidPem detail)
  let mut usable := #[]
  let mut certificateCount := 0
  let mut firstFailure : Option String := none
  for block in blocks do
    if block.label == "CERTIFICATE" then
      certificateCount := certificateCount + 1
      if block.der.isEmpty then
        if firstFailure.isNone then
          firstFailure := some "PEM CERTIFICATE block has an empty body"
      else
        match TLS13.X509.Certificate.decode block.der with
        | .ok _ => usable := usable.push block.der
        | .error detail =>
            if firstFailure.isNone then firstFailure := some detail
  if certificateCount == 0 then
    .error (.invalidPem "PEM bundle contains no CERTIFICATE blocks")
  else if usable.isEmpty then
    .error (.invalidPem
      (firstFailure.getD "PEM bundle contains no usable certificate"))
  else
    let normalized := String.join (usable.toList.map encodeCertificate)
    -- Keep this assertion at the exact parser the TLS client uses.
    match TLS13.X509.Chain.TrustStore.decodePEM normalized with
    | .ok _ => .ok normalized
    | .error detail => .error (.invalidPem detail)

private partial def readHandleBounded
    (handle : IO.FS.Handle) (limit : Nat)
    (accumulator : ByteArray := ByteArray.empty) :
    IO (Except ReadFailure ByteArray) := do
  if accumulator.size > limit then
    pure (.error (.tooLarge limit))
  else
    let requested := limit + 1 - accumulator.size
    try
      let bytes ← handle.read (USize.ofNat requested)
      if bytes.isEmpty then
        pure (.ok accumulator)
      else
        readHandleBounded handle limit (accumulator ++ bytes)
    catch error =>
      pure (.error (.io error))

/-!
Linux trust reads use an unbuffered descriptor from acquisition through the
one consuming close.  The backend is public only so descriptor custody and
delayed-close diagnostics can be tested without depending on a particular
host filesystem failure mode. A backend returning `.ok` from `openFile` must
return a valid descriptor and must report `read` and `close` failures through
their structural results rather than throwing; the production Posix backend
satisfies that contract.
-/
inductive LinuxConsumedClose where
  /-- The backend consumed the descriptor; an errno is diagnostic only. -/
  | consumed (diagnostic : Option Grpc.Posix.Errno)
deriving BEq, DecidableEq, Repr

structure LinuxReadBackend where
  openFile : System.FilePath →
    IO (Grpc.Posix.SysResult
      (Grpc.Posix.Fd × UInt64))
  read : Grpc.Posix.Fd → UInt32 →
    IO (Grpc.Posix.SysResult ByteArray)
  close : Grpc.Posix.Fd →
    IO LinuxConsumedClose

def productionLinuxReadBackend : LinuxReadBackend := {
  openFile := fun path =>
    Grpc.Posix.openBoundedRegularInputPathFollowAllowEmpty
      path.toString Grpc.Posix.Constants.signedInt64Max
  read := Grpc.Posix.read
  close := fun descriptor => do
    -- `readFileBoundedLinuxWith` admits only a C `int` descriptor. Therefore
    -- `Grpc.Posix.close` reaches the one-shot syscall, and any error
    -- it returns is a delayed diagnostic after consumption.
    match ← Grpc.Posix.close descriptor with
    | .ok () => pure (.consumed none)
    | .error error => pure (.consumed (some error))
}

private partial def readDescriptorBounded
    (backend : LinuxReadBackend) (descriptor : Grpc.Posix.Fd)
    (limit : Nat) (accumulator : ByteArray := ByteArray.empty) :
    IO (Except ReadFailure ByteArray) := do
  if accumulator.size > limit then
    pure (.error (.tooLarge limit))
  else
    let remaining := limit + 1 - accumulator.size
    let requested := min remaining
      Grpc.Posix.Constants.cIntMax.toNat
    match ← backend.read descriptor (UInt32.ofNat requested) with
    | .error error =>
        if error == Grpc.Posix.Errno.interrupted then
          readDescriptorBounded backend descriptor limit accumulator
        else
          pure (.error (.descriptor .read error))
    | .ok bytes =>
        if bytes.size > requested then
          -- A native read cannot return more than its requested count. Keep
          -- this injectable contract violation structural and bounded.
          pure (.error (.descriptor .read Grpc.Posix.Errno.io))
        else if bytes.isEmpty then
          pure (.ok accumulator)
        else
          readDescriptorBounded backend descriptor limit (accumulator ++ bytes)

private def closeDescriptorRead
    (backend : LinuxReadBackend) (descriptor : Grpc.Posix.Fd)
    (result : Except ReadFailure ByteArray) :
    IO (Except ReadFailure ByteArray) := do
  match ← backend.close descriptor with
  | .consumed none => pure result
  | .consumed (some error) =>
      -- The descriptor is no longer owned, but a delayed close diagnostic is
      -- still a trust-preparation failure and must not be silently discarded.
      pure (.error (.closeDiagnostic error))

/--
Linux implementation with explicit descriptor acquisition, bounded reads, and
exactly one consuming close on every contract-valid accepted-open path.
-/
def readFileBoundedLinuxWith
    (backend : LinuxReadBackend) (path : System.FilePath) (limit : Nat) :
    IO (Except ReadFailure ByteArray) := do
  match ← backend.openFile path with
  | .error error => pure (.error (.descriptor .open error))
  | .ok (descriptor, initialSize) =>
      if descriptor > Grpc.Posix.Constants.cIntMax then
        -- Such a number cannot have come from Linux `open(2)` and is rejected
        -- before this API accepts descriptor custody from an injected backend.
        pure (.error (.descriptor .open
          Grpc.Posix.Errno.invalidArgument))
      else
        let result : Except ReadFailure ByteArray ← try
          if initialSize.toNat > limit then
            pure (.error (.tooLarge limit))
          else
            readDescriptorBounded backend descriptor limit
        catch error =>
          -- A test seam or higher-level wrapper may throw before returning its
          -- structural read result. The descriptor is still exact here, so the
          -- ordinary close path must consume it before the exception is exposed.
          pure (.error (.io error))
        closeDescriptorRead backend descriptor result

/--
Read at most `limit` bytes plus one overflow sentinel byte.

The accumulator can never grow beyond `limit + 1`, even if the underlying file
changes while it is being read.
-/
def readFileBounded
    (path : System.FilePath) (limit : Nat) :
    IO (Except ReadFailure ByteArray) := do
  if System.Platform.isOSX then
    -- Darwin remains on Lean's Handle wrapper until its close boundary grows
    -- the same consuming-diagnostic contract as Linux `close(2)`.
    try
      IO.FS.withFile path IO.FS.Mode.read fun handle =>
        readHandleBounded handle limit
    catch error =>
      pure (.error (.io error))
  else
    readFileBoundedLinuxWith productionLinuxReadBackend path limit

private def productionProbe
    (path : System.FilePath) : IO (Except IO.Error Bool) := do
  try
    discard path.metadata
    pure (.ok true)
  catch error =>
    match error with
    | .noFileOrDirectory .. => pure (.ok false)
    | _ => pure (.error error)

def productionBackend : Backend := {
  platform := if System.Platform.isOSX then .macos else .linux
  getEnvironment := fun name => (IO.getEnv name).toIO
  probe := productionProbe
  read := fun path => readFileBounded path maximumBundleBytes
}

private def loadPath
    (backend : Backend) (source : Source) (path : System.FilePath) :
    IO (Except Error Bundle) := do
  match ← backend.read path with
  | .error (.io error) => pure (.error (.read path error))
  | .error (.descriptor operation error) =>
      pure (.error (.descriptor path operation error))
  | .error (.closeDiagnostic error) =>
      pure (.error (.closeDiagnostic path error))
  | .error (.tooLarge limit) => pure (.error (.tooLarge path limit))
  | .ok bytes =>
      if bytes.size > maximumBundleBytes then
        pure (.error (.tooLarge path maximumBundleBytes))
      else
        match validateBundle bytes with
        | .error error => pure (.error (.validation path error))
        | .ok pem =>
            if pem.toUTF8.size > maximumBundleBytes then
              pure (.error (.tooLarge path maximumBundleBytes))
            else
              pure (.ok (.mk source path pem))

private def explicitPath
    (environmentName value : String) : Except Error System.FilePath :=
  if value.isEmpty then
    .error (.emptyExplicitPath environmentName)
  else if containsNul value then
    .error (.explicitPathContainsNul environmentName)
  else
    .ok (System.FilePath.mk value)

private def loadDefaults
    (backend : Backend) : IO (Except Error Bundle) := do
  let paths := defaultPaths backend.platform
  for path in paths do
    match ← backend.probe path with
    | .error error => return .error (.probe path error)
    | .ok false => pure ()
    | .ok true => return ← loadPath backend .system path
  pure (.error (.noSystemBundle paths))

/-- Load according to `SSL_CERT_FILE`, `NIX_SSL_CERT_FILE`, then platform paths. -/
def loadWith (backend : Backend) : IO (Except Error Bundle) := do
  match ← backend.getEnvironment sslCertFileVariable with
  | some value =>
      match explicitPath sslCertFileVariable value with
      | .error error => pure (.error error)
      | .ok path => loadPath backend .sslCertFile path
  | none =>
      match ← backend.getEnvironment nixSslCertFileVariable with
      | some value =>
          match explicitPath nixSslCertFileVariable value with
          | .error error => pure (.error error)
          | .ok path => loadPath backend .nixSslCertFile path
      | none => loadDefaults backend

def load : IO (Except Error Bundle) :=
  loadWith productionBackend

end Grpc.TrustAnchors
