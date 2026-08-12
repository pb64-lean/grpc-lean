module

public section

/-!
# Per-call credential metadata

Refined per-call credential entries and their provider seam.  Entry values are
restricted to visible ASCII and entry names to legal lower-case gRPC metadata
keys; every ordinary rendering of an entry or credential set is redacted.
Plaintext access is intentionally named (`CredentialEntry.exposeValue`) and
limited to the call boundary.
-/

namespace Grpc

def isVisibleAsciiMetadataValue (value : String) : Bool :=
  !value.isEmpty && value.toList.all fun character =>
    0x20 <= character.toNat && character.toNat <= 0x7e

/-- A legal lower-case gRPC metadata key with no uppercase or control bytes. -/
def isMetadataKeyName (name : String) : Bool :=
  !name.isEmpty && name.toList.all fun character =>
    character.isLower || character.isDigit ||
      character == '-' || character == '_' || character == '.'

/--
One refined credential metadata entry whose value's only ordinary rendering is
redacted.  Plaintext access is intentionally named and limited to the gRPC
call boundary.
-/
structure CredentialEntry where
  private mk ::
  name : String
  private secret : String
  private validName : isMetadataKeyName name = true
  private validValue : isVisibleAsciiMetadataValue secret = true
deriving DecidableEq

namespace CredentialEntry

def of? (name value : String) : Option CredentialEntry :=
  if validName : isMetadataKeyName name = true then
    if validValue : isVisibleAsciiMetadataValue value = true then
      some (.mk name value validName validValue)
    else
      none
  else
    none

/-- Explicit plaintext access for constructing call metadata. -/
def exposeValue (entry : CredentialEntry) : String :=
  entry.secret

theorem visible_ascii (entry : CredentialEntry) :
    isVisibleAsciiMetadataValue entry.exposeValue = true :=
  entry.validValue

theorem lowercase_name (entry : CredentialEntry) :
    isMetadataKeyName entry.name = true :=
  entry.validName

/-- The `authorization` entry for a checked visible-ASCII header value. -/
def authorization (value : String)
    (h : isVisibleAsciiMetadataValue value = true) : CredentialEntry :=
  .mk "authorization" value (by decide) h

theorem authorization_name (value : String)
    (h : isVisibleAsciiMetadataValue value = true) :
    (authorization value h).name = "authorization" := by
  simp [authorization]

/--
RFC 6750 `token68` shape for bearer tokens:
`1*( ALPHA / DIGIT / "-" / "." / "_" / "~" / "+" / "/" ) *"="`.
An empty body fails, and after the first `=` only further `=` may follow.
-/
def isBearerToken68 (token : String) : Bool :=
  let isBodyChar := fun (character : Char) =>
    character.isAlpha || character.isDigit ||
      character == '-' || character == '.' || character == '_' ||
      character == '~' || character == '+' || character == '/'
  let characters := token.toList
  let body := characters.takeWhile isBodyChar
  !body.isEmpty && (characters.drop body.length).all (· == '=')

/--
`authorization: Bearer <token>` for an RFC 6750 `token68`-shaped token.
Malformed tokens — empty, whitespace-bearing, or containing any character
outside the `token68` alphabet — fail closed with `none` here instead of
composing a header the peer will reject remotely.
-/
def bearer? (token : String) : Option CredentialEntry :=
  if isBearerToken68 token then
    if h : isVisibleAsciiMetadataValue ("Bearer " ++ token) = true then
      some (authorization ("Bearer " ++ token) h)
    else
      none
  else
    none

instance : BEq CredentialEntry where
  beq left right :=
    left.name == right.name && left.exposeValue == right.exposeValue

instance : Repr CredentialEntry where
  reprPrec entry _ := Std.Format.text s!"{entry.name}: [REDACTED]"

instance : ToString CredentialEntry where
  toString entry := s!"{entry.name}: [REDACTED]"

end CredentialEntry

/--
Caller-supplied per-call credentials.  The transport invokes `fresh` once per
call so rotating providers can supply current material; every entry is a
refined `CredentialEntry`, so no unchecked or renderable secret text crosses
the call boundary.  `anonymous` sends no credential metadata.
-/
structure CallCredentials where
  private mk ::
  fresh : IO (Array CredentialEntry)

namespace CallCredentials

/-- Credentials that attach no metadata. -/
def anonymous : CallCredentials :=
  .mk (pure #[])

/-- Fixed credential entries attached to every call. -/
def ofEntries (entries : Array CredentialEntry) : CallCredentials :=
  .mk (pure entries)

/-- Per-call provider; invoked freshly for each transport invocation. -/
def ofProvider (provider : IO (Array CredentialEntry)) : CallCredentials :=
  .mk provider

/--
Fixed bearer-token credentials for every call, when the token is a legal
RFC 6750 `token68`; malformed tokens fail closed with `none`.
-/
def bearer? (token : String) : Option CallCredentials :=
  (CredentialEntry.bearer? token).map fun entry => ofEntries #[entry]

instance : Repr CallCredentials where
  reprPrec _ _ := Std.Format.text "[REDACTED]"

instance : ToString CallCredentials where
  toString _ := "[REDACTED]"

end CallCredentials

end Grpc
