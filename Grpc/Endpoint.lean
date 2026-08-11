module

public import Std.Http.Data.URI

public section

/-!
# Outbound endpoint parsing

A client shares one gRPC channel across the remote services it calls.  This
module is the pure endpoint boundary in front of that channel: parsing accepts
the conventional `host[:port]` and `http(s)://host[:port]` transport shapes
while applying strict numeric-port and host validation at the production
boundary.

DNS resolution, trust-anchor loading, TLS, socket ownership, and generated
service stubs are effectful adapter responsibilities.  They receive only the
refined values defined here.
-/

namespace Grpc

inductive Scheme where
  | http
  | https
deriving BEq, DecidableEq, Repr

namespace Scheme

def useTls : Scheme → Bool
  | .http => false
  | .https => true

def defaultPort : Scheme → UInt16
  | .http => 80
  | .https => 443

def text : Scheme → String
  | .http => "http"
  | .https => "https"

end Scheme

/--
An endpoint accepted by the production client.

An absent explicit port also represents the bare `host:` spelling accepted by
Java-style URI parsing, which observes the port as `-1` and emits only `host`.
The private constructor prevents paths, user information, queries, fragments,
unsupported schemes, or out-of-range ports from entering the connector.
-/
structure Endpoint where
  private mk ::
  scheme : Scheme
  host : Std.Http.URI.Host
  explicitPort : Option UInt16
deriving BEq, Repr

namespace Endpoint

def target (endpoint : Endpoint) : String :=
  let host := toString endpoint.host
  match endpoint.explicitPort with
  | none => host
  | some port => host ++ ":" ++ toString port

def effectivePort (endpoint : Endpoint) : UInt16 :=
  endpoint.explicitPort.getD endpoint.scheme.defaultPort

def useTls (endpoint : Endpoint) : Bool :=
  endpoint.scheme.useTls

def authority (endpoint : Endpoint) : String :=
  endpoint.target

/--
A stable, credential-free identity for the parsed transport endpoint.
Explicit and implicit default ports normalize to the same value, domain names
are already lowercase-normalized by `Std.Http.URI`, and IP literals use their
canonical parser representation.
-/
def canonicalIdentity (endpoint : Endpoint) : String :=
  endpoint.scheme.text ++ "://" ++ toString endpoint.host ++ ":" ++
    toString endpoint.effectivePort

def serverName (endpoint : Endpoint) : Option String :=
  match endpoint.host with
  | .name name => some name.val
  | .ipv4 address => some (toString address)
  | .ipv6 address => some (toString address)

/-- Endpoint construction makes the transport choice a function of the scheme. -/
theorem tls_iff_https (endpoint : Endpoint) :
    endpoint.useTls = true ↔ endpoint.scheme = .https := by
  constructor
  · intro usesTls
    cases scheme : endpoint.scheme with
    | http => simp [useTls, Scheme.useTls, scheme] at usesTls
    | https => rfl
  · intro https
    simp [useTls, Scheme.useTls, https]

/-- An omitted port has exactly the scheme's default effective port. -/
theorem omitted_port_uses_scheme_default
    (endpoint : Endpoint) (omitted : endpoint.explicitPort = none) :
    endpoint.effectivePort = endpoint.scheme.defaultPort := by
  simp [effectivePort, omitted]

inductive ParseError where
  | invalidUri
  | unsupportedScheme
  | missingAuthority
  | userInfoNotAllowed
  | queryNotAllowed
  | fragmentNotAllowed
  | pathNotAllowed
deriving BEq, DecidableEq, Repr

end Endpoint

def normalizeAddress (address : String) : String :=
  if address.contains "://" then address else "http://" ++ address

private def parseScheme (normalized : String) : Except Endpoint.ParseError Scheme :=
  if normalized.startsWith "http://" then
    .ok .http
  else if normalized.startsWith "https://" then
    .ok .https
  else
    .error .unsupportedScheme

private def parsedPort? : Std.Http.URI.Port → Option UInt16
  | .omitted | .empty => none
  | .value port => some port

/--
Parse an outbound endpoint under the conventional client scheme/path policy: a
missing scheme means `http`, only lower-case `http`/`https` are accepted, and
the path may only be empty or `/`.

`Std.Http.URI` deliberately applies strict host and UInt16 port validation, so
malformed hosts and out-of-range ports never reach the connector.
-/
def Endpoint.parse (address : String) : Except ParseError Endpoint := do
  let normalized := normalizeAddress address
  let uri ← match Std.Http.URI.parse? normalized with
    | some uri => pure uri
    | none => .error .invalidUri
  -- Only the exact lower-case scheme spellings are accepted.
  let scheme ← parseScheme normalized
  let authority ← match uri.authority with
    | some authority => pure authority
    | none => .error .missingAuthority
  if authority.userInfo.isSome then
    .error .userInfoNotAllowed
  -- `URI.Query` cannot distinguish no query from a trailing bare `?`.
  -- Both nonempty and empty query components are rejected.
  if normalized.contains "?" then
    .error .queryNotAllowed
  if uri.fragment.isSome then
    .error .fragmentNotAllowed
  let path := toString uri.path
  if path != "" && path != "/" then
    .error .pathNotAllowed
  pure (.mk scheme authority.host (parsedPort? authority.port))

end Grpc
