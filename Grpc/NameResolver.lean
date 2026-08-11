module

public import Grpc.Dns
public import Grpc.Endpoint

public section

/-!
# Network host and endpoint resolution

The native boundary returns only observations. Literal-host bypass, numeric
validation, canonicalization, ordering, and duplicate removal are explicit
Lean policy.
-/

namespace Grpc.NameResolver

def maximumRawAddresses : Nat := 64

inductive Family where
  | ipv4
  | ipv6
deriving BEq, DecidableEq, Inhabited, Repr

/--
One canonical numeric destination.

The private constructor ensures every value contains a parsed IP address, so
socket conversion is total and no downstream component re-parses text.
-/
structure Address where
  private mk ::
  private ip : Std.Net.IPAddr
  port : UInt16
deriving DecidableEq, Inhabited

namespace Address

instance : BEq Address where
  beq left right := decide (left = right)

def family (address : Address) : Family :=
  match address.ip with
  | .v4 _ => .ipv4
  | .v6 _ => .ipv6

/-- Canonical numeric host text, without IPv6 URI brackets. -/
def numericHost (address : Address) : String :=
  toString address.ip

/-- Whether this address is in IPv4 127/8 or is the IPv6 loopback address. -/
def isLoopback (address : Address) : Bool :=
  match address.ip with
  | .v4 _ => address.numericHost.startsWith "127."
  | .v6 _ => address.numericHost == "::1"

def authority (address : Address) : String :=
  match address.family with
  | .ipv4 => s!"{address.numericHost}:{address.port.toNat}"
  | .ipv6 => s!"[{address.numericHost}]:{address.port.toNat}"

/-- Convert a refined destination to the standard library's socket address. -/
def socketAddress (address : Address) : Std.Net.SocketAddress :=
  match address.ip with
  | .v4 ip => .v4 { addr := ip, port := address.port }
  | .v6 ip => .v6 { addr := ip, port := address.port }

instance : Repr Address where
  reprPrec address _ := repr address.authority

end Address

inductive Error where
  | lookup (error : Grpc.Dns.Error)
  | invalidNumericAddress (value : String)
  | tooManyAddresses (limit : Nat)
  | noAddresses

namespace Error

def render : Error → String
  | .lookup error => toString error
  | .invalidNumericAddress value =>
      s!"DNS returned a non-numeric address: {value.quote}"
  | .tooManyAddresses limit =>
      s!"DNS returned more than {limit} addresses"
  | .noAddresses => "DNS returned no addresses"

end Error

instance : ToString Error := ⟨Error.render⟩

abbrev Lookup :=
  String → UInt16 →
    IO (Except Grpc.Dns.Error (Array String))

private def canonicalNumeric
    (value : String) : Except Error Std.Net.IPAddr :=
  match Std.Net.IPv4Addr.ofString value with
  | some address => .ok (.v4 address)
  | none =>
      match Std.Net.IPv6Addr.ofString value with
      | some address => .ok (.v6 address)
      | none => .error (.invalidNumericAddress value)

private def pushUnique (addresses : Array Address) (address : Address) :
    Array Address :=
  if addresses.any (· == address) then addresses else addresses.push address

private def refineAddresses
    (port : UInt16) (raw : Array String) : Except Error (Array Address) := do
  let mut addresses := #[]
  for value in raw do
    let ip ← canonicalNumeric value
    addresses := pushUnique addresses (.mk ip port)
  if addresses.isEmpty then
    .error .noAddresses
  else
    .ok addresses

/--
Resolve one host and port using an injected single-operation lookup.

The raw result cap is enforced before numeric parsing or duplicate removal.
Platform order is preserved while canonical duplicate IP addresses are
removed.  Unlike endpoint resolution, this generic entry point has no refined
literal-host value available and therefore always invokes the supplied lookup.
-/
def resolveHostWith
    (lookup : Lookup) (host : String) (port : UInt16) :
    IO (Except Error (Array Address)) := do
  match ← lookup host port with
  | .error error => pure (.error (.lookup error))
  | .ok raw =>
      if raw.size > maximumRawAddresses then
        pure (.error (.tooManyAddresses maximumRawAddresses))
      else
        pure (refineAddresses port raw)

/-- Resolve one host and port through the production native lookup. -/
def resolveHost (host : String) (port : UInt16) :
    IO (Except Error (Array Address)) :=
  resolveHostWith Grpc.Dns.getAddrInfo host port

/--
Resolve one refined URI host and port using an injected lookup.  Typed IP
literals bypass the lookup; domain names use the same bounded generic policy
as `resolveHostWith`.
-/
def resolveUriHostWith
    (lookup : Lookup) (host : Std.Http.URI.Host) (port : UInt16) :
    IO (Except Error (Array Address)) :=
  match host with
  | .ipv4 address => pure (.ok #[.mk (.v4 address) port])
  | .ipv6 address => pure (.ok #[.mk (.v6 address) port])
  | .name name => resolveHostWith lookup name.val port

/-- Resolve one refined URI host and port through the production lookup. -/
def resolveUriHost (host : Std.Http.URI.Host) (port : UInt16) :
    IO (Except Error (Array Address)) :=
  resolveUriHostWith Grpc.Dns.getAddrInfo host port

/--
Resolve an endpoint using an injected single-operation lookup.

URI literals never reach DNS. Named hosts preserve platform order while
deduplicating canonical IP addresses.
-/
def resolveWith
    (lookup : Lookup) (endpoint : Endpoint) :
    IO (Except Error (Array Address)) := do
  resolveUriHostWith lookup endpoint.host endpoint.effectivePort

def resolve (endpoint : Endpoint) : IO (Except Error (Array Address)) :=
  resolveWith Grpc.Dns.getAddrInfo endpoint

end Grpc.NameResolver
