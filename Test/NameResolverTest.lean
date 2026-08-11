import Grpc

namespace NameResolverTest

open Grpc

private def fail (detail : String) : IO α :=
  throw (IO.userError detail)

private def expect (condition : Bool) (detail : String) : IO Unit := do
  unless condition do fail detail

private def endpoint (value : String) : IO Endpoint :=
  match Endpoint.parse value with
  | .ok parsed => pure parsed
  | .error error => fail s!"test endpoint {value.quote} failed: {repr error}"

private def expectAddress
    (address : Grpc.NameResolver.Address)
    (family : Grpc.NameResolver.Family)
    (host : String) (port : UInt16) : IO Unit := do
  expect (address.family == family) s!"address family changed for {host}"
  expect (address.numericHost == host) s!"numeric address changed for {host}"
  expect (address.port == port) s!"address port changed for {host}"

private def testLiteralBypassesLookup : IO Unit := do
  let calls ← IO.mkRef (#[] : Array (String × UInt16))
  let lookup : Grpc.NameResolver.Lookup := fun host port => do
    calls.modify (·.push (host, port))
    pure (.error (.resolver (IO.userError "literal reached DNS")))
  let ipv4 ← endpoint "http://127.0.0.1:7233"
  let ipv6 ← endpoint "https://[::1]"
  let .ok ipv4Addresses ← Grpc.NameResolver.resolveWith lookup ipv4
    | fail "IPv4 literal resolution failed"
  let .ok ipv6Addresses ← Grpc.NameResolver.resolveWith lookup ipv6
    | fail "IPv6 literal resolution failed"
  expect (ipv4Addresses.size == 1) "IPv4 literal produced multiple addresses"
  expect (ipv6Addresses.size == 1) "IPv6 literal produced multiple addresses"
  expectAddress ipv4Addresses[0]! .ipv4 "127.0.0.1" 7233
  expectAddress ipv6Addresses[0]! .ipv6 "::1" 443
  match ipv4Addresses[0]!.socketAddress with
  | .v4 socket =>
      expect (toString socket == "127.0.0.1:7233")
        "IPv4 socket conversion changed"
  | .v6 _ => fail "IPv4 destination became an IPv6 socket"
  match ipv6Addresses[0]!.socketAddress with
  | .v6 socket =>
      expect (toString socket == "[::1]:443")
        "IPv6 socket conversion changed"
  | .v4 _ => fail "IPv6 destination became an IPv4 socket"
  expect (← calls.get).isEmpty "literal endpoint invoked DNS"

private def testPolicyCanonicalizesAndDeduplicates : IO Unit := do
  let endpoint ← endpoint "https://api.example.test:8443"
  let calls ← IO.mkRef (#[] : Array (String × UInt16))
  let lookup : Grpc.NameResolver.Lookup := fun host port => do
    calls.modify (·.push (host, port))
    pure (.ok #[
      "127.0.0.1",
      "127.0.0.1",
      "0:0:0:0:0:0:0:1",
      "::1"
    ])
  let .ok addresses ←
      Grpc.NameResolver.resolveWith lookup endpoint
    | fail "fake DNS result was rejected"
  expect ((← calls.get) == #[("api.example.test", 8443)])
    "resolver did not make exactly one lookup with the effective port"
  expect (addresses.size == 2)
    "resolver did not preserve order and canonical deduplication"
  expectAddress addresses[0]! .ipv4 "127.0.0.1" 8443
  expectAddress addresses[1]! .ipv6 "::1" 8443
  expect (addresses[1]!.authority == "[::1]:8443")
    "IPv6 connector authority lost brackets"

private def testGenericHostResolution : IO Unit := do
  let calls ← IO.mkRef (#[] : Array (String × UInt16))
  let lookup : Grpc.NameResolver.Lookup := fun host port => do
    calls.modify (·.push (host, port))
    pure (.ok #[
      "0:0:0:0:0:0:0:1",
      "::1",
      "192.0.2.10",
      "192.0.2.10"
    ])
  let .ok addresses ← Grpc.NameResolver.resolveHostWith
      lookup "worker.internal" 7443
    | fail "generic host resolution failed"
  expect ((← calls.get) == #[("worker.internal", 7443)])
    "generic resolver did not make exactly one host-and-port lookup"
  expect (addresses.size == 2)
    "generic resolver changed canonical order or duplicate removal"
  expectAddress addresses[0]! .ipv6 "::1" 7443
  expectAddress addresses[1]! .ipv4 "192.0.2.10" 7443

  let oversized : Grpc.NameResolver.Lookup := fun _ _ =>
    pure (.ok (
      List.replicate
        (Grpc.NameResolver.maximumRawAddresses + 1)
        "not-an-address"
    ).toArray)
  match ← Grpc.NameResolver.resolveHostWith
      oversized "bounded.internal" 443 with
  | .error (.tooManyAddresses limit) =>
      expect (limit == Grpc.NameResolver.maximumRawAddresses)
        "generic raw-address cap changed"
  | _ => fail "generic resolver parsed an oversized raw result"

  let invalid : Grpc.NameResolver.Lookup := fun _ _ =>
    pure (.ok #["not-an-address"])
  match ← Grpc.NameResolver.resolveHostWith
      invalid "invalid.internal" 443 with
  | .error (.invalidNumericAddress "not-an-address") => pure ()
  | _ => fail "generic resolver changed invalid-address classification"

private def testUriHostResolution : IO Unit := do
  let calls ← IO.mkRef (#[] : Array (String × UInt16))
  let lookup : Grpc.NameResolver.Lookup := fun host port => do
    calls.modify (·.push (host, port))
    pure (.error (.resolver (IO.userError "literal URI host reached DNS")))
  let ipv4 ← endpoint "http://192.0.2.20"
  let ipv6 ← endpoint "http://[2001:db8::20]"
  let .ok ipv4Addresses ← Grpc.NameResolver.resolveUriHostWith
      lookup ipv4.host 8123
    | fail "typed URI IPv4 resolution failed"
  let .ok ipv6Addresses ← Grpc.NameResolver.resolveUriHostWith
      lookup ipv6.host 9443
    | fail "typed URI IPv6 resolution failed"
  expect (ipv4Addresses.size == 1)
    "typed URI IPv4 produced multiple addresses"
  expect (ipv6Addresses.size == 1)
    "typed URI IPv6 produced multiple addresses"
  expectAddress ipv4Addresses[0]! .ipv4 "192.0.2.20" 8123
  expectAddress ipv6Addresses[0]! .ipv6 "2001:db8::20" 9443
  expect (← calls.get).isEmpty "typed URI literal invoked lookup"

  let named ← endpoint "https://worker.internal"
  let namedCalls ← IO.mkRef (#[] : Array (String × UInt16))
  let namedLookup : Grpc.NameResolver.Lookup := fun host port => do
    namedCalls.modify (·.push (host, port))
    pure (.ok #["198.51.100.7", "198.51.100.7", "::1"])
  let .ok namedAddresses ← Grpc.NameResolver.resolveUriHostWith
      namedLookup named.host 7443
    | fail "named URI host resolution failed"
  expect ((← namedCalls.get) == #[("worker.internal", 7443)])
    "named URI host did not delegate exactly once to bounded lookup"
  expect (namedAddresses.size == 2)
    "named URI host bypassed canonical duplicate removal"
  expectAddress namedAddresses[0]! .ipv4 "198.51.100.7" 7443
  expectAddress namedAddresses[1]! .ipv6 "::1" 7443

private def testFailuresRemainSpecific : IO Unit := do
  let endpoint ← endpoint "api.example.test"
  let sentinel : IO.Error :=
    .permissionDenied (some "dns") 13 "injected resolver failure"
  let failing : Grpc.NameResolver.Lookup := fun _ _ =>
    pure (.error (.resolver sentinel))
  match ← Grpc.NameResolver.resolveWith failing endpoint with
  | .error (.lookup (.resolver
      (.permissionDenied (some "dns") 13 "injected resolver failure"))) =>
      pure ()
  | _ => fail "resolver lookup error changed shape"
  let invalid : Grpc.NameResolver.Lookup := fun _ _ =>
    pure (.ok #["not-an-address"])
  match ← Grpc.NameResolver.resolveWith invalid endpoint with
  | .error (.invalidNumericAddress "not-an-address") => pure ()
  | _ => fail "non-numeric native output was accepted"
  let empty : Grpc.NameResolver.Lookup := fun _ _ => pure (.ok #[])
  match ← Grpc.NameResolver.resolveWith empty endpoint with
  | .error .noAddresses => pure ()
  | _ => fail "empty DNS result was accepted"
  let oversized : Grpc.NameResolver.Lookup := fun _ _ =>
    pure (.ok (
      List.replicate
        (Grpc.NameResolver.maximumRawAddresses + 1)
        "127.0.0.1"
    ).toArray)
  match ← Grpc.NameResolver.resolveWith oversized endpoint with
  | .error (.tooManyAddresses limit) =>
      expect (limit == Grpc.NameResolver.maximumRawAddresses)
        "raw DNS result cap changed"
  | _ => fail "oversized raw DNS result reached quadratic deduplication"

private def testNativeValidationAndLocalhost : IO Unit := do
  let nulHost := "local" ++ String.singleton (Char.ofNat 0) ++ "host"
  match ← Grpc.Dns.getAddrInfo nulHost 80 with
  | .error .embeddedNul => pure ()
  | _ => fail "NUL hostname crossed the DNS boundary"
  match ← Grpc.Dns.getAddrInfo "localhost" 443 with
  | .error error => fail s!"localhost DNS failed: {error}"
  | .ok addresses =>
      expect (!addresses.isEmpty) "localhost resolved to no addresses"
      for address in addresses do
        expect (
          (Std.Net.IPv4Addr.ofString address).isSome ||
          (Std.Net.IPv6Addr.ofString address).isSome)
          s!"localhost DNS returned a non-numeric address: {address}"
  let localhost ← endpoint "http://localhost:7233"
  match ← Grpc.NameResolver.resolve localhost with
  | .error error => fail s!"localhost endpoint resolution failed: {error}"
  | .ok addresses =>
      expect (!addresses.isEmpty) "localhost endpoint resolved to no addresses"
      expect (addresses.all (·.port == 7233))
        "localhost endpoint lost its effective port"

def run : IO Unit := do
  testLiteralBypassesLookup
  testPolicyCanonicalizesAndDeduplicates
  testGenericHostResolution
  testUriHostResolution
  testFailuresRemainSpecific
  testNativeValidationAndLocalhost
  IO.println "network resolver tests passed"

end NameResolverTest

def main : IO Unit :=
  NameResolverTest.run
