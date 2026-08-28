import Grpc
import Http2.NameResolver

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
    (address : _root_.Http2.NameResolver.Address)
    (family : _root_.Http2.NameResolver.Family)
    (host : String) (port : UInt16) : IO Unit := do
  expect (address.family == family) s!"address family changed for {host}"
  expect (address.numericHost == host) s!"numeric address changed for {host}"
  expect (address.port == port) s!"address port changed for {host}"

private def testLiteralBypassesLookup : IO Unit := do
  let calls ← IO.mkRef (#[] : Array (String × UInt16))
  let lookup : _root_.Http2.NameResolver.Lookup := fun host port => do
    calls.modify (·.push (host, port))
    pure (.error (.resolver (IO.userError "literal reached DNS")))
  let ipv4 ← endpoint "http://127.0.0.1:50051"
  let ipv6 ← endpoint "https://[::1]"
  let .ok ipv4Addresses ← Grpc.NameResolver.resolveWith lookup ipv4
    | fail "IPv4 literal resolution failed"
  let .ok ipv6Addresses ← Grpc.NameResolver.resolveWith lookup ipv6
    | fail "IPv6 literal resolution failed"
  expect (ipv4Addresses.size == 1) "IPv4 literal produced multiple addresses"
  expect (ipv6Addresses.size == 1) "IPv6 literal produced multiple addresses"
  expectAddress ipv4Addresses[0]! .ipv4 "127.0.0.1" 50051
  expectAddress ipv6Addresses[0]! .ipv6 "::1" 443
  match ipv4Addresses[0]!.socketAddress with
  | .v4 socket =>
      expect (toString socket == "127.0.0.1:50051")
        "IPv4 socket conversion changed"
  | .v6 _ => fail "IPv4 destination became an IPv6 socket"
  match ipv6Addresses[0]!.socketAddress with
  | .v6 socket =>
      expect (toString socket == "[::1]:443")
        "IPv6 socket conversion changed"
  | .v4 _ => fail "IPv6 destination became an IPv4 socket"
  expect (← calls.get).isEmpty "literal endpoint invoked DNS"

private def testNamedEndpointPolicy : IO Unit := do
  let destination ← endpoint "https://api.example.test:8443"
  let calls ← IO.mkRef (#[] : Array (String × UInt16))
  let lookup : _root_.Http2.NameResolver.Lookup := fun host port => do
    calls.modify (·.push (host, port))
    pure (.ok #[
      "127.0.0.1",
      "127.0.0.1",
      "0:0:0:0:0:0:0:1",
      "::1"
    ])
  let .ok addresses ← Grpc.NameResolver.resolveWith lookup destination
    | fail "fake DNS result was rejected"
  expect ((← calls.get) == #[("api.example.test", 8443)])
    "endpoint resolver did not use the effective host and port exactly once"
  expect (addresses.size == 2)
    "endpoint resolver changed canonical order or duplicate removal"
  expectAddress addresses[0]! .ipv4 "127.0.0.1" 8443
  expectAddress addresses[1]! .ipv6 "::1" 8443
  expect (addresses[1]!.authority == "[::1]:8443")
    "IPv6 connector authority lost brackets"

private def testFailuresRemainSpecific : IO Unit := do
  let destination ← endpoint "api.example.test"
  let sentinel : IO.Error :=
    .permissionDenied (some "dns") 13 "injected resolver failure"
  let failing : _root_.Http2.NameResolver.Lookup := fun _ _ =>
    pure (.error (.resolver sentinel))
  match ← Grpc.NameResolver.resolveWith failing destination with
  | .error (.lookup (.resolver
      (.permissionDenied (some "dns") 13 "injected resolver failure"))) =>
      pure ()
  | _ => fail "resolver lookup error changed shape"
  let invalid : _root_.Http2.NameResolver.Lookup := fun _ _ =>
    pure (.ok #["not-an-address"])
  match ← Grpc.NameResolver.resolveWith invalid destination with
  | .error (.invalidNumericAddress "not-an-address") => pure ()
  | _ => fail "non-numeric native output was accepted"
  let empty : _root_.Http2.NameResolver.Lookup := fun _ _ => pure (.ok #[])
  match ← Grpc.NameResolver.resolveWith empty destination with
  | .error .noAddresses => pure ()
  | _ => fail "empty DNS result was accepted"
  let oversized : _root_.Http2.NameResolver.Lookup := fun _ _ =>
    pure (.ok (
      List.replicate
        (_root_.Http2.NameResolver.maximumRawAddresses + 1)
        "127.0.0.1"
    ).toArray)
  match ← Grpc.NameResolver.resolveWith oversized destination with
  | .error (.tooManyAddresses limit) =>
      expect (limit == _root_.Http2.NameResolver.maximumRawAddresses)
        "raw DNS result cap changed"
  | _ => fail "oversized raw DNS result reached address refinement"

private def testProductionEndpointResolution : IO Unit := do
  let localhost ← endpoint "http://localhost:50051"
  match ← Grpc.NameResolver.resolve localhost with
  | .error error => fail s!"localhost endpoint resolution failed: {error}"
  | .ok addresses =>
      expect (!addresses.isEmpty) "localhost endpoint resolved to no addresses"
      expect (addresses.all (·.port == 50051))
        "localhost endpoint lost its effective port"

def run : IO Unit := do
  testLiteralBypassesLookup
  testNamedEndpointPolicy
  testFailuresRemainSpecific
  testProductionEndpointResolution
  IO.println "gRPC endpoint resolver tests passed"

end NameResolverTest

def main : IO Unit :=
  NameResolverTest.run
