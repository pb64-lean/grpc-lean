import Lean.Elab.Tactic.Decide
import Grpc

namespace EndpointTest

open Grpc

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def endpointCases : List (String × String × Bool × UInt16) := [
  ("api.example.test", "api.example.test", false, 80),
  ("api.example.test:", "api.example.test", false, 80),
  ("api.example.test:7233", "api.example.test:7233", false, 7233),
  ("http://api.example.test", "api.example.test", false, 80),
  ("http://api.example.test/", "api.example.test", false, 80),
  ("https://API.EXAMPLE.TEST", "api.example.test", true, 443),
  ("https://api.example.test:8443/", "api.example.test:8443", true, 8443),
  ("http://127.0.0.1:7233", "127.0.0.1:7233", false, 7233),
  ("https://[::1]:7443", "[::1]:7443", true, 7443)
]

private def rejectedEndpointCases : List (String × Endpoint.ParseError) := [
  ("", .invalidUri),
  ("HTTP://api.example.test", .unsupportedScheme),
  ("grpc://api.example.test", .unsupportedScheme),
  ("http://", .invalidUri),
  ("http://user@api.example.test", .userInfoNotAllowed),
  ("http://api.example.test?", .queryNotAllowed),
  ("http://api.example.test?x=y", .queryNotAllowed),
  ("http://api.example.test#", .fragmentNotAllowed),
  ("http://api.example.test/path", .pathNotAllowed),
  ("http://api.example.test//", .pathNotAllowed),
  ("http://bad_host.example", .invalidUri)
]

private def testEndpoints : IO Unit := do
  for (input, target, useTls, effectivePort) in endpointCases do
    match Endpoint.parse input with
    | .error error =>
        fail s!"valid endpoint {input.quote} was rejected: {repr error}"
    | .ok endpoint =>
        if endpoint.target != target then
          fail s!"endpoint target mismatch for {input.quote}: {endpoint.target}"
        if endpoint.useTls != useTls then
          fail s!"endpoint TLS mismatch for {input.quote}"
        if endpoint.effectivePort != effectivePort then
          fail s!"endpoint port mismatch for {input.quote}"
        let scheme := if useTls then "https://" else "http://"
        let host := match endpoint.serverName with
          | some value =>
              if value.contains ":" then "[" ++ value ++ "]" else value
          | none => ""
        let expectedIdentity :=
          scheme ++ host ++ ":" ++ toString effectivePort
        if endpoint.canonicalIdentity != expectedIdentity then
          fail (s!"endpoint canonical identity mismatch for {input.quote}: " ++
            endpoint.canonicalIdentity)
        if endpoint.serverName.isNone then
          fail s!"endpoint omitted its TLS certificate identity for {input.quote}"
  for (input, expected) in rejectedEndpointCases do
    match Endpoint.parse input with
    | .error actual =>
        if actual != expected then
          fail s!"endpoint {input.quote} failed as {repr actual}, expected {repr expected}"
    | .ok endpoint =>
        fail s!"invalid endpoint {input.quote} was accepted as {endpoint.target}"

private def testCredentialRedaction : IO Unit := do
  let some entry :=
      CredentialEntry.of? "authorization" "Bearer production-api-key"
    | fail "visible ASCII credential entry was rejected"
  if entry.exposeValue != "Bearer production-api-key" then
    fail "credential metadata did not preserve the secret value"
  if entry.name != "authorization" then
    fail "credential metadata did not preserve the entry name"
  if (toString entry).splitOn "production-api-key" != [toString entry] ||
      (reprStr entry).splitOn "production-api-key" != [reprStr entry] then
    fail "credential entry leaked through ordinary rendering"
  if (CredentialEntry.of? "authorization" "Bearer production-api-kéy").isSome then
    fail "non-ASCII credential value crossed the metadata boundary"
  if (CredentialEntry.of? "authorization" "").isSome then
    fail "empty credential value crossed the metadata boundary"
  if (CredentialEntry.of? "Authorization" "Bearer x").isSome then
    fail "uppercase metadata key crossed the metadata boundary"
  if (CredentialEntry.of? "" "Bearer x").isSome then
    fail "empty metadata key crossed the metadata boundary"
  let endpoint ← match Endpoint.parse "https://api.example.test" with
    | .ok endpoint => pure endpoint
    | .error error => fail s!"test endpoint was rejected: {repr error}"
  let credentials := CallCredentials.ofEntries #[entry]
  if toString credentials != "[REDACTED]" ||
      reprStr credentials != "[REDACTED]" then
    fail "call credentials leaked through ordinary rendering"
  let fetched ← credentials.fresh
  if fetched.map (·.exposeValue) != #["Bearer production-api-key"] then
    fail "call credentials did not supply their fixed entries"
  let configuration : Grpc.ManagedChannel.Config := {
    endpoint
    credentials
    deadline := .default
  }
  if (reprStr configuration).contains "production-api-key" then
    fail "channel configuration rendering exposed the credential value"

private def testDeadlines : IO Unit := do
  if RpcDeadline.default.seconds != 10 ||
      RpcDeadline.default.grpcTimeoutValue != "10S" then
    fail "default RPC deadline changed"
  for invalid in [0, maxGrpcTimeoutSeconds + 1] do
    if (RpcDeadline.ofSeconds? invalid).isSome then
      fail s!"invalid RPC deadline {invalid} was accepted"
  for valid in [1, 10, maxGrpcTimeoutSeconds] do
    match RpcDeadline.ofSeconds? valid with
    | none => fail s!"valid RPC deadline {valid} was rejected"
    | some deadline =>
        if deadline.grpcTimeoutValue != s!"{valid}S" then
          fail s!"RPC deadline {valid} had the wrong wire value"

example :
    (Endpoint.parse "https://api.example.test").toOption.map
        (fun endpoint => endpoint.useTls) = some true := by
  native_decide

example :
    RpcDeadline.default.seconds > 0 ∧
      RpcDeadline.default.seconds <= maxGrpcTimeoutSeconds := by
  native_decide

end EndpointTest

def main : IO Unit := do
  EndpointTest.testEndpoints
  EndpointTest.testCredentialRedaction
  EndpointTest.testDeadlines
  IO.println "channel configuration tests passed"
