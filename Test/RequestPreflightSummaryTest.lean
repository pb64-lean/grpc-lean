import Grpc

open Grpc

namespace Test.RequestPreflightSummary

private abbrev PreflightResult := Headers.RequestHeaderPreflightResult

private def fail (message : String) : IO α :=
  throw (IO.userError message)

private def expect (condition : Bool) (message : String) : IO Unit := do
  unless condition do
    fail message

private def expectOk (context : String) (result : Except Status α) : IO α := do
  match result with
  | .ok value => pure value
  | .error status => fail s!"{context}: {status.code}: {status.messageD}"

private def reference (metadata : Metadata) : PreflightResult :=
  Headers.TestSupport.requestHeaderPreflightReferenceForBenchmark metadata

private def candidate (metadata : Metadata) : PreflightResult :=
  Headers.TestSupport.requestHeaderPreflightCandidateForBenchmark metadata

private def expectExact (label : String) (metadata : Metadata)
    (expected? : Option PreflightResult := none) : IO Unit := do
  let referenceResult := reference metadata
  let candidateResult := candidate metadata
  expect (candidateResult == referenceResult) <|
    s!"{label}: candidate result differs from the exact repeated-scan reference; " ++
      s!"reference={repr referenceResult}, candidate={repr candidateResult}"
  match expected? with
  | none => pure ()
  | some expected =>
      expect (referenceResult == expected) <|
        s!"{label}: reference result differs from the independent expectation; " ++
          s!"expected={repr expected}, actual={repr referenceResult}"

private def method : MethodName := {
  service := "acme.v1.WidgetService"
  method := "CreateWidget"
}

private def unknownMethod : MethodName := {
  service := "acme.v1.WidgetService"
  method := "MissingWidget"
}

private def basePseudoHeaders (scheme : String := "https")
    (path : String := method.path) : List Header := [
  Header.of ":method" "POST",
  Header.of ":scheme" scheme,
  Header.of ":path" path,
  Header.of ":authority" "widgets.internal"
]

private def metadataFrom (pseudo regular : List Header) : Metadata :=
  (pseudo ++ regular).foldl (fun metadata header => metadata.push header) Metadata.empty

private def pushOptional (metadata : Metadata) (name : String) :
    Option String → Metadata
  | none => metadata
  | some value => metadata.insert name value

private def replaceValues (metadata : Metadata) (name : String)
    (values : Array String) : Metadata :=
  let key := Header.normalizeName name
  let retained := metadata.filter fun header => header.name != key
  values.foldl (fun result value => result.insert name value) retained

private def replaceHeaderValue (metadata : Metadata) (name value : String) : Metadata :=
  let key := Header.normalizeName name
  metadata.map fun header =>
    if header.name == key then { header with value := value } else header

private def minimalAccepted (path : String := method.path) : Metadata :=
  metadataFrom (basePseudoHeaders (path := path)) [
    Header.of "content-type" "application/grpc",
    Header.of "te" "trailers"
  ]

private structure TimeoutCase where
  label : String
  raw? : Option String
  expected : Option Timeout

private def timeoutCases : Array TimeoutCase := #[
  { label := "absent", raw? := none, expected := none },
  { label := "hour", raw? := some "1H",
    expected := some { value := 1, unit := .hour } },
  { label := "minute", raw? := some "2M",
    expected := some { value := 2, unit := .minute } },
  { label := "second", raw? := some "3S",
    expected := some { value := 3, unit := .second } },
  { label := "millisecond", raw? := some "250m",
    expected := some { value := 250, unit := .millisecond } },
  { label := "microsecond", raw? := some "17u",
    expected := some { value := 17, unit := .microsecond } },
  { label := "nanosecond-boundary", raw? := some "99999999n",
    expected := some { value := 99999999, unit := .nanosecond } },
  { label := "leading-zero", raw? := some "00000001S",
    expected := some { value := 1, unit := .second } }
]

private structure ContentLengthCase where
  label : String
  raw? : Option String
  expected : Option Nat

private def contentLengthCases : Array ContentLengthCase := #[
  { label := "absent", raw? := none, expected := none },
  { label := "zero", raw? := some "0", expected := some 0 },
  { label := "one", raw? := some "1", expected := some 1 },
  { label := "uint64-max", raw? := some "18446744073709551615",
    expected := some 18446744073709551615 },
  { label := "boxed-nat", raw? := some "18446744073709551616",
    expected := some 18446744073709551616 }
]

private structure EncodingCase where
  label : String
  raw? : Option String
  usesGzip : Bool

private def encodingCases : Array EncodingCase := #[
  { label := "absent", raw? := none, usesGzip := false },
  { label := "identity", raw? := some "identity", usesGzip := false },
  { label := "gzip", raw? := some "gzip", usesGzip := true }
]

private structure AcceptEncodingCase where
  label : String
  values : Array String
  acceptsGzip : Bool

private def acceptEncodingCases : Array AcceptEncodingCase := #[
  { label := "absent", values := #[], acceptsGzip := false },
  { label := "identity", values := #["identity"], acceptsGzip := false },
  { label := "case-sensitive", values := #["GZIP"], acceptsGzip := false },
  { label := "parameter-not-token", values := #["gzip;q=1"], acceptsGzip := false },
  { label := "gzip", values := #["gzip"], acceptsGzip := true },
  { label := "comma-list", values := #["identity, gzip"], acceptsGzip := true },
  { label := "duplicate-second-match", values := #["br", " identity , gzip "],
    acceptsGzip := true }
]

/- Exhaust every combination of the accepted wire values that affect the
managed preflight result.  The expected value is constructed independently,
so this checks more than reference/candidate agreement. -/
private def testAcceptedCartesianProduct : IO Nat := do
  let schemes : Array String := #["http", "https"]
  let contentTypes : Array String := #["application/grpc", "application/grpc+proto"]
  let mut checked := 0
  for scheme in schemes do
    for contentType in contentTypes do
      for timeoutCase in timeoutCases do
        for lengthCase in contentLengthCases do
          for encodingCase in encodingCases do
            for acceptCase in acceptEncodingCases do
              let metadata := metadataFrom (basePseudoHeaders scheme) [
                Header.of "te" "trailers",
                Header.of "content-type" contentType
              ]
              let metadata := pushOptional metadata "grpc-timeout" timeoutCase.raw?
              let metadata := pushOptional metadata "content-length" lengthCase.raw?
              let metadata := pushOptional metadata "grpc-encoding" encodingCase.raw?
              let metadata := acceptCase.values.foldl
                (fun result value => result.insert "grpc-accept-encoding" value) metadata
              let expected : Headers.RequestPreflight := {
                method
                timeout := timeoutCase.expected
                contentLength := lengthCase.expected
                requestUsesGzip := encodingCase.usesGzip
                clientAcceptsGzip := acceptCase.acceptsGzip
              }
              let label := s!"accepted/{scheme}/{contentType}/{timeoutCase.label}/" ++
                s!"{lengthCase.label}/{encodingCase.label}/{acceptCase.label}"
              expectExact label metadata (some (.accept expected))
              checked := checked + 1
  expect (checked == 3360)
    s!"accepted Cartesian corpus checked {checked} cases instead of 3,360"
  pure checked

private def insertEverywhere (value : α) : List α → List (List α)
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
        (insertEverywhere value tail).map (fun suffix => head :: suffix)

private def permutations : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      (permutations tail).flatMap (insertEverywhere head)

/- Every regular-header ordering must produce the same parsed facts.  Pseudo
headers are permuted separately while remaining before regular metadata, as
required by HTTP/2. -/
private def testPermutations : IO Nat := do
  let regular : List Header := [
    Header.of "content-type" "application/grpc+proto",
    Header.of "te" "trailers",
    Header.of "grpc-timeout" "250m",
    Header.of "content-length" "18446744073709551616",
    Header.of "grpc-encoding" "gzip",
    Header.of "grpc-accept-encoding" "identity, gzip",
    Header.of "x-request-id" "permutation-control"
  ]
  let expected : PreflightResult := .accept {
    method
    timeout := some { value := 250, unit := .millisecond }
    contentLength := some 18446744073709551616
    requestUsesGzip := true
    clientAcceptsGzip := true
  }
  let mut checked := 0
  for ordering in permutations regular do
    expectExact s!"regular-permutation/{checked}"
      (metadataFrom (basePseudoHeaders) ordering) (some expected)
    checked := checked + 1
  expect (checked == 5040)
    s!"regular-header corpus checked {checked} permutations instead of 5,040"

  let fixedRegular : List Header := [
    Header.of "content-type" "application/grpc",
    Header.of "te" "trailers"
  ]
  let mut pseudoChecked := 0
  for ordering in permutations (basePseudoHeaders) do
    let metadata := metadataFrom ordering fixedRegular
    match Metadata.validate metadata with
    | .error status =>
        fail s!"pseudo-permutation/{pseudoChecked}: unexpectedly invalid: {status.messageD}"
    | .ok () => pure ()
    expectExact s!"pseudo-permutation/{pseudoChecked}" metadata
      (some (.accept {
        method
        timeout := none
        contentLength := none
        requestUsesGzip := false
        clientAcceptsGzip := false
      }))
    pseudoChecked := pseudoChecked + 1
  expect (pseudoChecked == 24)
    s!"pseudo-header corpus checked {pseudoChecked} permutations instead of 24"
  pure (checked + pseudoChecked)

private def duplicateStatus (name : String) : Status :=
  Status.invalidArgument s!"duplicate {Header.normalizeName name} header"

private def testSingletonDuplicates : IO Nat := do
  let base := minimalAccepted
  let cases : Array (String × Metadata × PreflightResult) := #[
    ("content-type/unsupported-first",
      replaceValues base "content-type" #["application/json", "application/grpc"],
      .unsupportedContentType),
    ("content-type/supported-first",
      replaceValues base "content-type" #["application/grpc", "application/json"],
      .reject (duplicateStatus "content-type")),
    ("content-type/two-supported",
      replaceValues base "content-type" #["application/grpc", "application/grpc+proto"],
      .reject (duplicateStatus "content-type")),
    ("content-type/three",
      replaceValues base "content-type"
        #["application/grpc", "application/grpc", "application/json"],
      .reject (duplicateStatus "content-type")),
    ("te/two-conflicting",
      replaceValues base "te" #["wrong", "trailers"],
      .reject (duplicateStatus "te")),
    ("te/three",
      replaceValues base "te" #["trailers", "trailers", "wrong"],
      .reject (duplicateStatus "te")),
    ("timeout/invalid-then-valid",
      replaceValues base "grpc-timeout" #["bad", "1S"],
      .reject (duplicateStatus "grpc-timeout")),
    ("timeout/three",
      replaceValues base "grpc-timeout" #["1S", "2S", "bad"],
      .reject (duplicateStatus "grpc-timeout")),
    ("content-length/invalid-then-valid",
      replaceValues base "content-length" #["bad", "1"],
      .reject (duplicateStatus "content-length")),
    ("content-length/three",
      replaceValues base "content-length" #["1", "2", "bad"],
      .reject (duplicateStatus "content-length")),
    ("encoding/unsupported-then-gzip",
      replaceValues base "grpc-encoding" #["deflate", "gzip"],
      .reject (duplicateStatus "grpc-encoding")),
    ("encoding/three",
      replaceValues base "grpc-encoding" #["identity", "gzip", "deflate"],
      .reject (duplicateStatus "grpc-encoding"))
  ]
  for (label, metadata, expected) in cases do
    expectExact s!"duplicate/{label}" metadata (some expected)
  pure cases.size

private structure ValidationStage where
  label : String
  good : Header
  bad : Header
  expected : Status
  deriving Inhabited

private def validationStages : Array ValidationStage := #[
  {
    label := "te"
    good := Header.of "te" "trailers"
    bad := Header.of "te" "not-trailers"
    expected := Status.invalidArgument "gRPC requests must send te: trailers"
  },
  {
    label := "timeout"
    good := Header.of "grpc-timeout" "1S"
    bad := Header.of "grpc-timeout" "not-a-timeout"
    expected := Status.invalidArgument "invalid grpc-timeout header not-a-timeout"
  },
  {
    label := "content-length"
    good := Header.of "content-length" "7"
    bad := Header.of "content-length" "not-a-length"
    expected := Status.invalidArgument "invalid content-length header not-a-length"
  },
  {
    label := "encoding"
    good := Header.of "grpc-encoding" "gzip"
    bad := Header.of "grpc-encoding" "deflate"
    expected := Status.unimplemented "unsupported grpc-encoding deflate"
  }
]

private def stagedMetadata (firstInvalid secondInvalid : Nat)
    (order : Array Nat) : Metadata :=
  let regular := order.foldl (init := [Header.of "content-type" "application/grpc"])
    fun headers index =>
      let stage := validationStages[index]!
      headers ++ [if index == firstInvalid || index == secondInvalid then stage.bad else stage.good]
  metadataFrom (basePseudoHeaders) regular

/- Every pair of fallible regular stages is exercised in semantic order and
reverse physical order.  The earlier validation stage, not the first bad
header encountered by the summary fold, must win. -/
private def testErrorPrecedence : IO Nat := do
  let forward : Array Nat := #[0, 1, 2, 3]
  let reverse : Array Nat := #[3, 2, 1, 0]
  let mut checked := 0
  for first in [0:validationStages.size] do
    for second in [first + 1:validationStages.size] do
      let expected : PreflightResult := .reject validationStages[first]!.expected
      expectExact (s!"precedence/{validationStages[first]!.label}-before-" ++
          s!"{validationStages[second]!.label}/forward")
        (stagedMetadata first second forward) (some expected)
      expectExact (s!"precedence/{validationStages[first]!.label}-before-" ++
          s!"{validationStages[second]!.label}/reverse")
        (stagedMetadata first second reverse) (some expected)
      checked := checked + 2

  let wrongMethod := replaceValues (minimalAccepted) ":method" #["GET"]
    |>.insert "grpc-timeout" "bad"
  expectExact "precedence/method-before-timeout" wrongMethod
    (some (.reject (Status.invalidArgument "gRPC requests must use POST")))
  checked := checked + 1

  let unsupportedBeforeMethod := replaceValues wrongMethod "content-type" #["application/json"]
  expectExact "precedence/http-415-before-method" unsupportedBeforeMethod
    (some .unsupportedContentType)
  checked := checked + 1

  let badScheme := replaceValues (minimalAccepted) ":scheme" #["ftp"]
    |>.insert "grpc-encoding" "deflate"
  expectExact "precedence/scheme-before-encoding" badScheme
    (some (.reject (Status.invalidArgument "unsupported gRPC scheme ftp")))
  checked := checked + 1

  let statusMetadata := metadataFrom [
      Header.of ":method" "POST",
      Header.of ":scheme" "https",
      Header.of ":status" "200",
      Header.of ":path" "/invalid"
    ] [
      Header.of "content-type" "application/grpc",
      Header.of "te" "trailers"
    ]
  expectExact "precedence/status-before-path" statusMetadata
    (some (.reject (Status.invalidArgument "gRPC requests must not include :status")))
  checked := checked + 1

  let badPath := replaceValues
    (replaceValues (minimalAccepted) ":path" #["/invalid"])
    "content-type" #["application/grpc", "application/grpc+proto"]
  expectExact "precedence/path-before-content-type-duplicate" badPath
    (some (.reject (Status.invalidArgument "invalid gRPC method path /invalid")))
  checked := checked + 1

  pure checked

/- A short-circuiting executable must remain total over arbitrary `Metadata`,
not only metadata admitted by `Metadata.validate`.  These physically invalid
orders put higher-precedence pseudo-header facts after a supported content type
or put a later unsupported content type after the supported first value. -/
private def testArbitraryOrderSuffixSafety : IO Nat := do
  let cases : Array (String × Metadata × PreflightResult) := #[
    ("supported-content-type-before-late-bad-method", #[
        Header.of "content-type" "application/grpc",
        Header.of ":method" "GET",
        Header.of ":scheme" "https",
        Header.of ":path" method.path,
        Header.of "te" "trailers"
      ], .reject (Status.invalidArgument "gRPC requests must use POST")),
    ("pending-bad-scheme-before-later-bad-method", #[
        Header.of ":scheme" "ftp",
        Header.of "content-type" "application/grpc",
        Header.of ":method" "GET",
        Header.of ":path" method.path,
        Header.of "te" "trailers"
      ], .reject (Status.invalidArgument "gRPC requests must use POST")),
    ("invalid-path-before-late-status", #[
        Header.of ":method" "POST",
        Header.of ":scheme" "https",
        Header.of ":path" "/invalid",
        Header.of "content-type" "application/grpc",
        Header.of "te" "trailers",
        Header.of ":status" "200"
      ], .reject (Status.invalidArgument "gRPC requests must not include :status")),
    ("later-unsupported-content-type-is-still-a-duplicate", #[
        Header.of ":method" "POST",
        Header.of ":scheme" "https",
        Header.of ":path" method.path,
        Header.of "content-type" "application/grpc",
        Header.of "te" "trailers",
        Header.of "content-type" "application/json"
      ], .reject (duplicateStatus "content-type"))
  ]
  for (label, metadata, expected) in cases do
    expectExact s!"arbitrary-order/{label}" metadata (some expected)
  pure cases.size

private def testDirectedValues : IO Nat := do
  let base := minimalAccepted
  let timeoutInvalid : Array String := #[
    "", "0S", "123456789S", "1x", "-1S", "+1S", "1.0S", " 1S"
  ]
  let mut checked := 0
  for value in timeoutInvalid do
    expectExact s!"invalid-timeout/{repr value}"
      (replaceValues base "grpc-timeout" #[value])
      (some (.reject (Status.invalidArgument s!"invalid grpc-timeout header {value}")))
    checked := checked + 1

  let lengthInvalid : Array String := #["", "-1", "+1", "1.0", " 1", "1 "]
  for value in lengthInvalid do
    expectExact s!"invalid-content-length/{repr value}"
      (replaceValues base "content-length" #[value])
      (some (.reject (Status.invalidArgument s!"invalid content-length header {value}")))
    checked := checked + 1

  let encodingInvalid : Array String := #["", "GZIP", "deflate", "br"]
  for value in encodingInvalid do
    expectExact s!"unsupported-encoding/{repr value}"
      (replaceValues base "grpc-encoding" #[value])
      (some (.reject (Status.unimplemented s!"unsupported grpc-encoding {value}")))
    checked := checked + 1

  let requiredCases : Array (String × Metadata × PreflightResult) := #[
    ("missing-method", replaceValues base ":method" #[],
      .reject (Status.invalidArgument "missing :method header")),
    ("missing-scheme", replaceValues base ":scheme" #[],
      .reject (Status.invalidArgument "missing :scheme header")),
    ("missing-path", replaceValues base ":path" #[],
      .reject (Status.invalidArgument "missing :path header")),
    ("invalid-path", replaceValues base ":path" #["/invalid"],
      .reject (Status.invalidArgument "invalid gRPC method path /invalid")),
    ("missing-content-type", replaceValues base "content-type" #[],
      .reject (Status.invalidArgument "missing content-type header")),
    ("missing-te", replaceValues base "te" #[],
      .reject (Status.invalidArgument "missing te header")),
    ("wrong-te", replaceValues base "te" #["Trailers"],
      .reject (Status.invalidArgument "gRPC requests must send te: trailers")),
    ("unknown-method-is-header-valid", replaceValues base ":path" #[unknownMethod.path],
      .accept {
        method := unknownMethod
        timeout := none
        contentLength := none
        requestUsesGzip := false
        clientAcceptsGzip := false
      })
  ]
  for (label, metadata, expected) in requiredCases do
    expectExact s!"directed/{label}" metadata (some expected)
  pure (checked + requiredCases.size)

private def decodeRejectedHeaders (frames : Array Http2.Frame) : IO Metadata := do
  let block := frames.foldl (init := ByteArray.empty) fun bytes frame =>
    if frame.header.frameType == .headers || frame.header.frameType == .continuation then
      bytes.append frame.payload
    else
      bytes
  expect (!block.isEmpty) "production rejection did not contain a header block"
  let decoded ← expectOk "decode production rejection" (Http2.Hpack.decodeHeaderBlock {} block)
  pure decoded.headers

private def productionRejectionHeaders (registry : Registry) (metadata : Metadata) :
    IO Metadata := do
  let decision ← expectOk "run production request preflight"
    (Http2.Transport.preflightEarlyRequest registry {} 1 metadata)
  match decision with
  | .accept _ _ => fail "production preflight unexpectedly accepted the request"
  | .reject frames _ => decodeRejectedHeaders frames

private def expectProductionGrpcStatus (label : String) (registry : Registry)
    (metadata : Metadata) (expected : Status) : IO Unit := do
  let headers ← productionRejectionHeaders registry metadata
  let actual ← expectOk s!"{label}: decode gRPC status" (Headers.statusFromTrailers headers)
  expect (actual == expected)
    s!"{label}: production status differs; expected={repr expected}, actual={repr actual}"

private def testProductionPath : IO Nat := do
  let registry := Registry.empty.registerUnary method fun request =>
    pure { data := request.data, status := Status.ok }
  let acceptedMetadata := minimalAccepted
    |>.insert "grpc-timeout" "250m"
    |>.insert "content-length" "7"
    |>.insert "grpc-encoding" "gzip"
    |>.insert "grpc-accept-encoding" "identity, gzip"
  let decision ← expectOk "production registered preflight"
    (Http2.Transport.preflightEarlyRequest registry {} 1 acceptedMetadata)
  match decision with
  | .reject _ _ => fail "production preflight rejected registered valid metadata"
  | .accept entry preflight =>
      expect (entry.name == method && entry.shape == .unary)
        "production preflight selected the wrong registered entry"
      expect (preflight == {
          method
          timeout := some { value := 250, unit := .millisecond }
          contentLength := some 7
          requestUsesGzip := true
          clientAcceptsGzip := true
        }) "production preflight changed accepted parsed facts"

  let unknownMetadata := replaceHeaderValue (minimalAccepted) ":path" unknownMethod.path
  expectProductionGrpcStatus "production/unknown-method" registry unknownMetadata
    (Status.unimplemented s!"unknown gRPC method {unknownMethod.path}")

  let unsupported := replaceValues (minimalAccepted) "content-type" #["application/json"]
  let unsupportedHeaders ← productionRejectionHeaders registry unsupported
  expect (Metadata.get? unsupportedHeaders ":status" == some "415")
    "production unsupported content type did not use HTTP 415"
  expect (Metadata.get? unsupportedHeaders "grpc-status" == none)
    "production HTTP 415 unexpectedly contained a gRPC status"

  let invalidMetadata := (replaceValues
      (replaceHeaderValue (minimalAccepted) ":method" "GET")
      "content-type" #["application/json"])
    |>.push { name := "bad header", value := "x" }
  expectProductionGrpcStatus "production/metadata-before-415" registry invalidMetadata
    (Status.invalidArgument "invalid gRPC metadata name bad header")

  let latePseudo := metadataFrom [Header.of ":method" "POST"] [
    Header.of "content-type" "application/json",
    Header.of ":scheme" "https",
    Header.of ":path" method.path,
    Header.of "te" "trailers"
  ]
  expectProductionGrpcStatus "production/late-pseudo-before-415" registry latePseudo
    (Status.invalidArgument "HTTP/2 pseudo-header :scheme appeared after regular metadata")

  let duplicatePseudo := metadataFrom [
    Header.of ":method" "POST",
    Header.of ":scheme" "http",
    Header.of ":scheme" "https",
    Header.of ":path" method.path
  ] [
    Header.of "content-type" "application/json",
    Header.of "te" "trailers"
  ]
  expectProductionGrpcStatus "production/duplicate-pseudo-before-415" registry duplicatePseudo
    (Status.invalidArgument "duplicate HTTP/2 pseudo-header :scheme")

  let forbidden := replaceValues (minimalAccepted) "content-type" #["application/json"]
    |>.insert "connection" "keep-alive"
  expectProductionGrpcStatus "production/forbidden-before-415" registry forbidden
    (Status.invalidArgument "HTTP/2 connection-specific metadata is forbidden: connection")
  pure 7

def main : IO Unit := do
  let accepted ← testAcceptedCartesianProduct
  let permuted ← testPermutations
  let duplicates ← testSingletonDuplicates
  let precedence ← testErrorPrecedence
  let arbitraryOrder ← testArbitraryOrderSuffixSafety
  let directed ← testDirectedValues
  let production ← testProductionPath
  let total := accepted + permuted + duplicates + precedence + arbitraryOrder + directed +
    production
  IO.println <| s!"request preflight summary matches the exact repeated-scan reference " ++
    s!"across {total} exhaustive and directed cases"

end Test.RequestPreflightSummary

def main : IO Unit :=
  Test.RequestPreflightSummary.main
