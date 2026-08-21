import Grpc

/-!
# Request-header preflight summary differential benchmark

Both benchmark-local wrappers perform the unchanged two-pass
`Metadata.validate`.  The reference wrapper then calls the former ten-lookup
classifier, while the candidate wrapper calls the one-scan classifier:
for accepted requests, the scaled comparison is therefore twelve complete
metadata traversals versus three.  Rejected requests retain their
path-specific scan counts: the candidate may stop during its third traversal
when the first content type fixes HTTP 415 or resolves a pending invalid-method
rejection.  An opaque selector chooses one noinline wrapper before warmup or
measurement, and the common recurrence contains only the indirect classifier
call plus a complete result digest.

Every directed fixture is metadata-valid and is checked against an independent
expected result before selection.  The fixture set covers the exact
default-config client base-header shapes (with a caller-selected RPC path),
including authorized and timeout-plus-authorized variants; synthetic accepted
requests at larger widths, every retained preflight field, response-encoding
token handling (including an early rejection with a long irrelevant value),
HTTP-415 precedence, duplicate singleton fields, and ordered semantic errors.
The digest observes every result tag, status field, method component, timeout
component, content length, and compression Boolean.

This executable reports no wall time.  It is intended for whole-process
`perf stat` instruction and branch counters.  Fixture construction, complete
semantic validation, selector construction, requested warmup, checksum checks,
and output are fixed process work; only the selected classification and full
result digest scale with `iterations`.
-/

namespace Grpc.RequestPreflightSummaryBenchmarkHarness

private abbrev Result := Headers.RequestHeaderPreflightResult
private abbrev Outcome := Except Status Result
private abbrev Classifier := Metadata → Outcome

private inductive Mode where
  | reference
  | candidate

/-- Symmetric production prefix plus the exact former repeated-scan seam. -/
@[noinline] private def classifyReference (metadata : Metadata) : Outcome := do
  Metadata.validate metadata
  pure (Headers.TestSupport.requestHeaderPreflightReferenceForBenchmark metadata)

/-- Symmetric production prefix plus the executable one-summary-pass seam. -/
@[noinline] private def classifyCandidate (metadata : Metadata) : Outcome := do
  Metadata.validate metadata
  pure (Headers.TestSupport.requestHeaderPreflightCandidateForBenchmark metadata)

private structure ClassifierBox where
  classify : Classifier
  /-- Keep the opaque choice observable without branching in the recurrence. -/
  candidateSelected : Bool

/-- Select exactly once; no mode value enters the scaling recurrence. -/
@[noinline] private opaque selectClassifierBox (mode : Mode) : ClassifierBox :=
  match mode with
  | .reference => {
      classify := classifyReference
      candidateSelected := false
    }
  | .candidate => {
      classify := classifyCandidate
      candidateSelected := true
    }

private structure Fixture where
  label : String
  metadata : Metadata
  expected : Result
  expectedHeaders : Nat

private def header (name value : String) : Header :=
  Header.of name value

private def requestPrefix (path : String) (method : String := "POST")
    (scheme : String := "https") (authority : String := "benchmark.local") : Metadata :=
  #[
    header ":method" method,
    header ":scheme" scheme,
    header ":path" path,
    header ":authority" authority
  ]

private def fillerHeaders (count : Nat) : Metadata :=
  (Array.range count).map fun index =>
    header s!"x-benchmark-{index}" s!"value-{index}-0123456789abcdef"

private def accepted (service method : String) (timeout : Option Timeout)
    (contentLength : Option Nat) (requestUsesGzip clientAcceptsGzip : Bool) : Result :=
  .accept {
    method := { service, method }
    timeout
    contentLength
    requestUsesGzip
    clientAcceptsGzip
  }

private def rejectedInvalid (message : String) : Result :=
  .reject (Status.invalidArgument message)

private def makeFixtures : Array Fixture :=
  let defaultMetadata :=
    (requestPrefix "/benchmark.Service/Unary" "POST" "http" "localhost").append #[
    header "te" "trailers",
    header "content-type" "application/grpc",
    header "grpc-accept-encoding" "identity,gzip"
  ]
  let clientAuth := defaultMetadata.push <|
    header "authorization" "BenchmarkScheme local-token"
  let clientTimeoutAuth := (defaultMetadata.push <|
    header "grpc-timeout" "250m").push <|
      header "authorization" "BenchmarkScheme local-token"
  let noAccept := (requestPrefix "/benchmark.Service/NoAccept").append #[
    header "content-type" "application/grpc",
    header "te" "trailers"
  ]
  let fullMetadata := (requestPrefix "/benchmark.Service/Full").append #[
    header "content-type" "application/grpc+proto",
    header "te" "trailers",
    header "grpc-timeout" "250m",
    header "content-length" "128",
    header "grpc-encoding" "gzip",
    header "grpc-accept-encoding" "identity, gzip",
    header "x-request-id" "0123456789abcdef"
  ]
  let wideMetadata :=
    ((requestPrefix "/benchmark.Service/Wide").append #[
      header "content-type" "application/grpc",
      header "te" "trailers",
      header "grpc-timeout" "99999999n",
      header "content-length" "4096",
      header "grpc-encoding" "identity",
      header "grpc-accept-encoding" "identity, deflate"
    ]).append (fillerHeaders 14)
  let acceptMultiple := (requestPrefix "/benchmark.Service/AcceptMultiple").append #[
    header "content-type" "application/grpc",
    header "te" "trailers",
    header "grpc-accept-encoding" "identity, deflate",
    header "grpc-accept-encoding" "br,   gzip   , identity"
  ]
  let duplicateContentType :=
    (requestPrefix "/benchmark.Service/DuplicateContentType").append #[
      header "content-type" "application/grpc",
      header "content-type" "application/grpc+proto",
      header "te" "trailers",
      header "x-control" "late"
    ]
  let unsupportedFirstDuplicate :=
    (requestPrefix "/benchmark.Service/UnsupportedContentType").append #[
      header "content-type" "application/json",
      header "content-type" "application/grpc",
      header "te" "trailers"
    ]
  let duplicateTe := (requestPrefix "/benchmark.Service/DuplicateTe").append #[
    header "content-type" "application/grpc",
    header "te" "trailers",
    header "te" "trailers"
  ]
  let invalidMethod :=
    (requestPrefix "/benchmark.Service/InvalidMethod" "GET").append #[
      header "content-type" "application/grpc",
      header "te" "trailers"
    ]
  let earlyMethodRejectLongAccept :=
    (requestPrefix "/benchmark.Service/EarlyMethodReject" "GET").append #[
      header "content-type" "application/grpc",
      header "te" "trailers",
      header "grpc-accept-encoding"
        "identity,deflate,br,zstd,snappy,lz4,brotli,compress,custom-one,custom-two,custom-three"
    ]
  let invalidScheme :=
    (requestPrefix "/benchmark.Service/InvalidScheme" "POST" "ftp").append #[
      header "content-type" "application/grpc",
      header "te" "trailers"
    ]
  let forbiddenStatus : Metadata := #[
    header ":method" "POST",
    header ":scheme" "https",
    header ":status" "200",
    header ":path" "/benchmark.Service/ForbiddenStatus",
    header ":authority" "benchmark.local",
    header "content-type" "application/grpc",
    header "te" "trailers"
  ]
  let missingContentType := (requestPrefix "/benchmark.Service/MissingContentType").append #[
    header "te" "trailers"
  ]
  let invalidTimeout := (requestPrefix "/benchmark.Service/InvalidTimeout").append #[
    header "content-type" "application/grpc",
    header "te" "trailers",
    header "grpc-timeout" "0m"
  ]
  let duplicateTimeout := (requestPrefix "/benchmark.Service/DuplicateTimeout").append #[
    header "content-type" "application/grpc",
    header "te" "trailers",
    header "grpc-timeout" "1S",
    header "grpc-timeout" "2S"
  ]
  let invalidContentLength :=
    (requestPrefix "/benchmark.Service/InvalidContentLength").append #[
      header "content-type" "application/grpc",
      header "te" "trailers",
      header "content-length" "NaN"
    ]
  let duplicateContentLength :=
    (requestPrefix "/benchmark.Service/DuplicateContentLength").append #[
      header "content-type" "application/grpc",
      header "te" "trailers",
      header "content-length" "1",
      header "content-length" "2"
    ]
  let unsupportedEncoding :=
    (requestPrefix "/benchmark.Service/UnsupportedEncoding").append #[
      header "content-type" "application/grpc",
      header "te" "trailers",
      header "grpc-encoding" "br"
    ]
  let duplicateEncoding :=
    (requestPrefix "/benchmark.Service/DuplicateEncoding").append #[
      header "content-type" "application/grpc",
      header "te" "trailers",
      header "grpc-encoding" "identity",
      header "grpc-encoding" "gzip"
    ]
  #[
    {
      label := "client_default_7"
      metadata := defaultMetadata
      expected := accepted "benchmark.Service" "Unary" none none false true
      expectedHeaders := 7
    },
    {
      label := "client_auth_8"
      metadata := clientAuth
      expected := accepted "benchmark.Service" "Unary" none none false true
      expectedHeaders := 8
    },
    {
      label := "client_timeout_auth_9"
      metadata := clientTimeoutAuth
      expected := accepted "benchmark.Service" "Unary"
        (some { value := 250, unit := .millisecond }) none false true
      expectedHeaders := 9
    },
    {
      label := "no_accept_6"
      metadata := noAccept
      expected := accepted "benchmark.Service" "NoAccept" none none false false
      expectedHeaders := 6
    },
    {
      label := "full_11"
      metadata := fullMetadata
      expected := accepted "benchmark.Service" "Full"
        (some { value := 250, unit := .millisecond }) (some 128) true true
      expectedHeaders := 11
    },
    {
      label := "wide_24"
      metadata := wideMetadata
      expected := accepted "benchmark.Service" "Wide"
        (some { value := 99999999, unit := .nanosecond }) (some 4096) false false
      expectedHeaders := 24
    },
    {
      label := "accept_multiple_8"
      metadata := acceptMultiple
      expected := accepted "benchmark.Service" "AcceptMultiple" none none false true
      expectedHeaders := 8
    },
    {
      label := "duplicate_content_type_8"
      metadata := duplicateContentType
      expected := rejectedInvalid "duplicate content-type header"
      expectedHeaders := 8
    },
    {
      label := "unsupported_first_duplicate_7"
      metadata := unsupportedFirstDuplicate
      expected := .unsupportedContentType
      expectedHeaders := 7
    },
    {
      label := "duplicate_te_7"
      metadata := duplicateTe
      expected := rejectedInvalid "duplicate te header"
      expectedHeaders := 7
    },
    {
      label := "invalid_method_6"
      metadata := invalidMethod
      expected := rejectedInvalid "gRPC requests must use POST"
      expectedHeaders := 6
    },
    {
      label := "early_method_reject_long_accept_7"
      metadata := earlyMethodRejectLongAccept
      expected := rejectedInvalid "gRPC requests must use POST"
      expectedHeaders := 7
    },
    {
      label := "invalid_scheme_6"
      metadata := invalidScheme
      expected := rejectedInvalid "unsupported gRPC scheme ftp"
      expectedHeaders := 6
    },
    {
      label := "forbidden_status_7"
      metadata := forbiddenStatus
      expected := rejectedInvalid "gRPC requests must not include :status"
      expectedHeaders := 7
    },
    {
      label := "missing_content_type_5"
      metadata := missingContentType
      expected := rejectedInvalid "missing content-type header"
      expectedHeaders := 5
    },
    {
      label := "invalid_timeout_7"
      metadata := invalidTimeout
      expected := rejectedInvalid "invalid grpc-timeout header 0m"
      expectedHeaders := 7
    },
    {
      label := "duplicate_timeout_8"
      metadata := duplicateTimeout
      expected := rejectedInvalid "duplicate grpc-timeout header"
      expectedHeaders := 8
    },
    {
      label := "invalid_content_length_7"
      metadata := invalidContentLength
      expected := rejectedInvalid "invalid content-length header NaN"
      expectedHeaders := 7
    },
    {
      label := "duplicate_content_length_8"
      metadata := duplicateContentLength
      expected := rejectedInvalid "duplicate content-length header"
      expectedHeaders := 8
    },
    {
      label := "unsupported_encoding_7"
      metadata := unsupportedEncoding
      expected := .reject (Status.unimplemented "unsupported grpc-encoding br")
      expectedHeaders := 7
    },
    {
      label := "duplicate_encoding_8"
      metadata := duplicateEncoding
      expected := rejectedInvalid "duplicate grpc-encoding header"
      expectedHeaders := 8
    }
  ]

@[inline] private def mix (digest value : UInt64) : UInt64 :=
  (digest ^^^ value) * 1099511628211

@[inline] private def boolDigest (digest : UInt64) (value : Bool) : UInt64 :=
  mix digest (if value then 1 else 0)

@[inline] private def stringDigest (digest : UInt64) (value : @& String) : UInt64 :=
  String.foldl (fun digest character =>
      mix digest (UInt64.ofNat character.toNat + 1))
    (mix digest (UInt64.ofNat value.utf8ByteSize)) value

@[inline] private def optionalStringDigest (digest : UInt64) : Option String → UInt64
  | none => mix digest 0
  | some value => stringDigest (mix digest 1) value

private def timeoutUnitTag : TimeoutUnit → UInt64
  | .hour => 1
  | .minute => 2
  | .second => 3
  | .millisecond => 4
  | .microsecond => 5
  | .nanosecond => 6

@[inline] private def timeoutDigest (digest : UInt64) : Option Timeout → UInt64
  | none => mix digest 0
  | some timeout =>
      let digest := mix digest 1
      let digest := mix digest (UInt64.ofNat timeout.value)
      mix digest (timeoutUnitTag timeout.unit)

@[inline] private def optionalNatDigest (digest : UInt64) : Option Nat → UInt64
  | none => mix digest 0
  | some value => mix (mix digest 1) (UInt64.ofNat value)

@[inline] private def statusDigest (digest : UInt64) (status : @& Status) : UInt64 :=
  let digest := mix digest (UInt64.ofNat status.code.toNat)
  optionalStringDigest digest status.message

/-- Complete stable observation of every field in every result constructor. -/
@[noinline] private def resultDigest : Result → UInt64
  | .unsupportedContentType => mix 14695981039346656037 1
  | .reject status =>
      let digest := mix 14695981039346656037 2
      statusDigest digest status
  | .accept preflight =>
      let digest := mix 14695981039346656037 3
      let digest := stringDigest digest preflight.method.service
      let digest := stringDigest digest preflight.method.method
      let digest := timeoutDigest digest preflight.timeout
      let digest := optionalNatDigest digest preflight.contentLength
      let digest := boolDigest digest preflight.requestUsesGzip
      boolDigest digest preflight.clientAcceptsGzip

/-- Observe metadata-validation failures as well as every classifier field. -/
@[noinline] private def outcomeDigest : Outcome → UInt64
  | .error status => statusDigest (mix 14695981039346656037 17) status
  | .ok result => mix (mix 14695981039346656037 19) (resultDigest result)

private def sameOutcome : Outcome → Outcome → Bool
  | .error left, .error right => left == right
  | .ok left, .ok right => left == right
  | _, _ => false

private def validateFixtures (fixtures : Array Fixture) : IO Nat := do
  for fixture in fixtures do
    unless fixture.metadata.size == fixture.expectedHeaders do
      throw (IO.userError <|
        s!"{fixture.label}: metadata size {fixture.metadata.size} != " ++
          s!"declared {fixture.expectedHeaders}")
    match Metadata.validate fixture.metadata with
    | .error status =>
        throw (IO.userError <|
          s!"{fixture.label}: fixture violates the already-validated seam contract: " ++
            status.messageD)
    | .ok () => pure ()
    let reference := classifyReference fixture.metadata
    let candidate := classifyCandidate fixture.metadata
    unless sameOutcome reference (.ok fixture.expected) do
      throw (IO.userError <|
        s!"{fixture.label}: reference result {repr reference} != " ++
          s!"independent expectation {repr (.ok fixture.expected : Outcome)}")
    unless sameOutcome candidate (.ok fixture.expected) do
      throw (IO.userError <|
        s!"{fixture.label}: candidate result {repr candidate} != " ++
          s!"independent expectation {repr (.ok fixture.expected : Outcome)}")
    unless sameOutcome reference candidate &&
        outcomeDigest reference == outcomeDigest candidate do
      throw (IO.userError s!"{fixture.label}: exact result or digest differs")
  pure fixtures.size

/-- One common indirect-call recurrence for both selected implementations. -/
@[noinline] private def runRepeated (classify : @& Classifier)
    (metadata : @& Metadata) (iterations : Nat) : UInt64 := Id.run do
  let mut digest : UInt64 := 0
  for _ in [0:iterations] do
    digest := digest + outcomeDigest (classify metadata)
  return digest

private def expectedDigest (fixture : @& Fixture) (iterations : Nat) : UInt64 :=
  outcomeDigest (.ok fixture.expected) * UInt64.ofNat iterations

private def parseNatural (label value : String) : IO Nat := do
  let some parsed := value.toNat?
    | throw (IO.userError s!"{label} must be a nonnegative decimal integer")
  pure parsed

private def parsePositive (label value : String) : IO Nat := do
  let parsed ← parseNatural label value
  unless parsed > 0 do
    throw (IO.userError s!"{label} must be positive")
  pure parsed

private def parseMode : String → Option Mode
  | "reference" => some .reference
  | "candidate" => some .candidate
  | _ => none

private def modeName : Mode → String
  | .reference => "reference"
  | .candidate => "candidate"

private def modeIsCandidate : Mode → Bool
  | .reference => false
  | .candidate => true

private def selectFixtures (fixtures : Array Fixture) (selection : String) :
    IO (Array Fixture) := do
  if selection == "all" then
    pure fixtures
  else
    let some fixture := fixtures.find? fun fixture => fixture.label == selection
      | throw (IO.userError s!"unknown fixture: {selection}")
    pure #[fixture]

private def runFixture (classify : @& Classifier) (mode : Mode)
    (fixture : @& Fixture) (iterations warmup semanticCases : Nat) : IO Unit := do
  let warmupDigest := runRepeated classify fixture.metadata warmup
  let expectedWarmup := expectedDigest fixture warmup
  unless warmupDigest == expectedWarmup do
    throw (IO.userError <|
      s!"{fixture.label}: warmup digest {warmupDigest} != expected {expectedWarmup}")

  let digest := runRepeated classify fixture.metadata iterations
  let expected := expectedDigest fixture iterations
  unless digest == expected do
    throw (IO.userError s!"{fixture.label}: digest {digest} != expected {expected}")

  IO.println <|
    s!"benchmark=grpc_request_preflight_summary_v1 mode={modeName mode} " ++
      s!"fixture={fixture.label} metadata_headers={fixture.metadata.size} " ++
      s!"iterations={iterations} warmup={warmup} digest={digest}"
  IO.println <|
    s!"request_preflight_summary_validation=pass cases={semanticCases} " ++
      "result=exact_reference_candidate_expected digest=validation_and_all_outcome_fields"
  IO.println <|
    "counter_scope=whole_process fixed=fixture_construction+directed_semantic_validation+" ++
      "selector+requested_warmup+digest_checks+output " ++
      "scaling=metadata_validate+selected_request_header_preflight+full_result_digest " ++
      "excluded=hpack+registry_lookup+response_encoding+socket+tls+handler+service"

def runMain (args : List String) : IO Unit := do
  let (modeText, selection, iterations, warmup) ← match args with
    | [mode, fixture, iterations] =>
        let iterations ← parsePositive "iterations" iterations
        pure (mode, fixture, iterations, Nat.min iterations 1000)
    | [mode, fixture, iterations, warmup] =>
        pure (mode, fixture,
          ← parsePositive "iterations" iterations,
          ← parseNatural "warmup" warmup)
    | _ => throw (IO.userError <|
        "usage: request_preflight_summary_benchmark (reference|candidate) " ++
          "<fixture|all> iterations [warmup]")
  let some mode := parseMode modeText
    | throw (IO.userError "mode must be reference or candidate")

  let fixtures := makeFixtures
  let semanticCases ← validateFixtures fixtures
  let selectedFixtures ← selectFixtures fixtures selection

  let classifierBox := selectClassifierBox mode
  unless classifierBox.candidateSelected == modeIsCandidate mode do
    throw (IO.userError "opaque classifier selection metadata mismatch")
  let selected := classifierBox.classify

  for fixture in selectedFixtures do
    runFixture selected mode fixture iterations warmup semanticCases

end Grpc.RequestPreflightSummaryBenchmarkHarness

def main (args : List String) : IO Unit :=
  Grpc.RequestPreflightSummaryBenchmarkHarness.runMain args
