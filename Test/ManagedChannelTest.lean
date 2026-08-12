import Grpc
import Test.CertificateFixtures

namespace ManagedChannelTest

open Grpc
open Grpc.ManagedChannel

private def fail (detail : String) : IO α :=
  throw (IO.userError detail)

private def expect (condition : Bool) (detail : String) : IO Unit := do
  unless condition do fail detail

private def expectNoSubstring
    (value needle : String) (detail : String) : IO Unit := do
  if (value.splitOn needle).length != 1 then
    fail detail

private def testCredentialValue : String := "Bearer production-api-key"

private def testCredentials : IO CallCredentials := do
  let some entry := CredentialEntry.of? "authorization" testCredentialValue
    | fail "test credential entry was rejected"
  pure (.ofEntries #[entry])

private def apiConfiguration (endpointText : String) :
    IO Grpc.ManagedChannel.Config := do
  let endpoint ← match Endpoint.parse endpointText with
    | .ok endpoint => pure endpoint
    | .error error =>
        fail s!"test endpoint {endpointText.quote} failed: {repr error}"
  pure {
    endpoint
    credentials := ← testCredentials
    deadline := .default
  }

private def addresses
    (configuration : Grpc.ManagedChannel.Config)
    (raw : Array String) :
    IO (Array NameResolver.Address) := do
  match ← NameResolver.resolveWith (fun _ _ => pure (.ok raw))
      configuration.endpoint with
  | .ok addresses => pure addresses
  | .error error => fail s!"test address refinement failed: {error}"

private def validPem : String :=
  CertificateFixtures.validCertificatePem

private def trustBundle : IO TrustAnchors.Bundle := do
  let backend : TrustAnchors.Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == TrustAnchors.sslCertFileVariable then
        pure (some "/test/anchors.pem")
      else
        pure none
    probe := fun _ =>
      pure (.error (IO.userError "unexpected trust path probe"))
    read := fun _ => pure (.ok validPem.toUTF8)
  }
  match ← TrustAnchors.loadWith backend with
  | .ok bundle => pure bundle
  | .error error => fail s!"test trust bundle failed: {error}"

private def awaitSignal (promise : IO.Promise (Option Unit)) : IO Unit := do
  let some (some ()) ← IO.wait promise.result?
    | fail "test synchronization promise was dropped"

private partial def waitForPhase
    (channel : Subchannel Resource)
    (expected : Grpc.ChannelLease.Phase)
    (remaining : Nat := 2_000) : IO Unit := do
  if (← channel.phase) == expected then
    pure ()
  else if remaining = 0 then
    fail s!"timed out waiting for channel phase {repr expected}"
  else
    IO.sleep 1
    waitForPhase channel expected (remaining - 1)

private partial def waitForSharedPhase
    (channel : ManagedChannel Resource)
    (expected : Grpc.ChannelLease.Phase)
    (remaining : Nat := 2_000) : IO Unit := do
  if (← channel.phase) == expected then
    pure ()
  else if remaining = 0 then
    fail s!"timed out waiting for shared channel phase {repr expected}"
  else
    IO.sleep 1
    waitForSharedPhase channel expected (remaining - 1)

private partial def waitForTask
    (task : Task α) (remaining : Nat := 2_000) : IO Unit := do
  if ← IO.hasFinished task then
    pure ()
  else if remaining = 0 then
    fail "timed out waiting for task completion"
  else
    IO.sleep 1
    waitForTask task (remaining - 1)

private partial def waitForInitializationCompletionWaiters
    (shared : ManagedChannel Resource)
    (expected : Nat)
    (remaining : Nat := 2_000) : IO Unit := do
  match ← ManagedChannel.TestSupport.initializationCompletionWaiters shared with
  | some actual =>
      if actual == expected then
        pure ()
      else if remaining == 0 then
        fail s!"timed out waiting for {expected} initializer waiters; got {actual}"
      else
        IO.sleep 1
        waitForInitializationCompletionWaiters shared expected (remaining - 1)
  | none =>
      fail "initializer disappeared while inspecting completion waiters"

private partial def waitForInitializationTaskFinished
    (shared : ManagedChannel Resource)
    (remaining : Nat := 2_000) : IO Unit := do
  match ← ManagedChannel.TestSupport.initializationTaskFinished shared with
  | some true => pure ()
  | some false =>
      if remaining == 0 then
        fail "timed out waiting for staged initializer completion"
      else
        IO.sleep 1
        waitForInitializationTaskFinished shared (remaining - 1)
  | none =>
      fail "initializer disappeared before its completion was inspected"

private partial def waitForCloseSettlementWaiters
    (shared : ManagedChannel Resource)
    (expected : Nat)
    (remaining : Nat := 2_000) : IO Unit := do
  let actual ← ManagedChannel.TestSupport.closeSettlementWaiters shared
  if actual == expected then
    pure ()
  else if remaining == 0 then
    fail s!"timed out waiting for {expected} close waiters; got {actual}"
  else
    IO.sleep 1
    waitForCloseSettlementWaiters shared expected (remaining - 1)

private partial def waitForCloseCompletion
    (shared : ManagedChannel Resource)
    (remaining : Nat := 2_000) : IO Unit := do
  if ← ManagedChannel.TestSupport.closeCompletionResolved shared then
    pure ()
  else if remaining == 0 then
    fail "timed out waiting for automatic close completion"
  else
    IO.sleep 1
    waitForCloseCompletion shared (remaining - 1)

private partial def waitForNoCloseOwner
    (shared : ManagedChannel Resource)
    (remaining : Nat := 2_000) : IO Unit := do
  let needsOwner ← ManagedChannel.TestSupport.closeNeedsOwner shared
  let starting ← ManagedChannel.TestSupport.closeOwnerStarting shared
  if !needsOwner && !starting then
    pure ()
  else if remaining == 0 then
    fail "timed out waiting for close ownership to settle"
  else
    IO.sleep 1
    waitForNoCloseOwner shared (remaining - 1)

private def expectOpenError
    (result : Except (OwnedOpenFailure Nat) (Subchannel Nat))
    (expected : OpenError) (disposition : OpenFailureDisposition)
    (detail : String) : IO Unit := do
  match result with
  | .error actual =>
      expect (actual.error == expected)
        s!"{detail}: expected {repr expected}, got {repr actual.error}"
      expect (actual.disposition == disposition)
        (s!"{detail}: expected disposition {repr disposition}, got " ++
          s!"{repr actual.disposition}")
      let expectedRetry :=
        disposition == .retryableTransport || disposition == .retryableLocal
      expect (actual.shouldRetry == expectedRetry)
        s!"{detail}: structural retry decision diverged from disposition"
      expect (!actual.hasCleanupUncertainty)
        s!"{detail}: ordinary setup error retained an unexpected resource"
      let snapshot ← actual.snapshot
      have _certified : snapshot.Invariant := snapshot.invariant
      expect (snapshot.custody == .ownerFree &&
          snapshot.physicalOwnerCount == 0)
        s!"{detail}: ordinary setup error exposed cleanup custody"
      expect (!(← actual.hasCleanupCustody))
        s!"{detail}: ordinary setup error claimed a cleanup owner"
      match ← actual.close with
      | .ok () => pure ()
      | .error error =>
          fail s!"{detail}: owner-free failure close returned {error}"
      let closedSnapshot ← actual.snapshot
      expect (closedSnapshot.custody == .ownerFree &&
          closedSnapshot.physicalOwnerCount == 0)
        s!"{detail}: owner-free close fabricated cleanup custody"
  | .ok channel =>
      discard <| Subchannel.close channel
      fail s!"{detail}: unexpectedly opened a channel"

private def expectCleanupInventory
    (shared : ManagedChannel Resource)
    (channelOwners initializationOwners uncertainInitializations
      pendingInitializations : Nat)
    (detail : String) : IO Unit := do
  let actual ← ManagedChannel.TestSupport.cleanupInventory shared
  let expected : CleanupInventory := {
    channelOwners
    initializationOwners
    uncertainInitializations
    pendingInitializations
  }
  expect (actual == expected)
    s!"{detail}: expected {repr expected}, got {repr actual}"

private def expectSupervisorSnapshot
    (shared : ManagedChannel Resource)
    (phase : Grpc.ChannelLease.Phase)
    (activeCount nextGeneration : Nat)
    (currentGeneration? : Option Nat)
    (closingGenerations retainedGenerations : List Nat)
    (initialization : ManagedChannel.TestSupport.SupervisorInitialization)
    (quarantinedInitializationOwnerCount : Nat)
    (quarantinedInitializationUncertainty : Bool)
    (cleanupInventory : CleanupInventory)
    (closeDriver : ManagedChannel.TestSupport.SupervisorCloseDriver)
    (detail : String) : IO Unit := do
  let snapshot ← ManagedChannel.TestSupport.supervisorSnapshot shared
  have _certified : snapshot.Invariant := snapshot.invariant
  expect (snapshot.phase == phase &&
      snapshot.activeCount == activeCount &&
      snapshot.nextGeneration == nextGeneration &&
      snapshot.currentGeneration? == currentGeneration? &&
      snapshot.closingGenerations == closingGenerations &&
      snapshot.retainedGenerations == retainedGenerations &&
      snapshot.initialization == initialization &&
      snapshot.quarantinedInitializationOwnerCount ==
        quarantinedInitializationOwnerCount &&
      snapshot.quarantinedInitializationUncertainty ==
        quarantinedInitializationUncertainty &&
      snapshot.cleanupInventory == cleanupInventory &&
      snapshot.closeDriver == closeDriver)
    (s!"{detail}: phase={repr snapshot.phase}, " ++
      s!"active={snapshot.activeCount}, next={snapshot.nextGeneration}, " ++
      s!"current={repr snapshot.currentGeneration?}, " ++
      s!"closing={repr snapshot.closingGenerations}, " ++
      s!"retained={repr snapshot.retainedGenerations}, " ++
      s!"initializer={repr snapshot.initialization}, " ++
      s!"quarantinedOwners={snapshot.quarantinedInitializationOwnerCount}, " ++
      s!"quarantinedUncertainty=" ++
        s!"{snapshot.quarantinedInitializationUncertainty}, " ++
      s!"inventory={repr snapshot.cleanupInventory}, " ++
      s!"driver={repr snapshot.closeDriver}")

private def forbiddenConnector (detail : String) : Connector Nat := {
  connect := fun _ _register => fail s!"{detail}: connector was invoked"
  selectedAlpn := fun _ => fail s!"{detail}: ALPN hook was invoked"
  close := fun _ => fail s!"{detail}: close hook was invoked"
}

private def registered
    (register : Nat → BaseIO (Option (RegistrationReceipt Nat)))
    (resource : Nat) : IO (ConnectResult Nat) := do
  let some receipt ← register resource
    | fail "test connector registration was rejected"
  pure (.connected receipt)

private instance : Inhabited ConnectAttempt where
  default := {
    address := default
    authority := ""
    scheme := ""
    credentials := .plaintext
  }

private def testOrderedPlaintextFallback : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.2", "::1"]
  let attempts ← IO.mkRef (#[] : Array ConnectAttempt)
  let closes ← IO.mkRef (#[] : Array Nat)
  let trustCalls ← IO.mkRef 0
  let alpnCalls ← IO.mkRef 0
  let connector : Connector Nat := {
    connect := fun attempt register => do
      attempts.modify (·.push attempt)
      if attempt.address.numericHost == "127.0.0.2" then
        discard <| register 1
        pure .failed
      else
        registered register 2
    selectedAlpn := fun _ => do
      alpnCalls.modify (· + 1)
      pure (some requiredAlpn)
    close := fun resource => closes.modify (·.push resource)
  }
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := do
      trustCalls.modify (· + 1)
      pure (.error (.noSystemBundle []))
    connector
  }
  let .ok channel ← Subchannel.openWith dependencies configuration
    | fail "ordered plaintext fallback did not open"
  let seen ← attempts.get
  expect (seen.size == 2) "plaintext addresses were not attempted in order"
  expect (seen[0]!.address.numericHost == "127.0.0.2" &&
      seen[1]!.address.numericHost == "::1")
    "plaintext address order changed"
  for attempt in seen do
    expect (attempt.authority == "localhost:50051")
      "plaintext attempt lost endpoint authority"
    expect (attempt.scheme == "http")
      "plaintext attempt lost endpoint scheme"
    match attempt.credentials with
    | .plaintext => pure ()
    | .tls _ => fail "HTTP endpoint used TLS"
  expect ((← closes.get) == #[1])
    "partially initialized failed attempt was not closed"
  expect ((← trustCalls.get) == 0)
    "plaintext endpoint loaded trust anchors"
  expect ((← alpnCalls.get) == 0)
    "plaintext endpoint queried ALPN"
  match ← Subchannel.close channel with
  | .ok () => pure ()
  | .error error => fail s!"plaintext channel close failed: {error}"
  expect ((← closes.get) == #[1, 2])
    "selected plaintext connection was not closed exactly once"

private def testRegistrationReceiptsAreOneShotAndSealed : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closes ← IO.mkRef (#[] : Array Nat)
  let allowLate ← IO.Promise.new
  let lateTask ← IO.mkRef
    (none : Option (Task (Except IO.Error Unit)))
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "registration receipt test loaded trust anchors"
    connector := {
      connect := fun _ register => do
        let some accepted ← register 1_001
          | fail "first registration receipt was rejected"
        let duplicate ← register 1_002
        expect duplicate.isNone
          "duplicate registration receipt was accepted"
        -- A rejected registration never transferred ownership; the connector
        -- remains responsible for closing that exact resource.
        closes.modify (·.push 1_002)
        let owner ← IO.asTask (do
          awaitSignal allowLate
          let rejected ← register 1_003
          expect rejected.isNone
            "late registration receipt was accepted after sealing"
          closes.modify (·.push 1_003))
        lateTask.set (some owner)
        pure (.connected accepted)
      selectedAlpn := fun _ =>
        fail "registration receipt test queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let .ok channel ← Subchannel.openWith dependencies configuration
    | fail "valid one-shot registration receipt did not open"
  allowLate.resolve (some ())
  let some owner ← lateTask.get
    | fail "late registration task was not retained by its test owner"
  match ← IO.wait owner with
  | .ok () => pure ()
  | .error error => throw error
  match ← Subchannel.close channel with
  | .ok () => pure ()
  | .error error => fail s!"registration receipt close failed: {error}"
  expect ((← closes.get) == #[1_002, 1_003, 1_001])
    "duplicate/late registration changed exact connector ownership"

  let twoDestinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]
  let attempt ← IO.mkRef 0
  let oldReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let mismatchCloses ← IO.mkRef (#[] : Array Nat)
  let mismatchDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok twoDestinations)
    loadTrust := fail "registration mismatch loaded trust anchors"
    connector := {
      connect := fun _ register => do
        let current ← attempt.get
        attempt.set (current + 1)
        if current == 0 then
          let some receipt ← register 1_011
            | fail "old registration receipt was rejected"
          oldReceipt.set (some receipt)
          pure .failed
        else
          let some _accepted ← register 1_012
            | fail "current registration receipt was rejected"
          let some stale ← oldReceipt.get
            | fail "stale registration receipt was lost"
          pure (.connected stale)
      selectedAlpn := fun _ =>
        fail "registration mismatch queried plaintext ALPN"
      close := fun resource => mismatchCloses.modify (·.push resource)
    }
  }
  expectOpenError (← Subchannel.openWith mismatchDependencies configuration)
    .initializationFailed .supervisorInvariant
    "stale receipt substituted for current registration"
  expect ((← mismatchCloses.get) == #[1_011, 1_012])
    "stale receipt mismatch erased or duplicated a registered resource"

private def testPlaintextPolicyAndAddressBound : IO Unit := do
  let remote ← apiConfiguration "http://api.example.test:50051"
  let resolveCalls ← IO.mkRef 0
  let remoteDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCalls.modify (· + 1)
      pure (.error .noAddresses)
    loadTrust := fail "remote plaintext loaded trust anchors"
    connector := forbiddenConnector "remote plaintext"
  }
  expectOpenError (← Subchannel.openWith remoteDependencies remote)
    .plaintextRequiresLoopback .terminalPolicy
    "syntactically remote plaintext endpoint"
  expect ((← resolveCalls.get) == 0)
    "syntactically remote plaintext endpoint reached DNS"

  let loopbackConfiguration ← apiConfiguration "http://localhost:50051"
  let mixed ←
    addresses loopbackConfiguration #["127.0.0.1", "203.0.113.9"]
  let mixedDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok mixed)
    loadTrust := fail "mixed plaintext loaded trust anchors"
    connector := forbiddenConnector "mixed plaintext"
  }
  expectOpenError (← Subchannel.openWith mixedDependencies loopbackConfiguration)
    .plaintextRequiresLoopback .terminalPolicy
    "mixed loopback/non-loopback DNS answer"

  let raw := (List.range (maximumConnectionAttempts + 1)).toArray.map fun index =>
    s!"127.0.0.{index + 1}"
  let first ← addresses loopbackConfiguration
    (raw.extract 0 maximumConnectionAttempts)
  let last ← addresses loopbackConfiguration
    (raw.extract maximumConnectionAttempts raw.size)
  let oversized := first ++ last
  expect (oversized.size == maximumConnectionAttempts + 1)
    "oversized address fixture was deduplicated"
  let oversizedDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok oversized)
    loadTrust := fail "oversized plaintext loaded trust anchors"
    connector := forbiddenConnector "oversized plaintext"
  }
  expectOpenError (← Subchannel.openWith oversizedDependencies loopbackConfiguration)
    .tooManyAddresses .terminalPolicy "oversized DNS answer"

private def testSanitizedSetupAndResourceFailures : IO Unit := do
  let secret := "credential=must-not-escape"
  let loopbackConfiguration ← apiConfiguration "http://localhost:50051"
  let dnsDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ =>
      throw (IO.userError s!"DNS failure containing {secret}")
    loadTrust := fail "DNS failure loaded trust anchors"
    connector := forbiddenConnector "DNS failure"
  }
  let dnsResult ← Subchannel.openWith dnsDependencies loopbackConfiguration
  expectOpenError dnsResult .resolution .retryableTransport
    "thrown DNS failure"
  match dnsResult with
  | .error error =>
      expectNoSubstring (toString error) secret
        "public DNS error leaked injected details"
      expectNoSubstring (reprStr error) secret
        "repr DNS error leaked injected details"
  | .ok _ => pure ()

  let secure ← apiConfiguration "https://api.example.test:8443"
  let secureDestinations ← addresses secure #["192.0.2.10"]
  let resolveCalls ← IO.mkRef 0
  let trustDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCalls.modify (· + 1)
      pure (.ok secureDestinations)
    loadTrust :=
      throw (IO.userError s!"trust failure containing {secret}")
    connector := forbiddenConnector "trust failure"
  }
  let trustResult ← Subchannel.openWith trustDependencies secure
  expectOpenError trustResult .trustAnchors .terminalPolicy
    "thrown trust failure"
  expect ((← resolveCalls.get) == 0)
    "HTTPS resolution ran after trust-anchor failure"
  match trustResult with
  | .error error =>
      expectNoSubstring (toString error) secret
        "public trust error leaked injected details"
  | .ok _ => pure ()

  let loopbacks ←
    addresses loopbackConfiguration #["127.0.0.1", "127.0.0.2"]
  let connectDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok loopbacks)
    loadTrust := fail "connect failure loaded trust anchors"
    connector := {
      connect := fun attempt _register =>
        if attempt.address.numericHost == "127.0.0.1" then
          throw (IO.userError s!"connect failure containing {secret}")
        else
          pure .failed
      selectedAlpn := fun _ => fail "plaintext queried ALPN"
      close := fun _ => fail "connection failure unexpectedly closed"
    }
  }
  let connectResult ← Subchannel.openWith connectDependencies loopbackConfiguration
  expectOpenError connectResult .connectionAttemptsFailed
    .retryableTransport "all connection attempts failed"
  match connectResult with
  | .error error =>
      expectNoSubstring (reprStr error) secret
        "public connect error leaked injected details"
  | .ok _ => pure ()

  let closeCalls ← IO.mkRef 0
  let cleanupDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok #[loopbacks[0]!])
    loadTrust := fail "cleanup failure loaded trust anchors"
    connector := {
      connect := fun _ register => do
        discard <| register 91
        throw (IO.userError
          "connector failed after publishing raw resource 91")
      selectedAlpn := fun _ => fail "cleanup failure queried ALPN"
      close := fun _ => do
        closeCalls.modify (· + 1)
        throw (IO.userError s!"cleanup failure containing {secret}")
    }
  }
  let cleanupResult ← Subchannel.openWith cleanupDependencies loopbackConfiguration
  let retainedOwner ← match cleanupResult with
  | .error failure =>
      expect (failure.error == .cleanupFailed)
        "failed-attempt cleanup failure changed classification"
      expect failure.hasCleanupUncertainty
        "failed-attempt cleanup failure erased its exact raw owner"
      let snapshot ← failure.snapshot
      have _certified : snapshot.Invariant := snapshot.invariant
      expect (snapshot.custody == .available &&
          snapshot.physicalOwnerCount == 1 && snapshot.cleanupAuthorized &&
          snapshot.failure == failure.failure)
        "cleanup failure did not expose one certified owned capability"
      expect (← failure.hasCleanupCustody)
        "cleanup failure did not retain exact direct custody"
      pure failure
  | .ok channel =>
      discard <| Subchannel.close channel
      fail "failed-attempt cleanup failure unexpectedly opened a channel"
  expect ((← closeCalls.get) == 1)
    "failed-attempt resource cleanup was not attempted exactly once"
  let diagnostic := retainedOwner.failure
  let beforeObservations ← retainedOwner.snapshot
  let observers ← (List.range 32).mapM fun _ => IO.asTask do
    let copied := diagnostic
    expect (copied == retainedOwner.failure &&
        copied.error == .cleanupFailed &&
        copied.disposition == .cleanupUncertain &&
        copied.primaryError == .connectionAttemptsFailed &&
        copied.primaryDisposition == .retryableTransport &&
        copied.hasCleanupUncertainty && !copied.shouldRetry)
      "copied immutable cleanup diagnostic changed structural policy"
  for observer in observers do
    match ← IO.wait observer with
    | .ok () => pure ()
    | .error error => throw error
  let afterObservations ← retainedOwner.snapshot
  expect (afterObservations == beforeObservations &&
      afterObservations.custody == .available &&
      afterObservations.physicalOwnerCount == 1 &&
      afterObservations.cleanupAuthorized)
    "concurrent copied diagnostic observations mutated exact custody"
  match cleanupResult with
  | .error error =>
      expectNoSubstring (toString error) secret
        "public cleanup error leaked injected details"
      expectNoSubstring (reprStr retainedOwner) secret
        "retained cleanup owner rendered connector details"
      expectNoSubstring (reprStr retainedOwner) "91"
        "retained cleanup owner rendered its exact raw resource"
  | .ok _ => pure ()
  match ← retainedOwner.close with
  | .error .transport => pure ()
  | result =>
      fail s!"retained cleanup owner changed terminal uncertainty: {repr result}"
  let quarantinedSnapshot ← retainedOwner.snapshot
  have _certified : quarantinedSnapshot.Invariant :=
    quarantinedSnapshot.invariant
  expect (quarantinedSnapshot.custody == .quarantined &&
      quarantinedSnapshot.physicalOwnerCount == 1 &&
      !quarantinedSnapshot.cleanupAuthorized &&
      !(← retainedOwner.hasCleanupCustody) &&
      (← retainedOwner.hasQuarantinedCustody))
    "direct close did not publish observation-only quarantine"
  match ← retainedOwner.close with
  | .error .transport => pure ()
  | result =>
      fail s!"repeated direct owner close changed result: {repr result}"
  expect ((← closeCalls.get) == 1)
    "observing quarantined cleanup retried the ambiguous close effect"
  expect (retainedOwner.failure == diagnostic)
    "direct close mutated the immutable cleanup diagnostic"

private def expectTlsAttempt
    (attempt : ConnectAttempt) (numericHost authority serverName pem : String) :
    IO Unit := do
  expect (attempt.address.numericHost == numericHost)
    "TLS attempt used the wrong numeric destination"
  expect (attempt.authority == authority)
    "TLS attempt lost endpoint authority"
  expect (attempt.scheme == "https")
    "TLS attempt lost endpoint scheme"
  match attempt.credentials with
  | .plaintext => fail "HTTPS endpoint used plaintext"
  | .tls policy =>
      expect (policy.serverName == serverName)
        "TLS attempt changed SNI/hostname verification input"
      expect (policy.alpnProtocols == #[requiredAlpn])
        "TLS attempt did not offer exactly h2"
      expect (policy.trustAnchorsPEM == pem)
        "TLS attempt changed the validated trust bundle"
      expect policy.verifyHostname
        "TLS attempt disabled hostname verification"

private def testHttpsPolicyAndAlpnFallback : IO Unit := do
  let configuration ← apiConfiguration "https://api.example.test:8443"
  let destinations ← addresses configuration #["192.0.2.10", "2001:db8::10"]
  let bundle ← trustBundle
  let attempts ← IO.mkRef (#[] : Array ConnectAttempt)
  let closes ← IO.mkRef (#[] : Array Nat)
  let connector : Connector Nat := {
    connect := fun attempt register => do
      attempts.modify (·.push attempt)
      if attempt.address.numericHost == "192.0.2.10" then
        registered register 10
      else
        registered register 11
    selectedAlpn := fun resource =>
      if resource == 10 then pure (some "http/1.1")
      else pure (some requiredAlpn)
    close := fun resource => closes.modify (·.push resource)
  }
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := pure (.ok bundle)
    connector
  }
  let .ok channel ← Subchannel.openWith dependencies configuration
    | fail "HTTPS fallback did not accept the h2 address"
  let seen ← attempts.get
  expect (seen.size == 2) "HTTPS fallback did not preserve address order"
  expectTlsAttempt seen[0]! "192.0.2.10"
    "api.example.test:8443" "api.example.test" bundle.pem
  expectTlsAttempt seen[1]! "2001:db8::10"
    "api.example.test:8443" "api.example.test" bundle.pem
  expect ((← closes.get) == #[10])
    "ALPN-mismatched connection was not closed before fallback"
  match ← Subchannel.close channel with
  | .ok () => pure ()
  | .error error => fail s!"HTTPS channel close failed: {error}"
  expect ((← closes.get) == #[10, 11])
    "selected HTTPS connection was not closed exactly once"

  let mismatchCloses ← IO.mkRef (#[] : Array Nat)
  let nextResource ← IO.mkRef 20
  let mismatchDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := pure (.ok bundle)
    connector := {
      connect := fun _ register => do
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun resource =>
        if resource == 20 then pure (some "http/1.1") else pure none
      close := fun resource => mismatchCloses.modify (·.push resource)
    }
  }
  expectOpenError (← Subchannel.openWith mismatchDependencies configuration)
    .alpnNegotiationFailed .retryableTransport
    "all HTTPS ALPN selections failed"
  expect ((← mismatchCloses.get) == #[20, 21])
    "ALPN failure did not close every connected resource"

  let failedAlpnCloseCount ← IO.mkRef 0
  let failedAlpnDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok #[destinations[0]!])
    loadTrust := pure (.ok bundle)
    connector := {
      connect := fun _ register => registered register 29
      selectedAlpn := fun _ => pure (some "http/1.1")
      close := fun resource => do
        expect (resource == 29)
          "failed ALPN cleanup closed the wrong raw resource"
        failedAlpnCloseCount.modify (· + 1)
        throw (IO.userError "deterministic failed ALPN cleanup")
    }
  }
  let failedAlpnShared ←
    ManagedChannel.createWith failedAlpnDependencies configuration
  let failedAlpnResult : Except CallError Unit ←
    ManagedChannel.unaryWith failedAlpnShared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match failedAlpnResult with
  | .error .cleanupUncertain => pure ()
  | _ => fail "failed ALPN cleanup was not contained"
  expect ((← failedAlpnCloseCount.get) == 1)
    "failed ALPN cleanup was not attempted exactly once"
  expectCleanupInventory failedAlpnShared 0 1 0 0
    "failed ALPN cleanup erased its exact raw owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
    failedAlpnShared) ==
      some (.cleanupUncertain 0 .alpnNegotiationFailed
        .retryableTransport 29))
    "failed ALPN cleanup retained the wrong raw resource"
  match ← ManagedChannel.close failedAlpnShared with
  | .error .transport => pure ()
  | _ => fail "failed ALPN cleanup published a clean shared close"
  expect ((← failedAlpnCloseCount.get) == 1)
    "shared close retried ambiguous ALPN cleanup"
  expectCleanupInventory failedAlpnShared 0 1 0 0
    "terminal ALPN cleanup failure erased its exact raw owner"

  let ipv6Configuration ←
    apiConfiguration "https://[2001:db8::1]:9443"
  let ipv6Destinations ← addresses ipv6Configuration #["203.0.113.1"]
  let ipv6Attempts ← IO.mkRef (#[] : Array ConnectAttempt)
  let ipv6Closes ← IO.mkRef 0
  let ipv6Dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok ipv6Destinations)
    loadTrust := pure (.ok bundle)
    connector := {
      connect := fun attempt register => do
        ipv6Attempts.modify (·.push attempt)
        registered register 30
      selectedAlpn := fun _ => pure (some requiredAlpn)
      close := fun _ => ipv6Closes.modify (· + 1)
    }
  }
  let .ok ipv6Channel ← Subchannel.openWith ipv6Dependencies ipv6Configuration
    | fail "HTTPS IPv6-literal channel did not open"
  let ipv6Seen ← ipv6Attempts.get
  expect (ipv6Seen.size == 1) "HTTPS IPv6 literal made extra attempts"
  expectTlsAttempt ipv6Seen[0]! "2001:db8::1"
    "[2001:db8::1]:9443" "2001:db8::1" bundle.pem
  discard <| Subchannel.close ipv6Channel
  expect ((← ipv6Closes.get) == 1)
    "HTTPS IPv6-literal connection was not closed"

private def testCallLeaseAndCloseLifecycle : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "call lifecycle loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 41
      selectedAlpn := fun _ => fail "call lifecycle queried ALPN"
      close := fun resource => do
        expect (resource == 41) "channel closed the wrong shared resource"
        closeCount.modify (· + 1)
    }
  }
  let .ok channel ← Subchannel.openWith dependencies configuration
    | fail "call lifecycle channel did not open"

  let secret := "metadata-or-peer-secret-must-not-escape"
  let detailsSecret := "binary-status-details-must-not-escape"
  let statusDetails := some detailsSecret.toUTF8
  let rpcFailure : Except CallError Nat ←
    Subchannel.unaryWith channel fun _ _ =>
      pure (.error (.rpc
        (Grpc.Status.error .permissionDenied secret) statusDetails))
  match rpcFailure with
  | .error error@(.rpc status observedDetails) =>
      expect (status.code == .permissionDenied && status.message == some secret)
        "public RPC error did not retain the exact peer status"
      expect (observedDetails == statusDetails)
        "public RPC error did not retain binary status details"
      expect (error.statusDetails? == statusDetails)
        "public RPC status-details accessor changed binary details"
      expectNoSubstring (toString error) secret
        "public RPC error text leaked the peer message"
      expectNoSubstring (reprStr error) secret
        "public RPC error repr leaked the peer message"
      expectNoSubstring (toString error) detailsSecret
        "public RPC error text leaked binary status details"
      expectNoSubstring (reprStr error) detailsSecret
        "public RPC error repr leaked binary status details"
      expectNoSubstring (toString error) "production-api-key"
        "public RPC error text leaked credential material"
  | _ => fail "RPC status was not retained"

  let actionFailure : Except CallError Unit ←
    Subchannel.unaryWith channel fun _ _ =>
      throw (IO.userError s!"action failure containing {secret}")
  match actionFailure with
  | .error .actionFailed => pure ()
  | _ => fail "thrown call action was not sanitized"

  let actionEntered : IO.Promise (Option Unit) ← IO.Promise.new
  let allowAction : IO.Promise (Option Unit) ← IO.Promise.new
  let worker ← IO.asTask <| Subchannel.unaryWith channel fun resource current => do
    expect (resource == 41) "call lease exposed the wrong shared resource"
    expect (
      (← current.credentials.fresh).map (·.exposeValue) ==
        #[testCredentialValue])
      "call lease did not receive fresh credential policy"
    expect (current.deadline.grpcTimeoutValue == "10S")
      "call lease did not receive fresh deadline policy"
    actionEntered.resolve (some ())
    awaitSignal allowAction
    pure (.ok 17)
  awaitSignal actionEntered
  let closer ← IO.asTask (Subchannel.close channel)
  waitForPhase channel .draining
  let rejected : Except CallError Unit ←
    Subchannel.unaryWith channel fun _ _ => pure (.ok ())
  match rejected with
  | .error .channelDraining => pure ()
  | _ => fail "draining channel admitted a new call"
  expect ((← closeCount.get) == 0)
    "transport closed before the exact call lease drained"
  allowAction.resolve (some ())
  match ← IO.wait worker with
  | .ok (.ok 17) => pure ()
  | _ => fail "leased call did not complete cleanly"
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | _ => fail "channel close did not join the active call"
  expect ((← channel.phase) == .closed)
    "clean close did not publish the closed phase"
  match ← Subchannel.close channel with
  | .ok () => pure ()
  | _ => fail "repeated channel close did not join completion"
  expect ((← closeCount.get) == 1)
    "shared connection close did not run exactly once"
  let afterClose : Except CallError Unit ←
    Subchannel.unaryWith channel fun _ _ => pure (.ok ())
  match afterClose with
  | .error .channelClosed => pure ()
  | _ => fail "closed channel admitted a new call"

private def testTransportCloseFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let secret := "transport-close-secret"
  let closeCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "transport close failure loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 51
      selectedAlpn := fun _ => fail "transport close failure queried ALPN"
      close := fun _ => do
        closeCount.modify (· + 1)
        throw (IO.userError secret)
    }
  }
  let .ok channel ← Subchannel.openWith dependencies configuration
    | fail "transport close failure channel did not open"
  let result ← Subchannel.close channel
  match result with
  | .error error@(.transport) =>
      expectNoSubstring (toString error) secret
        "public transport-close error leaked injected details"
      expectNoSubstring (reprStr error) secret
        "transport-close repr leaked injected details"
  | _ => fail "transport close failure was not reported"
  expect ((← channel.phase) == .draining)
    "ambiguous transport close published a closed phase"
  match ← Subchannel.close channel with
  | .error .transport => pure ()
  | _ => fail "repeated close did not join the original failure"
  expect ((← closeCount.get) == 1)
    "ambiguous transport close was retried"

private def testCallCleanupUncertaintyPoisonsChannel : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "cleanup-uncertainty test loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 61
      selectedAlpn := fun _ => fail "cleanup-uncertainty test queried ALPN"
      close := fun _ => closeCount.modify (· + 1)
    }
  }
  let .ok channel ← Subchannel.openWith dependencies configuration
    | fail "cleanup-uncertainty channel did not open"
  let result : Except CallError Unit ←
    Subchannel.unaryWith channel fun _ _ =>
      pure (.error .cleanupUncertain)
  match result with
  | .error .cleanupUncertain => pure ()
  | _ => fail "uncertain call cleanup was not contained"
  expect ((← channel.phase) == .closed)
    "uncertain call cleanup left the shared channel accepting"
  expect ((← closeCount.get) == 1)
    "uncertain call cleanup did not close the shared transport exactly once"
  let rejected : Except CallError Unit ←
    Subchannel.unaryWith channel fun _ _ => pure (.ok ())
  match rejected with
  | .error .channelClosed => pure ()
  | _ => fail "cleanup-poisoned channel admitted another call"
  match ← Subchannel.close channel with
  | .ok () => pure ()
  | _ => fail "close did not join cleanup-uncertainty containment"

private def testLazySharedSingleFlightAndReconnect : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let initialActionCount ← IO.mkRef 0
  let nextResource ← IO.mkRef 100
  let closes ← IO.mkRef (#[] : Array Nat)
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.ok destinations)
    loadTrust := fail "lazy plaintext owner loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ => fail "lazy plaintext owner queried ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  expect ((← resolveCount.get) == 0 && (← connectCount.get) == 0)
    "shared-channel construction performed eager network effects"

  let workers ← (List.range 8).mapM fun _ =>
    IO.asTask <| ManagedChannel.unaryWith shared fun resource _ => do
      initialActionCount.modify (· + 1)
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  expect ((← resolveCount.get) == 1 && (← connectCount.get) == 1)
    "concurrent first calls did not share one initialization"
  allowConnect.resolve (some ())
  for worker in workers do
    match ← IO.wait worker with
    | .ok (.ok 100) => pure ()
    | _ => fail "single-flight caller did not receive the shared generation"
  expect ((← resolveCount.get) == 1 && (← connectCount.get) == 1 &&
      (← initialActionCount.get) == 8)
    "copied successful task observers duplicated or lost one generation"
  expectCleanupInventory shared 0 0 0 0
    "copied successful task observers staged duplicate channel custody"

  let ambiguousCalls ← IO.mkRef 0
  let ambiguous : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ => do
      expect (resource == 100) "terminal call used the wrong generation"
      ambiguousCalls.modify (· + 1)
      pure (.error (.rpc
        (Grpc.Status.error .unavailable "ambiguous admitted RPC")))
  match ambiguous with
  | .error (.rpc status _) =>
      expect (status ==
          Grpc.Status.error .unavailable "ambiguous admitted RPC")
        "terminal shared call changed its exact status"
  | _ => fail "terminal shared call did not preserve its status"
  expect ((← ambiguousCalls.get) == 1)
    "terminal shared call was replayed"
  expect ((← closes.get) == #[100])
    "terminal generation was not retired exactly once"

  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 101 => pure ()
  | _ => fail "later RPC did not reconnect after terminal generation"
  expect ((← resolveCount.get) == 2 && (← connectCount.get) == 2)
    "recovery did not create exactly one later generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"lazy shared close failed: {error}"
  expect ((← closes.get) == #[100, 101])
    "shared close did not close the live generation exactly once"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | _ => fail "repeated shared close did not join cached completion"
  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelClosed => pure ()
  | _ => fail "closed shared owner admitted a new initialization"
  expect ((← connectCount.get) == 2)
    "post-close call performed a new connection"

private partial def awaitReconnectedGeneration
    (shared : ManagedChannel Nat)
    (remaining : Nat := 2_000) : IO Nat := do
  if remaining == 0 then
    fail "timed out waiting for the replacement shared generation"
  let result : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match result with
  | .ok 101 => pure 101
  | .ok 100 | .error .channelDraining =>
      IO.sleep 1
      awaitReconnectedGeneration shared (remaining - 1)
  | .ok resource =>
      fail s!"replacement call selected unexpected resource {resource}"
  | .error error =>
      fail s!"replacement call failed unexpectedly: {error}"

/--
A scoped caller retains G even after another caller retires G and the shared
cache reconnects to H. This is the transport-level fact that makes a namespace
probe and its following mutation/evidence inseparable.
-/
private def testSharedGenerationScopePinsAcrossReconnect : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let nextResource ← IO.mkRef 100
  let closes ← IO.mkRef (#[] : Array Nat)
  let scopeEntered ← IO.Promise.new
  let retirementEntered ← IO.Promise.new
  let replacementConnected ← IO.Promise.new
  let trace ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation-scope plaintext owner loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ =>
        fail "generation-scope plaintext owner queried ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let scopedCaller ← IO.asTask <|
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      let first ← generation.invoke fun resource _ => do
        trace.modify (·.push resource)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
      match first with
      | .error error => return .error error
      | .ok () => pure ()
      scopeEntered.resolve (some ())
      awaitSignal replacementConnected
      generation.invoke fun resource _ => do
        trace.modify (·.push resource)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal scopeEntered
  let exactStatus :=
    Grpc.Status.error .unavailable "retire G while its scoped lease is held"
  let retiringCaller :
      Task (Except IO.Error (Except CallError Unit)) ← IO.asTask <|
    ManagedChannel.unaryWith shared fun resource _ => do
      expect (resource == 100) "retirement did not target G"
      retirementEntered.resolve (some ())
      pure (Except.error (.rpc exactStatus) :
        Except Grpc.UnaryCall.Error Unit)
  awaitSignal retirementEntered
  let replacement ← awaitReconnectedGeneration shared
  expect (replacement == 101) "shared cache did not reconnect to H"
  expectSupervisorSnapshot shared .accepting 2 2 (some 1) [0] [] .idle
    0 false { channelOwners := 1 } .absent
    "reconnect did not atomically retain the pinned retired generation"
  replacementConnected.resolve (some ())
  match ← IO.wait scopedCaller with
  | .ok (.ok ()) => pure ()
  | _ => fail "pinned G scope did not settle successfully"
  match ← IO.wait retiringCaller with
  | .ok (.error (.rpc status _)) =>
      expect (status == exactStatus)
        "G retirement changed the admitted peer status"
  | _ => fail "G retirement was replayed or changed classification"
  expect ((← trace.get) == #[100, 100])
    "reconnect changed the resource inside the pinned G scope"
  expect ((← connectCount.get) == 2)
    "generation-scope race opened an unexpected number of generations"
  expect ((← closes.get) == #[100])
    "retired G was not closed exactly once after its scoped lease drained"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"generation-scope shared close failed: {error}"
  expect ((← closes.get) == #[100, 101])
    "final close did not close H exactly once"

private def testEscapedGenerationScopeIsRevoked : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closes ← IO.mkRef (#[] : Array Nat)
  let escaped ← IO.mkRef
    (none : Option (ManagedChannel.TestSupport.GenerationInvoker Nat Unit))
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "escaped generation loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => registered register 401
      selectedAlpn := fun _ => fail "escaped generation queried ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let scopeResult : Except CallError Unit ←
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      escaped.set (some generation)
      pure (.ok ())
  match scopeResult with
  | .ok () => pure ()
  | .error error => fail s!"generation scope failed before escape: {error}"
  let some generation ← escaped.get
    | fail "generation scope did not publish its test capability"
  let invoked ← IO.mkRef false
  let rejected : Except CallError Unit ← generation.invoke fun _ _ => do
    invoked.set true
    pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .scopeClosed => pure ()
  | _ => fail "escaped generation capability was not revoked"
  expect (!(← invoked.get))
    "revoked generation capability reached the retained resource"
  expect ((← closes.get).isEmpty)
    "scope revocation closed a healthy cached generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"escaped-generation shared close failed: {error}"
  expect ((← closes.get) == #[401])
    "final close did not own the escaped generation exactly once"

private def testGenerationScopeDrainsAdmittedInvocation : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let entered ← IO.Promise.new
  let allowCompletion ← IO.Promise.new
  let finished ← IO.mkRef false
  let invocationTask ← IO.mkRef
    (none : Option (Task (Except IO.Error (Except CallError Unit))))
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation drain loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => registered register 402
      selectedAlpn := fun _ => fail "generation drain queried ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let scopedTask ← IO.asTask <|
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      let task : Task (Except IO.Error (Except CallError Unit)) ← IO.asTask <|
        generation.invoke fun resource _ => do
          expect (resource == 402)
            "admitted generation invocation selected the wrong resource"
          entered.resolve (some ())
          awaitSignal allowCompletion
          finished.set true
          pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
      invocationTask.set (some task)
      awaitSignal entered
      pure (.ok 17)
  awaitSignal entered
  expect (!(← IO.hasFinished scopedTask))
    "generation callback returned before its admitted invocation drained"
  expect (!(← finished.get))
    "admitted generation invocation ignored its completion fence"
  allowCompletion.resolve (some ())
  match ← IO.wait scopedTask with
  | .ok (.ok 17) => pure ()
  | _ => fail "generation scope did not preserve its callback result"
  let some task ← invocationTask.get
    | fail "generation scope lost its admitted invocation task"
  match ← IO.wait task with
  | .ok (.ok ()) => pure ()
  | _ => fail "admitted generation invocation did not settle cleanly"
  expect (← finished.get)
    "generation scope returned without the admitted invocation's effect"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"generation-drain shared close failed: {error}"
  expect ((← closes.get) == #[402])
    "generation-drain final close did not close exactly once"

private def testGenerationScopePreservesDetachedRetirement : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let nextResource ← IO.mkRef 501
  let entered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let invocationTask ← IO.mkRef
    (none : Option (Task (Except IO.Error (Except CallError Unit))))
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation retirement loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ => fail "generation retirement queried ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let exactStatus :=
    Grpc.Status.error .unavailable "detached exact-generation retirement"
  let scopedTask ← IO.asTask <|
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      let task : Task (Except IO.Error (Except CallError Unit)) ← IO.asTask <|
        generation.invoke fun resource _ => do
          expect (resource == 501)
            "retiring generation invocation selected the wrong resource"
          entered.resolve (some ())
          awaitSignal allowFailure
          pure (Except.error (.rpc exactStatus) :
            Except Grpc.UnaryCall.Error Unit)
      invocationTask.set (some task)
      awaitSignal entered
      -- The domain callback has no result-level knowledge of the detached
      -- call. The generation supervisor must still retain its exact status.
      pure (.ok 29)
  awaitSignal entered
  expect (!(← IO.hasFinished scopedTask))
    "generation scope abandoned an admitted retiring invocation"
  allowFailure.resolve (some ())
  match ← IO.wait scopedTask with
  | .ok (.error (.rpc status _)) =>
      expect (status == exactStatus)
        "generation scope changed the detached retirement status"
  | _ => fail "generation scope discarded detached retirement evidence"
  let some task ← invocationTask.get
    | fail "generation scope lost its retiring invocation task"
  match ← IO.wait task with
  | .ok (.error (.rpc status _)) =>
      expect (status == exactStatus)
        "retiring invocation itself changed peer status"
  | _ => fail "retiring invocation did not return its exact peer status"
  expect ((← closes.get) == #[501])
    "retired generation was not closed exactly once after drain"
  let replacement : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  match replacement with
  | .ok 502 => pure ()
  | _ => fail "detached retirement did not permit a fresh generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"retirement shared close failed: {error}"
  expect ((← closes.get) == #[501, 502])
    "final close did not close the replacement generation exactly once"

private def testGenerationRetirementMergesBySeverity : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let rpcEntered ← IO.Promise.new
  let cleanupEntered ← IO.Promise.new
  let allowRpc ← IO.Promise.new
  let allowCleanup ← IO.Promise.new
  let nextResource ← IO.mkRef 503
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "retirement severity loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ =>
        fail "retirement severity queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let exactStatus :=
    Grpc.Status.error .unavailable "earlier concurrent retirement"
  let result : Except CallError Unit ←
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      let rpc : Task (Except IO.Error (Except CallError Unit)) ← IO.asTask <|
        generation.invoke fun _ _ => do
          rpcEntered.resolve (some ())
          awaitSignal allowRpc
          pure (Except.error (.rpc exactStatus) :
            Except Grpc.UnaryCall.Error Unit)
      let cleanup : Task (Except IO.Error (Except CallError Unit)) ←
        IO.asTask <| generation.invoke fun _ _ => do
          cleanupEntered.resolve (some ())
          awaitSignal allowCleanup
          pure (Except.error .cleanupUncertain :
            Except Grpc.UnaryCall.Error Unit)
      awaitSignal rpcEntered
      awaitSignal cleanupEntered
      allowRpc.resolve (some ())
      waitForTask rpc
      match ← IO.wait rpc with
      | .ok (.error (.rpc status _)) =>
          expect (status == exactStatus)
            "earlier retiring invocation changed exact peer status"
      | _ => return .error .actionFailed
      allowCleanup.resolve (some ())
      waitForTask cleanup
      match ← IO.wait cleanup with
      | .ok (.error .cleanupUncertain) => pure (.ok ())
      | _ => pure (.error .actionFailed)
  match result with
  | .error .cleanupUncertain => pure ()
  | _ => fail "earlier RPC retirement masked later cleanup uncertainty"
  expect ((← closes.get) == #[503])
    "severity-merged retirement did not close its exact generation"
  let callbackResult : Except CallError Unit ←
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      let rpc ← generation.invoke fun _ _ =>
        pure (Except.error (.rpc exactStatus) :
          Except Grpc.UnaryCall.Error Unit)
      match rpc with
      | .error (.rpc status _) =>
          expect (status == exactStatus)
            "callback-merge invocation changed exact peer status"
      | _ => return .error .actionFailed
      pure (.error .cleanupUncertain)
  match callbackResult with
  | .error .cleanupUncertain => pure ()
  | _ => fail "sticky RPC retirement masked stronger callback evidence"
  expect ((← closes.get) == #[503, 504])
    "callback severity merge did not retire its exact generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"retirement severity final close failed: {error}"

private def testLocalCallCompletionDoesNotRetireGeneration : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  for isDeadline in [true, false] do
    let connectCount ← IO.mkRef 0
    let closes ← IO.mkRef (#[] : Array Nat)
    let dependencies : ManagedChannel.Dependencies Nat := {
      resolve := fun _ => pure (.ok destinations)
      loadTrust := fail "local call completion loaded plaintext trust anchors"
      connector := {
        connect := fun _ register => do
          connectCount.modify (· + 1)
          registered register 601
        selectedAlpn := fun _ =>
          fail "local call completion queried ALPN"
        close := fun resource => closes.modify (·.push resource)
      }
    }
    let shared ← ManagedChannel.createWith dependencies configuration
    let localError := if isDeadline then
        Grpc.UnaryCall.Error.localDeadlineExceeded
      else
        Grpc.UnaryCall.Error.ownerCancelled
    let scopeResult : Except CallError Nat ←
      ManagedChannel.TestSupport.withGeneration shared fun generation => do
        let failed ← generation.invoke fun _ _ =>
          pure (Except.error localError :
            Except Grpc.UnaryCall.Error Nat)
        match isDeadline, failed with
        | true, .error .localDeadlineExceeded => pure ()
        | false, .error .ownerCancelled => pure ()
        | _, _ => return .error .supervisorInvariant
        -- A local call completion must not poison the scope. The next exact
        -- invocation remains admissible on the same retained resource.
        generation.invoke fun resource _ =>
          pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
    match scopeResult with
    | .ok 601 => pure ()
    | _ => fail "local call completion poisoned its exact generation scope"
    let mapped := if isDeadline then
        CallError.localDeadlineExceeded
      else
        CallError.ownerCancelled
    expect (!requiresGenerationRetirement mapped)
      "local call completion was classified as generation-retiring"
    expect ((← closes.get).isEmpty)
      "local call completion retired a healthy generation"
    expect ((← connectCount.get) == 1)
      "local call completion reconnected the shared channel"
    match ← ManagedChannel.close shared with
    | .ok () => pure ()
    | .error error => fail s!"local-completion shared close failed: {error}"
    expect ((← closes.get) == #[601])
      "local-completion final close did not close exactly once"

private def allGrpcCodes : List Grpc.Code := [
  .ok,
  .cancelled,
  .unknown,
  .invalidArgument,
  .deadlineExceeded,
  .notFound,
  .alreadyExists,
  .permissionDenied,
  .resourceExhausted,
  .failedPrecondition,
  .aborted,
  .outOfRange,
  .unimplemented,
  .internal,
  .unavailable,
  .dataLoss,
  .unauthenticated
]

private def testSharedRpcRetirementClassification : IO Unit := do
  let expectedAmbiguous : List Grpc.Code := [
    .cancelled,
    .unknown,
    .deadlineExceeded,
    .resourceExhausted,
    .internal,
    .unavailable
  ]
  expect (transportAmbiguousRpcCodes == expectedAmbiguous)
    "transport-ambiguous RPC code table changed"
  expect (allGrpcCodes.length == 17)
    "gRPC status classification fixture is not exhaustive"

  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  for code in allGrpcCodes do
    let connectCount ← IO.mkRef 0
    let nextResource ← IO.mkRef 1
    let closes ← IO.mkRef (#[] : Array Nat)
    let actionCount ← IO.mkRef 0
    let dependencies : ManagedChannel.Dependencies Nat := {
      resolve := fun _ => pure (.ok destinations)
      loadTrust := fail "status classification loaded trust anchors"
      connector := {
        connect := fun _ register => do
          connectCount.modify (· + 1)
          let resource ← nextResource.get
          nextResource.set (resource + 1)
          registered register resource
        selectedAlpn := fun _ =>
          fail "status classification queried plaintext ALPN"
        close := fun resource => closes.modify (·.push resource)
      }
    }
    let shared ← ManagedChannel.createWith dependencies configuration
    let failed : Except CallError Nat ←
      ManagedChannel.unaryWith shared fun _ _ => do
        actionCount.modify (· + 1)
        pure (.error (.rpc
          (Grpc.Status.error code "bounded classification fixture")))
    match failed with
    | .error (.rpc actual _) =>
        expect (actual ==
            Grpc.Status.error code "bounded classification fixture")
          s!"shared call changed classified status {repr code}"
    | _ => fail s!"shared call did not preserve classified status {repr code}"
    expect ((← actionCount.get) == 1)
      s!"shared call replayed classified status {repr code}"

    let shouldRetire := rpcCodeRequiresGenerationRetirement code
    expect (
      requiresGenerationRetirement
        (.rpc (Grpc.Status.error code "bounded classification fixture")) ==
          shouldRetire)
      s!"call-error retirement disagreed for status {repr code}"
    if shouldRetire then
      expect ((← closes.get) == #[1])
        s!"transport-ambiguous status {repr code} did not retire generation"
    else
      expect ((← closes.get).isEmpty)
        s!"application status {repr code} retired a healthy generation"

    let recovered : Except CallError Nat ←
      ManagedChannel.unaryWith shared fun resource _ =>
        pure (Except.ok resource :
          Except Grpc.UnaryCall.Error Nat)
    let expectedResource := if shouldRetire then 2 else 1
    match recovered with
    | .ok resource =>
        expect (resource == expectedResource)
          s!"status {repr code} selected generation {resource}, \
            expected {expectedResource}"
    | .error error =>
        fail s!"status {repr code} prevented later RPC: {error}"
    expect ((← connectCount.get) == (if shouldRetire then 2 else 1))
      s!"status {repr code} produced the wrong reconnection count"

    match ← ManagedChannel.close shared with
    | .ok () => pure ()
    | .error error =>
        fail s!"status {repr code} left shared close failed: {error}"
    let expectedCloses := if shouldRetire then #[1, 2] else #[1]
    expect ((← closes.get) == expectedCloses)
      s!"status {repr code} changed exact generation close ownership"

private def testSharedRpcRetirementCloseFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeTaskAttempts ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "retirement close-failure loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        registered register 401
      selectedAlpn := fun _ =>
        fail "retirement close-failure queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 401)
          "retirement close-failure closed the wrong resource"
        closeCount.modify (· + 1)
        throw (IO.userError "deterministic retirement close failure")
    }
    beforeClaimedCloseTask := do
      closeTaskAttempts.modify (· + 1)
      throw (IO.userError "deterministic claimed-close task allocation failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let expected :=
    Grpc.Status.error .unavailable "exact admitted retirement failure"
  let failed : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (.error (.rpc expected))
  match failed with
  | .error (.rpc actual _) =>
      expect (actual == expected)
        "failed generation retirement overwrote the admitted RPC status"
  | _ =>
      fail "failed generation retirement did not return the admitted RPC status"
  expect ((← connectCount.get) == 1)
    "failed generation retirement replayed the admitted RPC"
  expect ((← closeCount.get) == 1)
    "failed generation retirement did not close exactly once"
  expect ((← closeTaskAttempts.get) == 1)
    "failed generation retirement did not exercise the inline close fallback"
  waitForSharedPhase shared .draining
  expectCleanupInventory shared 1 0 0 0
    "failed generation retirement did not retain its exact channel owner"

  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelDraining => pure ()
  | _ =>
      fail "failed generation retirement admitted a later initialization"
  expect ((← connectCount.get) == 1)
    "failed generation retirement reconnected"

  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | _ =>
      fail "shared close forgot failed generation-retirement cleanup"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | _ =>
      fail "repeated shared close lost generation-retirement uncertainty"
  expect ((← closeCount.get) == 1)
    "ambiguous generation cleanup was retried"
  expectCleanupInventory shared 1 0 0 0
    "terminal retirement failure erased its exact channel owner"

private def testSharedInitializationCleanupUncertainty : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeTaskAttempts ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "failed initialization loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 301
        throw (IO.userError
          "connector failed after publishing raw resource 301")
      selectedAlpn := fun _ =>
        fail "failed initialization queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 301)
          "failed initialization closed the wrong resource"
        closeCount.modify (· + 1)
        throw (IO.userError "deterministic initialization close failure")
    }
    beforeClaimedCloseTask := do
      closeTaskAttempts.modify (· + 1)
      throw (IO.userError "deterministic claimed-close task allocation failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let result : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match result with
  | .error .cleanupUncertain => pure ()
  | _ => fail "failed initialization cleanup was not contained"
  expect ((← connectCount.get) == 1)
    "failed initialization was retried before returning"
  expect ((← closeCount.get) == 1)
    "failed initialization cleanup was not attempted exactly once"
  expect ((← closeTaskAttempts.get) == 2)
    ("failed initialization did not exercise both the non-inline handoff " ++
      "and caller-owned inline recovery")
  waitForSharedPhase shared .draining
  expectCleanupInventory shared 0 1 0 0
    "failed initialization did not retain its exact raw owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
    shared) ==
      some (.cleanupUncertain 0 .connectionAttemptsFailed
        .retryableTransport 301))
    "failed initialization retained the wrong raw cleanup capability"

  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | _ =>
      fail "shared close forgot failed-initialization cleanup uncertainty"
  expect ((← shared.phase) == .draining)
    "uncertain initialization cleanup published a clean closed phase"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | _ =>
      fail "repeated shared close did not retain initialization uncertainty"
  expect ((← closeCount.get) == 1)
    "ambiguous initialization cleanup was retried"
  expectCleanupInventory shared 0 1 0 0
    "terminal initialization failure erased its exact raw owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
    shared) ==
      some (.cleanupUncertain 0 .connectionAttemptsFailed
        .retryableTransport 301))
    "repeated close changed the retained raw cleanup capability"
  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelDraining => pure ()
  | _ => fail "cleanup-uncertain shared owner admitted another initialization"
  expect ((← connectCount.get) == 1)
    "cleanup-uncertain shared owner reconnected"

private def testCancelledSoleWaiterTerminalHandoffSelfDrives : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeTaskAttempts ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "cancelled sole waiter loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 1_318
        connectorEntered.resolve (some ())
        awaitSignal allowFailure
        pure .failed
      selectedAlpn := fun _ =>
        fail "cancelled sole waiter queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_318)
          "cancelled sole waiter closed the wrong exact resource"
        closeCount.modify (· + 1)
        throw (IO.userError
          "cancelled sole waiter deterministic cleanup failure")
    }
    beforeClaimedCloseTask := do
      closeTaskAttempts.modify (· + 1)
      throw (IO.userError
        "cancelled sole waiter deterministic close-task allocation failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  cancellation.cancel
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ => fail "cancelled sole initialization waiter returned the wrong result"
  -- No admitted lease or future caller remains to recover a failed detached
  -- close-task allocation. The terminal initializer must therefore drop only
  -- its now data-only task handle and drive the retained owner inline.
  try
    expectCleanupInventory shared 0 0 0 1
      "cancelled sole waiter did not leave its initializer task reachable"
  finally
  allowFailure.resolve (some ())
  waitForCloseCompletion shared
  waitForNoCloseOwner shared
  expect ((← shared.phase) == .draining)
    "automatic sole-waiter containment published a clean closed phase"
  expectCleanupInventory shared 0 1 0 0
    "automatic sole-waiter containment stranded its terminal task or owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .connectionAttemptsFailed
          .retryableTransport 1_318))
    "automatic sole-waiter containment retained the wrong exact owner"
  expect (!(← ManagedChannel.TestSupport.hasRetainedCloseTask shared) &&
      !(← ManagedChannel.TestSupport.closeNeedsOwner shared) &&
      !(← ManagedChannel.TestSupport.closeOwnerStarting shared))
    "automatic sole-waiter containment left undriven close custody"
  expect ((← connectCount.get) == 1 && (← closeCount.get) == 1 &&
      (← closeTaskAttempts.get) == 1 && (← actionCount.get) == 0)
    "automatic sole-waiter containment duplicated or skipped an effect"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"settled sole-waiter containment changed result: {repr result}"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 1)
    "observing sole-waiter completion retried allocation or cleanup"

private def testTerminalHandoffDoesNotJoinExistingInlineCloser : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeTaskAttempts ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let closeAllocationEntered ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "inline-closer handoff loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 1_319
        connectorEntered.resolve (some ())
        awaitSignal allowFailure
        pure .failed
      selectedAlpn := fun _ =>
        fail "inline-closer handoff queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_319)
          "inline-closer handoff closed the wrong exact resource"
        closeCount.modify (· + 1)
        throw (IO.userError
          "inline-closer handoff deterministic cleanup failure")
    }
    beforeClaimedCloseTask := do
      closeTaskAttempts.modify (· + 1)
      closeAllocationEntered.resolve (some ())
      throw (IO.userError
        "inline-closer handoff deterministic close-task allocation failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  cancellation.cancel
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ => fail "inline-closer handoff cancellation returned the wrong result"

  let closer ← IO.asTask (ManagedChannel.close shared)
  awaitSignal closeAllocationEntered
  try
    IO.sleep 10
    expect (!(← IO.hasFinished closer))
      "inline closer did not join the still-pending initializer"
    expect (← ManagedChannel.TestSupport.closeOwnerStarting shared)
      "inline closer lost its joining-start custody"
    expectCleanupInventory shared 0 0 0 1
      "inline closer removed the pending initializer before terminal transfer"
  finally
    allowFailure.resolve (some ())
  match ← IO.wait closer with
  | .ok (.error .transport) => pure ()
  | _ => fail "terminal handoff did not release its existing inline closer"
  expectCleanupInventory shared 0 1 0 0
    "existing inline closer stranded its terminal task or exact owner"
  expect ((← connectCount.get) == 1 && (← closeCount.get) == 1 &&
      (← closeTaskAttempts.get) == 1 && (← actionCount.get) == 0)
    "existing inline closer duplicated or skipped an effect"
  expect (!(← ManagedChannel.TestSupport.closeNeedsOwner shared) &&
      !(← ManagedChannel.TestSupport.closeOwnerStarting shared) &&
      !(← ManagedChannel.TestSupport.hasRetainedCloseTask shared))
    "existing inline closer left structural close custody"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"repeated inline-closer handoff changed result: {repr result}"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 1)
    "repeated inline-closer handoff retried allocation or cleanup"

private def testExternalInlineCloserRetainsTransferredInitializer :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeTaskAttempts ← IO.mkRef 0
  let handoffCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let handoffEntered ← IO.Promise.new
  let allowHandoff ← IO.Promise.new
  let closeAllocationEntered ← IO.Promise.new
  let allowCloseAllocation ← IO.Promise.new
  let inlinePublicationEntered ← IO.Promise.new
  let allowInlinePublication ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "post-transfer inline closer loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 1_323
        connectorEntered.resolve (some ())
        awaitSignal allowFailure
        pure .failed
      selectedAlpn := fun _ =>
        fail "post-transfer inline closer queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_323)
          "post-transfer inline closer closed the wrong exact resource"
        closeCount.modify (· + 1)
        throw (IO.userError
          "post-transfer inline closer deterministic cleanup failure")
    }
    beforeInitializationCloseHandoff := do
      handoffCount.modify (· + 1)
      handoffEntered.resolve (some ())
      awaitSignal allowHandoff
    beforeClaimedCloseTask := do
      closeTaskAttempts.modify (· + 1)
      closeAllocationEntered.resolve (some ())
      awaitSignal allowCloseAllocation
      throw (IO.userError
        "post-transfer inline closer deterministic task allocation failure")
    afterInlineCloseDriverPublication := do
      inlinePublicationEntered.resolve (some ())
      awaitSignal allowInlinePublication
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  cancellation.cancel
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "post-transfer inline closer cancellation returned the wrong result"

  -- The initializer has already transferred its exact terminal owner and
  -- close claim, but remains the one live task behind the handoff seam.
  allowFailure.resolve (some ())
  awaitSignal handoffEntered
  expectSupervisorSnapshot shared .draining 0 1 none [] []
    (.failed .cleanupUncertain 0 (some 0)) 0 false {
      initializationOwners := 1
      pendingInitializations := 1
    } .needsOwner
    "terminal transfer did not retain its owner, task, and close custody"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .connectionAttemptsFailed
          .retryableTransport 1_323))
    "terminal transfer retained the wrong exact initialization owner"
  expect (!(← ManagedChannel.TestSupport.closeCompletionResolved shared))
    "terminal transfer published completion before its live task handoff"

  -- An external joiner wins needs-owner custody. Its forced allocation
  -- failure must run inline without erasing the different task identity.
  let closer ← IO.asTask (ManagedChannel.close shared)
  awaitSignal closeAllocationEntered
  try
    try
      expectSupervisorSnapshot shared .draining 0 1 none [] []
        (.failed .cleanupUncertain 0 (some 0)) 0 false {
          initializationOwners := 1
          pendingInitializations := 1
        } .startingJoining
        "external allocation changed more than joining-driver custody"
    finally
      allowCloseAllocation.resolve (some ())
    awaitSignal inlinePublicationEntered
    expectSupervisorSnapshot shared .draining 0 1 none [] []
      (.failed .cleanupUncertain 0 (some 0)) 0 false {
        initializationOwners := 1
        pendingInitializations := 1
      } .inline
      "inline fallback publication changed initializer custody"
    expect (!(← IO.hasFinished closer))
      "external inline closer did not join the transferred initializer"
    expect ((← ManagedChannel.TestSupport.initializationTaskFinished
        shared) == some false)
      "external inline closer lost or completed the paused initializer"
    expect (!(← ManagedChannel.TestSupport.closeCompletionResolved shared))
      "external inline fallback completed before joining its initializer"
  finally
    allowInlinePublication.resolve (some ())
    allowHandoff.resolve (some ())

  match ← IO.wait closer with
  | .ok (.error .transport) => pure ()
  | _ =>
    fail "post-transfer external inline close returned the wrong result"
  expectSupervisorSnapshot shared .draining 0 1 none [] []
    (.failed .cleanupUncertain 0 none) 0 false {
      initializationOwners := 1
    } .inlineTerminal
    "external inline closer did not settle terminal custody coherently"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .connectionAttemptsFailed
          .retryableTransport 1_323))
    "external inline closer changed the retained exact owner"
  expect ((← connectCount.get) == 1 && (← closeCount.get) == 1 &&
      (← closeTaskAttempts.get) == 1 && (← handoffCount.get) == 1 &&
      (← actionCount.get) == 0)
    "post-transfer race duplicated or skipped an owned effect"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"repeated post-transfer inline close returned {repr result}"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 1)
    "repeated post-transfer close retried allocation or cleanup"

private def testSharedCleanupFailureIsConsumedOnceAcrossTwoWaiters :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowConnectorFailure ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "two-waiter cleanup failure loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 1_307
        connectorEntered.resolve (some ())
        awaitSignal allowConnectorFailure
        pure .failed
      selectedAlpn := fun _ =>
        fail "two-waiter cleanup failure queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_307)
          "two-waiter cleanup failure closed the wrong resource"
        closeCount.modify (· + 1)
        throw (IO.userError
          "deterministic two-waiter initialization cleanup failure")
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let firstCancellation ← Grpc.Cancellation.create
  let first ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared firstCancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  let secondCancellation ← Grpc.Cancellation.create
  let second ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared secondCancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  waitForInitializationCompletionWaiters shared 2
  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  expect (!(← IO.hasFinished closer))
    "joined close returned while cleanup-failure waiters retained leases"
  allowConnectorFailure.resolve (some ())

  match ← IO.wait first with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ => fail "first cleanup-failure waiter returned the wrong result"
  match ← IO.wait second with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ => fail "second cleanup-failure waiter returned the wrong result"
  expect ((← connectCount.get) == 1 &&
      (← closeCount.get) == 1 && (← actionCount.get) == 0)
    "two cleanup-failure waiters duplicated an effect or reached the action"
  waitForSharedPhase shared .draining
  expectCleanupInventory shared 0 1 0 0
    "stale cleanup-failure waiter duplicated or erased exact custody"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .connectionAttemptsFailed
          .retryableTransport 1_307))
    "stale cleanup-failure waiter changed authoritative terminal evidence"
  match ← IO.wait closer with
  | .ok (.error .transport) => pure ()
  | _ =>
      fail "two-waiter cleanup uncertainty allowed clean joined close"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"repeated two-waiter close changed outcome: {repr result}"
  expect ((← closeCount.get) == 1)
    "two-waiter settlement retried ambiguous initialization cleanup"

private def testMismatchedCleanupFailureIsQuarantined : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let quarantinedCloseCount ← IO.mkRef 0
  let failureDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "quarantine fixture loaded trust anchors"
    connector := {
      connect := fun _ register => do
        discard <| register 1_308
        pure .failed
      selectedAlpn := fun _ =>
        fail "quarantine fixture queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_308)
          "quarantine fixture closed the wrong resource"
        quarantinedCloseCount.modify (· + 1)
        throw (IO.userError "deterministic quarantined cleanup failure")
    }
  }
  let failure ← match ← Subchannel.openWith failureDependencies configuration with
    | .error failure =>
        expect (failure.error == .cleanupFailed)
          "quarantine fixture did not retain cleanup custody"
        pure failure
    | .ok channel =>
        discard <| Subchannel.close channel
        fail "quarantine fixture unexpectedly opened a channel"
  expect ((← quarantinedCloseCount.get) == 1)
    "quarantine fixture did not attempt cleanup exactly once"

  let sharedCloseCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowConnector ← IO.Promise.new
  let sharedDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "mismatch quarantine loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectorEntered.resolve (some ())
        awaitSignal allowConnector
        registered register 1_309
      selectedAlpn := fun _ =>
        fail "mismatch quarantine queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_309)
          "mismatch quarantine closed the wrong live generation"
        sharedCloseCount.modify (· + 1)
    }
  }
  let shared ← ManagedChannel.createWith sharedDependencies configuration
  let caller ← IO.asTask <| ManagedChannel.unaryWith shared fun resource _ => do
    actionCount.modify (· + 1)
    pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectorEntered

  let injected ←
    ManagedChannel.TestSupport.settleInitializationFailureForGeneration
      shared 99 failure
  match injected with
  | .cleanupUncertain => pure ()
  | _ => fail "mismatched cleanup owner was not contained"
  waitForSharedPhase shared .draining
  expectCleanupInventory shared 0 1 0 1
    "mismatched cleanup owner erased the live pending initializer"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared).isNone)
    "mismatched cleanup owner overwrote the authoritative pending slot"
  expect ((← ManagedChannel.TestSupport.quarantinedInitializationEvidence
      shared) == [{
        generation := 99
        primaryError := .connectionAttemptsFailed
        primaryDisposition := .retryableTransport
        resource := 1_308
      }])
    "mismatched cleanup owner retained the wrong quarantine evidence"

  let duplicate ←
    ManagedChannel.TestSupport.settleInitializationFailureForGeneration
      shared 99 failure
  match duplicate with
  | .cleanupUncertain => pure ()
  | _ => fail "duplicate mismatched cleanup observation changed classification"
  try
    expectCleanupInventory shared 0 1 1 1
      ("duplicate mismatched owner wrapper fabricated no owner but did " ++
        "retain one sticky uncertainty bit")
  finally
    -- Never strand the initializer/close tasks if the mid-race assertion
    -- fails: the test executable must report rather than appear to deadlock.
    allowConnector.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ => fail "quarantine fixture caller returned the wrong result"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result => fail s!"quarantined owner allowed clean close: {repr result}"
  expectCleanupInventory shared 0 1 1 0
    "terminal quarantine changed exact retained custody"
  expect ((← sharedCloseCount.get) == 1 &&
      (← actionCount.get) == 0 &&
      (← quarantinedCloseCount.get) == 1)
    "quarantine settlement duplicated cleanup or admitted work after drain"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result => fail s!"repeated quarantined close changed outcome: {repr result}"
  expect ((← sharedCloseCount.get) == 1 &&
      (← quarantinedCloseCount.get) == 1)
    "repeated close retried a quarantined cleanup capability"

private def makeCleanupFailure
    (configuration : Grpc.ManagedChannel.Config)
    (destinations : Array Grpc.NameResolver.Address)
    (resource : Nat)
    (closeCount : IO.Ref Nat)
    (detail : String) : IO (OwnedOpenFailure Nat) := do
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail s!"{detail}: loaded trust anchors"
    connector := {
      connect := fun _ register => do
        discard <| register resource
        pure .failed
      selectedAlpn := fun _ =>
        fail s!"{detail}: queried plaintext ALPN"
      close := fun actual => do
        expect (actual == resource)
          s!"{detail}: closed the wrong exact resource"
        closeCount.modify (· + 1)
        throw (IO.userError s!"{detail}: deterministic cleanup failure")
    }
  }
  match ← Subchannel.openWith dependencies configuration with
  | .error failure =>
      expect (failure.primaryError == .connectionAttemptsFailed)
        s!"{detail}: lost its sanitized transport cause"
      expect (failure.primaryDisposition == .retryableTransport)
        s!"{detail}: changed its primary retry class"
      expect (failure.error == .cleanupFailed &&
          failure.disposition == .cleanupUncertain &&
          !failure.shouldRetry && failure.hasCleanupUncertainty)
        s!"{detail}: cleanup uncertainty did not govern effective policy"
      pure failure
  | .ok channel =>
      discard <| Subchannel.close channel
      fail s!"{detail}: unexpectedly opened a channel"

private def testOwnedCleanupCustodyTransfersToSharedSupervisor : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let sharedDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "direct custody transfer resolved an endpoint"
    loadTrust := fail "direct custody transfer loaded trust anchors"
    connector := forbiddenConnector "direct custody transfer"
  }

  -- An available exact owner transfers into shared state in one step. The
  -- wrapper becomes data-only, and direct close must not compete with or
  -- replay the supervisor-owned cleanup debt.
  let availableCloseCount ← IO.mkRef 0
  let available ← makeCleanupFailure configuration destinations
    1_320 availableCloseCount "available custody transfer"
  let availableBefore ← available.snapshot
  expect (availableBefore.custody == .available &&
      availableBefore.physicalOwnerCount == 1 &&
      availableBefore.cleanupAuthorized)
    "available transfer fixture did not begin with one exact owner"
  let availableShared ←
    ManagedChannel.createWith sharedDependencies configuration
  match ←
      ManagedChannel.TestSupport.settleInitializationFailureForGeneration
        availableShared 41 available with
  | .cleanupUncertain => pure ()
  | result => fail s!"available custody transfer returned {repr result}"
  let availableAfter ← available.snapshot
  expect (availableAfter.custody == .transferred &&
      availableAfter.physicalOwnerCount == 0 &&
      !availableAfter.cleanupAuthorized &&
      !(← available.hasCleanupCustody))
    "available custody transfer left exact authority in the wrapper"
  match ← available.close with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"transferred wrapper direct close returned {repr result}"
  expect ((← available.snapshot).custody == .transferred)
    "direct close changed transferred wrapper custody"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      availableShared) ==
        some (.cleanupUncertain 41 .connectionAttemptsFailed
          .retryableTransport 1_320))
    "available transfer retained the wrong exact supervisor owner"
  match ← ManagedChannel.close availableShared with
  | .error .transport => pure ()
  | result =>
      fail s!"available transfer shared close returned {repr result}"
  expectCleanupInventory availableShared 0 1 0 0
    "available transfer shared close erased its cleanup debt"
  expect ((← availableCloseCount.get) == 1)
    "available transfer shared close replayed the raw connector close"

  -- Once direct close publishes quarantine, the wrapper remains the sole
  -- observation-only home of the raw value. Shared supervision records
  -- missing authority and never steals or replays that value.
  let quarantinedCloseCount ← IO.mkRef 0
  let quarantined ← makeCleanupFailure configuration destinations
    1_321 quarantinedCloseCount "quarantined custody transfer"
  match ← quarantined.close with
  | .error .transport => pure ()
  | result => fail s!"quarantine direct close returned {repr result}"
  let quarantinedBefore ← quarantined.snapshot
  expect (quarantinedBefore.custody == .quarantined &&
      quarantinedBefore.physicalOwnerCount == 1 &&
      !quarantinedBefore.cleanupAuthorized &&
      !(← quarantined.hasCleanupCustody) &&
      (← quarantined.hasQuarantinedCustody))
    "direct close did not revoke cleanup and transfer authority"
  let quarantinedShared ←
    ManagedChannel.createWith sharedDependencies configuration
  match ←
      ManagedChannel.TestSupport.settleInitializationFailureForGeneration
        quarantinedShared 42 quarantined with
  | .cleanupUncertain => pure ()
  | result => fail s!"quarantined custody observation returned {repr result}"
  let quarantinedAfter ← quarantined.snapshot
  expect (quarantinedAfter == quarantinedBefore &&
      quarantinedAfter.custody == .quarantined &&
      quarantinedAfter.physicalOwnerCount == 1 &&
      !quarantinedAfter.cleanupAuthorized)
    "shared observation stole quarantined direct custody"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      quarantinedShared) ==
        some (.cleanupAuthorityMissing 42 .connectionAttemptsFailed
          .retryableTransport))
    "quarantined direct owner was treated as transferable authority"
  match ← ManagedChannel.close quarantinedShared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"quarantined observation shared close returned {repr result}"
  expectCleanupInventory quarantinedShared 0 0 1 0
    "quarantined direct owner fabricated shared cleanup authority"
  expect ((← quarantinedCloseCount.get) == 1)
    "quarantined observation replayed the ambiguous raw connector close"

private def testDirectCloseRacesSharedCustodyTransfer : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let rawCloseCount ← IO.mkRef 0
  let failure ← makeCleanupFailure configuration destinations
    1_322 rawCloseCount "direct close versus transfer race"
  let sharedDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "custody race resolved an endpoint"
    loadTrust := fail "custody race loaded trust anchors"
    connector := forbiddenConnector "custody race"
  }
  let shared ← ManagedChannel.createWith sharedDependencies configuration
  let start ← IO.Promise.new
  let directCloser ← IO.asTask do
    awaitSignal start
    failure.close
  let transfer ← IO.asTask do
    awaitSignal start
    ManagedChannel.TestSupport.settleInitializationFailureForGeneration
      shared 43 failure
  start.resolve (some ())

  let directResult ← match ← IO.wait directCloser with
    | .ok result => pure result
    | .error error => throw error
  match directResult with
  | .error .transport | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"racing direct close returned a non-linearizable {repr result}"
  let transferResult ← match ← IO.wait transfer with
    | .ok result => pure result
    | .error error => throw error
  match transferResult with
  | .cleanupUncertain => pure ()
  | result => fail s!"racing supervisor transfer returned {repr result}"

  let afterRace ← failure.snapshot
  let transferWon := afterRace.custody == .transferred
  let quarantineWon := afterRace.custody == .quarantined
  expect ((transferWon || quarantineWon) &&
      !afterRace.cleanupAuthorized &&
      !(← failure.hasCleanupCustody) &&
      afterRace.physicalOwnerCount == (if quarantineWon then 1 else 0))
    "direct-close/transfer race did not publish one terminal custody branch"
  if transferWon then
    expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
        shared) ==
          some (.cleanupUncertain 43 .connectionAttemptsFailed
            .retryableTransport 1_322))
      "winning supervisor transfer lost its exact owner"
  else
    expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
        shared) ==
          some (.cleanupAuthorityMissing 43 .connectionAttemptsFailed
            .retryableTransport))
      "winning direct quarantine was treated as transferable"

  -- Re-presenting the copied wrapper cannot mint another owner. A second
  -- supervisor records missing-authority uncertainty while the first keeps
  -- the sole exact debt.
  let aliasShared ← ManagedChannel.createWith sharedDependencies configuration
  match ←
      ManagedChannel.TestSupport.settleInitializationFailureForGeneration
        aliasShared 44 failure with
  | .cleanupUncertain => pure ()
  | result => fail s!"repeated custody transfer returned {repr result}"
  if transferWon then
    expectCleanupInventory shared 0 1 0 0
      "repeated transfer removed the first supervisor's exact owner"
  else
    expectCleanupInventory shared 0 0 1 0
      "direct quarantine fabricated an exact supervisor owner"
  expectCleanupInventory aliasShared 0 0 1 0
    "repeated transfer fabricated a second exact owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      aliasShared) ==
        some (.cleanupAuthorityMissing 44 .connectionAttemptsFailed
          .retryableTransport))
    "repeated transfer did not retain fail-closed missing-authority evidence"
  match transferWon, ← ManagedChannel.close shared with
  | true, .error .transport | false, .error .supervisorInvariant => pure ()
  | _, result => fail s!"custody race shared close returned {repr result}"
  match ← ManagedChannel.close aliasShared with
  | .error .supervisorInvariant => pure ()
  | result => fail s!"repeated-transfer shared close returned {repr result}"
  expect ((← rawCloseCount.get) == 1)
    "direct-close/transfer race replayed the raw connector close"

private def testCopiedCleanupDiagnosticIsSupervisorInert : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let failedCloseCount ← IO.mkRef 0
  let owned ← makeCleanupFailure configuration destinations
    1_316 failedCloseCount "copied cleanup diagnostic"
  let diagnostic := owned.failure
  let ownedBefore ← owned.snapshot
  expect (ownedBefore.custody == .available &&
      ownedBefore.physicalOwnerCount == 1)
    "copied-diagnostic fixture did not begin with one exact owner"

  let liveCloseCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowConnector ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "copied-diagnostic fixture loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectorEntered.resolve (some ())
        awaitSignal allowConnector
        registered register 1_317
      selectedAlpn := fun _ =>
        fail "copied-diagnostic fixture queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_317)
          "copied-diagnostic fixture closed the wrong live resource"
        liveCloseCount.modify (· + 1)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration

  match ← ManagedChannel.TestSupport.observeInitializationDiagnosticForGeneration
      shared 77 diagnostic with
  | .cleanupUncertain => pure ()
  | result =>
      fail s!"idle copied diagnostic changed classification: {repr result}"
  expect ((← shared.phase) == .accepting)
    "idle copied diagnostic poisoned shared admission"
  expectCleanupInventory shared 0 0 0 0
    "idle copied diagnostic fabricated supervisor debt"

  let caller ← IO.asTask <| ManagedChannel.unaryWith shared fun resource _ => do
    actionCount.modify (· + 1)
    pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectorEntered
  try
    expectCleanupInventory shared 0 0 0 1
      "pending copied-diagnostic fixture lost its exact task"
    for generation in [99, 0] do
      match ←
          ManagedChannel.TestSupport.observeInitializationDiagnosticForGeneration
            shared generation diagnostic with
      | .cleanupUncertain => pure ()
      | result =>
          fail (s!"copied diagnostic generation {generation} changed " ++
            s!"classification: {repr result}")
      expect ((← shared.phase) == .accepting)
        s!"copied diagnostic generation {generation} poisoned shared admission"
      expectCleanupInventory shared 0 0 0 1
        (s!"copied diagnostic generation {generation} replaced the exact " ++
          "pending initializer")
    let ownedAfter ← owned.snapshot
    expect (ownedAfter == ownedBefore &&
        ownedAfter.custody == .available &&
        ownedAfter.physicalOwnerCount == 1)
      "copied diagnostic observation mutated its source owner"
  finally
    allowConnector.resolve (some ())
  match ← IO.wait caller with
  | .ok (.ok 1_317) => pure ()
  | _ => fail "copied-diagnostic live caller returned the wrong result"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"copied-diagnostic shared close returned {repr result}"
  expect ((← actionCount.get) == 1 && (← liveCloseCount.get) == 1 &&
      (← failedCloseCount.get) == 1)
    "copied diagnostic changed live action or exact cleanup effects"
  match ← owned.close with
  | .error .transport => pure ()
  | result => fail s!"copied-diagnostic owner close returned {repr result}"
  expect ((← failedCloseCount.get) == 1)
    "copied-diagnostic owner close retried ambiguous cleanup"

private def testSameOwnedCleanupFailureAcrossGenerationsTransfersOnce :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let failedCloseCount ← IO.mkRef 0
  let failure ← makeCleanupFailure configuration destinations
    1_311 failedCloseCount "same owned cleanup failure"
  expect ((← failedCloseCount.get) == 1)
    "same-owner fixture did not attempt cleanup exactly once"

  let liveCloseCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowConnector ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "same-owner shared fixture loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectorEntered.resolve (some ())
        awaitSignal allowConnector
        registered register 1_312
      selectedAlpn := fun _ =>
        fail "same-owner shared fixture queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_312)
          "same-owner shared fixture closed the wrong live resource"
        liveCloseCount.modify (· + 1)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <| ManagedChannel.unaryWith shared fun resource _ => do
    actionCount.modify (· + 1)
    pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectorEntered

  -- The second white-box observation deliberately guesses the authoritative
  -- pending generation without presenting its exact completion identity. It
  -- must quarantine uncertainty, never replace or strand the live task.
  for generation in [99, 0] do
    match ←
        ManagedChannel.TestSupport.settleInitializationFailureForGeneration
          shared generation failure with
    | .cleanupUncertain => pure ()
    | result =>
        fail s!"same owner generation {generation} returned {repr result}"
  let transferred ← failure.snapshot
  expect (transferred.custody == .transferred &&
      transferred.physicalOwnerCount == 0 &&
      !(← failure.hasCleanupCustody))
    "repeated transfer left or fabricated custody in the source wrapper"
  match ← failure.close with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"repeatedly transferred wrapper direct close returned {repr result}"
  waitForSharedPhase shared .draining
  try
    expectCleanupInventory shared 0 1 1 1
      "one cleanup owner was retained more than once"
    expect ((← ManagedChannel.TestSupport.quarantinedInitializationEvidence
        shared) == [{
          generation := 99
          primaryError := .connectionAttemptsFailed
          primaryDisposition := .retryableTransport
          resource := 1_311
        }])
      "one cleanup owner changed identity across generations"
    expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
        shared) == none)
      ("generation-only alias replaced the authoritative pending slot " ++
        "without completion identity")
  finally
    allowConnector.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ =>
      fail "same-owner live caller returned the wrong result"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"same-owner joined close returned {repr result}"
  expectCleanupInventory shared 0 1 1 0
    "same-owner terminal inventory changed exact custody"
  expect ((← failedCloseCount.get) == 1 &&
      (← liveCloseCount.get) == 1 && (← actionCount.get) == 0)
    "same-owner settlement duplicated cleanup or admitted terminal work"

  -- Reusing the now-transferred wrapper in another supervisor cannot
  -- fabricate an owner. It records sticky missing-authority evidence.
  let aliasShared ← ManagedChannel.createWith dependencies configuration
  match ←
      ManagedChannel.TestSupport.settleInitializationFailureForGeneration
        aliasShared 7 failure with
  | .cleanupUncertain => pure ()
  | result =>
      fail s!"cross-supervisor transferred wrapper returned {repr result}"
  waitForSharedPhase aliasShared .draining
  expectCleanupInventory aliasShared 0 0 1 0
    "cross-supervisor transferred wrapper fabricated exact custody"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      aliasShared) ==
        some (.cleanupAuthorityMissing 7 .connectionAttemptsFailed
          .retryableTransport))
    "cross-supervisor wrapper lost its fail-closed primary evidence"
  match ← ManagedChannel.close aliasShared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"cross-supervisor wrapper allowed clean close: {repr result}"

private def testDistinctOwnedCleanupFailuresAtSameGenerationAreBothRetained :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let firstCloseCount ← IO.mkRef 0
  let secondCloseCount ← IO.mkRef 0
  let firstFailure ← makeCleanupFailure configuration destinations
    1_313 firstCloseCount "first distinct cleanup owner"
  let secondFailure ← makeCleanupFailure configuration destinations
    1_314 secondCloseCount "second distinct cleanup owner"
  let firstSnapshot ← firstFailure.snapshot
  let secondSnapshot ← secondFailure.snapshot
  expect (firstSnapshot == secondSnapshot &&
      firstSnapshot.custody == .available &&
      secondSnapshot.custody == .available &&
      firstSnapshot.physicalOwnerCount == 1 &&
      secondSnapshot.physicalOwnerCount == 1)
    ("same-diagnostic snapshots were not observationally equal before " ++
      "their distinct exact owners transferred")

  let liveCloseCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowConnector ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "distinct-owner shared fixture loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectorEntered.resolve (some ())
        awaitSignal allowConnector
        registered register 1_315
      selectedAlpn := fun _ =>
        fail "distinct-owner shared fixture queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_315)
          "distinct-owner fixture closed the wrong live resource"
        liveCloseCount.modify (· + 1)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <| ManagedChannel.unaryWith shared fun resource _ => do
    actionCount.modify (· + 1)
    pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectorEntered

  for failure in [firstFailure, secondFailure] do
    match ←
        ManagedChannel.TestSupport.settleInitializationFailureForGeneration
          shared 99 failure with
    | .cleanupUncertain => pure ()
    | result =>
        fail s!"distinct same-generation owner returned {repr result}"
  let firstTransferred ← firstFailure.snapshot
  let secondTransferred ← secondFailure.snapshot
  expect (firstTransferred == secondTransferred &&
      firstTransferred.custody == .transferred &&
      secondTransferred.custody == .transferred &&
      firstTransferred.physicalOwnerCount == 0 &&
      secondTransferred.physicalOwnerCount == 0)
    ("observationally equal snapshots did not independently transfer both " ++
      "hidden exact owners")
  waitForSharedPhase shared .draining
  try
    expectCleanupInventory shared 0 2 0 1
      "same-generation owners were deduplicated by diagnostic generation"
    expect ((← ManagedChannel.TestSupport.quarantinedInitializationEvidence
        shared) == [{
          generation := 99
          primaryError := .connectionAttemptsFailed
          primaryDisposition := .retryableTransport
          resource := 1_314
        }, {
          generation := 99
          primaryError := .connectionAttemptsFailed
          primaryDisposition := .retryableTransport
          resource := 1_313
        }])
      "distinct same-generation owners lost exact owner identity"
  finally
    allowConnector.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ =>
      fail "distinct-owner live caller returned the wrong result"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"distinct-owner joined close returned {repr result}"
  expectCleanupInventory shared 0 2 0 0
    "distinct-owner terminal inventory changed exact custody"
  expect ((← firstCloseCount.get) == 1 &&
      (← secondCloseCount.get) == 1 &&
      (← liveCloseCount.get) == 1 && (← actionCount.get) == 0)
    "distinct owner settlement retried or discarded a cleanup effect"

private def testStaleOwnerFreeWaiterUsesAuthoritativeFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let cleanupCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let firstConnectorEntered ← IO.Promise.new
  let allowFirstFailure ← IO.Promise.new
  let cancelledSettlementEntered ← IO.Promise.new
  let allowCancelledSettlement ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "authoritative stale-waiter test loaded trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count =>
          (count, count + 1)
        if attempt == 0 then
          firstConnectorEntered.resolve (some ())
          awaitSignal allowFirstFailure
          pure .failed
        else
          discard <| register 1_310
          pure .failed
      selectedAlpn := fun _ =>
        fail "authoritative stale-waiter test queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_310)
          "authoritative stale-waiter test closed the wrong resource"
        cleanupCount.modify (· + 1)
        throw (IO.userError
          "deterministic authoritative-generation cleanup failure")
    }
    beforeCancelledInitializationSettlement := do
      cancelledSettlementEntered.resolve (some ())
      awaitSignal allowCancelledSettlement
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let staleCancellation ← Grpc.Cancellation.create
  let stale ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared staleCancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal firstConnectorEntered
  let peerCancellation ← Grpc.Cancellation.create
  let peer ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared peerCancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  waitForInitializationCompletionWaiters shared 2
  staleCancellation.cancel
  awaitSignal cancelledSettlementEntered

  allowFirstFailure.resolve (some ())
  match ← IO.wait peer with
  | .ok (.error (.rpc status _)) =>
      expect (status.code == .unavailable)
        "generation-zero retryable failure changed status"
  | _ => fail "peer did not settle generation-zero retryable failure"
  expect ((← shared.phase) == .accepting)
    "retryable generation zero poisoned admission"

  let terminal : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match terminal with
  | .error .cleanupUncertain => pure ()
  | _ => fail "generation-one cleanup failure was not contained"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 1 .connectionAttemptsFailed
          .retryableTransport 1_310))
    "generation one did not publish authoritative terminal custody"
  expectCleanupInventory shared 0 1 0 0
    "generation-one cleanup failure changed exact custody"

  allowCancelledSettlement.resolve (some ())
  match ← IO.wait stale with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ =>
      fail "stale owner-free waiter masked authoritative cleanup uncertainty"
  expect ((← connectCount.get) == 2 &&
      (← cleanupCount.get) == 1 && (← actionCount.get) == 0)
    "authoritative stale-waiter settlement changed effect counts"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"authoritative stale-waiter close returned {repr result}"
  expect ((← cleanupCount.get) == 1)
    "authoritative stale-waiter close retried ambiguous cleanup"

private def testSharedPreOpenFailureIsOwnerFreeAndRetryable : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let initializationAttempts ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "pre-open failure unexpectedly resolved"
    loadTrust := fail "pre-open failure unexpectedly loaded trust anchors"
    connector := forbiddenConnector "pre-open failure"
    beforeInitializationOpen := do
      initializationAttempts.modify (· + 1)
      throw (IO.userError "secret pre-open initialization failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let first : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match first with
  | .error .actionFailed => pure ()
  | _ => fail "pre-open initialization failure was not normalized"
  expect ((← initializationAttempts.get) == 1)
    "pre-open failure ran more than once for one call"
  expect ((← shared.phase) == .accepting)
    "owner-free pre-open failure poisoned channel admission"
  expectCleanupInventory shared 0 0 0 0
    "owner-free pre-open failure created cleanup debt"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared).isNone)
    "known pre-open failure created false uncertainty evidence"
  expect (!(← ManagedChannel.TestSupport.hasRetainedCloseTask shared))
    "known pre-open failure spuriously claimed shared close"
  let second : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ =>
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match second with
  | .error .actionFailed => pure ()
  | _ => fail "owner-free pre-open failure was not retryable"
  expect ((← initializationAttempts.get) == 2)
    "later call did not retry owner-free pre-open setup"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"owner-free pre-open close failed: {error}"
  expect ((← shared.phase) == .closed)
    "owner-free pre-open close did not publish closed"
  expectCleanupInventory shared 0 0 0 0
    "owner-free pre-open close changed the clean inventory"

private def testInitializationTaskAllocationFailureIsRetryable : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let allocationAttempts ← IO.mkRef 0
  let initializationBodies ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.ok destinations)
    loadTrust :=
      fail "initializer allocation failure loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        registered register 1_301
      selectedAlpn := fun _ =>
        fail "initializer allocation failure queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationTaskAllocation := do
      let attempt ← allocationAttempts.modifyGet fun count =>
        (count, count + 1)
      if attempt == 0 then
        throw (IO.userError "deterministic initializer task allocation failure")
    beforeInitializationOpen := initializationBodies.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let first : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match first with
  | .error .actionFailed => pure ()
  | result =>
      fail s!"initializer allocation failure returned {repr result}"
  expect ((← shared.phase) == .accepting)
    "initializer allocation failure poisoned shared admission"
  expectCleanupInventory shared 0 0 0 0
    "initializer allocation failure published terminal custody"
  expect ((← ManagedChannel.TestSupport.nextInitializationGeneration
      shared) == 0)
    "initializer allocation failure published a generation"
  expect ((← allocationAttempts.get) == 1 &&
      (← initializationBodies.get) == 0 &&
      (← resolveCount.get) == 0 && (← connectCount.get) == 0 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "initializer allocation failure crossed a forbidden effect boundary"

  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ => do
      actionCount.modify (· + 1)
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 1_301 => pure ()
  | result =>
      fail s!"initializer allocation failure did not retry: {repr result}"
  expect ((← allocationAttempts.get) == 2 &&
      (← initializationBodies.get) == 1 &&
      (← resolveCount.get) == 1 && (← connectCount.get) == 1 &&
      (← actionCount.get) == 1)
    "initializer allocation retry changed exact effect counts"
  expect ((← ManagedChannel.TestSupport.nextInitializationGeneration
      shared) == 1)
    "initializer allocation retry published the wrong generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"initializer allocation recovery close failed: {error}"
  expect ((← closes.get) == #[1_301])
    "initializer allocation recovery did not close its generation once"

private def testInitializationWaitsForSupervisorPublication : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let publicationEntered ← IO.Promise.new
  let allowPublication ← IO.Promise.new
  let taskBodyEntered ← IO.Promise.new
  let allowTaskBody ← IO.Promise.new
  let claimEntered ← IO.Promise.new
  let allowClaim ← IO.Promise.new
  let publicationCount ← IO.mkRef 0
  let taskBodyCount ← IO.mkRef 0
  let openCount ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.ok destinations)
    loadTrust :=
      fail "publication-gated initializer loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        registered register 1_307
      selectedAlpn := fun _ =>
        fail "publication-gated initializer queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationTaskBody := do
      taskBodyCount.modify (· + 1)
      taskBodyEntered.resolve (some ())
      awaitSignal allowTaskBody
    beforeInitializationTaskPublication := do
      publicationCount.modify (· + 1)
      publicationEntered.resolve (some ())
      awaitSignal allowPublication
    beforeCancelledInitializationClaim := do
      claimEntered.resolve (some ())
      awaitSignal allowClaim
    beforeInitializationOpen := openCount.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun resource _ => do
        actionCount.modify (· + 1)
        pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal claimEntered
  try
    expectSupervisorSnapshot shared .accepting 1 0 none [] [] .idle 0 false
      {} .absent
      "admitted initializer changed supervisor state before its claim"
  finally
    allowClaim.resolve (some ())
  awaitSignal publicationEntered

  -- The publication seam runs while the state transition is still owned by
  -- the supervisor. The detached task must remain behind its private gate:
  -- none of its body, opening, connector, or user effects may start early.
  expect (!(← taskBodyEntered.isResolved))
    "initializer body crossed the supervisor-publication gate"
  expect (!(← IO.hasFinished caller))
    "initializer caller settled before supervisor publication"
  expect ((← publicationCount.get) == 1 &&
      (← taskBodyCount.get) == 0 && (← openCount.get) == 0 &&
      (← resolveCount.get) == 0 && (← connectCount.get) == 0 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "initializer publication gate leaked a pre-publication effect"

  allowPublication.resolve (some ())
  awaitSignal taskBodyEntered
  try
    expectSupervisorSnapshot shared .accepting 1 1 none [] [] (.pending 0)
      0 false { pendingInitializations := 1 } .absent
      "published initializer did not expose pending generation zero"
  finally
    allowTaskBody.resolve (some ())
  match ← IO.wait caller with
  | .ok (.ok 1_307) => pure ()
  | _ => fail "publication-gated initializer returned the wrong result"
  expect ((← publicationCount.get) == 1 &&
      (← taskBodyCount.get) == 1 && (← openCount.get) == 1 &&
      (← resolveCount.get) == 1 && (← connectCount.get) == 1 &&
      (← actionCount.get) == 1)
    "published initializer changed exact effect counts"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"publication-gated close returned {repr result}"
  expect ((← closes.get) == #[1_307])
    "publication-gated initializer did not close its generation exactly once"
  expectCleanupInventory shared 0 0 0 0
    "publication-gated initializer retained cleanup custody"

private def testOwnerAdoptionFailureRollsBackStructurally : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let adoptionAttempts ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let cleanDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "clean adoption rollback loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count =>
          (count, count + 1)
        registered register (1_302 + attempt)
      selectedAlpn := fun _ =>
        fail "clean adoption rollback queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
      beforeOwnerAdoption := do
        let attempt ← adoptionAttempts.modifyGet fun count =>
          (count, count + 1)
        if attempt == 0 then
          throw (IO.userError "deterministic owner allocation failure")
    }
  }
  let clean ← ManagedChannel.createWith cleanDependencies configuration
  let first : Except CallError Unit ←
    ManagedChannel.unaryWith clean fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match first with
  | .error .actionFailed => pure ()
  | result =>
      fail s!"clean adoption rollback returned {repr result}"
  expect ((← clean.phase) == .accepting)
    "clean adoption rollback poisoned shared admission"
  expectCleanupInventory clean 0 0 0 0
    "clean adoption rollback invented terminal custody"
  expect ((← adoptionAttempts.get) == 1 &&
      (← connectCount.get) == 1 && (← actionCount.get) == 0 &&
      (← closes.get) == #[1_302])
    "clean adoption rollback changed exact resource custody"

  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith clean fun resource _ => do
      actionCount.modify (· + 1)
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 1_303 => pure ()
  | result =>
      fail s!"clean adoption rollback did not retry: {repr result}"
  match ← ManagedChannel.close clean with
  | .ok () => pure ()
  | .error error => fail s!"clean adoption rollback close failed: {error}"
  expect ((← adoptionAttempts.get) == 2 &&
      (← connectCount.get) == 2 && (← actionCount.get) == 1 &&
      (← closes.get) == #[1_302, 1_303])
    "clean adoption recovery changed exact resource custody"

  let ambiguousConnectCount ← IO.mkRef 0
  let ambiguousCloseCount ← IO.mkRef 0
  let ambiguousActionCount ← IO.mkRef 0
  let ambiguousDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust :=
      fail "ambiguous adoption rollback loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        ambiguousConnectCount.modify (· + 1)
        registered register 1_304
      selectedAlpn := fun _ =>
        fail "ambiguous adoption rollback queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_304)
          "ambiguous adoption rollback closed the wrong resource"
        ambiguousCloseCount.modify (· + 1)
        throw (IO.userError "deterministic adoption rollback ambiguity")
      beforeOwnerAdoption :=
        throw (IO.userError "deterministic owner allocation failure")
    }
  }
  let ambiguous ←
    ManagedChannel.createWith ambiguousDependencies configuration
  let failed : Except CallError Unit ←
    ManagedChannel.unaryWith ambiguous fun _ _ => do
      ambiguousActionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match failed with
  | .error .cleanupUncertain => pure ()
  | result =>
      fail s!"ambiguous adoption rollback returned {repr result}"
  waitForSharedPhase ambiguous .draining
  expectCleanupInventory ambiguous 0 1 0 0
    "ambiguous adoption rollback lost its exact raw owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      ambiguous) ==
        some (.cleanupUncertain 0 .initializationFailed
          .retryableLocal 1_304))
    "ambiguous adoption rollback retained the wrong resource"
  expect ((← ambiguousConnectCount.get) == 1 &&
      (← ambiguousCloseCount.get) == 1 &&
      (← ambiguousActionCount.get) == 0)
    "ambiguous adoption rollback changed exact effect counts"
  match ← ManagedChannel.close ambiguous with
  | .error .transport => pure ()
  | result =>
      fail s!"ambiguous adoption rollback allowed clean close: {repr result}"
  match ← ManagedChannel.close ambiguous with
  | .error .transport => pure ()
  | result =>
      fail s!"repeated ambiguous adoption close changed outcome: {repr result}"
  expectCleanupInventory ambiguous 0 1 0 0
    "repeated ambiguous adoption close changed exact custody"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      ambiguous) ==
        some (.cleanupUncertain 0 .initializationFailed
          .retryableLocal 1_304))
    "repeated ambiguous adoption close changed the retained resource"
  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith ambiguous fun _ _ => do
      ambiguousActionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelDraining => pure ()
  | result =>
      fail s!"ambiguous adoption rollback admitted a retry: {repr result}"
  expect ((← ambiguousConnectCount.get) == 1 &&
      (← ambiguousCloseCount.get) == 1 &&
      (← ambiguousActionCount.get) == 0)
    "ambiguous adoption rollback retried an effect"

private def testInitializationDebtPoisonsAdmissionAtomically : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeEntered ← IO.Promise.new
  let allowCloseFailure ← IO.Promise.new
  let ownerStartEntered ← IO.Promise.new
  let allowOwnerStart ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "atomic debt test loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 811
        pure .failed
      selectedAlpn := fun _ => fail "atomic debt test queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 811) "atomic debt test closed the wrong resource"
        closeCount.modify (· + 1)
        closeEntered.resolve (some ())
        awaitSignal allowCloseFailure
        throw (IO.userError "deterministic ambiguous initialization close")
    }
    beforeClaimedCloseTask := do
      ownerStartEntered.resolve (some ())
      awaitSignal allowOwnerStart
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let first ← IO.asTask <| ManagedChannel.unaryWith shared fun _ _ =>
    pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal closeEntered
  allowCloseFailure.resolve (some ())
  awaitSignal ownerStartEntered

  try
    expect ((← shared.phase) == .draining)
      "retained initialization debt was published before admission poison"
    expectCleanupInventory shared 0 1 0 1
      ("atomic initialization debt publication lost its exact owner or " ++
        "reachable task")
    let concurrent : Except CallError Unit ←
      ManagedChannel.unaryWith shared fun _ _ =>
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
    match concurrent with
    | .error .channelDraining => pure ()
    | _ => fail "concurrent caller entered after cleanup debt was retained"
    expect ((← connectCount.get) == 1)
      "concurrent caller initialized a replacement after cleanup ambiguity"
  finally
    allowOwnerStart.resolve (some ())
  waitForTask first
  match ← IO.wait first with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ => fail "atomic cleanup-debt caller returned the wrong result"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | _ => fail "atomic cleanup debt allowed shared close to claim success"
  expect ((← closeCount.get) == 1)
    "atomic cleanup-debt containment retried the ambiguous close"

private def testCleanOpeningFailurePreservesUnavailableAndRetry : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      let attempt ← resolveCount.modifyGet fun count => (count, count + 1)
      if attempt == 0 then
        pure (.error .noAddresses)
      else
        pure (.ok destinations)
    loadTrust := fail "clean opening retry loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        registered register 901
      selectedAlpn := fun _ =>
        fail "clean opening retry queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 901) "clean opening retry closed wrong resource"
        closeCount.modify (· + 1)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let first : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match first with
  | .error (.rpc status _) =>
      expect (status.code == .unavailable)
        "clean resolver failure lost upstream UNAVAILABLE status"
  | _ => fail "clean resolver failure did not surface as an RPC status"
  expect ((← shared.phase) == .accepting)
    "owner-free opening failure poisoned the shared channel"
  expectCleanupInventory shared 0 0 0 0
    "owner-free opening failure invented cleanup debt"
  expect ((← actionCount.get) == 0)
    "failed channel opening invoked the RPC action"

  let second : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ => do
      actionCount.modify (· + 1)
      pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  match second with
  | .ok 901 => pure ()
  | _ => fail "later caller did not retry clean channel initialization"
  expect ((← resolveCount.get) == 2 && (← connectCount.get) == 1 &&
      (← actionCount.get) == 1)
    "clean opening retry changed initialization/action counts"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"clean opening retry close failed: {error}"
  expect ((← closeCount.get) == 1)
    "clean opening retry did not close its exact generation"

private def testTerminalPolicyFailureClosesSharedOwner : IO Unit := do
  let configuration ← apiConfiguration "http://api.example.test:50051"
  let initializationAttempts ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.error .noAddresses)
    loadTrust := fail "terminal plaintext policy loaded trust anchors"
    connector := forbiddenConnector "terminal plaintext policy"
    beforeInitializationOpen := initializationAttempts.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let first : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match first with
  | .error .actionFailed => pure ()
  | result =>
      fail s!"terminal endpoint policy returned the wrong result: {repr result}"
  waitForSharedPhase shared .closed
  expect ((← initializationAttempts.get) == 1 &&
      (← resolveCount.get) == 0 && (← actionCount.get) == 0)
    "terminal endpoint policy retried or reached a forbidden effect"
  expectCleanupInventory shared 0 0 0 0
    "terminal endpoint policy invented cleanup debt"

  let second : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match second with
  | .error .channelClosed => pure ()
  | result =>
      fail s!"terminal endpoint policy admitted a later generation: {repr result}"
  expect ((← initializationAttempts.get) == 1 &&
      (← resolveCount.get) == 0 && (← actionCount.get) == 0)
    "terminal endpoint policy restarted after shared close"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"clean terminal-policy close changed outcome: {error}"

private def testTrustPreparationIsTerminalAndPinned : IO Unit := do
  let configuration ← apiConfiguration "https://api.example.test:8443"
  let destinations ← addresses configuration #["192.0.2.10"]

  let failedLoads ← IO.mkRef 0
  let failedResolves ← IO.mkRef 0
  let failedConnects ← IO.mkRef 0
  let failedActions ← IO.mkRef 0
  let failedDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      failedResolves.modify (· + 1)
      pure (.ok destinations)
    loadTrust := do
      failedLoads.modify (· + 1)
      pure (.error (.emptyExplicitPath TrustAnchors.sslCertFileVariable))
    connector := {
      connect := fun _ _ => do
        failedConnects.modify (· + 1)
        pure .failed
      selectedAlpn := fun _ => fail "failed trust preparation queried ALPN"
      close := fun _ => fail "failed trust preparation acquired a network owner"
    }
  }
  let failed ← ManagedChannel.createWith failedDependencies configuration
  let firstFailure : Except CallError Unit ←
    ManagedChannel.unaryWith failed fun _ _ => do
      failedActions.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match firstFailure with
  | .error .actionFailed => pure ()
  | result =>
      fail s!"shared trust preparation returned {repr result}"
  waitForSharedPhase failed .closed
  expect ((← failedLoads.get) == 1 && (← failedResolves.get) == 0 &&
      (← failedConnects.get) == 0 && (← failedActions.get) == 0)
    "terminal trust preparation crossed resolver, connector, or RPC policy"
  expectCleanupInventory failed 0 0 0 0
    "terminal trust preparation created network cleanup custody"
  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith failed fun _ _ => do
      failedActions.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelClosed => pure ()
  | result =>
      fail s!"terminal trust preparation admitted another call: {repr result}"
  expect ((← failedLoads.get) == 1 && (← failedResolves.get) == 0 &&
      (← failedConnects.get) == 0 && (← failedActions.get) == 0)
    "terminal trust preparation was reloaded after shared close"
  match ← ManagedChannel.close failed with
  | .ok () => pure ()
  | .error error => fail s!"terminal trust preparation close failed: {error}"

  let bundle ← trustBundle
  let successfulLoads ← IO.mkRef 0
  let successfulResolves ← IO.mkRef 0
  let successfulConnects ← IO.mkRef 0
  let nextResource ← IO.mkRef 1_401
  let closes ← IO.mkRef (#[] : Array Nat)
  let successfulDependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      successfulResolves.modify (· + 1)
      pure (.ok destinations)
    loadTrust := do
      successfulLoads.modify (· + 1)
      pure (.ok bundle)
    connector := {
      connect := fun _ register => do
        successfulConnects.modify (· + 1)
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ => pure (some requiredAlpn)
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let successful ←
    ManagedChannel.createWith successfulDependencies configuration
  let retired : Except CallError Unit ←
    ManagedChannel.unaryWith successful fun resource _ => do
      expect (resource == 1_401)
        "trust cache retirement used the wrong first generation"
      pure (Except.error (.rpc
        (Grpc.Status.error .unavailable "retire cached-trust generation")) :
          Except Grpc.UnaryCall.Error Unit)
  match retired with
  | .error (.rpc status _) =>
      expect (status.code == .unavailable)
        "trust cache retirement changed its RPC status"
  | result => fail s!"trust cache retirement returned {repr result}"
  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith successful fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 1_402 => pure ()
  | result => fail s!"trust cache reconnect returned {repr result}"
  expect ((← successfulLoads.get) == 1 &&
      (← successfulResolves.get) == 2 &&
      (← successfulConnects.get) == 2)
    "shared trust preparation was not pinned across connection generations"
  expect ((← closes.get) == #[1_401])
    "trust cache retirement did not close its exact generation"
  match ← ManagedChannel.close successful with
  | .ok () => pure ()
  | .error error => fail s!"cached trust shared close failed: {error}"
  expect ((← closes.get) == #[1_401, 1_402])
    "cached trust shared close changed exact generation custody"
  expectCleanupInventory successful 0 0 0 0
    "cached trust close retained network custody"

private def testConnectorInvariantPoisonsSharedClose : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]
  let initializationAttempts ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let oldReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "connector invariant loaded trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count => (count, count + 1)
        if attempt == 0 then
          let some stale ← register 1_101
            | fail "connector invariant first registration was rejected"
          oldReceipt.set (some stale)
          pure .failed
        else
          let some _accepted ← register 1_102
            | fail "connector invariant second registration was rejected"
          let some stale ← oldReceipt.get
            | fail "connector invariant lost its stale receipt"
          pure (.connected stale)
      selectedAlpn := fun _ =>
        fail "connector invariant queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationOpen := initializationAttempts.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let first : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match first with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"connector contract violation was not an invariant: {repr result}"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"connector invariant allowed clean shared close: {repr result}"
  expect ((← shared.phase) == .draining)
    "connector invariant published a clean closed phase"
  let inventory ← ManagedChannel.TestSupport.cleanupInventory shared
  expect (inventory == ({ invariantInitializations := 1 } : CleanupInventory))
    s!"connector invariant retained the wrong terminal inventory: {repr inventory}"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.connectorInvariant 0))
    "connector invariant lost its exact initialization generation"
  expect ((← initializationAttempts.get) == 1 &&
      (← connectCount.get) == 2 && (← actionCount.get) == 0 &&
      (← closes.get) == #[1_101, 1_102])
    "connector invariant changed exact attempt/resource ownership"

  let second : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match second with
  | .error .channelDraining => pure ()
  | result =>
      fail s!"connector invariant admitted a later generation: {repr result}"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"repeated invariant close changed outcome: {repr result}"
  expect ((← initializationAttempts.get) == 1 &&
      (← connectCount.get) == 2 && (← actionCount.get) == 0 &&
      (← closes.get) == #[1_101, 1_102])
    "repeated invariant close retried an effect"

private def invariantCleanupDependencies
    (destinations : Array Grpc.NameResolver.Address)
    (firstResource : Nat)
    (connectCount : IO.Ref Nat)
    (oldReceipt : IO.Ref (Option (RegistrationReceipt Nat)))
    (closes : IO.Ref (Array Nat)) : ManagedChannel.Dependencies Nat := {
  resolve := fun _ => pure (.ok destinations)
  loadTrust := fail "composite connector invariant loaded trust anchors"
  connector := {
    connect := fun _ register => do
      let attempt ← connectCount.modifyGet fun count => (count, count + 1)
      if attempt == 0 then
        let some stale ← register firstResource
          | fail "composite invariant first registration was rejected"
        oldReceipt.set (some stale)
        pure .failed
      else
        let some _accepted ← register (firstResource + 1)
          | fail "composite invariant second registration was rejected"
        let some stale ← oldReceipt.get
          | fail "composite invariant lost its stale receipt"
        pure (.connected stale)
    selectedAlpn := fun _ =>
      fail "composite connector invariant queried plaintext ALPN"
    close := fun resource => do
      closes.modify (·.push resource)
      if resource == firstResource + 1 then
        throw (IO.userError
          "deterministic connector-invariant rollback failure")
  }
}

private def testConnectorInvariantCleanupPreservesBothCauses : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]

  -- Direct opening exposes both sanitized facts while cleanup uncertainty
  -- governs retry and rendering policy.
  let directConnectCount ← IO.mkRef 0
  let directOldReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let directCloses ← IO.mkRef (#[] : Array Nat)
  let directFailure ← match ← Subchannel.openWith
      (invariantCleanupDependencies destinations 1_320
        directConnectCount directOldReceipt directCloses)
      configuration with
    | .error failure => pure failure
    | .ok channel =>
        discard <| Subchannel.close channel
        fail "composite connector invariant unexpectedly opened a channel"
  expect (directFailure.primaryError == .initializationFailed &&
      directFailure.primaryDisposition == .supervisorInvariant)
    "composite cleanup erased its sanitized connector invariant"
  expect (directFailure.error == .cleanupFailed &&
      directFailure.disposition == .cleanupUncertain &&
      !directFailure.shouldRetry && directFailure.hasCleanupUncertainty)
    "composite cleanup did not govern effective opening policy"
  let directSnapshot ← directFailure.snapshot
  have _certified : directSnapshot.Invariant := directSnapshot.invariant
  expect (directSnapshot.custody == .available &&
      directSnapshot.physicalOwnerCount == 1 &&
      directSnapshot.failure == directFailure.failure)
    "composite direct failure lost its exact owned authority"
  match ← directFailure.close with
  | .error .transport => pure ()
  | result =>
      fail s!"composite direct owner changed cached uncertainty: {repr result}"
  expect ((← directConnectCount.get) == 2 &&
      (← directCloses.get) == #[1_320, 1_321])
    "composite direct failure changed exact rollback effects"

  -- The lazy shared owner transfers authority once and retains the primary
  -- invariant as orthogonal terminal evidence.
  let connectCount ← IO.mkRef 0
  let oldReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let closes ← IO.mkRef (#[] : Array Nat)
  let actionCount ← IO.mkRef 0
  let shared ← ManagedChannel.createWith
    (invariantCleanupDependencies destinations 1_330
      connectCount oldReceipt closes)
    configuration
  let opened : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match opened with
  | .error .cleanupUncertain => pure ()
  | result =>
      fail s!"composite connector invariant returned {repr result}"
  waitForSharedPhase shared .draining
  let inventory ← ManagedChannel.TestSupport.cleanupInventory shared
  expect (inventory == ({
      initializationOwners := 1
      invariantInitializations := 1
    } : CleanupInventory))
    s!"composite connector invariant lost overlapping evidence: {repr inventory}"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .initializationFailed
          .supervisorInvariant 1_331))
    "composite connector invariant retained the wrong exact owner or cause"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"composite joined close lost invariant precedence: {repr result}"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"repeated composite close changed precedence: {repr result}"
  expect ((← connectCount.get) == 2 &&
      (← actionCount.get) == 0 &&
      (← closes.get) == #[1_330, 1_331])
    "composite shared settlement retried cleanup or reached the action"

private def testCloseOwnsCancelledCompositeOpenFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let staleReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let secondAttemptEntered ← IO.Promise.new
  let allowInvariant ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "close-owned composite loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count =>
          (count, count + 1)
        if attempt == 0 then
          let some receipt ← register 1_340
            | fail "close-owned composite rejected first registration"
          staleReceipt.set (some receipt)
          pure .failed
        else
          let some _accepted ← register 1_341
            | fail "close-owned composite rejected second registration"
          secondAttemptEntered.resolve (some ())
          awaitSignal allowInvariant
          let some stale ← staleReceipt.get
            | fail "close-owned composite lost its stale receipt"
          pure (.connected stale)
      selectedAlpn := fun _ =>
        fail "close-owned composite queried plaintext ALPN"
      close := fun resource => do
        closes.modify (·.push resource)
        if resource == 1_341 then
          throw (IO.userError
            "deterministic close-owned composite rollback failure")
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal secondAttemptEntered
  cancellation.cancel
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "cancelled composite initializer did not release its caller"
  expectCleanupInventory shared 0 0 0 1
    "cancelled composite initializer lost its staged task"

  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  expect (!(← IO.hasFinished closer))
    "composite close returned before the staged initializer settled"
  allowInvariant.resolve (some ())
  match ← IO.wait closer with
  | .ok (.error .supervisorInvariant) => pure ()
  | _ =>
      fail "close-owned composite lost invariant close precedence"
  let inventory ← ManagedChannel.TestSupport.cleanupInventory shared
  expect (inventory == ({
      initializationOwners := 1
      invariantInitializations := 1
    } : CleanupInventory))
    s!"close-owned composite lost overlapping evidence: {repr inventory}"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .initializationFailed
          .supervisorInvariant 1_341))
    "close-owned composite retained the wrong primary or exact owner"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"repeated close-owned composite changed outcome: {repr result}"
  expect ((← connectCount.get) == 2 &&
      (← actionCount.get) == 0 &&
      (← closes.get) == #[1_340, 1_341])
    "close-owned composite retried rollback or reached the action"

private def testInvocationDeadlineStartsBeforeInitialization : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "invocation deadline loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 991
      selectedAlpn := fun _ =>
        fail "invocation deadline queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let some deadline := Grpc.RpcDeadline.ofSeconds? 1
    | fail "one-second invocation deadline fixture was rejected"
  let shared ← ManagedChannel.createWith dependencies configuration
  let startedAt ← IO.monoMsNow
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationDeadline shared deadline
      fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectEntered
  waitForTask caller 3_000
  let elapsed := (← IO.monoMsNow) - startedAt
  match ← IO.wait caller with
  | .ok (.error .localDeadlineExceeded) => pure ()
  | _ => fail "lazy initialization ignored the absolute invocation deadline"
  expect (elapsed < 2_500)
    "lazy initialization deadline began after connection setup"
  expect ((← connectCount.get) == 1 && (← actionCount.get) == 0)
    "expired lazy initialization reached the RPC action or reconnected"
  expectCleanupInventory shared 0 0 0 1
    "expired lazy initialization lost its staged exact task"
  expect ((← shared.phase) == .accepting)
    "owner deadline poisoned a still-owned initializer"

  allowConnect.resolve (some ())
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"deadline-staged initializer did not settle on close: {error}"
  expect ((← closes.get) == #[991])
    "deadline-staged initializer did not close its exact resource"
  expectCleanupInventory shared 0 0 0 0
    "deadline-staged initializer left cleanup debt after close"

private def testInvocationOwnerCancellationPrecedesDeadline : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "combined cancellation loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 992
      selectedAlpn := fun _ =>
        fail "combined cancellation queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let some deadline := Grpc.RpcDeadline.ofSeconds? 10
    | fail "ten-second invocation deadline fixture was rejected"
  let cancellation ← Grpc.Cancellation.create
  let shared ← ManagedChannel.createWith dependencies configuration
  let startedAt ← IO.monoMsNow
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationDeadlineAndCancellation
      shared deadline cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectEntered
  cancellation.cancel
  waitForTask caller
  let elapsed := (← IO.monoMsNow) - startedAt
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ => fail "combined invocation cancellation lost owner provenance"
  expect (elapsed < 2_000)
    "owner cancellation waited for the later invocation deadline"
  expect ((← actionCount.get) == 0)
    "owner-cancelled lazy initialization reached the RPC action"
  expectCleanupInventory shared 0 0 0 1
    "owner-cancelled invocation lost its staged initializer"

  allowConnect.resolve (some ())
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"owner-cancelled initializer did not settle on close: {error}"
  expect ((← closes.get) == #[992])
    "owner-cancelled initializer did not close its exact resource"

private def testGenerationSetupUsesFirstInvocationBudget : IO Unit := do
  let base ← apiConfiguration "http://localhost:50051"
  let some deadline := Grpc.RpcDeadline.ofSeconds? 1
    | fail "generation setup deadline fixture was rejected"
  let configuration := { base with deadline }
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let callbackCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation setup deadline loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 993
      selectedAlpn := fun _ =>
        fail "generation setup deadline queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      callbackCount.modify (· + 1)
      generation.invoke fun resource _ =>
        pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  waitForTask caller 3_000
  match ← IO.wait caller with
  | .ok (.error .localDeadlineExceeded) => pure ()
  | _ => fail "generation-scoped lazy setup escaped its first-call budget"
  expect ((← callbackCount.get) == 0)
    "expired generation setup entered its callback"
  expectCleanupInventory shared 0 0 0 1
    "expired generation setup lost its staged initializer"
  allowConnect.resolve (some ())
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"generation setup deadline close failed: {error}"
  expect ((← closes.get) == #[993])
    "generation setup deadline did not close its exact staged resource"

private def testGenerationScopeOutlivesConsumedFirstBudget : IO Unit := do
  let base ← apiConfiguration "http://localhost:50051"
  let some deadline := Grpc.RpcDeadline.ofSeconds? 1
    | fail "generation lifetime deadline fixture was rejected"
  let configuration := { base with deadline }
  let destinations ← addresses configuration #["127.0.0.1"]
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation lifetime test loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 994
      selectedAlpn := fun _ =>
        fail "generation lifetime test queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let result : Except CallError Nat ←
    ManagedChannel.TestSupport.withGeneration shared fun generation => do
      let first ← generation.invoke fun resource _ =>
        pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
      match first with
      | .ok 994 => pure ()
      | _ => return .error .supervisorInvariant
      -- The prepared setup budget belongs only to the first invocation.  The
      -- long-lived generation scope itself must remain unbounded.
      IO.sleep 1_100
      generation.invoke fun resource _ =>
        pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  match result with
  | .ok 994 => pure ()
  | _ => fail "consumed first-call budget capped the generation callback"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"long generation scope close failed: {error}"
  expect ((← closes.get) == #[994])
    "long generation scope changed exact connection ownership"

private def testGenerationFirstPolicyTransfersWithoutRestart : IO Unit := do
  let base ← apiConfiguration "http://localhost:50051"
  let some setupDeadline := Grpc.RpcDeadline.ofSeconds? 3
    | fail "generation transfer setup deadline fixture was rejected"
  let some firstDeadline := Grpc.RpcDeadline.ofSeconds? 1
    | fail "generation transfer first deadline fixture was rejected"
  let configuration := { base with deadline := setupDeadline }
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let actionStarts ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation transfer test loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 998
      selectedAlpn := fun _ =>
        fail "generation transfer test queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.withGeneration shared fun generation =>
      generation.invokeWithDeadline firstDeadline fun resource _ => do
        actionStarts.modify (· + 1)
        pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  IO.sleep 1_200
  allowConnect.resolve (some ())
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.error .localDeadlineExceeded) => pure ()
  | _ => fail "first generation policy restarted its clock after setup"
  expect ((← actionStarts.get) == 0)
    "expired transferred first policy reached transport action"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"generation policy transfer close failed: {error}"
  expect ((← closes.get) == #[998])
    "generation policy transfer changed exact connection ownership"

private def testExplicitGenerationPolicyGovernsSetup : IO Unit := do
  let base ← apiConfiguration "http://localhost:50051"
  let some defaultDeadline :=
      Grpc.RpcDeadline.ofSeconds? 1
    | fail "explicit generation default deadline fixture was rejected"
  let some firstDeadline :=
      Grpc.RpcDeadline.ofSeconds? 10
    | fail "explicit generation first deadline fixture was rejected"
  let configuration := { base with deadline := defaultDeadline }
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let callbackCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "explicit generation policy loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 999
      selectedAlpn := fun _ =>
        fail "explicit generation policy queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared firstDeadline none fun generation => do
        callbackCount.modify (· + 1)
        generation.invokeWithDeadline firstDeadline fun resource _ => do
          actionCount.modify (· + 1)
          pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  IO.sleep 1_200
  expect (!(← IO.hasFinished caller))
    "channel default deadline overrode the declared first setup policy"
  allowConnect.resolve (some ())
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.ok 999) => pure ()
  | _ => fail "explicit first policy did not own setup and its first call"
  expect ((← callbackCount.get) == 1 && (← actionCount.get) == 1)
    "explicit first policy did not admit exactly one callback and action"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"explicit generation policy close failed: {error}"
  expect ((← closes.get) == #[999])
    "explicit generation policy changed exact resource ownership"

private def testExplicitGenerationPolicyCancelsSetup : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let some firstDeadline :=
      Grpc.RpcDeadline.ofSeconds? 70
    | fail "explicit cancellation deadline fixture was rejected"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let callbackCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "explicit generation cancellation loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 1000
      selectedAlpn := fun _ =>
        fail "explicit generation cancellation queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let startedAt ← IO.monoMsNow
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared firstDeadline (some cancellation) fun generation => do
        callbackCount.modify (· + 1)
        generation.invokeWithPolicy firstDeadline (some cancellation)
          fun resource _ =>
            pure (Except.ok resource :
              Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  cancellation.cancel
  waitForTask caller
  let elapsed := (← IO.monoMsNow) - startedAt
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ => fail "declared generation cancellation lost owner provenance"
  expect (elapsed < 2_000)
    "declared generation cancellation waited for the long-poll deadline"
  expect ((← callbackCount.get) == 0)
    "cancelled generation setup entered its callback"
  expectCleanupInventory shared 0 0 0 1
    "cancelled explicit generation setup lost its staged initializer"
  allowConnect.resolve (some ())
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"explicit generation cancellation close failed: {error}"
  expect ((← closes.get) == #[1000])
    "explicit generation cancellation lost its staged resource"

private def testExplicitGenerationPolicyMismatchIsSticky : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let some declaredDeadline :=
      Grpc.RpcDeadline.ofSeconds? 3
    | fail "declared generation deadline fixture was rejected"
  let some otherDeadline :=
      Grpc.RpcDeadline.ofSeconds? 1
    | fail "mismatched generation deadline fixture was rejected"
  let destinations ← addresses configuration #["127.0.0.1"]
  let nextResource ← IO.mkRef 1001
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "generation mismatch loaded trust anchors"
    connector := {
      connect := fun _ register => do
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ =>
        fail "generation mismatch queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let deadlineMismatch : Except CallError Unit ←
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared declaredDeadline none fun generation => do
        let mismatched ← generation.invokeWithDeadline otherDeadline
          fun _ _ => do
            actionCount.modify (· + 1)
            pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
        match mismatched with
        | .error .supervisorInvariant => pure ()
        | _ => return .error .actionFailed
        let later ← generation.invokeWithDeadline declaredDeadline
          fun _ _ => do
            actionCount.modify (· + 1)
            pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
        match later with
        | .error .supervisorInvariant => pure (.ok ())
        | _ => pure (.error .actionFailed)
  match deadlineMismatch with
  | .error .supervisorInvariant => pure ()
  | _ => fail "deadline policy mismatch was not a sticky invariant"
  let cancellation ← Grpc.Cancellation.create
  let cancellationMismatch : Except CallError Unit ←
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared declaredDeadline none fun generation =>
        generation.invokeWithPolicy declaredDeadline (some cancellation)
          fun _ _ => do
            actionCount.modify (· + 1)
            pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match cancellationMismatch with
  | .error .supervisorInvariant => pure ()
  | _ => fail "cancellation capability mismatch was not an invariant"
  expect ((← actionCount.get) == 0)
    "mismatched explicit policy reached the transport action"
  expect ((← closes.get) == #[1001, 1002])
    "mismatched explicit policies did not retire their exact generations"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"generation mismatch final close failed: {error}"

private def testFirstBudgetSelectionAndAdmissionAreAtomic : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let some declaredDeadline :=
      Grpc.RpcDeadline.ofSeconds? 3
    | fail "atomic admission deadline fixture was rejected"
  let some mismatchedDeadline :=
      Grpc.RpcDeadline.ofSeconds? 1
    | fail "atomic admission mismatch fixture was rejected"
  let destinations ← addresses configuration #["127.0.0.1"]
  let firstSelected ← IO.Promise.new
  let allowFirstAdmission ← IO.Promise.new
  let admissionAttempts ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "atomic generation admission loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1003
      selectedAlpn := fun _ =>
        fail "atomic generation admission queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeGenerationScopeAdmission := do
      let attempt ← admissionAttempts.modifyGet fun current =>
        (current, current + 1)
      if attempt == 0 then
        firstSelected.resolve (some ())
        awaitSignal allowFirstAdmission
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let result : Except CallError Unit ←
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared declaredDeadline none fun generation => do
        let mismatched : Task
            (Except IO.Error (Except CallError Unit)) ← IO.asTask <|
          generation.invokeWithDeadline mismatchedDeadline fun _ _ => do
            actionCount.modify (· + 1)
            pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
        awaitSignal firstSelected
        let matching : Task
            (Except IO.Error (Except CallError Unit)) ← IO.asTask <|
          generation.invokeWithDeadline declaredDeadline fun _ _ => do
            actionCount.modify (· + 1)
            pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
        IO.sleep 50
        expect (!(← IO.hasFinished matching))
          "matching call bypassed serialized first-budget admission"
        expect ((← actionCount.get) == 0)
          "transport started before the first policy decision"
        allowFirstAdmission.resolve (some ())
        waitForTask mismatched
        waitForTask matching
        match ← IO.wait mismatched, ← IO.wait matching with
        | .ok (.error .supervisorInvariant),
            .ok (.error .supervisorInvariant) => pure (.ok ())
        | _, _ => pure (.error .actionFailed)
  match result with
  | .error .supervisorInvariant => pure ()
  | _ => fail "concurrent policy mismatch did not poison its generation"
  expect ((← actionCount.get) == 0)
    "concurrent policy mismatch reached a transport action"
  expect ((← admissionAttempts.get) == 2)
    "concurrent policy decisions bypassed the admission gate"
  expect ((← closes.get) == #[1003])
    "concurrent policy mismatch did not retire its exact generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"atomic admission final close failed: {error}"

private def testGenerationAdmissionQueueConsumesDeadline : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let some firstDeadline :=
      Grpc.RpcDeadline.ofSeconds? 3
    | fail "queued admission first deadline fixture was rejected"
  let some queuedDeadline :=
      Grpc.RpcDeadline.ofSeconds? 1
    | fail "queued admission deadline fixture was rejected"
  let destinations ← addresses configuration #["127.0.0.1"]
  let firstSelected ← IO.Promise.new
  let allowFirstAdmission ← IO.Promise.new
  let admissionAttempts ← IO.mkRef 0
  let firstActions ← IO.mkRef 0
  let queuedActions ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "queued generation admission loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1004
      selectedAlpn := fun _ =>
        fail "queued generation admission queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeGenerationScopeAdmission := do
      let attempt ← admissionAttempts.modifyGet fun current =>
        (current, current + 1)
      if attempt == 0 then
        firstSelected.resolve (some ())
        awaitSignal allowFirstAdmission
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let result : Except CallError Unit ←
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared firstDeadline none fun generation => do
        let first : Task (Except IO.Error (Except CallError Unit)) ←
          IO.asTask <| generation.invokeWithDeadline firstDeadline fun _ _ => do
            firstActions.modify (· + 1)
            pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
        awaitSignal firstSelected
        let requestedAt ← IO.monoMsNow
        let queued : Task (Except IO.Error (Except CallError Unit)) ←
          IO.asTask <|
            generation.invokeWithDeadlineAt requestedAt queuedDeadline
              fun _ _ => do
                queuedActions.modify (· + 1)
                pure (Except.ok () :
                  Except Grpc.UnaryCall.Error Unit)
        IO.sleep 1_100
        expect (!(← IO.hasFinished queued))
          "queued call bypassed the serialized admission decision"
        allowFirstAdmission.resolve (some ())
        waitForTask first
        waitForTask queued
        match ← IO.wait first, ← IO.wait queued with
        | .ok (.ok ()), .ok (.error .localDeadlineExceeded) => pure (.ok ())
        | _, _ => pure (.error .actionFailed)
  match result with
  | .ok () => pure ()
  | _ => fail "generation admission queue did not charge elapsed deadline"
  expect ((← firstActions.get) == 1 && (← queuedActions.get) == 0)
    "expired queued invocation reached its transport action"
  expect ((← admissionAttempts.get) == 2)
    "queued deadline test bypassed the admission gate"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"queued admission final close failed: {error}"
  expect ((← closes.get) == #[1004])
    "queued admission deadline changed exact resource ownership"

private def testRejectedGenerationScopeSettlesBudget : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let shared ← ManagedChannel.createWith
    { resolve := fun _ => fail "closed generation scope resolved"
      loadTrust := fail "closed generation scope loaded trust anchors"
      connector := forbiddenConnector "closed generation scope" }
    configuration
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"generation rejection setup close failed: {error}"
  let some deadline :=
      Grpc.RpcDeadline.ofSeconds? 99_999_999
    | fail "long generation rejection deadline fixture was rejected"
  let callbackCount ← IO.mkRef 0
  let rejected : Except CallError Unit ←
    ManagedChannel.TestSupport.withGenerationWithFirstPolicy
      shared deadline none fun
        (_ : ManagedChannel.TestSupport.GenerationInvoker Nat Unit) => do
        callbackCount.modify (· + 1)
        pure (.ok ())
  match rejected with
  | .error .channelClosed => pure ()
  | _ => fail "closed channel admitted an explicit generation scope"
  expect ((← callbackCount.get) == 0)
    "rejected generation scope entered its callback"

private def testInvocationGateRejectsPostDeadlineStart : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let actionEntered ← IO.Promise.new
  let allowClaim ← IO.Promise.new
  let starts ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "invocation gate test loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 995
      selectedAlpn := fun _ =>
        fail "invocation gate test queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let some deadline := Grpc.RpcDeadline.ofSeconds? 1
    | fail "invocation gate deadline fixture was rejected"
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationPermit shared deadline
      fun _ _ claimStart => do
        actionEntered.resolve (some ())
        awaitSignal allowClaim
        match ← claimStart with
        | none => pure (.error .ownerCancelled)
        | some _ =>
            starts.modify (· + 1)
            pure (.ok ())
  awaitSignal actionEntered
  IO.sleep 1_100
  allowClaim.resolve (some ())
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.error .localDeadlineExceeded) => pure ()
  | _ => fail "post-deadline start gate lost deadline provenance"
  expect ((← starts.get) == 0)
    "transport start was admitted after the absolute deadline"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"invocation gate close failed: {error}"
  expect ((← closes.get) == #[995])
    "invocation gate test changed exact connection ownership"

private def testSetupIsDeductedFromCallBudget : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let observedRemaining ← IO.mkRef (none : Option Nat)
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "remaining budget test loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 996
      selectedAlpn := fun _ =>
        fail "remaining budget test queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let some deadline := Grpc.RpcDeadline.ofSeconds? 3
    | fail "remaining budget deadline fixture was rejected"
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationPermit shared deadline
      fun _ _ claimStart => do
        let remaining ← claimStart
        observedRemaining.set remaining
        match remaining with
        | some _ => pure (.ok ())
        | none => pure (.error .ownerCancelled)
  awaitSignal connectEntered
  IO.sleep 1_200
  allowConnect.resolve (some ())
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.ok ()) => pure ()
  | _ => fail "remaining invocation budget did not admit the call"
  let some remaining ← observedRemaining.get
    | fail "remaining invocation budget was not observed"
  expect (0 < remaining && remaining < 2_500)
    "lazy setup restarted the full peer-call deadline"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"remaining budget close failed: {error}"
  expect ((← closes.get) == #[996])
    "remaining budget test changed exact connection ownership"

private def testDeadlineOverridesLateActionEvidence : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let nextResource ← IO.mkRef 997
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "late action deadline test loaded trust anchors"
    connector := {
      connect := fun _ register => do
        let resource ← nextResource.get
        nextResource.set (resource + 1)
        registered register resource
      selectedAlpn := fun _ =>
        fail "late action deadline test queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let some deadline := Grpc.RpcDeadline.ofSeconds? 1
    | fail "late action deadline fixture was rejected"
  let shared ← ManagedChannel.createWith dependencies configuration
  let peerStatusDetails :=
    some (ByteArray.mk #[0x08, 0x03, 0x12, 0x02, 0xaa, 0xbb])
  let success ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationDeadline shared deadline
      fun _ _ => do
        IO.sleep 1_100
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  let encoding ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationDeadline shared deadline
      fun _ _ => do
        IO.sleep 1_100
        pure (Except.error .requestEncoding :
          Except Grpc.UnaryCall.Error Unit)
  let peer ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInvocationDeadline shared deadline
      fun _ _ => do
        IO.sleep 1_100
        pure (Except.error (.rpc
          (Grpc.Status.invalidArgument "late peer evidence")
          peerStatusDetails) :
          Except Grpc.UnaryCall.Error Unit)
  for task in #[success, encoding] do
    waitForTask task 3_000
    match ← IO.wait task with
    | .ok (.error .localDeadlineExceeded) => pure ()
    | _ => fail "late nonterminal result escaped absolute deadline provenance"
  waitForTask peer 3_000
  match ← IO.wait peer with
  | .ok (.error (.rpc status observedDetails)) =>
      expect (status == Grpc.Status.invalidArgument "late peer evidence")
        "late exact peer status changed after local expiration"
      expect (observedDetails == peerStatusDetails)
        "late exact peer status details changed after local expiration"
  | _ => fail "late exact peer evidence was rewritten as a local deadline"

  let unavailableStatus :=
    Grpc.Status.error .unavailable "late transport owner evidence"
  let unavailableDetails :=
    some (ByteArray.mk #[0x08, 0x0e, 0x12, 0x02, 0xcc, 0xdd])
  let unavailable : Except CallError Unit ←
    ManagedChannel.TestSupport.unaryWithInvocationDeadline shared deadline
      fun _ _ => do
        IO.sleep 1_100
        pure (Except.error (.rpc unavailableStatus unavailableDetails) :
          Except Grpc.UnaryCall.Error Unit)
  match unavailable with
  | .error (.rpc status observedDetails) =>
      expect (status == unavailableStatus)
        "late transport status lost exact provenance"
      expect (observedDetails == unavailableDetails)
        "late transport status details lost exact provenance"
  | _ => fail "late transport status was rewritten as a local deadline"
  expect ((← closes.get) == #[997])
    "late ambiguous transport evidence did not retire its generation"

  let failed : Except CallError Unit ←
    ManagedChannel.TestSupport.unaryWithInvocationDeadline shared deadline
      fun _ _ => do
        IO.sleep 1_100
        pure (Except.error .actionFailed :
          Except Grpc.UnaryCall.Error Unit)
  match failed with
  | .error .callActionFailed => pure ()
  | _ => fail "late call-owner failure was rewritten as a local deadline"
  expect ((← closes.get) == #[997, 998])
    "late call-owner failure did not retire its generation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"late action deadline close failed: {error}"
  expect ((← closes.get) == #[997, 998])
    "late owner-evidence test changed exact connection ownership"

private def testBoundedCloseRetainsBlockedInitialization : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeTaskAttempts ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "bounded initializer close loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 1_301
      selectedAlpn := fun _ =>
        fail "bounded initializer close queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeClaimedCloseTask := closeTaskAttempts.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <| ManagedChannel.unaryWith shared fun resource _ =>
    pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered

  match ← ManagedChannel.closeWithin shared 0 with
  | .stillClosing => pure ()
  | observation =>
      fail s!"blocked initializer close returned {repr observation}"
  expect ((← shared.phase) == .draining)
    "bounded initializer close did not publish draining"
  expect (← ManagedChannel.TestSupport.hasRetainedCloseTask shared)
    "bounded initializer close lost its detached driver"
  expect (!(← ManagedChannel.TestSupport.closeNeedsOwner shared) &&
      !(← ManagedChannel.TestSupport.closeOwnerStarting shared))
    "bounded initializer close retained unpublished driver custody"
  expectCleanupInventory shared 0 0 0 1
    "bounded initializer timeout discarded the staged task"
  expect ((← connectCount.get) == 1 && (← closeTaskAttempts.get) == 1 &&
      (← closes.get).isEmpty)
    "bounded initializer timeout changed exact ownership"

  allowConnect.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .channelDraining) => pure ()
  | _ =>
      fail "bounded initializer caller did not settle"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result =>
      fail s!"bounded initializer joined close returned {repr result}"
  expect ((← closes.get) == #[1_301] && (← closeTaskAttempts.get) == 1)
    "bounded initializer close duplicated its generation or driver"
  expectCleanupInventory shared 0 0 0 0
    "bounded initializer joined close retained cleanup custody"

private def testBoundedCloseRetainsBlockedEstablishedGeneration : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeTaskAttempts ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeEntered ← IO.Promise.new
  let allowClose ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "bounded established close loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1_302
      selectedAlpn := fun _ =>
        fail "bounded established close queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_302)
          "bounded established close received the wrong generation"
        closeCount.modify (· + 1)
        closeEntered.resolve (some ())
        awaitSignal allowClose
    }
    beforeClaimedCloseTask := closeTaskAttempts.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Nat ← ManagedChannel.unaryWith shared
    fun resource _ =>
      pure (Except.ok resource : Except Grpc.UnaryCall.Error Nat)
  match initialized with
  | .ok 1_302 => pure ()
  | result => fail s!"bounded established close did not initialize: {repr result}"

  match ← ManagedChannel.closeWithin shared 0 with
  | .stillClosing => pure ()
  | observation =>
      fail s!"bounded established close returned {repr observation}"
  awaitSignal closeEntered
  for _ in [0:8] do
    match ← ManagedChannel.closeWithin shared 1 with
    | .stillClosing => pure ()
    | observation =>
        fail s!"repeated bounded close returned {repr observation}"
  expect ((← ManagedChannel.TestSupport.closeSettlementWaiters shared) == 0)
    "repeated bounded timeouts accumulated completion selectors"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 1)
    "repeated bounded close duplicated driver or transport cleanup"
  expect (← ManagedChannel.TestSupport.hasRetainedCloseTask shared)
    "bounded established timeout discarded the close task"
  expectCleanupInventory shared 1 0 0 0
    "bounded established timeout discarded exact generation custody"

  -- Nat deadlines larger than UInt64 must remain pending instead of wrapping
  -- the native timer to zero.
  let hugeDeadline := (← IO.monoMsNow) + (2 : Nat) ^ 64
  let hugeObserver ← IO.asTask <|
    ManagedChannel.awaitCloseUntil shared hugeDeadline
  waitForCloseSettlementWaiters shared 1
  IO.sleep 10
  expect (!(← IO.hasFinished hugeObserver))
    "enormous absolute deadline wrapped to an immediate timeout"
  allowClose.resolve (some ())
  match ← IO.wait hugeObserver with
  | .ok (.settled (.ok ())) => pure ()
  | _ => fail "enormous-deadline observer lost close completion"
  waitForCloseSettlementWaiters shared 0
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"bounded established joined close returned {repr result}"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 1)
    "joined established close repeated an already-owned effect"
  expectCleanupInventory shared 0 0 0 0
    "bounded established close did not discharge exact custody"

private def testCloseSettlementRepeatedWakeup : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  for index in [0:8] do
    let resource := 1_400 + index
    let closeTaskAttempts ← IO.mkRef 0
    let closeCount ← IO.mkRef 0
    let closeEntered ← IO.Promise.new
    let allowClose ← IO.Promise.new
    let dependencies : ManagedChannel.Dependencies Nat := {
      resolve := fun _ => pure (.ok destinations)
      loadTrust := fail "settlement wakeup loaded plaintext trust anchors"
      connector := {
        connect := fun _ register => registered register resource
        selectedAlpn := fun _ =>
          fail "settlement wakeup queried plaintext ALPN"
        close := fun actual => do
          expect (actual == resource)
            "settlement wakeup received the wrong generation"
          closeCount.modify (· + 1)
          closeEntered.resolve (some ())
          awaitSignal allowClose
      }
      beforeClaimedCloseTask := closeTaskAttempts.modify (· + 1)
    }
    let shared ← ManagedChannel.createWith dependencies configuration
    let initialized : Except CallError Nat ← ManagedChannel.unaryWith shared
      fun actual _ =>
        pure (Except.ok actual : Except Grpc.UnaryCall.Error Nat)
    match initialized with
    | .ok actual =>
        expect (actual == resource)
          "settlement wakeup initialized the wrong generation"
    | result => fail s!"settlement wakeup initialization returned {repr result}"

    let observer ← IO.asTask (ManagedChannel.closeWithin shared 5_000)
    awaitSignal closeEntered
    waitForCloseSettlementWaiters shared 1
    expect ((← closeTaskAttempts.get) == 1 &&
        (← closeCount.get) == 1)
      "settlement wakeup changed exact in-flight close counts"
    allowClose.resolve (some ())
    match ← IO.wait observer with
    | .ok (.settled (.ok ())) => pure ()
    | _ => fail "settlement wakeup observer returned the wrong result"
    waitForCloseSettlementWaiters shared 0
    match ← ManagedChannel.close shared with
    | .ok () => pure ()
    | result => fail s!"settlement wakeup joined close returned {repr result}"
    expect ((← closeTaskAttempts.get) == 1 &&
        (← closeCount.get) == 1)
      "settlement wakeup duplicated task or transport ownership"
    expect ((← shared.phase) == .closed)
      "settlement wakeup did not retain terminal phase"
    expectCleanupInventory shared 0 0 0 0
      "settlement wakeup retained cleanup custody"

private def testBoundedClosePreservesLaterFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeCount ← IO.mkRef 0
  let closeEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "bounded close failure loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1_303
      selectedAlpn := fun _ =>
        fail "bounded close failure queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_303)
          "bounded close failure received the wrong generation"
        closeCount.modify (· + 1)
        closeEntered.resolve (some ())
        awaitSignal allowFailure
        throw (IO.userError "deterministic bounded transport close failure")
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Unit ← ManagedChannel.unaryWith shared
    fun _ _ => pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match initialized with
  | .ok () => pure ()
  | result => fail s!"bounded close failure did not initialize: {repr result}"

  match ← ManagedChannel.closeWithin shared 0 with
  | .stillClosing => pure ()
  | observation => fail s!"bounded failing close returned {repr observation}"
  awaitSignal closeEntered
  expectCleanupInventory shared 1 0 0 0
    "bounded failing close timeout discarded exact generation custody"
  allowFailure.resolve (some ())
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result => fail s!"joined bounded failure returned {repr result}"
  expect ((← closeCount.get) == 1)
    "bounded close failure retried ambiguous transport cleanup"
  expectCleanupInventory shared 1 0 0 0
    "bounded close failure erased retained transport custody"

  -- An already-terminal completion outranks an already-expired observation
  -- boundary and returns the exact cached failure.
  match ← ManagedChannel.awaitCloseUntil shared 0 with
  | .settled (.error .transport) => pure ()
  | observation =>
      fail s!"terminal close lost the deadline boundary: {repr observation}"
  expect ((← closeCount.get) == 1)
    "terminal boundary observation repeated transport cleanup"

private def testBoundedCloseDriverFailureRetainsCustody : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeTaskAttempts ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let allocationEntered ← IO.Promise.new
  let allowAllocation ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "bounded driver failure loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1_304
      selectedAlpn := fun _ =>
        fail "bounded driver failure queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_304)
          "bounded driver failure received the wrong generation"
        closeCount.modify (· + 1)
    }
    beforeClaimedCloseTask := do
      let attempt ← closeTaskAttempts.modifyGet fun count =>
        (count, count + 1)
      if attempt == 0 then
        allocationEntered.resolve (some ())
        awaitSignal allowAllocation
      throw (IO.userError "deterministic bounded driver allocation failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Unit ← ManagedChannel.unaryWith shared
    fun _ _ => pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match initialized with
  | .ok () => pure ()
  | result => fail s!"bounded driver failure did not initialize: {repr result}"

  let requester ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal allocationEntered
  try
    expectSupervisorSnapshot shared .draining 0 1 (some 0) [] [] .idle
      0 false {} .startingBounded
      "bounded close did not publish starting custody before allocation"
  finally
    allowAllocation.resolve (some ())
  match ← IO.wait requester with
  | .ok .needsDriver => pure ()
  | .ok observation =>
      fail s!"bounded driver allocation failure returned {repr observation}"
  | .error error =>
      fail s!"bounded driver allocation task raised: {error}"
  expectSupervisorSnapshot shared .draining 0 1 (some 0) [] [] .idle
    0 false {} .needsOwner
    "bounded allocation rollback changed generation or inventory state"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 0)
    "bounded driver allocation failure crossed a cleanup boundary"

  -- The joining API retakes the restored structural state and preserves its
  -- synchronous fallback when allocation fails again with no active leases.
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"joining close did not recover bounded custody: {repr result}"
  expect ((← closeTaskAttempts.get) == 2 && (← closeCount.get) == 1)
    "joining fallback changed exact driver or close counts"
  expect (!(← ManagedChannel.TestSupport.closeNeedsOwner shared) &&
      !(← ManagedChannel.TestSupport.closeOwnerStarting shared))
    "joining fallback left unpublished close custody"

private def testJoiningCloseRetakesRacingBoundedFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeTaskAttempts ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let firstAllocationEntered ← IO.Promise.new
  let allowFirstFailure ← IO.Promise.new
  let secondAllocationEntered ← IO.Promise.new
  let allowSecondAllocation ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "racing bounded driver failure loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1_305
      selectedAlpn := fun _ =>
        fail "racing bounded driver failure queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_305)
          "racing bounded driver failure received the wrong generation"
        closeCount.modify (· + 1)
    }
    beforeClaimedCloseTask := do
      let attempt ← closeTaskAttempts.modifyGet fun count => (count, count + 1)
      if attempt == 0 then
        firstAllocationEntered.resolve (some ())
        awaitSignal allowFirstFailure
        throw (IO.userError "deterministic first close-driver failure")
      else if attempt == 1 then
        secondAllocationEntered.resolve (some ())
        awaitSignal allowSecondAllocation
      else
        fail "racing bounded close allocated a third driver"
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Unit ← ManagedChannel.unaryWith shared
    fun _ _ => pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match initialized with
  | .ok () => pure ()
  | result => fail s!"racing bounded driver did not initialize: {repr result}"

  let bounded ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal firstAllocationEntered
  expectSupervisorSnapshot shared .draining 0 1 (some 0) [] [] .idle
    0 false {} .startingBounded
    "racing bounded allocation changed generation or inventory state"
  let joining ← IO.asTask (ManagedChannel.close shared)
  allowFirstFailure.resolve (some ())
  match ← IO.wait bounded with
  | .ok .needsDriver => pure ()
  | _ => fail "racing bounded failure returned the wrong observation"

  -- The joining path retakes the restored needs-owner state instead of
  -- waiting forever on a completion owner that allocation never published.
  awaitSignal secondAllocationEntered
  expectSupervisorSnapshot shared .draining 0 1 (some 0) [] [] .idle
    0 false {} .startingJoining
    "joining retake changed more than restored driver custody"
  allowSecondAllocation.resolve (some ())
  match ← IO.wait joining with
  | .ok (.ok ()) => pure ()
  | _ => fail "joining close did not settle racing failure"
  expect ((← closeTaskAttempts.get) == 2 && (← closeCount.get) == 1)
    "racing bounded/joining callers duplicated driver or transport cleanup"
  match ← ManagedChannel.requestClose shared with
  | .settled (.ok ()) => pure ()
  | observation => fail s!"repeated terminal request returned {repr observation}"
  expect ((← closeTaskAttempts.get) == 2 && (← closeCount.get) == 1)
    "repeated terminal request started another close generation"

private def testBoundedWaitObservesRacingDriverFailure : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let closeTaskAttempts ← IO.mkRef 0
  let allocationEntered ← IO.Promise.new
  let allowAllocationFailure ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "bounded waiter race resolved an endpoint"
    loadTrust := fail "bounded waiter race loaded trust anchors"
    connector := forbiddenConnector "bounded waiter race"
    beforeClaimedCloseTask := do
      let attempt ← closeTaskAttempts.modifyGet fun count => (count, count + 1)
      if attempt == 0 then
        allocationEntered.resolve (some ())
        awaitSignal allowAllocationFailure
      throw (IO.userError "deterministic bounded waiter driver failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let allocating ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal allocationEntered
  let deadline := (← IO.monoMsNow) + 500
  let waiting ← IO.asTask (ManagedChannel.awaitCloseUntil shared deadline)
  waitForCloseSettlementWaiters shared 1

  allowAllocationFailure.resolve (some ())
  match ← IO.wait allocating with
  | .ok .needsDriver => pure ()
  | _ => fail "first bounded allocator did not restore custody"
  expect (← ManagedChannel.TestSupport.closeNeedsOwner shared)
    "racing allocator failure did not publish needs-owner custody"
  match ← IO.wait waiting with
  | .ok .needsDriver => pure ()
  | _ => fail "bounded waiter mislabeled restored custody as still closing"
  waitForCloseSettlementWaiters shared 0
  expect ((← closeTaskAttempts.get) == 1)
    "bounded waiter duplicated the racing allocation attempt"
  expect (!(← ManagedChannel.TestSupport.hasRetainedCloseTask shared) &&
      !(← ManagedChannel.TestSupport.closeOwnerStarting shared))
    "bounded waiter reported a nonexistent close driver"

  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"joining close did not settle waiter race: {repr result}"
  expect ((← closeTaskAttempts.get) == 2)
    "joining close did not retake bounded waiter custody exactly once"

private def testCloseObservationResamplesRetakenCustody : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let closeTaskAttempts ← IO.mkRef 0
  let firstAllocationEntered ← IO.Promise.new
  let allowFirstFailure ← IO.Promise.new
  let observationEntered ← IO.Promise.new
  let allowObservation ← IO.Promise.new
  let secondAllocationEntered ← IO.Promise.new
  let allowSecondAllocation ← IO.Promise.new
  let observationCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "custody resample resolved an endpoint"
    loadTrust := fail "custody resample loaded trust anchors"
    connector := forbiddenConnector "custody resample"
    beforeClaimedCloseTask := do
      let attempt ← closeTaskAttempts.modifyGet fun count =>
        (count, count + 1)
      if attempt == 0 then
        firstAllocationEntered.resolve (some ())
        awaitSignal allowFirstFailure
        throw (IO.userError "deterministic first close allocation failure")
      else if attempt == 1 then
        secondAllocationEntered.resolve (some ())
        awaitSignal allowSecondAllocation
      else
        fail "custody resample allocated a third close driver"
    beforeCloseObservationFinalCheck := do
      let attempt ← observationCount.modifyGet fun count =>
        (count, count + 1)
      if attempt == 0 then
        observationEntered.resolve (some ())
        awaitSignal allowObservation
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let firstAllocator ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal firstAllocationEntered

  -- This caller has already observed the first allocator's structural
  -- `starting` custody and is paused at the final observation boundary.
  let observer ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal observationEntered

  -- Allocation failure restores exact needs-owner custody. A third caller
  -- takes it and pauses while publishing the replacement driver.
  allowFirstFailure.resolve (some ())
  match ← IO.wait firstAllocator with
  | .ok .needsDriver => pure ()
  | _ => fail "first custody allocator returned the wrong result"
  expect (← ManagedChannel.TestSupport.closeNeedsOwner shared)
    "first allocation failure did not restore needs-owner custody"
  let secondAllocator ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal secondAllocationEntered
  expect (!(← ManagedChannel.TestSupport.closeNeedsOwner shared) &&
      (← ManagedChannel.TestSupport.closeOwnerStarting shared))
    "replacement caller did not take restored close custody"

  -- The paused observer must classify the final state, not report stale
  -- needs-driver evidence after another caller has taken that obligation.
  allowObservation.resolve (some ())
  match ← IO.wait observer with
  | .ok .stillClosing => pure ()
  | _ => fail "custody observer returned stale needs-driver evidence"

  allowSecondAllocation.resolve (some ())
  match ← IO.wait secondAllocator with
  | .ok (.settled (.ok ())) | .ok .stillClosing => pure ()
  | _ => fail "replacement close driver returned the wrong result"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"custody resample close returned {repr result}"
  expect ((← closeTaskAttempts.get) == 2)
    "custody resample duplicated the replacement driver"
  expect ((← shared.phase) == .closed)
    "custody resample did not retain terminal phase"
  expectCleanupInventory shared 0 0 0 0
    "custody resample retained cleanup custody"

private def testCloseCompletionWinsObservationBoundary : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let publicationEntered ← IO.Promise.new
  let allowPublication ← IO.Promise.new
  let observationEntered ← IO.Promise.new
  let allowObservation ← IO.Promise.new
  let publicationAttempts ← IO.mkRef 0
  let observationAttempts ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "close boundary race resolved an endpoint"
    loadTrust := fail "close boundary race loaded trust anchors"
    connector := forbiddenConnector "close boundary race"
    beforeCloseCompletionPublication := do
      publicationAttempts.modify (· + 1)
      publicationEntered.resolve (some ())
      awaitSignal allowPublication
    beforeCloseObservationFinalCheck := do
      observationAttempts.modify (· + 1)
      observationEntered.resolve (some ())
      awaitSignal allowObservation
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let observer ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal publicationEntered
  awaitSignal observationEntered
  let joiner ← IO.asTask (ManagedChannel.close shared)

  -- Publication occurs after the observer's first completion check and its
  -- custody sample, but before the final authoritative completion check.
  allowPublication.resolve (some ())
  match ← IO.wait joiner with
  | .ok (.ok ()) => pure ()
  | _ => fail "close boundary joiner did not observe terminal completion"
  allowObservation.resolve (some ())
  match ← IO.wait observer with
  | .ok (.settled (.ok ())) => pure ()
  | _ => fail "close completion lost the observation boundary"
  expect ((← publicationAttempts.get) == 1 &&
      (← observationAttempts.get) == 1)
    "close boundary race repeated publication or observation"
  expect ((← shared.phase) == .closed)
    "close boundary race did not retain terminal phase"

private def testSharedExplicitCloseTaskFailureFallsBackInline : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let closeTaskAttempts ← IO.mkRef 0
  let completionPublicationEntered ← IO.Promise.new
  let allowCompletionPublication ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "explicit close fallback loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        registered register 501
      selectedAlpn := fun _ =>
        fail "explicit close fallback queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 501)
          "explicit close fallback closed the wrong resource"
        closeCount.modify (· + 1)
    }
    beforeClaimedCloseTask := do
      closeTaskAttempts.modify (· + 1)
      throw (IO.userError "deterministic claimed-close task allocation failure")
    beforeCloseCompletionPublication := do
      completionPublicationEntered.resolve (some ())
      awaitSignal allowCompletionPublication
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match initialized with
  | .ok 501 => pure ()
  | _ => fail "explicit close fallback did not initialize its generation"

  let closer ← IO.asTask (ManagedChannel.close shared)
  awaitSignal completionPublicationEntered
  try
    expectSupervisorSnapshot shared .closed 0 1 none [] [] .idle
      0 false {} .inline
      "inline close did not expose its pre-completion publication window"
    expect (!(← ManagedChannel.TestSupport.closeCompletionResolved shared))
      "inline close resolved completion before its publication seam"
  finally
    allowCompletionPublication.resolve (some ())
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | .ok (.error error) =>
      fail s!"inline claimed-close fallback failed: {error}"
  | .error error => fail s!"inline claimed-close fallback raised: {error}"
  expectSupervisorSnapshot shared .closed 0 1 none [] [] .idle
    0 false {} .inlineTerminal
    "inline completion did not publish its terminal driver state"
  expect ((← connectCount.get) == 1 && (← closeCount.get) == 1)
    "inline claimed-close fallback changed exact transport ownership"
  expect ((← closeTaskAttempts.get) == 1)
    "explicit close did not exercise the inline close fallback"

  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"repeated close did not join inline fallback: {error}"
  expect ((← closeTaskAttempts.get) == 1 && (← closeCount.get) == 1)
    "repeated close started a second claimed-close owner"

private def testCloseTaskHandlePrecedesCleanup : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeCount ← IO.mkRef 0
  let publicationEntered ← IO.Promise.new
  let allowPublication ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "close-task gating test loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 1_306
      selectedAlpn := fun _ =>
        fail "close-task gating test queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_306)
          "close-task gating test received the wrong generation"
        closeCount.modify (· + 1)
    }
    beforeClaimedCloseTaskPublication := do
      publicationEntered.resolve (some ())
      awaitSignal allowPublication
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Unit ← ManagedChannel.unaryWith shared
    fun _ _ => pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match initialized with
  | .ok () => pure ()
  | result => fail s!"close-task gating test did not initialize: {repr result}"

  let requester ← IO.asTask (ManagedChannel.requestClose shared)
  awaitSignal publicationEntered
  expectSupervisorSnapshot shared .draining 0 1 (some 0) [] [] .idle
    0 false {} .startingBounded
    "close-task publication seam exposed the wrong pre-detachment state"
  expect ((← closeCount.get) == 0)
    "close effect began before the exact task handle was retained"
  match ← ManagedChannel.requestClose shared with
  | .stillClosing => pure ()
  | observation =>
      fail s!"pre-publication observer returned {repr observation}"
  expect ((← closeCount.get) == 0)
    "repeated observer released the unpublished close task"

  allowPublication.resolve (some ())
  match ← IO.wait requester with
  | .ok .stillClosing | .ok (.settled (.ok ())) => pure ()
  | _ => fail "published close-task requester returned the wrong observation"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | result => fail s!"close-task gating join returned {repr result}"
  expect (← ManagedChannel.TestSupport.hasRetainedCloseTask shared)
    "close-task gating test did not retain the exact handle"
  expect ((← closeCount.get) == 1)
    "close-task gating test changed exact cleanup count"

private def testSharedCloseCompletionPublicationFailureSettles : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeCount ← IO.mkRef 0
  let publicationAttempts ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "completion-publication test loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 601
      selectedAlpn := fun _ =>
        fail "completion-publication test queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 601)
          "completion-publication test closed the wrong resource"
        closeCount.modify (· + 1)
    }
    beforeCloseCompletionPublication := do
      publicationAttempts.modify (· + 1)
      throw (IO.userError
        "deterministic close-completion publication failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match initialized with
  | .ok 601 => pure ()
  | _ => fail "completion-publication test did not initialize"

  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForTask closer
  match ← IO.wait closer with
  | .ok (.error .completionDropped) => pure ()
  | _ => fail "close-completion publication failure did not settle waiters"
  expect ((← shared.phase) == .closed)
    "completion publication failure changed the closed transport state"
  expect ((← closeCount.get) == 1 &&
      (← publicationAttempts.get) == 1)
    "completion publication failure changed exact close ownership"

  match ← ManagedChannel.close shared with
  | .error .completionDropped => pure ()
  | _ => fail "repeated close lost the published completion failure"
  expect ((← closeCount.get) == 1 &&
      (← publicationAttempts.get) == 1)
    "repeated close republished or repeated transport cleanup"
  expect (← ManagedChannel.TestSupport.hasRetainedCloseTask shared)
    "supervisor state erased the exact detached close-task owner"

private def testSharedCloseTaskPublicationFailureJoinsLocalOwner : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let closeCount ← IO.mkRef 0
  let publicationAttempts ← IO.mkRef 0
  let closeEntered ← IO.Promise.new
  let allowClose ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "close-task publication test loaded trust anchors"
    connector := {
      connect := fun _ register => registered register 602
      selectedAlpn := fun _ =>
        fail "close-task publication test queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 602)
          "close-task publication test closed the wrong resource"
        closeCount.modify (· + 1)
        closeEntered.resolve (some ())
        awaitSignal allowClose
    }
    beforeClaimedCloseTaskPublication := do
      publicationAttempts.modify (· + 1)
      throw (IO.userError
        "deterministic close-task publication failure")
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let initialized : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match initialized with
  | .ok 602 => pure ()
  | _ => fail "close-task publication test did not initialize"

  let closer ← IO.asTask (ManagedChannel.close shared)
  awaitSignal closeEntered
  expect (!(← IO.hasFinished closer))
    "failed close-task state publication did not preserve its live owner"
  expect (← ManagedChannel.TestSupport.hasRetainedCloseTask shared)
    "failed close-task state publication erased the exact promise owner"
  allowClose.resolve (some ())
  waitForTask closer
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | _ => fail "promise-owned close task did not settle completion"
  expect ((← shared.phase) == .closed)
    "promise-owned close task did not publish closed"
  expect ((← closeCount.get) == 1 &&
      (← publicationAttempts.get) == 1)
    "close-task publication fallback changed exact close ownership"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | _ => fail "repeated close lost promise-owned completion"
  expect ((← closeCount.get) == 1 &&
      (← publicationAttempts.get) == 1)
    "repeated close restarted the promise-owned task"

private def testSharedCloseJoinsInitialization : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "shared close plaintext owner loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 201
      selectedAlpn := fun _ => fail "shared close queried ALPN"
      close := fun _ => closeCount.modify (· + 1)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let caller ← IO.asTask <| ManagedChannel.unaryWith shared fun _ _ => do
    actionCount.modify (· + 1)
    pure (Except.ok 7 : Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  try
    let rejected : Except CallError Unit ←
      ManagedChannel.unaryWith shared fun _ _ =>
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
    match rejected with
    | .error .channelDraining => pure ()
    | _ => fail "draining shared owner admitted another call"
    expect (!(← IO.hasFinished closer))
      "shared close returned before initialization settled"
    expect ((← connectCount.get) == 1)
      "close race started a second initialization"
    expectCleanupInventory shared 0 0 0 1
      "close race lost the exact reachable initializer task"
  finally
    allowConnect.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .channelDraining) => pure ()
  | _ => fail "pre-close admitted call did not settle"
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | _ => fail "shared close did not join initialization and call"
  expect ((← closeCount.get) == 1)
    "shared close did not close the initialized generation exactly once"
  expect ((← actionCount.get) == 0)
    "successful initialization admitted work after close won the race"
  expectCleanupInventory shared 0 0 0 0
    "successful shared close retained cleanup debt"

private def testCallerOwnedInitializationTaskFailureIsSticky : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let taskBodyCount ← IO.mkRef 0
  let openCount ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.error .noAddresses)
    loadTrust :=
      fail "caller-owned task failure loaded plaintext trust anchors"
    connector := {
      connect := fun _ _ => do
        connectCount.modify (· + 1)
        pure .failed
      selectedAlpn := fun _ =>
        fail "caller-owned task failure queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationTaskBody := do
      taskBodyCount.modify (· + 1)
      throw (IO.userError "deterministic initializer task-envelope failure")
    beforeInitializationOpen := openCount.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let result : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match result with
  | .error .cleanupUncertain => pure ()
  | result =>
      fail s!"caller-owned task-envelope failure returned {repr result}"
  waitForSharedPhase shared .draining
  expectCleanupInventory shared 0 0 1 0
    "caller-owned task-envelope failure lost sticky evidence"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.taskUncertain 0))
    "caller-owned task-envelope failure retained the wrong generation"
  expect ((← taskBodyCount.get) == 1 && (← openCount.get) == 0 &&
      (← resolveCount.get) == 0 && (← connectCount.get) == 0 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "caller-owned task-envelope failure crossed an effect boundary"
  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelDraining => pure ()
  | result =>
      fail s!"caller-owned task-envelope failure admitted a retry: {repr result}"
  for _ in [0, 1] do
    match ← ManagedChannel.close shared with
    | .error .supervisorInvariant => pure ()
    | result =>
        fail s!"caller-owned task-envelope close changed outcome: {repr result}"
  expectCleanupInventory shared 0 0 1 0
    "repeated caller-owned task-envelope close erased evidence"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.taskUncertain 0) && (← taskBodyCount.get) == 1 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "repeated caller-owned task-envelope close retried an effect"

private def testCancellationSelectedTaskFailureOutranksCancellation :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let taskBodyCount ← IO.mkRef 0
  let openCount ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let taskBodyEntered ← IO.Promise.new
  let allowTaskFailure ← IO.Promise.new
  let cancellationSelected ← IO.Promise.new
  let allowCancellationSettlement ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.error .noAddresses)
    loadTrust :=
      fail "cancellation-selected task failure loaded plaintext trust anchors"
    connector := {
      connect := fun _ _ => do
        connectCount.modify (· + 1)
        pure .failed
      selectedAlpn := fun _ =>
        fail "cancellation-selected task failure queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationTaskBody := do
      taskBodyCount.modify (· + 1)
      taskBodyEntered.resolve (some ())
      awaitSignal allowTaskFailure
      throw (IO.userError "deterministic cancelled task-envelope failure")
    beforeInitializationOpen := openCount.modify (· + 1)
    beforeCancelledInitializationSettlement := do
      cancellationSelected.resolve (some ())
      awaitSignal allowCancellationSettlement
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal taskBodyEntered
  cancellation.cancel
  awaitSignal cancellationSelected
  allowTaskFailure.resolve (some ())
  waitForInitializationTaskFinished shared
  allowCancellationSettlement.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .cleanupUncertain) => pure ()
  | _ =>
      fail "selected cancellation masked task uncertainty"
  waitForSharedPhase shared .draining
  expectCleanupInventory shared 0 0 1 0
    "cancellation-selected task failure lost sticky evidence"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.taskUncertain 0))
    "cancellation-selected task failure retained the wrong generation"
  expect ((← taskBodyCount.get) == 1 && (← openCount.get) == 0 &&
      (← resolveCount.get) == 0 && (← connectCount.get) == 0 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "cancellation-selected task failure crossed an effect boundary"
  for _ in [0, 1] do
    match ← ManagedChannel.close shared with
    | .error .supervisorInvariant => pure ()
    | result =>
        fail s!"cancellation-selected task close changed outcome: {repr result}"
  expectCleanupInventory shared 0 0 1 0
    "repeated cancellation-selected close erased task evidence"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.taskUncertain 0) && (← taskBodyCount.get) == 1 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "repeated cancellation-selected close retried an effect"

private def testCloseOwnedInitializationTaskFailureIsSticky : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let taskBodyCount ← IO.mkRef 0
  let openCount ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let taskBodyEntered ← IO.Promise.new
  let allowTaskFailure ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.error .noAddresses)
    loadTrust :=
      fail "close-owned task failure loaded plaintext trust anchors"
    connector := {
      connect := fun _ _ => do
        connectCount.modify (· + 1)
        pure .failed
      selectedAlpn := fun _ =>
        fail "close-owned task failure queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationTaskBody := do
      taskBodyCount.modify (· + 1)
      taskBodyEntered.resolve (some ())
      awaitSignal allowTaskFailure
      throw (IO.userError "deterministic close-owned task-envelope failure")
    beforeInitializationOpen := openCount.modify (· + 1)
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal taskBodyEntered
  cancellation.cancel
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "cancelled close-owned task returned the wrong result"
  expectCleanupInventory shared 0 0 0 1
    "cancelled close-owned task was not retained"

  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  expect (!(← IO.hasFinished closer))
    "shared close returned before its outer-error initializer"
  allowTaskFailure.resolve (some ())
  match ← IO.wait closer with
  | .ok (.error .supervisorInvariant) => pure ()
  | _ =>
      fail "close-owned task uncertainty returned the wrong result"
  expectCleanupInventory shared 0 0 1 0
    "close-owned task failure lost sticky evidence"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.taskUncertain 0))
    "close-owned task failure retained the wrong generation"
  expect ((← taskBodyCount.get) == 1 && (← openCount.get) == 0 &&
      (← resolveCount.get) == 0 && (← connectCount.get) == 0 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "close-owned task failure crossed an effect boundary"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"repeated close-owned task close changed outcome: {repr result}"
  expectCleanupInventory shared 0 0 1 0
    "repeated close-owned task close erased evidence"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.taskUncertain 0) && (← taskBodyCount.get) == 1 &&
      (← actionCount.get) == 0 && (← closes.get).isEmpty)
    "repeated close-owned task close retried an effect"

private def testCancellationSelectedRetryableFailureStaysOwnerCancelled :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let initializationAttempts ← IO.mkRef 0
  let resolveCount ← IO.mkRef 0
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let initializationEntered ← IO.Promise.new
  let allowInitializationFailure ← IO.Promise.new
  let cancellationSelected ← IO.Promise.new
  let allowCancellationSettlement ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.ok destinations)
    loadTrust :=
      fail "retryable cancellation race loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        registered register 1_201
      selectedAlpn := fun _ =>
        fail "retryable cancellation race queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeInitializationOpen := do
      let attempt ← initializationAttempts.modifyGet fun count =>
        (count, count + 1)
      if attempt == 0 then
        initializationEntered.resolve (some ())
        awaitSignal allowInitializationFailure
        throw (IO.userError "deterministic owner-free setup failure")
    beforeCancelledInitializationSettlement := do
      cancellationSelected.resolve (some ())
      awaitSignal allowCancellationSettlement
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal initializationEntered
  cancellation.cancel
  awaitSignal cancellationSelected
  allowInitializationFailure.resolve (some ())
  waitForInitializationTaskFinished shared
  allowCancellationSettlement.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "retryable completion overrode selected cancellation"
  expect ((← shared.phase) == .accepting)
    "retryable cancellation race poisoned shared admission"
  expectCleanupInventory shared 0 0 0 0
    "retryable cancellation race left initialization debt"
  expect ((← initializationAttempts.get) == 1 &&
      (← resolveCount.get) == 0 && (← connectCount.get) == 0 &&
      (← actionCount.get) == 0)
    "retryable cancellation race crossed an unexpected effect boundary"

  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ => do
      actionCount.modify (· + 1)
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 1_201 => pure ()
  | result =>
      fail s!"retryable cancellation race did not admit a fresh generation: {repr result}"
  expect ((← initializationAttempts.get) == 2 &&
      (← resolveCount.get) == 1 && (← connectCount.get) == 1 &&
      (← actionCount.get) == 1)
    "retryable cancellation recovery changed exact attempt counts"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"retryable cancellation recovery close failed: {error}"
  expect ((← closes.get) == #[1_201])
    "retryable cancellation recovery did not close its generation once"

private def testCancellationSelectedInvariantOutranksOwnerCancellation :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let staleReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let connectorEntered ← IO.Promise.new
  let allowConnectorResult ← IO.Promise.new
  let cancellationSelected ← IO.Promise.new
  let allowCancellationSettlement ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust :=
      fail "invariant cancellation race loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count =>
          (count, count + 1)
        if attempt == 0 then
          let some receipt ← register 1_202
            | fail "invariant race rejected its first registration"
          staleReceipt.set (some receipt)
          pure .failed
        else
          let some _accepted ← register 1_203
            | fail "invariant race rejected its second registration"
          connectorEntered.resolve (some ())
          awaitSignal allowConnectorResult
          let some stale ← staleReceipt.get
            | fail "invariant race lost its stale receipt"
          pure (.connected stale)
      selectedAlpn := fun _ =>
        fail "invariant cancellation race queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeCancelledInitializationSettlement := do
      cancellationSelected.resolve (some ())
      awaitSignal allowCancellationSettlement
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  cancellation.cancel
  awaitSignal cancellationSelected
  allowConnectorResult.resolve (some ())
  waitForInitializationTaskFinished shared
  allowCancellationSettlement.resolve (some ())
  match ← IO.wait caller with
  | .ok (.error .supervisorInvariant) => pure ()
  | _ =>
      fail "selected cancellation masked a connector invariant"
  waitForSharedPhase shared .draining
  expect ((← actionCount.get) == 0 &&
      (← connectCount.get) == 2 &&
      (← closes.get) == #[1_202, 1_203])
    "invariant cancellation race changed exact resource custody"
  let inventory ← ManagedChannel.TestSupport.cleanupInventory shared
  expect (inventory.channelOwners == 0 &&
      inventory.initializationOwners == 0 &&
      inventory.uncertainInitializations == 0 &&
      inventory.invariantInitializations == 1 &&
      inventory.pendingInitializations ≤ 1)
    s!"invariant cancellation race lost sticky evidence: {repr inventory}"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.connectorInvariant 0))
    "invariant cancellation race retained the wrong generation evidence"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result =>
      fail s!"invariant cancellation race allowed clean close: {repr result}"
  let settledInventory ← ManagedChannel.TestSupport.cleanupInventory shared
  expect (settledInventory ==
      ({ invariantInitializations := 1 } : CleanupInventory))
    "joined invariant cancellation close retained its terminal task"

private def runAdmittedLateCancellation
    (shared : ManagedChannel Nat)
    (failureEntered allowFailure claimEntered allowClaim :
      IO.Promise (Option Unit))
    (actionCount : IO.Ref Nat)
    (expectFailure : Except CallError Unit → IO Unit) : IO Unit := do
  let action := fun _ _ => do
    actionCount.modify (· + 1)
    pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  let first ← IO.asTask (ManagedChannel.unaryWith shared action)
  awaitSignal failureEntered

  let cancellation ← Grpc.Cancellation.create
  let admitted ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation action
  awaitSignal claimEntered

  allowFailure.resolve (some ())
  let .ok firstResult ← IO.wait first
    | fail "published-failure owner task raised"
  expectFailure firstResult
  waitForSharedPhase shared .draining

  -- This caller already owns an outer lease and passed its initial
  -- cancellation check. Cancellation becomes visible only after the first
  -- caller has published terminal initialization evidence.
  cancellation.cancel
  allowClaim.resolve (some ())
  let .ok admittedResult ← IO.wait admitted
    | fail "admitted published-failure waiter raised"
  expectFailure admittedResult

private def testAdmittedIdleClaimCannotRestartDuringDrain : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let claimEntered ← IO.Promise.new
  let allowClaim ← IO.Promise.new
  let resolveCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => do
      resolveCount.modify (· + 1)
      pure (.error .noAddresses)
    loadTrust := fail "idle-drain race loaded plaintext trust anchors"
    connector := forbiddenConnector "idle-drain admitted race"
    beforeCancelledInitializationClaim := do
      claimEntered.resolve (some ())
      awaitSignal allowClaim
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let admitted ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal claimEntered
  match ← ManagedChannel.requestClose shared with
  | .stillClosing => pure ()
  | result => fail s!"idle-drain close request returned {repr result}"
  waitForSharedPhase shared .draining
  allowClaim.resolve (some ())
  match ← IO.wait admitted with
  | .ok (.error .channelDraining) => pure ()
  | _ => fail "admitted idle claim did not observe shared drain"
  expect ((← resolveCount.get) == 0 && (← actionCount.get) == 0)
    "admitted idle claim restarted initialization during drain"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"idle-drain joined close failed: {error}"

private def testAdmittedCancellationPreservesPublishedTerminalPolicy :
    IO Unit := do
  let configuration ← apiConfiguration "http://api.example.test:50051"
  let failureEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let claimEntered ← IO.Promise.new
  let allowClaim ← IO.Promise.new
  let initializationCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => fail "terminal-policy race unexpectedly resolved"
    loadTrust := fail "terminal-policy race unexpectedly loaded trust anchors"
    connector := forbiddenConnector "terminal-policy admitted race"
    beforeInitializationOpen := do
      initializationCount.modify (· + 1)
      failureEntered.resolve (some ())
      awaitSignal allowFailure
    beforeCancelledInitializationClaim := do
      claimEntered.resolve (some ())
      awaitSignal allowClaim
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  runAdmittedLateCancellation shared failureEntered allowFailure
    claimEntered allowClaim actionCount fun
    | .error .actionFailed => pure ()
    | result => fail s!"published terminal policy returned {repr result}"
  expect ((← initializationCount.get) == 1 && (← actionCount.get) == 0)
    "admitted waiter restarted initialization during policy drain"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.terminalPolicy 0 .plaintextRequiresLoopback))
    "terminal policy did not remain generation-indexed while draining"
  expectCleanupInventory shared 0 0 0 0
    "capability-free terminal policy created cleanup debt"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error => fail s!"terminal-policy race close failed: {error}"

private def testAdmittedCancellationPreservesPublishedInvariant : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]
  let failureEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let claimEntered ← IO.Promise.new
  let allowClaim ← IO.Promise.new
  let oldReceipt ← IO.mkRef (none : Option (RegistrationReceipt Nat))
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "published invariant loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count => (count, count + 1)
        if attempt == 0 then
          let some receipt ← register 1_207
            | fail "published invariant rejected first registration"
          oldReceipt.set (some receipt)
          pure .failed
        else
          let some _accepted ← register 1_208
            | fail "published invariant rejected second registration"
          failureEntered.resolve (some ())
          awaitSignal allowFailure
          let some stale ← oldReceipt.get
            | fail "published invariant lost stale receipt"
          pure (.connected stale)
      selectedAlpn := fun _ =>
        fail "published invariant queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
    beforeCancelledInitializationClaim := do
      claimEntered.resolve (some ())
      awaitSignal allowClaim
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  runAdmittedLateCancellation shared failureEntered allowFailure
    claimEntered allowClaim actionCount fun
    | .error .supervisorInvariant => pure ()
    | result => fail s!"published connector invariant returned {repr result}"
  expect ((← connectCount.get) == 2 && (← actionCount.get) == 0 &&
      (← closes.get) == #[1_207, 1_208])
    "published connector invariant changed exact effects"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.connectorInvariant 0))
    "published connector invariant lost its generation evidence"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | result => fail s!"published invariant close returned {repr result}"

private def testAdmittedCancellationPreservesPublishedCleanupUncertainty :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let failureEntered ← IO.Promise.new
  let allowFailure ← IO.Promise.new
  let claimEntered ← IO.Promise.new
  let allowClaim ← IO.Promise.new
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "published cleanup loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 1_209
        failureEntered.resolve (some ())
        awaitSignal allowFailure
        pure .failed
      selectedAlpn := fun _ =>
        fail "published cleanup queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_209)
          "published cleanup closed the wrong exact resource"
        closeCount.modify (· + 1)
        throw (IO.userError "deterministic published cleanup ambiguity")
    }
    beforeCancelledInitializationClaim := do
      claimEntered.resolve (some ())
      awaitSignal allowClaim
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  runAdmittedLateCancellation shared failureEntered allowFailure
    claimEntered allowClaim actionCount fun
    | .error .cleanupUncertain => pure ()
    | result => fail s!"published cleanup uncertainty returned {repr result}"
  expect ((← connectCount.get) == 1 && (← closeCount.get) == 1 &&
      (← actionCount.get) == 0)
    "published cleanup uncertainty changed exact effects"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.cleanupUncertain 0 .connectionAttemptsFailed
        .retryableTransport 1_209))
    "published cleanup uncertainty lost its exact owner"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result => fail s!"published cleanup close returned {repr result}"

private def testCloseOwnsCancelledCleanupFailureSettlement : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let closeCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let connectorEntered ← IO.Promise.new
  let allowConnectorFailure ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust :=
      fail "close-owned cleanup failure loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        discard <| register 1_204
        connectorEntered.resolve (some ())
        awaitSignal allowConnectorFailure
        pure .failed
      selectedAlpn := fun _ =>
        fail "close-owned cleanup failure queried plaintext ALPN"
      close := fun resource => do
        expect (resource == 1_204)
          "close-owned initializer closed the wrong resource"
        closeCount.modify (· + 1)
        throw (IO.userError "deterministic close-owned cleanup ambiguity")
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  cancellation.cancel
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "cancelled close-owned initializer returned the wrong result"
  expectCleanupInventory shared 0 0 0 1
    "cancelled close-owned initializer was not staged"

  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  expect (!(← IO.hasFinished closer))
    "shared close returned before its staged initializer"
  allowConnectorFailure.resolve (some ())
  match ← IO.wait closer with
  | .ok (.error .transport) => pure ()
  | _ =>
      fail "close-owned cleanup ambiguity returned the wrong result"
  expect ((← shared.phase) == .draining)
    "close-owned cleanup ambiguity published a clean closed phase"
  expectCleanupInventory shared 0 1 0 0
    "close-owned cleanup ambiguity lost its exact owner"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) ==
        some (.cleanupUncertain 0 .connectionAttemptsFailed
          .retryableTransport 1_204))
    "close-owned cleanup ambiguity retained the wrong resource"
  expect ((← connectCount.get) == 1 &&
      (← closeCount.get) == 1 && (← actionCount.get) == 0)
    "close-owned cleanup ambiguity changed exact effect counts"
  match ← ManagedChannel.close shared with
  | .error .transport => pure ()
  | result =>
      fail s!"repeated close-owned cleanup changed outcome: {repr result}"
  expect ((← closeCount.get) == 1)
    "repeated close retried ambiguous initialization cleanup"

private def testCloseOwnsCancelledInvariantSettlement : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ←
    addresses configuration #["127.0.0.1", "127.0.0.2"]
  let connectCount ← IO.mkRef 0
  let actionCount ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let staleReceipt ← IO.mkRef
    (none : Option (RegistrationReceipt Nat))
  let connectorEntered ← IO.Promise.new
  let allowInvariant ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust :=
      fail "close-owned invariant loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        let attempt ← connectCount.modifyGet fun count =>
          (count, count + 1)
        if attempt == 0 then
          let some receipt ← register 1_205
            | fail "close-owned invariant rejected first registration"
          staleReceipt.set (some receipt)
          pure .failed
        else
          let some _accepted ← register 1_206
            | fail "close-owned invariant rejected second registration"
          connectorEntered.resolve (some ())
          awaitSignal allowInvariant
          let some stale ← staleReceipt.get
            | fail "close-owned invariant lost its stale receipt"
          pure (.connected stale)
      selectedAlpn := fun _ =>
        fail "close-owned invariant queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCount.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectorEntered
  cancellation.cancel
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "cancelled close-owned invariant returned the wrong result"
  expectCleanupInventory shared 0 0 0 1
    "cancelled invariant initializer was not staged"

  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  expect (!(← IO.hasFinished closer))
    "invariant close returned before its staged initializer"
  allowInvariant.resolve (some ())
  match ← IO.wait closer with
  | .ok (.error .supervisorInvariant) => pure ()
  | _ =>
      fail "close-owned connector invariant returned the wrong result"
  expect ((← shared.phase) == .draining)
    "close-owned invariant published a clean closed phase"
  let inventory ← ManagedChannel.TestSupport.cleanupInventory shared
  expect (inventory == ({ invariantInitializations := 1 } : CleanupInventory))
    s!"close-owned invariant retained the wrong inventory: {repr inventory}"
  expect ((← ManagedChannel.TestSupport.failedInitializationEvidence?
      shared) == some (.connectorInvariant 0))
    "close-owned invariant retained the wrong generation evidence"
  expect ((← connectCount.get) == 2 &&
      (← actionCount.get) == 0 &&
      (← closes.get) == #[1_205, 1_206])
    "close-owned invariant changed exact resource custody"
  match ← ManagedChannel.close shared with
  | .error .supervisorInvariant => pure ()
  | _ =>
      fail "repeated close-owned invariant changed outcome"
  let rejected : Except CallError Unit ←
    ManagedChannel.unaryWith shared fun _ _ => do
      actionCount.modify (· + 1)
      pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  match rejected with
  | .error .channelDraining => pure ()
  | result =>
      fail s!"close-owned invariant admitted a later call: {repr result}"
  expect ((← connectCount.get) == 2 &&
      (← actionCount.get) == 0 &&
      (← closes.get) == #[1_205, 1_206])
    "repeated close-owned invariant retried an effect"

private def testSharedInitializationCancellationSettlesOnLaterCall :
    IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let cancelledActionCalls ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "cancelled initialization loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 701
      selectedAlpn := fun _ =>
        fail "cancelled initialization queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun resource _ => do
        cancelledActionCalls.modify (· + 1)
        pure (Except.ok resource :
          Except Grpc.UnaryCall.Error Nat)
  awaitSignal connectEntered
  cancellation.cancel
  -- The connector remains deliberately blocked: only cancellation-aware
  -- initialization waiting can make this caller terminal.
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "staged initialization cancellation did not map to ownerCancelled"
  expect ((← cancelledActionCalls.get) == 0)
    "cancelled initialization reached the RPC action"
  expect ((← connectCount.get) == 1)
    "cancelled initialization started more than one connector"
  expect ((← shared.phase) == .accepting)
    "cancelled initializer changed the shared acceptance phase"
  expectCleanupInventory shared 0 0 0 1
    "cancelled initialization was removed from supervisor state"

  allowConnect.resolve (some ())
  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 701 => pure ()
  | result =>
      fail s!"later caller did not settle staged initialization: {repr result}"
  expect ((← connectCount.get) == 1)
    "later caller replaced rather than joined staged initialization"
  expectCleanupInventory shared 0 0 0 0
    "later caller left initialization cleanup debt"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"staged-initialization recovery close failed: {error}"
  expect ((← closes.get) == #[701])
    "recovered staged resource was not closed exactly once"
  expectCleanupInventory shared 0 0 0 0
    "recovered staged resource lost cleanup ownership"

private def testSharedInitializationCancellationPrunesWaiters : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let actionCalls ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "waiter-pruning initialization loaded plaintext trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 703
      selectedAlpn := fun _ =>
        fail "waiter-pruning initialization queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  for index in [0:128] do
    let cancellation ← Grpc.Cancellation.create
    let caller ← IO.asTask <|
      ManagedChannel.TestSupport.unaryWithInitializationCancellation
        shared cancellation fun _ _ => do
          actionCalls.modify (· + 1)
          pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
    if index == 0 then awaitSignal connectEntered
    waitForInitializationCompletionWaiters shared 1
    cancellation.cancel
    waitForTask caller
    match ← IO.wait caller with
    | .ok (.error .ownerCancelled) => pure ()
    | _ => fail "reused initializer cancellation did not settle its caller"
    waitForInitializationCompletionWaiters shared 0
  expect ((← connectCount.get) == 1)
    "reused cancellations started more than one initializer"
  expect ((← actionCalls.get) == 0)
    "cancelled initializer waiter reached the RPC action"
  expectCleanupInventory shared 0 0 0 1
    "reused cancellations lost the exact staged initializer"

  allowConnect.resolve (some ())
  let recovered : Except CallError Nat ←
    ManagedChannel.unaryWith shared fun resource _ =>
      pure (Except.ok resource :
        Except Grpc.UnaryCall.Error Nat)
  match recovered with
  | .ok 703 => pure ()
  | result =>
      fail s!"waiter-pruning initializer did not recover: {repr result}"
  match ← ManagedChannel.close shared with
  | .ok () => pure ()
  | .error error =>
      fail s!"waiter-pruning shared close failed: {error}"
  expect ((← closes.get) == #[703])
    "waiter-pruning initializer resource was not closed exactly once"

private def testSharedInitializationCancellationSettlesOnClose : IO Unit := do
  let configuration ← apiConfiguration "http://localhost:50051"
  let destinations ← addresses configuration #["127.0.0.1"]
  let connectCount ← IO.mkRef 0
  let actionCalls ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Nat)
  let connectEntered ← IO.Promise.new
  let allowConnect ← IO.Promise.new
  let dependencies : ManagedChannel.Dependencies Nat := {
    resolve := fun _ => pure (.ok destinations)
    loadTrust := fail "close-settled cancellation loaded trust anchors"
    connector := {
      connect := fun _ register => do
        connectCount.modify (· + 1)
        connectEntered.resolve (some ())
        awaitSignal allowConnect
        registered register 702
      selectedAlpn := fun _ =>
        fail "close-settled cancellation queried plaintext ALPN"
      close := fun resource => closes.modify (·.push resource)
    }
  }
  let shared ← ManagedChannel.createWith dependencies configuration
  let cancellation ← Grpc.Cancellation.create
  let caller ← IO.asTask <|
    ManagedChannel.TestSupport.unaryWithInitializationCancellation
      shared cancellation fun _ _ => do
        actionCalls.modify (· + 1)
        pure (Except.ok () : Except Grpc.UnaryCall.Error Unit)
  awaitSignal connectEntered
  cancellation.cancel
  waitForTask caller
  match ← IO.wait caller with
  | .ok (.error .ownerCancelled) => pure ()
  | _ =>
      fail "close-settled cancellation did not map to ownerCancelled"
  expect ((← actionCalls.get) == 0)
    "close-settled cancellation reached the RPC action"
  expectCleanupInventory shared 0 0 0 1
    "close-settled initializer was not retained"

  let closer ← IO.asTask (ManagedChannel.close shared)
  waitForSharedPhase shared .draining
  expect (!(← IO.hasFinished closer))
    "shared close returned before the retained initializer settled"
  allowConnect.resolve (some ())
  waitForTask closer
  match ← IO.wait closer with
  | .ok (.ok ()) => pure ()
  | _ =>
      fail "shared close did not settle retained initialization"
  expect ((← connectCount.get) == 1)
    "shared close changed exact initialization ownership"
  expect ((← closes.get) == #[702])
    "shared close did not close the retained resource exactly once"
  expect ((← shared.phase) == .closed)
    "shared close did not publish closed after retained initialization"
  expectCleanupInventory shared 0 0 0 0
    "shared close lost retained initialization cleanup ownership"

def run : IO Unit := do
  testOrderedPlaintextFallback
  testRegistrationReceiptsAreOneShotAndSealed
  testPlaintextPolicyAndAddressBound
  testSanitizedSetupAndResourceFailures
  testHttpsPolicyAndAlpnFallback
  testCallLeaseAndCloseLifecycle
  testTransportCloseFailure
  testCallCleanupUncertaintyPoisonsChannel
  testLazySharedSingleFlightAndReconnect
  testSharedGenerationScopePinsAcrossReconnect
  testEscapedGenerationScopeIsRevoked
  testGenerationScopeDrainsAdmittedInvocation
  testGenerationScopePreservesDetachedRetirement
  testGenerationRetirementMergesBySeverity
  testLocalCallCompletionDoesNotRetireGeneration
  testSharedRpcRetirementClassification
  testSharedRpcRetirementCloseFailure
  testSharedInitializationCleanupUncertainty
  testCancelledSoleWaiterTerminalHandoffSelfDrives
  testTerminalHandoffDoesNotJoinExistingInlineCloser
  testExternalInlineCloserRetainsTransferredInitializer
  testSharedCleanupFailureIsConsumedOnceAcrossTwoWaiters
  testMismatchedCleanupFailureIsQuarantined
  testOwnedCleanupCustodyTransfersToSharedSupervisor
  testDirectCloseRacesSharedCustodyTransfer
  testCopiedCleanupDiagnosticIsSupervisorInert
  testSameOwnedCleanupFailureAcrossGenerationsTransfersOnce
  testDistinctOwnedCleanupFailuresAtSameGenerationAreBothRetained
  testStaleOwnerFreeWaiterUsesAuthoritativeFailure
  testSharedPreOpenFailureIsOwnerFreeAndRetryable
  testInitializationTaskAllocationFailureIsRetryable
  testInitializationWaitsForSupervisorPublication
  testOwnerAdoptionFailureRollsBackStructurally
  testInitializationDebtPoisonsAdmissionAtomically
  testCleanOpeningFailurePreservesUnavailableAndRetry
  testTerminalPolicyFailureClosesSharedOwner
  testTrustPreparationIsTerminalAndPinned
  testConnectorInvariantPoisonsSharedClose
  testConnectorInvariantCleanupPreservesBothCauses
  testCloseOwnsCancelledCompositeOpenFailure
  testInvocationDeadlineStartsBeforeInitialization
  testInvocationOwnerCancellationPrecedesDeadline
  testGenerationSetupUsesFirstInvocationBudget
  testGenerationScopeOutlivesConsumedFirstBudget
  testGenerationFirstPolicyTransfersWithoutRestart
  testExplicitGenerationPolicyGovernsSetup
  testExplicitGenerationPolicyCancelsSetup
  testExplicitGenerationPolicyMismatchIsSticky
  testFirstBudgetSelectionAndAdmissionAreAtomic
  testGenerationAdmissionQueueConsumesDeadline
  testRejectedGenerationScopeSettlesBudget
  testInvocationGateRejectsPostDeadlineStart
  testSetupIsDeductedFromCallBudget
  testDeadlineOverridesLateActionEvidence
  testBoundedCloseRetainsBlockedInitialization
  testBoundedCloseRetainsBlockedEstablishedGeneration
  testCloseSettlementRepeatedWakeup
  testBoundedClosePreservesLaterFailure
  testBoundedCloseDriverFailureRetainsCustody
  testJoiningCloseRetakesRacingBoundedFailure
  testBoundedWaitObservesRacingDriverFailure
  testCloseObservationResamplesRetakenCustody
  testCloseCompletionWinsObservationBoundary
  testSharedExplicitCloseTaskFailureFallsBackInline
  testCloseTaskHandlePrecedesCleanup
  testSharedCloseCompletionPublicationFailureSettles
  testSharedCloseTaskPublicationFailureJoinsLocalOwner
  testSharedCloseJoinsInitialization
  testCallerOwnedInitializationTaskFailureIsSticky
  testCancellationSelectedTaskFailureOutranksCancellation
  testCloseOwnedInitializationTaskFailureIsSticky
  testCancellationSelectedRetryableFailureStaysOwnerCancelled
  testCancellationSelectedInvariantOutranksOwnerCancellation
  testAdmittedIdleClaimCannotRestartDuringDrain
  testAdmittedCancellationPreservesPublishedTerminalPolicy
  testAdmittedCancellationPreservesPublishedInvariant
  testAdmittedCancellationPreservesPublishedCleanupUncertainty
  testCloseOwnsCancelledCleanupFailureSettlement
  testCloseOwnsCancelledInvariantSettlement
  testSharedInitializationCancellationSettlesOnLaterCall
  testSharedInitializationCancellationPrunesWaiters
  testSharedInitializationCancellationSettlesOnClose
  IO.println "transport channel tests passed"

end ManagedChannelTest

def main : IO Unit :=
  ManagedChannelTest.run
