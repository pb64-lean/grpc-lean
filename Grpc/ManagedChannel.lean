module

public import Grpc.Client
public import Grpc.Cancellation
public import Grpc.ChannelOwner
public import Grpc.ManagedChannel.Config
public import Grpc.NameResolver
public import Grpc.TrustAnchors
public import Grpc.UnaryCall
public import Std.Async.Timer
public import Std.Sync.CancellationToken

public section

/-!
# Production shared gRPC channel

One connection is selected by ordered address attempts and then transferred to
the proof-bearing shared owner. HTTP is restricted to loopback before any
credential metadata can exist. HTTPS always uses a validated trust bundle, hostname
verification, SNI, and an exact `h2` ALPN result.

All injectable hooks return resources or bounded local failures. RPC failures
retain the exact peer `Grpc.Status` for parity-sensitive service adapters,
while generic `ToString`/`Repr` rendering omits its description and never
includes hostnames, paths, metadata, or credentials.

Connection establishment itself is intentionally not described as locally
bounded: the resolver and client connector do not expose cancellable
DNS/TCP/TLS initialization. The standard DNS and TCP-connect promises expose
no selector unregister/cancel operation; `Connector.connect` is a plain `IO`
action; and `Grpc.Client` does not publish the in-progress native socket to
this owner. A cancelled caller may stop awaiting the staged initialization task,
but never cancels or removes it; a later call or shared close must settle that
same task and retain or close every resource-bearing result. If the task is
already terminal when cancellation is selected, terminal policy, supervisor
invariant, and cleanup uncertainty take precedence over owner cancellation.
Every typed unary through the production lazy shared owner starts one absolute
monotonic invocation budget before this setup. Expiration therefore bounds the
caller even though it cannot yet interrupt the native initializer itself.
Established generations otherwise have joined close, configured message-size
limits, redacted credential metadata, transport-dead retirement, and lazy
single-flight
opening retry after only clean transport or local setup failure, without
replaying an ambiguous RPC. A shared owner pins its first trust-preparation
result across every later connection generation; local trust preparation has
no connector owner and is terminal policy, never a retryable transport
`UNAVAILABLE`. Linux trust-file descriptor consumption is proved by the
production trust backend; Darwin's finalizer-backed fallback remains a
documented platform gap.
Endpoint policy closes the shared owner; a connector contract violation keeps
sticky generation evidence and fails close. Failed initialization cleanup is
retained as an exact raw cleanup capability; failed generation close is
retained as an exact channel capability. Exact debt or sticky uncertainty
prevents a later shared close from claiming success, and no ambiguous close
effect is retried.
-/

namespace Grpc

open Std.Async

def requiredAlpn : String := "h2"
def maximumConnectionAttempts : Nat := 64

structure TlsPolicy where
  serverName : String
  alpnProtocols : Array String
  trustAnchorsPEM : String
  verifyHostname : Bool

inductive ChannelCredentials where
  | plaintext
  | tls (policy : TlsPolicy)

structure ConnectAttempt where
  address : NameResolver.Address
  authority : String
  scheme : String
  credentials : ChannelCredentials
  /-- Maximum uncompressed bytes accepted for one outbound request message. -/
  maxSendMessageBytes : Nat := defaultMaxMessageBytes
  /-- Maximum bytes accepted for one inbound response message. -/
  maxReceiveMessageBytes : Nat := defaultMaxMessageBytes

/-!
An opaque one-shot receipt is the only value a connector may return as a
successful connection. Its private cell is created by the channel registrar,
so the result cannot substitute a different raw resource after registration.
-/
structure RegistrationReceipt (Resource : Type) where
  private mk ::
  private cell : IO.Ref (Option Resource)

inductive ConnectResult (Resource : Type) where
  | connected (receipt : RegistrationReceipt Resource)
  | failed

structure Connector (Resource : Type) where
  /--
  Register the exact raw resource through the nonthrowing callback immediately
  after acquisition. It returns an opaque receipt only when transfer is
  accepted. Exactly one registration is accepted while the attempt is open;
  duplicate or late registrations return `none` and remain connector-owned.
  `.connected` can carry only the accepted receipt, while `.failed` or an outer
  exception makes the channel close the journaled owner.
  -/
  connect :
    ConnectAttempt →
      (Resource → BaseIO (Option (RegistrationReceipt Resource))) →
      IO (ConnectResult Resource)
  selectedAlpn : Resource → IO (Option String)
  close : Resource → IO Unit
  /--
  Deterministic post-connect adoption-allocation seam. Production leaves this
  empty; tests raise after the accepted receipt is consumed, while `adopt`
  still holds the exact raw resource and before `Owner.create`, to prove that
  clean rollback is retryable and ambiguous rollback retains that resource.
  -/
  beforeOwnerAdoption : IO Unit := pure ()

structure ManagedChannel.Dependencies (Resource : Type) where
  resolve :
    Endpoint →
      IO (Except NameResolver.Error
        (Array NameResolver.Address))
  loadTrust :
    IO (Except TrustAnchors.Error
      TrustAnchors.Bundle)
  connector : Connector Resource
  /--
  Deterministic pre-acquisition failure seam. Production leaves this empty;
  failures here are normalized inside the initialization task as owner-free
  setup failures because no resolver, trust, or connector effect has begun.
  -/
  beforeInitializationOpen : IO Unit := pure ()
  /--
  Deterministic initialization-task allocation seam. Production leaves this
  empty; failure occurs before resolver, trust, or connector effects and is
  therefore a clean local retryable failure with no published generation.
  -/
  beforeInitializationTaskAllocation : IO Unit := pure ()
  /--
  Deterministic task-envelope failure seam. Production leaves this empty;
  tests raise inside the allocated task but before the fixed-shape opening
  action begins. It is deliberately outside local-failure normalization, so
  the supervisor must retain sticky uncertain-generation evidence while no
  resolver, trust, connector, or owner effect can be leaked by the seam.
  -/
  beforeInitializationTaskBody : IO Unit := pure ()
  /--
  Deterministic task-publication seam. Production leaves this empty; tests may
  pause after the initializer task is allocated but before it is installed in
  shared supervisor state. The task remains behind a private gate throughout
  this hook, so resolver, trust, and connector effects cannot begin early.
  Exceptions are observational and cannot discard the already allocated task.
  -/
  beforeInitializationTaskPublication : IO Unit := pure ()
  /--
  Deterministic cancellation/completion race seam. Production leaves this
  empty; tests may pause after cancellation wins selection but before the
  initializer's terminal result is inspected. Exceptions are observational
  only and are contained so this seam cannot alter cleanup custody.
  -/
  beforeCancelledInitializationSettlement : IO Unit := pure ()
  /--
  Deterministic admitted-caller race seam. Production leaves this empty;
  tests may pause after the initial cancellation check but before the shared
  initialization state is claimed. Exceptions are observational only.
  -/
  beforeCancelledInitializationClaim : IO Unit := pure ()
  /--
  Deterministic terminal-handoff race seam. Production leaves this empty;
  tests may pause after terminal authority and its close claim are stored but
  before the initializer presents its exact completion identity to the close
  supervisor. Exceptions are observational and contained.
  -/
  beforeInitializationCloseHandoff : IO Unit := pure ()
  /--
  Deterministic generation-admission race seam. Production leaves this empty;
  tests may pause after first-budget selection while the authoritative
  admission lock is still held.
  -/
  beforeGenerationScopeAdmission : IO Unit := pure ()
  /--
  Deterministic task-allocation failure seam. Production leaves this empty;
  tests raise here to prove that a joining close retains its inline completion
  owner, while a bounded request restores explicit needs-owner custody rather
  than blocking inside cleanup.
  -/
  beforeClaimedCloseTask : IO Unit := pure ()
  /--
  Deterministic inline-fallback publication seam. Production leaves this
  empty; tests may pause after joining allocation failure has atomically
  published the task-free inline driver, but before that owner starts joined
  cleanup. Exceptions are observational and contained.
  -/
  afterInlineCloseDriverPublication : IO Unit := pure ()
  /--
  Deterministic detached-owner publication failure seam. Production leaves
  this empty; if it raises, the exact task is still published as the mutex-held
  `CloseDriverState.detached` owner before its start gate is released.
  -/
  beforeClaimedCloseTaskPublication : IO Unit := pure ()
  /--
  Deterministic close-completion publication failure seam. Production leaves
  this empty; the shared owner still publishes a terminal result if it raises.
  -/
  beforeCloseCompletionPublication : IO Unit := pure ()
  /--
  Deterministic observation-boundary seam. Production leaves this empty and
  exceptions are contained. Tests pause after the first completion check but
  before the final completion and custody snapshot, proving that terminal
  publication or a racing driver claim wins that boundary without changing
  cleanup ownership.
  -/
  beforeCloseObservationFinalCheck : IO Unit := pure ()

inductive OpenError where
  | plaintextRequiresLoopback
  | resolution
  | trustAnchors
  | tooManyAddresses
  | connectionAttemptsFailed
  | alpnNegotiationFailed
  | cleanupFailed
  | initializationFailed
deriving BEq, DecidableEq, Repr

namespace OpenError

def render : OpenError → String
  | .plaintextRequiresLoopback =>
      "plaintext channel endpoints must resolve only to loopback"
  | .resolution => "channel endpoint resolution failed"
  | .trustAnchors => "channel trust-anchor loading failed"
  | .tooManyAddresses => "channel endpoint returned too many addresses"
  | .connectionAttemptsFailed => "channel connection attempts failed"
  | .alpnNegotiationFailed => "channel TLS did not negotiate h2"
  | .cleanupFailed => "channel failed-attempt cleanup failed"
  | .initializationFailed => "channel initialization failed"

end OpenError

instance : ToString OpenError := ⟨OpenError.render⟩

/-!
An initialization failure is an immutable, data-only diagnostic. Transient
transport failure and clean local setup failure may admit a later generation;
endpoint and local trust policy plus connector-contract failures are terminal;
and cleanup uncertainty is structural. Exact raw-resource authority never
appears in this freely copyable value. Direct opening returns a separate opaque
`OwnedOpenFailure`, while the lazy shared initializer transfers that owner's
authority into supervisor state before publishing this diagnostic to waiters.
-/

inductive OpenFailureDisposition where
  | retryableTransport
  | retryableLocal
  | terminalPolicy
  | supervisorInvariant
  | cleanupUncertain
deriving BEq, DecidableEq, Repr

private structure ClaimedCleanupOwner (Resource : Type) where
  resource : Resource

private inductive TransportOpenFailure where
  | resolution
  | connectionAttemptsFailed
  | alpnNegotiationFailed
deriving BEq, DecidableEq

private inductive PolicyOpenFailure where
  | plaintextRequiresLoopback
  | tooManyAddresses
  | trustAnchors
deriving BEq, DecidableEq

private inductive PrimaryOpenFailure where
  | transport (failure : TransportOpenFailure)
  | localSetup
  | policy (failure : PolicyOpenFailure)
  | invariant
deriving BEq, DecidableEq

private inductive OpenFailureKind where
  | ownerFree (primary : PrimaryOpenFailure)
  | cleanupFailed (primary : PrimaryOpenFailure)
deriving BEq, DecidableEq

private def OpenFailureKind.hasCleanupUncertainty :
    OpenFailureKind → Bool
  | .ownerFree _ => false
  | .cleanupFailed _ => true

structure OpenFailure where
  private mk ::
  private kind : OpenFailureKind
deriving BEq, DecidableEq

private inductive OwnedCleanupState (Resource : Type) where
  | available (owner : ClaimedCleanupOwner Resource)
  /--
  The connector already returned ambiguously.  The raw value remains reachable
  solely so it is not silently discarded, but no close or transfer authority
  survives this transition.
  -/
  | quarantined (owner : ClaimedCleanupOwner Resource)
  | transferred

/-!
The direct-opening boundary keeps exact cleanup authority in this opaque
wrapper, separate from its immutable diagnostic. Copies alias one internal
state cell; only `OwnedOpenFailure.close` or the private shared-supervisor
transfer may change that cell. Merely reading or copying `failure` is inert.
-/
structure OwnedOpenFailure (Resource : Type) where
  private mk ::
  failure : OpenFailure
  private cleanupState? : Option (IO.Ref (OwnedCleanupState Resource))
  private coherent :
    failure.kind.hasCleanupUncertainty = cleanupState?.isSome

inductive OpenFailureCustodyPhase where
  | ownerFree
  | available
  | quarantined
  | transferred
deriving BEq, DecidableEq, Repr

private def openFailureSnapshotCoherent
    (failure : OpenFailure) (custody : OpenFailureCustodyPhase) : Prop :=
  match custody with
  | .ownerFree => failure.kind.hasCleanupUncertainty = false
  | .available | .quarantined | .transferred =>
      failure.kind.hasCleanupUncertainty = true

structure OwnedOpenFailureSnapshot where
  private mk ::
  failure : OpenFailure
  custody : OpenFailureCustodyPhase
  private certified : openFailureSnapshotCoherent failure custody

namespace OpenFailureCustodyPhase

/-- Exact number of raw resource values still represented by this phase. -/
def physicalOwnerCount : OpenFailureCustodyPhase → Nat
  | .available | .quarantined => 1
  | .ownerFree | .transferred => 0

theorem physicalOwnerCount_le_one (phase : OpenFailureCustodyPhase) :
    phase.physicalOwnerCount ≤ 1 := by
  cases phase <;> decide

/-- Only the unpublished exact owner may move into shared supervision. -/
def cleanupAuthorized : OpenFailureCustodyPhase → Bool
  | .available => true
  | .ownerFree | .quarantined | .transferred => false

theorem cleanup_authorized_iff_available
    (phase : OpenFailureCustodyPhase) :
    phase.cleanupAuthorized = true ↔ phase = .available := by
  cases phase <;> simp [cleanupAuthorized]

end OpenFailureCustodyPhase

namespace OwnedOpenFailureSnapshot

/--
Snapshot equality is observational only: equal diagnostics and phases do not
identify, merge, or compare the exact cleanup owners hidden by two wrappers.
-/
instance : BEq OwnedOpenFailureSnapshot where
  beq left right :=
    left.failure == right.failure && left.custody == right.custody

def physicalOwnerCount (snapshot : OwnedOpenFailureSnapshot) : Nat :=
  snapshot.custody.physicalOwnerCount

theorem physicalOwnerCount_le_one (snapshot : OwnedOpenFailureSnapshot) :
    snapshot.physicalOwnerCount ≤ 1 :=
  snapshot.custody.physicalOwnerCount_le_one

def cleanupAuthorized (snapshot : OwnedOpenFailureSnapshot) : Bool :=
  snapshot.custody.cleanupAuthorized

theorem cleanup_authorized_iff_available
    (snapshot : OwnedOpenFailureSnapshot) :
    snapshot.cleanupAuthorized = true ↔ snapshot.custody = .available :=
  snapshot.custody.cleanup_authorized_iff_available

end OwnedOpenFailureSnapshot

namespace OpenFailure

private def primary (failure : OpenFailure) : PrimaryOpenFailure :=
  match failure.kind with
  | .ownerFree primary | .cleanupFailed primary => primary

end OpenFailure

namespace PrimaryOpenFailure

private def error : PrimaryOpenFailure → OpenError
  | .transport .resolution => .resolution
  | .transport .connectionAttemptsFailed => .connectionAttemptsFailed
  | .transport .alpnNegotiationFailed => .alpnNegotiationFailed
  | .localSetup | .invariant => .initializationFailed
  | .policy .plaintextRequiresLoopback => .plaintextRequiresLoopback
  | .policy .tooManyAddresses => .tooManyAddresses
  | .policy .trustAnchors => .trustAnchors

private def disposition :
    PrimaryOpenFailure → OpenFailureDisposition
  | .transport _ => .retryableTransport
  | .localSetup => .retryableLocal
  | .policy _ => .terminalPolicy
  | .invariant => .supervisorInvariant

private def isInvariant :
    PrimaryOpenFailure → Bool
  | .invariant => true
  | .transport _ | .localSetup | .policy _ => false

end PrimaryOpenFailure

namespace OpenFailure

/-- The sanitized opening cause before failed cleanup made retry unsafe. -/
def primaryError (failure : OpenFailure) : OpenError :=
  failure.primary.error

/-- Retry/policy/invariant class of the sanitized cause before cleanup. -/
def primaryDisposition
    (failure : OpenFailure) : OpenFailureDisposition :=
  failure.primary.disposition

def error (failure : OpenFailure) : OpenError :=
  match failure.kind with
  | .ownerFree primary => primary.error
  | .cleanupFailed _ => .cleanupFailed

def disposition (failure : OpenFailure) : OpenFailureDisposition :=
  match failure.kind with
  | .ownerFree primary => primary.disposition
  | .cleanupFailed _ => .cleanupUncertain

/-- Whether failed cleanup makes this opening outcome terminal and nonretryable. -/
def hasCleanupUncertainty (failure : OpenFailure) : Bool :=
  match failure.kind with
  | .ownerFree _ => false
  | .cleanupFailed _ => true

def shouldRetry (failure : OpenFailure) : Bool :=
  match failure.kind with
  | .ownerFree (.transport _)
  | .ownerFree .localSetup => true
  | .ownerFree (.policy _)
  | .ownerFree .invariant
  | .cleanupFailed _ => false

def render (failure : OpenFailure) : String :=
  failure.error.render

/-- Cleanup uncertainty is encoded directly in the immutable failure shape. -/
theorem error_eq_cleanupFailed_iff (failure : OpenFailure) :
    failure.error = .cleanupFailed ↔
      failure.hasCleanupUncertainty = true := by
  cases kindEq : failure.kind with
  | ownerFree primary =>
      cases primary with
      | transport transport =>
          cases transport <;>
            simp [error, hasCleanupUncertainty, kindEq,
              PrimaryOpenFailure.error]
      | localSetup =>
          simp [error, hasCleanupUncertainty, kindEq,
            PrimaryOpenFailure.error]
      | policy policy =>
          cases policy <;>
            simp [error, hasCleanupUncertainty, kindEq,
              PrimaryOpenFailure.error]
      | invariant =>
          simp [error, hasCleanupUncertainty, kindEq,
            PrimaryOpenFailure.error]
  | cleanupFailed primary =>
      simp [error, hasCleanupUncertainty, kindEq]

/-- The only retryable dispositions are the two structurally clean variants. -/
theorem shouldRetry_iff (failure : OpenFailure) :
    failure.shouldRetry = true ↔
      failure.disposition = .retryableTransport ∨
      failure.disposition = .retryableLocal := by
  cases kindEq : failure.kind with
  | ownerFree primary =>
      cases primary with
      | transport transport =>
          cases transport <;>
            simp [shouldRetry, disposition, kindEq,
              PrimaryOpenFailure.disposition]
      | localSetup =>
          simp [shouldRetry, disposition, kindEq,
            PrimaryOpenFailure.disposition]
      | policy policy =>
          cases policy <;>
            simp [shouldRetry, disposition, kindEq,
              PrimaryOpenFailure.disposition]
      | invariant =>
          simp [shouldRetry, disposition, kindEq,
            PrimaryOpenFailure.disposition]
  | cleanupFailed primary =>
      simp [shouldRetry, disposition, kindEq]

end OpenFailure

namespace OwnedOpenFailureSnapshot

/-- Certified diagnostic/custody coherence of the one-hot snapshot. -/
def Invariant (snapshot : OwnedOpenFailureSnapshot) : Prop :=
  match snapshot.custody with
  | .ownerFree => snapshot.failure.hasCleanupUncertainty = false
  | .available | .quarantined | .transferred =>
      snapshot.failure.hasCleanupUncertainty = true

theorem invariant (snapshot : OwnedOpenFailureSnapshot) :
    snapshot.Invariant := by
  have certified := snapshot.certified
  cases custodyEq : snapshot.custody <;>
    simpa [Invariant, custodyEq, openFailureSnapshotCoherent,
      OpenFailure.hasCleanupUncertainty,
      OpenFailureKind.hasCleanupUncertainty] using certified

theorem ownerFree_iff (snapshot : OwnedOpenFailureSnapshot) :
    snapshot.custody = .ownerFree ↔
      snapshot.failure.hasCleanupUncertainty = false := by
  have certified := snapshot.invariant
  cases phaseEq : snapshot.custody <;>
    simp_all [Invariant]

theorem cleanupShaped_iff (snapshot : OwnedOpenFailureSnapshot) :
    (snapshot.custody = .available ∨
        snapshot.custody = .quarantined ∨
        snapshot.custody = .transferred) ↔
      snapshot.failure.hasCleanupUncertainty = true := by
  have certified := snapshot.invariant
  cases phaseEq : snapshot.custody <;>
    simp_all [Invariant]

end OwnedOpenFailureSnapshot

instance : ToString OpenFailure := ⟨OpenFailure.render⟩

/-- Never render the retained resource or connector diagnostics. -/
instance : Repr OpenFailure where
  reprPrec failure _ := Std.Format.text failure.render

namespace OwnedOpenFailure

def error (failure : OwnedOpenFailure Resource) : OpenError :=
  failure.failure.error

def primaryError (failure : OwnedOpenFailure Resource) : OpenError :=
  failure.failure.primaryError

def disposition
    (failure : OwnedOpenFailure Resource) : OpenFailureDisposition :=
  failure.failure.disposition

def primaryDisposition
    (failure : OwnedOpenFailure Resource) : OpenFailureDisposition :=
  failure.failure.primaryDisposition

def shouldRetry (failure : OwnedOpenFailure Resource) : Bool :=
  failure.failure.shouldRetry

def hasCleanupUncertainty
    (failure : OwnedOpenFailure Resource) : Bool :=
  failure.failure.hasCleanupUncertainty

def render (failure : OwnedOpenFailure Resource) : String :=
  failure.failure.render

def snapshot (failure : OwnedOpenFailure Resource) :
    BaseIO OwnedOpenFailureSnapshot := do
  match cleanupEq : failure.cleanupState? with
  | none =>
      have certified :
          failure.failure.kind.hasCleanupUncertainty = false := by
        simpa [cleanupEq] using failure.coherent
      pure (.mk failure.failure .ownerFree certified)
  | some state =>
      have certified :
          failure.failure.kind.hasCleanupUncertainty = true := by
        simpa [cleanupEq] using failure.coherent
      match ← state.get with
      | .available _ => pure (.mk failure.failure .available certified)
      | .quarantined _ => pure (.mk failure.failure .quarantined certified)
      | .transferred => pure (.mk failure.failure .transferred certified)

def hasCleanupCustody (failure : OwnedOpenFailure Resource) : BaseIO Bool := do
  pure ((← failure.snapshot).cleanupAuthorized)

/-- Observation only: this phase retains a raw value but grants no effect. -/
def hasQuarantinedCustody
    (failure : OwnedOpenFailure Resource) : BaseIO Bool := do
  pure ((← failure.snapshot).custody == .quarantined)

private inductive CustodyView (Resource : Type) where
  | ownerFree (primary : PrimaryOpenFailure)
  | cleanupUncertain
      (primary : PrimaryOpenFailure)
      (owner : ClaimedCleanupOwner Resource)
  | cleanupQuarantined (primary : PrimaryOpenFailure)
  | cleanupAliased (primary : PrimaryOpenFailure)

private def takeCustodyView (failure : OwnedOpenFailure Resource) :
    BaseIO (CustodyView Resource) :=
  match failure.cleanupState? with
  | none => pure (.ownerFree failure.failure.primary)
  | some state => do
      state.modifyGet fun
        | .available owner =>
            (.cleanupUncertain failure.failure.primary owner, .transferred)
        | .quarantined owner =>
            (.cleanupQuarantined failure.failure.primary,
              .quarantined owner)
        | .transferred =>
            (.cleanupAliased failure.failure.primary, .transferred)

end OwnedOpenFailure

instance : ToString (OwnedOpenFailure Resource) :=
  ⟨OwnedOpenFailure.render⟩

/-- Never traverse or render retained raw cleanup authority. -/
instance : Repr (OwnedOpenFailure Resource) where
  reprPrec failure _ := Std.Format.text failure.render

inductive CallError where
  | channelDraining
  | channelClosed
  /-- An exact-generation capability was used after its callback returned. -/
  | scopeClosed
  /-- The local monotonic deadline won and the exact call was joined. -/
  | localDeadlineExceeded
  /--
  Local owner cancellation won. Any admitted inner call was joined; an
  unfinished lazy initializer remains staged for a later waiter or close owner.
  -/
  | ownerCancelled
  | actionFailed
  | supervisorInvariant
  | requestEncoding
  /--
  The exact terminal status and optional binary status details returned by the
  peer. Delivery adapters preserve both values at their public gRPC boundary.
  -/
  | rpc (status : Grpc.Status) (statusDetails : Option ByteArray := none)
  | responseDecoding
  | callActionFailed
  | cleanupUncertain

namespace CallError

/-- Opaque peer-provided `grpc-status-details-bin` bytes, when unambiguous. -/
def statusDetails? : CallError → Option ByteArray
  | .rpc _ statusDetails => statusDetails
  | _ => none

def render : CallError → String
  | .channelDraining => "transport channel is draining"
  | .channelClosed => "transport channel is closed"
  | .scopeClosed => "transport generation scope is closed"
  | .localDeadlineExceeded => "transport local deadline exceeded"
  | .ownerCancelled => "transport call was cancelled by its local owner"
  | .actionFailed => "transport call action failed"
  | .supervisorInvariant => "transport call supervisor invariant failed"
  | .requestEncoding => "transport request encoding failed"
  | .rpc status _ =>
      s!"transport RPC failed with status code {status.code.toNat}"
  | .responseDecoding => "transport response decoding failed"
  | .callActionFailed => "transport call action failed after cleanup"
  | .cleanupUncertain =>
      "transport call cleanup was uncertain; the channel was closed"

end CallError

instance : ToString CallError := ⟨CallError.render⟩

/--
Generic diagnostics remain bounded: consumers that deliberately propagate a
peer status must inspect the `rpc` payload instead of accidentally rendering a
possibly sensitive server description.
-/
instance : Repr CallError where
  reprPrec error _ := Std.Format.text (CallError.render error)

namespace OpenFailureDisposition

/--
grpc-java performs resolution and transport establishment inside the call, so
clean failures in those phases surface as `UNAVAILABLE`. Clean local setup
remains a local action error; endpoint and trust preparation policy are
terminal for the shared owner; connector contract violations are supervisor
failures; and cleanup uncertainty is never made retryable.
-/
def callError : OpenFailureDisposition → CallError
  | .retryableTransport =>
      .rpc (Grpc.Status.error .unavailable
        "transport opening failed")
  | .retryableLocal | .terminalPolicy => .actionFailed
  | .supervisorInvariant => .supervisorInvariant
  | .cleanupUncertain => .cleanupUncertain

end OpenFailureDisposition

namespace OpenFailure

def callError (failure : OpenFailure) : CallError :=
  failure.disposition.callError

end OpenFailure

inductive CloseError where
  | transport
  | supervisorInvariant
  | completionDropped
deriving BEq, DecidableEq, Repr

/--
A bounded observation of the one shared close generation. `stillClosing`
retains all exact cleanup/resource custody; its close driver is either a task
retained by the shared supervisor or one starter's structural publication
obligation. `needsDriver` records that no close driver was published and
authoritative needs-owner custody was available at the observation's final
state snapshot; it is not itself a reservation, so a concurrent caller may
take that custody immediately afterward. Neither nonterminal result claims
that transport cleanup completed.
-/
inductive CloseObservation where
  | settled (result : Except CloseError Unit)
  | stillClosing
  | needsDriver
deriving Repr

/--
Default per-component production observation budget for a shared transport
generation.  A host application's independent process-wide watchdog, when
present, remains the hard bound if earlier cleanup has already consumed the
apparent margin.  A nonterminal observation leaves the staged owner graph
holding the exact channel capability.
-/
def productionCloseBudgetMilliseconds : Nat := 10_000

namespace CloseError

def render : CloseError → String
  | .transport => "transport close failed"
  | .supervisorInvariant => "transport close supervisor invariant failed"
  | .completionDropped => "transport close completion was dropped"

end CloseError

instance : ToString CloseError := ⟨CloseError.render⟩

namespace OwnedOpenFailure

/--
Classify direct cleanup custody without retrying a connector close that already
returned ambiguously. The first close irreversibly quarantines the raw value;
later closes return the same cached result. Quarantine is observation-only and
cannot subsequently transfer cleanup authority into a shared supervisor. A
wrapper with no cleanup authority closes cleanly. A private wrapper whose
authority was already transferred to a shared supervisor fails closed if
misused directly.
-/
def close (failure : OwnedOpenFailure Resource) :
    BaseIO (Except CloseError Unit) := do
  match failure.cleanupState? with
  | none => pure (.ok ())
  | some state =>
      state.modifyGet fun
        | .available owner => (.error .transport, .quarantined owner)
        | .quarantined owner => (.error .transport, .quarantined owner)
        | .transferred => (.error .supervisorInvariant, .transferred)

def callError (failure : OwnedOpenFailure Resource) : CallError :=
  failure.failure.callError

end OwnedOpenFailure

structure Subchannel (Resource : Type) where
  private mk ::
  private configuration : ManagedChannel.Config
  private owner : ChannelOwner.Owner Resource

namespace Subchannel

def endpoint (channel : Subchannel Resource) : Endpoint :=
  channel.configuration.endpoint

def phase (channel : Subchannel Resource) :
    IO ChannelLease.Phase := do
  pure (← channel.owner.snapshot).phase

end Subchannel

private def syntacticLoopback (endpoint : Endpoint) : Bool :=
  match endpoint.host with
  | .name name => name.val == "localhost"
  | .ipv4 address => (toString address).startsWith "127."
  | .ipv6 address => toString address == "::1"

private def closeAttempt
    (connector : Connector Resource) (resource : Resource) :
    IO (Option Resource) := do
  try
    connector.close resource
    pure none
  catch _ =>
    pure (some resource)

private def transportOpenFailure
    (failure : TransportOpenFailure) : OwnedOpenFailure Resource :=
  .mk (.mk (.ownerFree (.transport failure))) none (by rfl)

private def localOpenFailure : OwnedOpenFailure Resource :=
  .mk (.mk (.ownerFree .localSetup)) none (by rfl)

private def policyOpenFailure
    (failure : PolicyOpenFailure) : OwnedOpenFailure Resource :=
  .mk (.mk (.ownerFree (.policy failure))) none (by rfl)

private def invariantOpenFailure : OwnedOpenFailure Resource :=
  .mk (.mk (.ownerFree .invariant)) none (by rfl)

private def cleanupOpenFailure
    (primary : PrimaryOpenFailure)
    (resource : Resource) : BaseIO (OwnedOpenFailure Resource) := do
  let state ← IO.mkRef
    (OwnedCleanupState.available ({ resource } : ClaimedCleanupOwner Resource))
  pure (.mk (.mk (.cleanupFailed primary)) (some state) (by rfl))

private def adopt
    (configuration : ManagedChannel.Config)
    (connector : Connector Resource) (resource : Resource) :
    IO (Except (OwnedOpenFailure Resource) (Subchannel Resource)) := do
  try
    connector.beforeOwnerAdoption
    let owner ← ChannelOwner.Owner.create resource {
      close := connector.close
    }
    pure (.ok (.mk configuration owner))
  catch _ =>
    match ← closeAttempt connector resource with
    | none =>
        pure (.error localOpenFailure)
    | some retained =>
        pure (.error (← cleanupOpenFailure .localSetup retained))

namespace RegistrationReceipt

private def create (resource : Resource) : BaseIO (RegistrationReceipt Resource) :=
  .mk <$> IO.mkRef (some resource)

private def take
    (receipt : RegistrationReceipt Resource) : BaseIO (Option Resource) :=
  receipt.cell.modifyGet fun current =>
    (current, none)

private def same
    (left right : RegistrationReceipt Resource) : BaseIO Bool :=
  left.cell.ptrEq right.cell

end RegistrationReceipt

private inductive RegistrationJournalState (Resource : Type) where
  | open (receipt : Option (RegistrationReceipt Resource) := none)
  | sealed

private def registerResource
    (journal : IO.Ref (RegistrationJournalState Resource))
    (resource : Resource) : BaseIO (Option (RegistrationReceipt Resource)) := do
  let receipt ← RegistrationReceipt.create resource
  let accepted ← journal.modifyGet fun
    | .open none => (true, .open (some receipt))
    | current => (false, current)
  if accepted then pure (some receipt) else pure none

private def sealRegistration
    (journal : IO.Ref (RegistrationJournalState Resource)) :
    BaseIO (Option (RegistrationReceipt Resource)) :=
  journal.modifyGet fun
    | .open receipt => (receipt, .sealed)
    | .sealed => (none, .sealed)

private partial def tryAddresses
    (configuration : ManagedChannel.Config)
    (connector : Connector Resource)
    (credentials : ChannelCredentials)
    (addresses : List NameResolver.Address)
    (sawAlpnFailure : Bool := false) :
    IO (Except (OwnedOpenFailure Resource) (Subchannel Resource)) := do
  match addresses with
  | [] =>
      if sawAlpnFailure then
        pure (.error (transportOpenFailure .alpnNegotiationFailed))
      else
        pure (.error (transportOpenFailure .connectionAttemptsFailed))
  | address :: remaining =>
      let attempt : ConnectAttempt := {
        address
        authority := configuration.endpoint.authority
        scheme := configuration.endpoint.scheme.text
        credentials
        maxSendMessageBytes := configuration.maxSendMessageBytes
        maxReceiveMessageBytes := configuration.maxReceiveMessageBytes
      }
      let journal ← IO.mkRef
        (RegistrationJournalState.open
          (none : Option (RegistrationReceipt Resource)))
      let register := registerResource journal
      let outcome : Except IO.Error (ConnectResult Resource) ← try
        pure (Except.ok (← connector.connect attempt register))
      catch error =>
        pure (Except.error error)
      -- Seal before inspecting the result. A connector-owned task that calls
      -- the registrar later receives `none` and cannot transfer a resource
      -- into an attempt whose outcome is already being settled.
      let registered ← sealRegistration journal
      let failedAttempt :
          IO (Except (OwnedOpenFailure Resource) (Subchannel Resource)) := do
        match registered with
        | some receipt =>
            match ← receipt.take with
            | some resource =>
                match ← closeAttempt connector resource with
                | some retained =>
                    pure (.error (← cleanupOpenFailure
                      (.transport .connectionAttemptsFailed)
                      retained))
                | none =>
                    tryAddresses configuration connector credentials remaining
                      sawAlpnFailure
            | none =>
                pure (.error invariantOpenFailure)
        | none =>
            tryAddresses configuration connector credentials remaining
              sawAlpnFailure
      match outcome with
      | .error _ | .ok .failed => failedAttempt
      | .ok (.connected returned) =>
          let resource ← match registered with
            | none =>
                return .error invariantOpenFailure
            | some accepted =>
                if ← returned.same accepted then
                  match ← returned.take with
                  | some resource => pure resource
                  | none =>
                      return .error invariantOpenFailure
                else
                  -- The returned receipt belongs to some other journal. Do
                  -- not steal its capability; close only this attempt's exact
                  -- accepted resource and fail the connector boundary closed.
                  match ← accepted.take with
                  | some resource =>
                      match ← closeAttempt connector resource with
                      | some retained =>
                          return .error (← cleanupOpenFailure
                            .invariant retained)
                      | none =>
                          return .error invariantOpenFailure
                  | none =>
                      return .error invariantOpenFailure
          match credentials with
          | .plaintext =>
              adopt configuration connector resource
          | .tls _ =>
              let selected ←
                try
                  some <$> connector.selectedAlpn resource
                catch _ =>
                  pure none
              match selected with
              | some (some protocol) =>
                  if protocol == requiredAlpn then
                    adopt configuration connector resource
                  else
                    match ← closeAttempt connector resource with
                    | some retained =>
                        pure (.error (← cleanupOpenFailure
                          (.transport .alpnNegotiationFailed)
                          retained))
                    | none =>
                        tryAddresses configuration connector credentials remaining true
              | some none | none =>
                  match ← closeAttempt connector resource with
                  | some retained =>
                      pure (.error (← cleanupOpenFailure
                        (.transport .alpnNegotiationFailed)
                        retained))
                  | none =>
                      tryAddresses configuration connector credentials remaining true

private def resolved
    (dependencies : ManagedChannel.Dependencies Resource) (endpoint : Endpoint) :
    IO (Except (OwnedOpenFailure Resource)
      (Array NameResolver.Address)) := do
  try
    match ← dependencies.resolve endpoint with
    | .ok addresses => pure (.ok addresses)
    | .error (.tooManyAddresses _) =>
        pure (.error (policyOpenFailure .tooManyAddresses))
    | .error _ =>
        pure (.error (transportOpenFailure .resolution))
  catch _ =>
    pure (.error (transportOpenFailure .resolution))

private def trustBundle
    (dependencies : ManagedChannel.Dependencies Resource) :
    IO (Except (OwnedOpenFailure Resource)
      TrustAnchors.Bundle) := do
  try
    match ← dependencies.loadTrust with
    | .ok bundle => pure (.ok bundle)
    | .error _ =>
        pure (.error (policyOpenFailure .trustAnchors))
  catch _ =>
    pure (.error (policyOpenFailure .trustAnchors))

namespace Subchannel

/--
Create the one shared channel. No credential metadata is constructed during
setup.
-/
def openWith
    (dependencies : ManagedChannel.Dependencies Resource)
    (configuration : ManagedChannel.Config) :
    IO (Except (OwnedOpenFailure Resource) (Subchannel Resource)) := do
  let endpoint := configuration.endpoint
  let credentials ←
    if endpoint.useTls then
      let trust ← match ← trustBundle dependencies with
        | .ok trust => pure trust
        | .error failure => return .error failure
      let some serverName := endpoint.serverName
        | return .error invariantOpenFailure
      pure (.tls {
        serverName
        alpnProtocols := #[requiredAlpn]
        trustAnchorsPEM := trust.pem
        verifyHostname := true
      })
    else
      if !syntacticLoopback endpoint then
        return .error (policyOpenFailure .plaintextRequiresLoopback)
      pure .plaintext
  let addresses ← match ← resolved dependencies endpoint with
    | .ok addresses => pure addresses
    | .error failure => return .error failure
  if addresses.size > maximumConnectionAttempts then
    pure (.error (policyOpenFailure .tooManyAddresses))
  else if !endpoint.useTls && !addresses.all (·.isLoopback) then
    pure (.error (policyOpenFailure .plaintextRequiresLoopback))
  else if addresses.isEmpty then
    pure (.error (transportOpenFailure .connectionAttemptsFailed))
  else
    tryAddresses configuration dependencies.connector credentials addresses.toList

end Subchannel

private def grpcConfiguration (attempt : ConnectAttempt) : Grpc.Client.Config := {
  address := attempt.address.socketAddress
  authority := attempt.authority
  scheme := attempt.scheme
  maxSendMessageSize := attempt.maxSendMessageBytes
  maxReceiveMessageSize := attempt.maxReceiveMessageBytes
}

/-- Run grpc-lean's cooperative close to completion at the IO-owned channel boundary. -/
private def closeGrpcConnection (connection : Grpc.Client.Connection) : IO Unit :=
  Async.block (Grpc.Client.close connection)

def Connector.production : Connector Grpc.Client.Connection := {
  connect := fun attempt register => do
    try
      let connection ← match attempt.credentials with
        | .plaintext =>
            Grpc.Client.connect (grpcConfiguration attempt)
        | .tls policy =>
            Grpc.Client.connectTls (grpcConfiguration attempt) {
              serverName := some policy.serverName
              alpnProtocols := policy.alpnProtocols
              trustAnchorsPEM := some policy.trustAnchorsPEM
              verifyHostname := policy.verifyHostname
            }
      -- `register` is `BaseIO`: once the FFI returns a live connection, no
      -- throwable Lean effect occurs before the channel journals ownership.
      let some receipt ← register connection
        | closeGrpcConnection connection
          return .failed
      pure (.connected receipt)
    catch _ =>
      -- grpc-lean owns and shuts down pre-Connection sockets/sessions before
      -- throwing. Every resource it returns is explicitly closed by this
      -- adapter before fallback or rejection.
      pure .failed
  selectedAlpn := fun connection =>
    match connection.tls with
    | some session => Grpc.Tls.ClientSession.alpnSelected session
    | none => pure none
  close := closeGrpcConnection
}

def ManagedChannel.Dependencies.production : ManagedChannel.Dependencies Grpc.Client.Connection := {
  resolve := NameResolver.resolve
  loadTrust := TrustAnchors.load
  connector := Connector.production
}

def Subchannel.connect
    (configuration : ManagedChannel.Config) :
    IO (Except (OwnedOpenFailure Grpc.Client.Connection)
      (Subchannel Grpc.Client.Connection)) :=
  Subchannel.openWith ManagedChannel.Dependencies.production configuration

private def mapUseError :
    ChannelOwner.UseError → CallError
  | .unavailable .draining => .channelDraining
  | .unavailable .closed => .channelClosed
  | .action _ => .actionFailed
  | .cleanupUncertain => .cleanupUncertain
  | .supervisorInvariant => .supervisorInvariant

private def mapCallError : UnaryCall.Error → CallError
  | .requestEncoding => .requestEncoding
  | .localDeadlineExceeded => .localDeadlineExceeded
  | .ownerCancelled => .ownerCancelled
  | .rpc status statusDetails => .rpc status statusDetails
  | .responseDecoding => .responseDecoding
  | .actionFailed => .callActionFailed
  | .cleanupUncertain => .cleanupUncertain

namespace Subchannel

/--
Trusted injectable seam used by deterministic lifecycle tests. The exact
shared-owner lease surrounds the whole action, including its local
deadline/cancellation.

Production callers use `unary`; because this hook is generic in `Response`, a
malicious action could otherwise return the leased `Resource` as its response.
-/
def unaryWith
    (channel : Subchannel Resource)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) := do
  match ← channel.owner.withResourceChecked fun resource => do
      let result ← action resource channel.configuration
      match result with
      | .error .cleanupUncertain =>
          pure .cleanupUncertain
      | result =>
          pure (.release result) with
  | .error error => pure (.error (mapUseError error))
  | .ok (.error error) => pure (.error (mapCallError error))
  | .ok (.ok response) => pure (.ok response)

/-- Run a generated typed unary RPC with an explicit fresh relative deadline. -/
def unaryWithDeadline
    (channel : Subchannel Grpc.Client.Connection)
    (deadline : RpcDeadline)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  unaryWith channel fun connection configuration =>
    (UnaryCall.unary
      connection { configuration with deadline } method encode decode request).block

/--
Run a generated typed unary RPC whose terminal owner can cancel and join the
exact active call before the relative deadline expires.
-/
def unaryWithDeadlineAndCancellation
    (channel : Subchannel Grpc.Client.Connection)
    (deadline : RpcDeadline)
    (cancellation : Cancellation)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  unaryWith channel fun connection configuration =>
    (UnaryCall.unaryCancellable
      connection { configuration with deadline } (some cancellation)
      method encode decode request).block

/-- Run a cancellable unary RPC with the channel's default deadline. -/
def unaryWithCancellation
    (channel : Subchannel Grpc.Client.Connection)
    (cancellation : Cancellation)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  unaryWithDeadlineAndCancellation channel channel.configuration.deadline
    cancellation method encode decode request

/-- Run a generated typed unary RPC with the channel's default call policy. -/
def unary
    (channel : Subchannel Grpc.Client.Connection)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  unaryWithDeadline channel channel.configuration.deadline
    method encode decode request

def close (channel : Subchannel Resource) : IO (Except CloseError Unit) := do
  match ← channel.owner.close with
  | .ok () => pure (.ok ())
  | .error (.transport _) => pure (.error .transport)
  | .error (.supervisorInvariant _) => pure (.error .supervisorInvariant)
  | .error .completionDropped => pure (.error .completionDropped)

end Subchannel

/-! ## Lazy reconnecting shared channel -/

private abbrev InitializationTask (Resource : Type) :=
  Task (Except IO.Error (Except OpenFailure (Subchannel Resource)))

private abbrev CloseTask := Task (Except IO.Error Unit)

private structure PendingInitialization (Resource : Type) where
  generation : Nat
  task : InitializationTask Resource
  completion : Cancellation

/--
One terminal initialization outcome retained by the shared supervisor. Every
constructor carries the generation whose pending task was consumed.
Capability-free policy evidence preserves caller precedence without making a
clean close dirty. A successfully transferred owned failure carries the exact
raw capability; an impossible already-transferred observation carries explicit
uncertainty without fabricating one.
-/
private inductive FailedInitialization (Resource : Type) where
  /-- Capability-free policy evidence retained while the shared owner drains. -/
  | terminalPolicy
      (generation : Nat)
      (failure : PolicyOpenFailure)
  | cleanupUncertain
      (generation : Nat)
      (primary : PrimaryOpenFailure)
      (owner : ClaimedCleanupOwner Resource)
  | cleanupAuthorityMissing
      (generation : Nat) (primary : PrimaryOpenFailure)
  | taskUncertain (generation : Nat)
  | connectorInvariant (generation : Nat)

/--
An owner-bearing direct failure observed after its one-hot initialization slot
no longer matches. This is unreachable for a well-formed shared initializer,
but the exact capability still cannot be discarded. Each entry exists only
after a successful authority transfer, so copied diagnostics add nothing while
distinct direct owners remain distinct even when their generations match.
-/
private structure QuarantinedInitializationOwner (Resource : Type) where
  generation : Nat
  primary : PrimaryOpenFailure
  owner : ClaimedCleanupOwner Resource

/--
The single initialization slot. A terminal transfer may retain its exact
pending task until that task is observed complete; the optional task and one
terminal outcome are bounded and generation-coherent in the same constructor.
-/
private inductive InitializationState (Resource : Type) where
  | idle
  | pending (initialization : PendingInitialization Resource)
  | failed
      (failure : FailedInitialization Resource)
      (pending? : Option (PendingInitialization Resource))

private structure ConnectedGeneration (Resource : Type) where
  generation : Nat
  channel : Subchannel Resource

private structure CloseClaim where
  decision : ChannelLease.BeginCloseDecision
  drained : Bool

/-!
An unlocked close-task allocation carries an opaque ticket. The state-owned
`starting*` constructor is the authority to publish that exact allocation;
pointer identity prevents a delayed starter from consuming a later attempt.
-/
private structure CloseStarterTicket where
  identity : IO.Ref Unit

namespace CloseStarterTicket

private def create : BaseIO CloseStarterTicket :=
  .mk <$> IO.mkRef ()

private def same (left right : CloseStarterTicket) : BaseIO Bool :=
  left.identity.ptrEq right.identity

end CloseStarterTicket

/--
The one authoritative close-driver slot. Unlike an external publication bit,
this sum retains the exact detached task handle in the same mutex value as the
resource graph. `inlineTerminal` records the only driver form with no task
handle after it has published terminal completion; detached tasks remain
reachable after termination.
-/
private inductive CloseDriverState where
  | absent
  | needsOwner
  /-- Bounded task allocation may still restore `needsOwner`. -/
  | startingBounded (ticket : CloseStarterTicket)
  /-- A joining starter owns fallback through terminal completion. -/
  | startingJoining (ticket : CloseStarterTicket)
  | detached (ticket : CloseStarterTicket) (owner : CloseTask)
  | inline
  | inlineTerminal

private def CloseDriverState.publishClaim
    (driver : CloseDriverState)
    (decision : ChannelLease.BeginCloseDecision) :
    CloseDriverState :=
  if decision == ChannelLease.BeginCloseDecision.claimed then
    match driver with
    | .absent => .needsOwner
    | .needsOwner | .startingBounded _ | .startingJoining _
    | .detached _ _ | .inline | .inlineTerminal => driver
  else
    driver

private def CloseDriverState.isNeedsOwner : CloseDriverState → Bool
  | .needsOwner => true
  | .absent | .startingBounded _ | .startingJoining _
  | .detached _ _ | .inline | .inlineTerminal => false

private def CloseDriverState.starting : CloseDriverState → Bool
  | .startingBounded _ | .startingJoining _ | .inline => true
  | .absent | .needsOwner | .detached _ _ | .inlineTerminal => false

private def CloseDriverState.hasDetachedTask : CloseDriverState → Bool
  | .detached _ _ => true
  | .absent | .needsOwner | .startingBounded _ | .startingJoining _
  | .inline | .inlineTerminal => false

/-!
The shared/lazy layer has already transferred any exact cleanup capability
from `OwnedOpenFailure` into `SharedState`, so it returns only a data-only
diagnostic to a caller. Its projection remains structural nonetheless: retryable
constructors cannot carry close custody, while each terminal constructor owns
the optional close claim created by the authoritative state transition.  This
prevents a freely paired `disposition + claim` record from describing an
impossible retryable close claim or misclassifying terminal evidence.
-/
private inductive OpeningFailure where
  | retryableTransport
  | retryableLocal
  | terminalPolicy (closeClaim? : Option CloseClaim)
  | supervisorInvariant (closeClaim? : Option CloseClaim)
  | cleanupUncertain (closeClaim? : Option CloseClaim)

private def OpeningFailure.callError : OpeningFailure → CallError
  | .retryableTransport => OpenFailureDisposition.callError .retryableTransport
  | .retryableLocal => OpenFailureDisposition.callError .retryableLocal
  | .terminalPolicy _ => OpenFailureDisposition.callError .terminalPolicy
  | .supervisorInvariant _ => OpenFailureDisposition.callError .supervisorInvariant
  | .cleanupUncertain _ => OpenFailureDisposition.callError .cleanupUncertain

private def OpeningFailure.closeClaim? : OpeningFailure → Option CloseClaim
  | .retryableTransport | .retryableLocal => none
  | .terminalPolicy claim
  | .supervisorInvariant claim
  | .cleanupUncertain claim => claim

private def OpeningFailure.cancellationMayMask : OpeningFailure → Bool
  | .retryableTransport | .retryableLocal => true
  | .terminalPolicy _ | .supervisorInvariant _ | .cleanupUncertain _ => false

private theorem OpeningFailure.closeClaim_eq_none_of_cancellationMayMask
    (failure : OpeningFailure) (retryable : failure.cancellationMayMask = true) :
    failure.closeClaim? = none := by
  cases failure <;> simp_all [OpeningFailure.cancellationMayMask,
    OpeningFailure.closeClaim?]

private inductive InitializationUnavailable where
  | draining
  | closed

private def InitializationUnavailable.callError :
    InitializationUnavailable → CallError
  | .draining => .channelDraining
  | .closed => .channelClosed

private inductive ConnectedError where
  | opening (failure : OpeningFailure)
  | ownerCancelled
  | unavailable (failure : InitializationUnavailable)

private inductive InitializationRace where
  | completed
  | cancelled

/--
Bounded terminal custody and evidence retained by a shared channel. Subchannel
and raw-initialization counts denote exact cleanup capabilities. Uncertain-task
and connector-invariant counts are sanitized fail-closed generation evidence,
not owners; a pending initializer is the exact staged task awaiting settlement.
-/
structure CleanupInventory where
  channelOwners : Nat := 0
  initializationOwners : Nat := 0
  uncertainInitializations : Nat := 0
  invariantInitializations : Nat := 0
  pendingInitializations : Nat := 0
deriving BEq, Repr

namespace CleanupInventory

/-- `closed` requires empty exact custody and empty fail-closed evidence. -/
def isClean (inventory : CleanupInventory) : Bool :=
  inventory.channelOwners == 0 &&
    inventory.initializationOwners == 0 &&
    inventory.uncertainInitializations == 0 &&
    inventory.invariantInitializations == 0 &&
    inventory.pendingInitializations == 0

theorem isClean_iff (inventory : CleanupInventory) :
    inventory.isClean = true ↔
      inventory.channelOwners = 0 ∧
      inventory.initializationOwners = 0 ∧
      inventory.uncertainInitializations = 0 ∧
      inventory.invariantInitializations = 0 ∧
      inventory.pendingInitializations = 0 := by
  simp [isClean, and_assoc]

end CleanupInventory

private structure SharedStateData (Resource : Type) where
  model : ChannelLease.State :=
    ChannelLease.State.initial
  nextGeneration : Nat := 0
  current : Option (ConnectedGeneration Resource) := none
  /--
  The unique lazy-initialization slot. A failed value permanently retains its
  generation-indexed evidence and any exact raw owner it actually claimed,
  plus at most one exact task while terminal transfer awaits task completion.
  -/
  initialization : InitializationState Resource := .idle
  /--
  Exact cleanup owners whose explicitly supplied direct-owned failure did not
  match the authoritative initialization slot. They are never retried and
  permanently prevent a clean shared close. The opaque owned wrapper, rather
  than its data-only diagnostic generation, proves a new exact capability.
  -/
  quarantinedInitializationOwners :
    List (QuarantinedInitializationOwner Resource) := []
  /--
  Sticky missing-authority evidence from re-presenting an already-transferred
  `OwnedOpenFailure` outside its authoritative slot. No exact owner is
  fabricated, but admission and clean close are permanently denied. Copied
  data-only `OpenFailure` observations never set this bit.
  -/
  quarantinedInitializationUncertainty : Bool := false
  /--
  Exact generations staged in supervisor state before their close effect runs.
  -/
  closing : List (ConnectedGeneration Resource) := []
  /--
  Exact generations whose close attempt failed. They remain reachable and are
  not retried by final shared close.
  -/
  retained : List (ConnectedGeneration Resource) := []
  /-- Exact one-hot custody for the close claim, starter, or detached task. -/
  closeDriver : CloseDriverState := .absent

private def InitializationState.cleanupInventory :
    InitializationState Resource → CleanupInventory
  | .idle => {}
  | .pending _ => { pendingInitializations := 1 }
  | .failed (.terminalPolicy _ _) pending? => {
      pendingInitializations := if pending?.isSome then 1 else 0
    }
  | .failed (.cleanupUncertain _ primary _) pending? => {
      initializationOwners := 1
      invariantInitializations := if primary.isInvariant then 1 else 0
      pendingInitializations := if pending?.isSome then 1 else 0
    }
  | .failed (.cleanupAuthorityMissing _ primary) pending? => {
      uncertainInitializations := 1
      invariantInitializations := if primary.isInvariant then 1 else 0
      pendingInitializations := if pending?.isSome then 1 else 0
    }
  | .failed (.taskUncertain _) pending? => {
      uncertainInitializations := 1
      pendingInitializations := if pending?.isSome then 1 else 0
    }
  | .failed (.connectorInvariant _) pending? => {
      invariantInitializations := 1
      pendingInitializations := if pending?.isSome then 1 else 0
    }

private def InitializationState.hasReachableTask :
    InitializationState Resource → Bool
  | .idle | .failed _ none => false
  | .pending _ | .failed _ (some _) => true

/--
The inventory's task bit is not bookkeeping detached from custody: it is one
exactly when the state constructor still stores the initializer task handle.
-/
private theorem InitializationState.pendingInventory_eq_reachableTask
    (state : InitializationState Resource) :
    state.cleanupInventory.pendingInitializations =
      if state.hasReachableTask then 1 else 0 := by
  cases state with
  | idle => rfl
  | pending _ => rfl
  | failed failure pending? =>
      cases failure <;> cases pending? <;> rfl

/-!
Transferred terminal authority may temporarily coexist with the one exact
initializer task until that task is observed terminal. Those are distinct,
bounded capabilities; invariant evidence remains an orthogonal diagnostic bit.
-/
private theorem InitializationState.cleanupInventory_atMostTwo
    (state : InitializationState Resource) :
    let inventory := state.cleanupInventory
    inventory.initializationOwners +
        inventory.uncertainInitializations +
        inventory.pendingInitializations ≤ 2 ∧
      inventory.invariantInitializations ≤ 1 := by
  cases state with
  | idle => simp [InitializationState.cleanupInventory]
  | pending _ => simp [InitializationState.cleanupInventory]
  | failed failure pending? =>
      cases pending? <;> cases failure <;>
        simp [InitializationState.cleanupInventory] <;>
        split <;> simp_all

private def SharedStateData.cleanupInventory
    (state : SharedStateData Resource) : CleanupInventory :=
  let initialization := state.initialization.cleanupInventory
  { initialization with
    channelOwners := state.closing.length + state.retained.length
    initializationOwners :=
      initialization.initializationOwners +
        state.quarantinedInitializationOwners.length
    uncertainInitializations :=
      initialization.uncertainInitializations +
        (if state.quarantinedInitializationUncertainty then 1 else 0)
    invariantInitializations :=
      initialization.invariantInitializations +
        (state.quarantinedInitializationOwners.filter
          (fun retained => retained.primary.isInvariant)).length }

private def InitializationState.exactOwnerCount :
    InitializationState Resource → Nat
  | .failed (.cleanupUncertain _ _ _) _ => 1
  | .idle | .pending _
  | .failed (.terminalPolicy _ _) _
  | .failed (.cleanupAuthorityMissing _ _) _
  | .failed (.taskUncertain _) _
  | .failed (.connectorInvariant _) _ => 0

private def InitializationState.missingAuthorityCount :
    InitializationState Resource → Nat
  | .failed (.cleanupAuthorityMissing _ _) _ => 1
  | .idle | .pending _
  | .failed (.terminalPolicy _ _) _
  | .failed (.cleanupUncertain _ _ _) _
  | .failed (.taskUncertain _) _
  | .failed (.connectorInvariant _) _ => 0

private def InitializationState.taskOwnerCount :
    InitializationState Resource → Nat
  | .pending _ | .failed _ (some _) => 1
  | .idle | .failed _ none => 0

private def InitializationState.isTerminal :
    InitializationState Resource → Bool
  | .failed _ _ => true
  | .idle | .pending _ => false

private def FailedInitialization.generation :
    FailedInitialization Resource → Nat
  | .terminalPolicy generation _
  | .cleanupUncertain generation _ _
  | .cleanupAuthorityMissing generation _
  | .taskUncertain generation
  | .connectorInvariant generation => generation

/-!
The initializer slot is indexed below the allocation frontier.  A terminal
transfer may retain its exact task only when both values describe the same
generation; this is the non-tautological link between diagnostic authority and
the task capability stored beside it.
-/
private def InitializationState.generationCoherent
    (state : InitializationState Resource)
    (nextGeneration : Nat) : Prop :=
  match state with
  | .idle => True
  | .pending initialization => initialization.generation < nextGeneration
  -- Once the exact task is gone, a retained terminal generation is
  -- diagnostic-only and need not have come from this allocator. Test seams
  -- deliberately exercise such observations without advancing the frontier.
  | .failed _ none => True
  | .failed failure (some initialization) =>
      initialization.generation < nextGeneration ∧
        failure.generation = initialization.generation

private def InitializationState.taskGeneration? :
    InitializationState Resource → Option Nat
  | .idle | .failed _ none => none
  | .pending initialization | .failed _ (some initialization) =>
      some initialization.generation

/-! A live initializer task and an installed/staged channel never alias. -/
private def InitializationState.taskDisjoint
    (state : InitializationState Resource)
    (channelGenerations : List Nat) : Prop :=
  match state.taskGeneration? with
  | none => True
  | some generation => generation ∉ channelGenerations

private theorem InitializationState.authority_one_hot
    (state : InitializationState Resource) :
    state.exactOwnerCount + state.missingAuthorityCount ≤ 1 := by
  cases state with
  | idle | pending => simp [exactOwnerCount, missingAuthorityCount]
  | failed failure pending? =>
      cases failure <;> simp [exactOwnerCount, missingAuthorityCount]

private theorem InitializationState.task_owner_at_most_one
    (state : InitializationState Resource) :
    state.taskOwnerCount ≤ 1 := by
  cases state with
  | idle | pending => simp [taskOwnerCount]
  | failed failure pending? => cases pending? <;> simp [taskOwnerCount]

private def CloseDriverState.authorityCount : CloseDriverState → Nat
  | .absent | .inlineTerminal => 0
  | .needsOwner | .startingBounded _ | .startingJoining _
  | .detached _ _ | .inline => 1

private theorem CloseDriverState.authority_at_most_one
    (driver : CloseDriverState) : driver.authorityCount ≤ 1 := by
  cases driver <;> simp [authorityCount]

/-!
The lifecycle phase and close-driver sum describe one custody graph. Accepting
has no close authority, draining always has some driver form, and closed keeps
the owner that published it: inline (including the completion-publication
window), terminal inline, or the exact detached task handle.
-/
private def CloseDriverState.phaseCoherent
    (driver : CloseDriverState)
    (phase : ChannelLease.Phase) : Prop :=
  match phase, driver with
  | .accepting, .absent => True
  | .draining, .needsOwner
  | .draining, .startingBounded _
  | .draining, .startingJoining _
  | .draining, .detached _ _
  | .draining, .inline
  | .draining, .inlineTerminal => True
  | .closed, .detached _ _
  | .closed, .inline
  | .closed, .inlineTerminal => True
  | _, _ => False

/-!
Only custody-preserving driver edges may rebuild the certified state. The
ticketed edges are selected only after pointer-identity admission at the
unlocked task-allocation boundary.
-/
private inductive CloseDriverState.Transition :
    CloseDriverState → CloseDriverState → Prop where
  | lastReleaseInline : Transition .needsOwner .inline
  | takeBounded (ticket) : Transition .needsOwner (.startingBounded ticket)
  | takeJoining (ticket) : Transition .needsOwner (.startingJoining ticket)
  | boundedDetached (ticket owner) :
      Transition (.startingBounded ticket) (.detached ticket owner)
  | boundedRestore (ticket) :
      Transition (.startingBounded ticket) .needsOwner
  | joiningDetached (ticket owner) :
      Transition (.startingJoining ticket) (.detached ticket owner)
  | joiningRestore (ticket) :
      Transition (.startingJoining ticket) .needsOwner
  | joiningInline (ticket) :
      Transition (.startingJoining ticket) .inline
  | inlineTerminal : Transition .inline .inlineTerminal

private def SharedStateData.channelGenerationIds
    (state : SharedStateData Resource) : List Nat :=
  state.current.toList.map (fun generation => generation.generation) ++
    state.closing.map (fun generation => generation.generation) ++
    state.retained.map (fun generation => generation.generation)

private def SharedStateData.hasTerminalEvidence
    (state : SharedStateData Resource) : Bool :=
  state.initialization.isTerminal ||
    !state.quarantinedInitializationOwners.isEmpty ||
    state.quarantinedInitializationUncertainty ||
    !state.retained.isEmpty

private def SharedStateData.currentExcludesInitializerTask
    (state : SharedStateData Resource) : Prop :=
  state.current.isSome = true →
    state.initialization.taskGeneration? = none

private structure SharedStateData.Valid
    (state : SharedStateData Resource) : Prop where
  generationIdsUnique : state.channelGenerationIds.Nodup
  generationsBelow : ∀ generation,
    generation ∈ state.channelGenerationIds →
      generation < state.nextGeneration
  initializationGenerationCoherent :
    state.initialization.generationCoherent state.nextGeneration
  initializationTaskDisjoint :
    state.initialization.taskDisjoint state.channelGenerationIds
  currentExcludesInitializerTask : state.currentExcludesInitializerTask
  initializationAuthorityOneHot :
    state.initialization.exactOwnerCount +
      state.initialization.missingAuthorityCount ≤ 1
  initializationTaskOneHot : state.initialization.taskOwnerCount ≤ 1
  closeDriverAuthorityOneHot : state.closeDriver.authorityCount ≤ 1
  closeDriverPhaseCoherent :
    state.closeDriver.phaseCoherent state.model.phase
  modelInvariant : state.model.Invariant
  terminalNonaccepting : state.hasTerminalEvidence = true →
    state.model.phase ≠ .accepting
  closedDrained : state.model.phase = .closed →
    state.model.activeCount = 0 ∧
      state.current = none ∧
      state.closing = [] ∧
      state.retained = [] ∧
      state.cleanupInventory.isClean = true

/--
The mutex never stores an unchecked ownership graph. Every transition must
construct the new data together with its generation, authority, lifecycle,
and terminal-drain certificate before publication.
-/
private structure SharedState (Resource : Type) extends SharedStateData Resource where
  certified : toSharedStateData.Valid

namespace SharedState

private def ofData
    (data : SharedStateData Resource)
    (generationIdsUnique : data.channelGenerationIds.Nodup)
    (generationsBelow : ∀ generation,
      generation ∈ data.channelGenerationIds →
        generation < data.nextGeneration)
    (initializationGenerationCoherent :
      data.initialization.generationCoherent data.nextGeneration)
    (initializationTaskDisjoint :
      data.initialization.taskDisjoint data.channelGenerationIds)
    (currentExcludesInitializerTask :
      data.currentExcludesInitializerTask)
    (closeDriverPhaseCoherent :
      data.closeDriver.phaseCoherent data.model.phase)
    (terminalNonaccepting : data.hasTerminalEvidence = true →
      data.model.phase ≠ .accepting)
    (closedDrained : data.model.phase = .closed →
      data.model.activeCount = 0 ∧
        data.current = none ∧
        data.closing = [] ∧
        data.retained = [] ∧
        data.cleanupInventory.isClean = true) :
    SharedState Resource := {
  toSharedStateData := data
  certified := {
    generationIdsUnique
    generationsBelow
    initializationGenerationCoherent
    initializationTaskDisjoint
    currentExcludesInitializerTask
    initializationAuthorityOneHot := data.initialization.authority_one_hot
    initializationTaskOneHot := data.initialization.task_owner_at_most_one
    closeDriverAuthorityOneHot := data.closeDriver.authority_at_most_one
    closeDriverPhaseCoherent
    modelInvariant := data.model.invariant
    terminalNonaccepting
    closedDrained
  }
}

private theorem generation_ids_unique (state : SharedState Resource) :
    state.toSharedStateData.channelGenerationIds.Nodup :=
  state.certified.generationIdsUnique

private theorem generations_below (state : SharedState Resource) :
    ∀ generation,
      generation ∈ state.toSharedStateData.channelGenerationIds →
        generation < state.nextGeneration :=
  state.certified.generationsBelow

private theorem initialization_generation_coherent
    (state : SharedState Resource) :
    state.initialization.generationCoherent state.nextGeneration :=
  state.certified.initializationGenerationCoherent

private theorem initialization_task_disjoint
    (state : SharedState Resource) :
    state.initialization.taskDisjoint
      state.toSharedStateData.channelGenerationIds :=
  state.certified.initializationTaskDisjoint

private theorem current_excludes_initializer_task
    (state : SharedState Resource) :
    state.toSharedStateData.currentExcludesInitializerTask :=
  state.certified.currentExcludesInitializerTask

private theorem close_driver_phase_coherent
    (state : SharedState Resource) :
    state.closeDriver.phaseCoherent state.model.phase :=
  state.certified.closeDriverPhaseCoherent

private theorem model_invariant (state : SharedState Resource) :
    state.model.Invariant :=
  state.certified.modelInvariant

private theorem terminal_nonaccepting (state : SharedState Resource) :
    state.toSharedStateData.hasTerminalEvidence = true →
      state.model.phase ≠ .accepting :=
  state.certified.terminalNonaccepting

private theorem closed_drained (state : SharedState Resource) :
    state.model.phase = .closed →
      state.model.activeCount = 0 ∧
        state.current = none ∧
        state.closing = [] ∧
        state.retained = [] ∧
        state.cleanupInventory.isClean = true :=
  state.certified.closedDrained

private def initial : SharedState Resource := {
  toSharedStateData := {}
  certified := by
    constructor
    · simp [SharedStateData.channelGenerationIds]
    · simp [SharedStateData.channelGenerationIds]
    · simp [InitializationState.generationCoherent]
    · simp [InitializationState.taskDisjoint,
        InitializationState.taskGeneration?]
    · simp [SharedStateData.currentExcludesInitializerTask]
    · exact InitializationState.authority_one_hot _
    · exact InitializationState.task_owner_at_most_one _
    · exact CloseDriverState.authority_at_most_one _
    · simp [CloseDriverState.phaseCoherent,
        ChannelLease.State.initial_phase]
    · exact ChannelLease.State.initial.invariant
    · simp [SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal]
    · simp [ChannelLease.State.initial_phase]
}

private def Invariant (state : SharedState Resource) : Prop :=
  state.toSharedStateData.Valid

private theorem invariant (state : SharedState Resource) : state.Invariant :=
  state.certified

private def cleanupInventory
    (state : SharedState Resource) : CleanupInventory :=
  state.toSharedStateData.cleanupInventory

private def withCloseDriver
    (state : SharedState Resource)
    (driver : CloseDriverState)
    (_transition : state.closeDriver.Transition driver)
    (phaseCoherent : driver.phaseCoherent state.model.phase) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with closeDriver := driver
  }
  apply SharedState.ofData data
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique
  · intro generation member
    exact state.generations_below generation (by
      simpa [data, SharedStateData.channelGenerationIds] using member)
  · simpa [data] using state.initialization_generation_coherent
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.initialization_task_disjoint
  · simpa [data] using state.current_excludes_initializer_task
  · simpa [data] using phaseCoherent
  · intro terminal
    apply state.terminal_nonaccepting
    simpa [data, SharedStateData.hasTerminalEvidence] using terminal
  · intro closed
    have drained := state.closed_drained closed
    simpa [data, SharedStateData.cleanupInventory] using drained

private theorem draining_of_closeDriver
    (state : SharedState Resource)
    (driver : CloseDriverState)
    (slot : state.closeDriver = driver)
    (onlyDraining : ∀ phase,
      driver.phaseCoherent phase → phase = .draining) :
    state.model.phase = .draining := by
  apply onlyDraining state.model.phase
  rw [← slot]
  exact state.close_driver_phase_coherent

private def takeBoundedCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (slot : state.closeDriver = .needsOwner) : SharedState Resource :=
  state.withCloseDriver (.startingBounded ticket) (by
    rw [slot]
    exact .takeBounded ticket) (by
    have draining := state.draining_of_closeDriver .needsOwner slot (by
      intro phase coherent
      cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def takeJoiningCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (slot : state.closeDriver = .needsOwner) : SharedState Resource :=
  state.withCloseDriver (.startingJoining ticket) (by
    rw [slot]
    exact .takeJoining ticket) (by
    have draining := state.draining_of_closeDriver .needsOwner slot (by
      intro phase coherent
      cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def publishBoundedCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (owner : CloseTask)
    (slot : state.closeDriver = .startingBounded ticket) :
    SharedState Resource :=
  state.withCloseDriver (.detached ticket owner) (by
    rw [slot]
    exact .boundedDetached ticket owner) (by
    have draining := state.draining_of_closeDriver
      (.startingBounded ticket) slot (by
        intro phase coherent
        cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def publishJoiningCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (owner : CloseTask)
    (slot : state.closeDriver = .startingJoining ticket) :
    SharedState Resource :=
  state.withCloseDriver (.detached ticket owner) (by
    rw [slot]
    exact .joiningDetached ticket owner) (by
    have draining := state.draining_of_closeDriver
      (.startingJoining ticket) slot (by
        intro phase coherent
        cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def restoreBoundedCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (slot : state.closeDriver = .startingBounded ticket) :
    SharedState Resource :=
  state.withCloseDriver .needsOwner (by
    rw [slot]
    exact .boundedRestore ticket) (by
    have draining := state.draining_of_closeDriver
      (.startingBounded ticket) slot (by
        intro phase coherent
        cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def restoreJoiningCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (slot : state.closeDriver = .startingJoining ticket) :
    SharedState Resource :=
  state.withCloseDriver .needsOwner (by
    rw [slot]
    exact .joiningRestore ticket) (by
    have draining := state.draining_of_closeDriver
      (.startingJoining ticket) slot (by
        intro phase coherent
        cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def inlineJoiningCloseDriver
    (state : SharedState Resource)
    (ticket : CloseStarterTicket)
    (slot : state.closeDriver = .startingJoining ticket) :
    SharedState Resource :=
  state.withCloseDriver .inline (by
    rw [slot]
    exact .joiningInline ticket) (by
    have draining := state.draining_of_closeDriver
      (.startingJoining ticket) slot (by
        intro phase coherent
        cases phase <;> simp_all [CloseDriverState.phaseCoherent])
    simpa [CloseDriverState.phaseCoherent, draining])

private def markInlineCloseTerminal
    (state : SharedState Resource)
    (slot : state.closeDriver = .inline) : SharedState Resource :=
  state.withCloseDriver .inlineTerminal (by
    rw [slot]
    exact .inlineTerminal) (by
    have coherent := state.close_driver_phase_coherent
    rw [slot] at coherent
    cases phase : state.model.phase <;>
      simp_all [CloseDriverState.phaseCoherent])

/-!
Lease acquisition and release alter only the core model while preserving its
phase.  Rebuild the certificate explicitly so a dependent record update can
never retain a proof about the previous model by accident.
-/
private def withModelSamePhase
    (state : SharedState Resource)
    (model : ChannelLease.State)
    (samePhase : model.phase = state.model.phase) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with model
  }
  apply ofData data
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique
  · intro generation member
    exact state.generations_below generation (by
      simpa [data, SharedStateData.channelGenerationIds] using member)
  · simpa [data] using state.initialization_generation_coherent
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.initialization_task_disjoint
  · simpa [data] using state.current_excludes_initializer_task
  · simpa [data, samePhase] using state.close_driver_phase_coherent
  · intro terminal accepting
    apply state.terminal_nonaccepting (by
      simpa [data, SharedStateData.hasTerminalEvidence] using terminal)
    simpa [data, samePhase] using accepting
  · intro closed
    have oldClosed : state.model.phase = .closed := by
      rw [← samePhase]
      exact closed
    have drained := state.closed_drained oldClosed
    refine ⟨model.closed_active_count_zero closed, ?_⟩
    exact drained.2

private theorem beginClose_driver_phaseCoherent
    (driver : CloseDriverState)
    (model : ChannelLease.State)
    (coherent : driver.phaseCoherent model.phase) :
    (driver.publishClaim
      (ChannelLease.beginClose model).decision).phaseCoherent
        (ChannelLease.beginClose model).state.phase := by
  cases phase : model.phase with
  | accepting =>
      have driverAbsent : driver = .absent := by
        cases driver <;>
          simp_all [CloseDriverState.phaseCoherent, phase]
      subst driver
      rw [ChannelLease.beginClose_accepting_phase model phase,
        ChannelLease.beginClose_accepting_decision model phase]
      simp [CloseDriverState.publishClaim, CloseDriverState.phaseCoherent]
  | draining =>
      rw [ChannelLease.beginClose_draining_state model phase,
        ChannelLease.beginClose_draining_decision model phase]
      simpa [CloseDriverState.publishClaim,
        CloseDriverState.phaseCoherent, phase] using coherent
  | closed =>
      rw [ChannelLease.beginClose_closed_state model phase,
        ChannelLease.beginClose_closed_decision model phase]
      simpa [CloseDriverState.publishClaim,
        CloseDriverState.phaseCoherent, phase] using coherent

/-! Publish the core close transition and its one-hot driver in one value. -/
private def beginClose (state : SharedState Resource) :
    SharedState Resource × CloseClaim := by
  let transition := ChannelLease.beginClose state.model
  let driver := state.closeDriver.publishClaim transition.decision
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      model := transition.state
      closeDriver := driver
  }
  let next : SharedState Resource := ofData data
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique)
    (by
      intro generation member
      exact state.generations_below generation (by
        simpa [data, SharedStateData.channelGenerationIds] using member))
    (by simpa [data] using state.initialization_generation_coherent)
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.initialization_task_disjoint)
    (by simpa [data] using state.current_excludes_initializer_task)
    (by
      simpa [data, driver, transition] using
        beginClose_driver_phaseCoherent state.closeDriver state.model
          state.close_driver_phase_coherent)
    (by
      intro _
      exact ChannelLease.beginClose_phase_nonaccepting state.model)
    (by
      intro closed
      have oldClosed := ChannelLease.beginClose_closed_implies_closed state.model (by
        simpa [data, transition] using closed)
      have drained := state.closed_drained oldClosed
      refine ⟨?_, drained.2⟩
      rw [ChannelLease.beginClose_activeCount state.model]
      exact drained.1)
  exact (next, {
    decision := transition.decision
    drained := transition.state.activeCount == 0
  })

private def withTerminalInitialization
    (state : SharedState Resource)
    (failure : FailedInitialization Resource)
    (pending? : Option (PendingInitialization Resource))
    (generationCoherent :
      (InitializationState.failed failure pending?).generationCoherent
        state.nextGeneration)
    (taskDisjoint :
      (InitializationState.failed failure pending?).taskDisjoint
        state.toSharedStateData.channelGenerationIds)
    (currentExcludesTask : state.current.isSome = true →
      (InitializationState.failed failure pending?).taskGeneration? = none)
    (notClosed : state.model.phase ≠ .closed) :
    SharedState Resource × CloseClaim := by
  let transition := ChannelLease.beginClose state.model
  let driver := state.closeDriver.publishClaim transition.decision
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      model := transition.state
      initialization := .failed failure pending?
      closeDriver := driver
  }
  let next : SharedState Resource := ofData data
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique)
    (by
      intro generation member
      exact state.generations_below generation (by
        simpa [data, SharedStateData.channelGenerationIds] using member))
    (by simpa [data] using generationCoherent)
    (by simpa [data, SharedStateData.channelGenerationIds] using taskDisjoint)
    (by
      intro present
      exact currentExcludesTask (by simpa [data] using present))
    (by
      simpa [data, driver, transition] using
        beginClose_driver_phaseCoherent state.closeDriver state.model
          state.close_driver_phase_coherent)
    (by
      intro _
      exact ChannelLease.beginClose_phase_nonaccepting state.model)
    (by
      intro closed
      have oldClosed := ChannelLease.beginClose_closed_implies_closed state.model (by
        simpa [data, transition] using closed)
      exact False.elim (notClosed oldClosed))
  exact (next, {
    decision := transition.decision
    drained := transition.state.activeCount == 0
  })

private theorem not_closed_of_pending
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (slot : state.initialization = .pending initialization) :
    state.model.phase ≠ .closed := by
  intro closed
  have drained := state.closed_drained closed
  have clean := (CleanupInventory.isClean_iff _).mp drained.2.2.2.2
  have pendingZero := clean.2.2.2.2
  simp [SharedStateData.cleanupInventory, slot,
    InitializationState.cleanupInventory] at pendingZero

private def failPendingInitialization
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (failure : FailedInitialization Resource)
    (slot : state.initialization = .pending initialization)
    (sameGeneration : failure.generation = initialization.generation) :
    SharedState Resource × CloseClaim :=
  state.withTerminalInitialization failure (some initialization)
    (by
      have coherent := state.initialization_generation_coherent
      rw [slot] at coherent
      exact ⟨coherent, sameGeneration⟩)
    (by
      have disjoint := state.initialization_task_disjoint
      simpa [slot, InitializationState.taskDisjoint,
        InitializationState.taskGeneration?] using disjoint)
    (by
      have excluded := state.current_excludes_initializer_task
      simpa [SharedStateData.currentExcludesInitializerTask, slot,
        InitializationState.taskGeneration?] using excluded)
    (state.not_closed_of_pending initialization slot)

private def failPendingInitializationWithoutTask
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (failure : FailedInitialization Resource)
    (slot : state.initialization = .pending initialization) :
    SharedState Resource × CloseClaim :=
  state.withTerminalInitialization failure none
    (by simp [InitializationState.generationCoherent])
    (by simp [InitializationState.taskDisjoint,
      InitializationState.taskGeneration?])
    (by simp [InitializationState.taskGeneration?])
    (state.not_closed_of_pending initialization slot)

private def failIdleInitialization
    (state : SharedState Resource)
    (failure : FailedInitialization Resource)
    (notClosed : state.model.phase ≠ .closed) :
    SharedState Resource × CloseClaim :=
  state.withTerminalInitialization failure none
    (by simp [InitializationState.generationCoherent])
    (by simp [InitializationState.taskDisjoint,
      InitializationState.taskGeneration?])
    (by simp [InitializationState.taskGeneration?])
    notClosed

private theorem not_closed_of_failed_pending
    (state : SharedState Resource)
    (failure : FailedInitialization Resource)
    (initialization : PendingInitialization Resource)
    (slot : state.initialization = .failed failure (some initialization)) :
    state.model.phase ≠ .closed := by
  intro closed
  have drained := state.closed_drained closed
  have clean := (CleanupInventory.isClean_iff _).mp drained.2.2.2.2
  have pendingZero := clean.2.2.2.2
  cases failure <;>
    simp [SharedStateData.cleanupInventory, slot,
      InitializationState.cleanupInventory] at pendingZero

private def clearPendingInitialization
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (slot : state.initialization = .pending initialization) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with initialization := .idle
  }
  apply ofData data
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique
  · intro generation member
    exact state.generations_below generation (by
      simpa [data, SharedStateData.channelGenerationIds] using member)
  · simp [data, InitializationState.generationCoherent]
  · simp [data, InitializationState.taskDisjoint,
      InitializationState.taskGeneration?]
  · simp [data, SharedStateData.currentExcludesInitializerTask,
      InitializationState.taskGeneration?]
  · simpa [data] using state.close_driver_phase_coherent
  · intro terminal accepting
    apply state.terminal_nonaccepting (by
      simpa [data, slot, SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal] using terminal)
    exact accepting
  · intro closed
    exact False.elim (state.not_closed_of_pending initialization slot closed)

private def clearFailedInitializationTask
    (state : SharedState Resource)
    (failure : FailedInitialization Resource)
    (initialization : PendingInitialization Resource)
    (slot : state.initialization = .failed failure (some initialization)) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with initialization := .failed failure none
  }
  apply ofData data
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique
  · intro generation member
    exact state.generations_below generation (by
      simpa [data, SharedStateData.channelGenerationIds] using member)
  · simp [data, InitializationState.generationCoherent]
  · simp [data, InitializationState.taskDisjoint,
      InitializationState.taskGeneration?]
  · simp [data, SharedStateData.currentExcludesInitializerTask,
      InitializationState.taskGeneration?]
  · simpa [data] using state.close_driver_phase_coherent
  · intro _ accepting
    apply state.terminal_nonaccepting
    · simp [slot, SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal]
    · exact accepting
  · intro closed
    exact False.elim
      (state.not_closed_of_failed_pending failure initialization slot closed)

private def allocatePendingInitialization
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (generation : initialization.generation = state.nextGeneration)
    (noCurrent : state.current = none)
    (idle : state.initialization = .idle)
    (accepting : state.model.phase = .accepting) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      nextGeneration := state.nextGeneration + 1
      initialization := .pending initialization
  }
  apply ofData data
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique
  · intro candidate member
    have below := state.generations_below candidate (by
      simpa [data, SharedStateData.channelGenerationIds] using member)
    change candidate < state.nextGeneration + 1
    omega
  · simp [data, InitializationState.generationCoherent, generation]
  · simp only [data, InitializationState.taskDisjoint,
      InitializationState.taskGeneration?]
    intro member
    have below := state.generations_below state.nextGeneration (by
      simpa [data, generation, SharedStateData.channelGenerationIds] using
        member)
    omega
  · simp [data, noCurrent,
      SharedStateData.currentExcludesInitializerTask]
  · simpa [data] using state.close_driver_phase_coherent
  · intro terminal phase
    apply state.terminal_nonaccepting
    · simpa [data, idle, SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal] using terminal
    · exact phase
  · intro closed
    rw [accepting] at closed
    contradiction

private def initializationAdmission
    (state : SharedState Resource) :
    Except InitializationUnavailable
      (PLift (state.model.phase = .accepting)) :=
  match phase : state.model.phase with
  | .accepting => .ok ⟨rfl⟩
  | .draining => .error .draining
  | .closed => .error .closed

end SharedState

namespace SharedState

private theorem no_current_of_pending
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (slot : state.initialization = .pending initialization) :
    state.current = none := by
  cases present : state.current with
  | none => rfl
  | some generation =>
      have excluded := state.current_excludes_initializer_task
      have noTask := excluded (by simp [present])
      rw [slot] at noTask
      simp [InitializationState.taskGeneration?] at noTask

private theorem no_current_of_failed_pending
    (state : SharedState Resource)
    (failure : FailedInitialization Resource)
    (initialization : PendingInitialization Resource)
    (slot : state.initialization = .failed failure (some initialization)) :
    state.current = none := by
  cases present : state.current with
  | none => rfl
  | some generation =>
      have excluded := state.current_excludes_initializer_task
      have noTask := excluded (by simp [present])
      rw [slot] at noTask
      simp [InitializationState.taskGeneration?] at noTask

/-!
Consume the authoritative pending task and publish its successful channel in
one certified value. Freshness and the frontier bound come from the pre-state
task slot; no intermediate state can forget that proof before installing the
channel owner.
-/
private def publishPendingGeneration
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (generation : ConnectedGeneration Resource)
    (slot : state.initialization = .pending initialization)
    (sameGeneration :
      generation.generation = initialization.generation)
    (accepting : state.model.phase = .accepting) :
    SharedState Resource := by
  have noCurrent := state.no_current_of_pending initialization slot
  have coherent := state.initialization_generation_coherent
  rw [slot] at coherent
  have disjoint := state.initialization_task_disjoint
  rw [slot] at disjoint
  have fresh :
      generation.generation ∉
        state.toSharedStateData.channelGenerationIds := by
    simpa [InitializationState.taskDisjoint,
      InitializationState.taskGeneration?, sameGeneration] using disjoint
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      current := some generation
      initialization := .idle
  }
  have generationIds : data.channelGenerationIds =
      generation.generation ::
        state.toSharedStateData.channelGenerationIds := by
    simp [data, SharedStateData.channelGenerationIds, noCurrent]
  apply ofData data
  · have unique := List.nodup_cons.mpr
      ⟨fresh, state.generation_ids_unique⟩
    rw [generationIds]
    exact unique
  · intro candidate member
    rw [generationIds] at member
    rcases List.mem_cons.mp member with same | previous
    · cases same
      simpa [sameGeneration] using coherent
    · exact state.generations_below candidate previous
  · simp [data, InitializationState.generationCoherent]
  · simp [data, InitializationState.taskDisjoint,
      InitializationState.taskGeneration?]
  · simp [data, SharedStateData.currentExcludesInitializerTask,
      InitializationState.taskGeneration?]
  · simpa [data] using state.close_driver_phase_coherent
  · intro terminal phase
    apply state.terminal_nonaccepting
    · simpa [data, slot, SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal] using terminal
    · exact phase
  · intro closed
    rw [accepting] at closed
    contradiction

private def stagePendingGeneration
    (state : SharedState Resource)
    (initialization : PendingInitialization Resource)
    (generation : ConnectedGeneration Resource)
    (slot : state.initialization = .pending initialization)
    (sameGeneration :
      generation.generation = initialization.generation) :
    SharedState Resource := by
  have noCurrent := state.no_current_of_pending initialization slot
  have coherent := state.initialization_generation_coherent
  rw [slot] at coherent
  have disjoint := state.initialization_task_disjoint
  rw [slot] at disjoint
  have fresh : generation.generation ∉ state.channelGenerationIds := by
    simpa [InitializationState.taskDisjoint,
      InitializationState.taskGeneration?, sameGeneration] using disjoint
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      initialization := .idle
      closing := generation :: state.closing
  }
  have generationIds : data.channelGenerationIds =
      generation.generation :: state.channelGenerationIds := by
    simp [data, SharedStateData.channelGenerationIds, noCurrent]
  apply ofData data
  · rw [generationIds]
    exact List.nodup_cons.mpr ⟨fresh, state.generation_ids_unique⟩
  · intro candidate member
    rw [generationIds] at member
    rcases List.mem_cons.mp member with same | previous
    · cases same
      simpa [sameGeneration] using coherent
    · exact state.generations_below candidate previous
  · simp [data, InitializationState.generationCoherent]
  · simp [data, InitializationState.taskDisjoint,
      InitializationState.taskGeneration?]
  · simp [data, noCurrent,
      SharedStateData.currentExcludesInitializerTask,
      InitializationState.taskGeneration?]
  · simpa [data] using state.close_driver_phase_coherent
  · intro terminal phase
    apply state.terminal_nonaccepting
    · simpa [data, slot, SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal] using terminal
    · exact phase
  · intro closed
    exact False.elim (state.not_closed_of_pending initialization slot closed)

private def stageFailedPendingGeneration
    (state : SharedState Resource)
    (failure : FailedInitialization Resource)
    (initialization : PendingInitialization Resource)
    (generation : ConnectedGeneration Resource)
    (slot : state.initialization = .failed failure (some initialization))
    (sameGeneration :
      generation.generation = initialization.generation) :
    SharedState Resource := by
  have noCurrent :=
    state.no_current_of_failed_pending failure initialization slot
  have coherent := state.initialization_generation_coherent
  rw [slot] at coherent
  have disjoint := state.initialization_task_disjoint
  rw [slot] at disjoint
  have fresh : generation.generation ∉ state.channelGenerationIds := by
    simpa [InitializationState.taskDisjoint,
      InitializationState.taskGeneration?, sameGeneration] using disjoint
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      initialization := .failed failure none
      closing := generation :: state.closing
  }
  have generationIds : data.channelGenerationIds =
      generation.generation :: state.channelGenerationIds := by
    simp [data, SharedStateData.channelGenerationIds, noCurrent]
  apply ofData data
  · rw [generationIds]
    exact List.nodup_cons.mpr ⟨fresh, state.generation_ids_unique⟩
  · intro candidate member
    rw [generationIds] at member
    rcases List.mem_cons.mp member with same | previous
    · cases same
      simpa [sameGeneration] using coherent.1
    · exact state.generations_below candidate previous
  · simp [data, InitializationState.generationCoherent]
  · simp [data, InitializationState.taskDisjoint,
      InitializationState.taskGeneration?]
  · simp [data, noCurrent,
      SharedStateData.currentExcludesInitializerTask,
      InitializationState.taskGeneration?]
  · simpa [data] using state.close_driver_phase_coherent
  · intro _ phase
    apply state.terminal_nonaccepting
    · simp [slot, SharedStateData.hasTerminalEvidence,
        InitializationState.isTerminal]
    · exact phase
  · intro closed
    exact False.elim
      (state.not_closed_of_failed_pending failure initialization slot closed)

private theorem not_closed_of_current
    (state : SharedState Resource)
    (generation : ConnectedGeneration Resource)
    (slot : state.current = some generation) :
    state.model.phase ≠ .closed := by
  intro closed
  have drained := state.closed_drained closed
  rw [slot] at drained
  simp at drained

private def stageCurrentGeneration
    (state : SharedState Resource)
    (generation : ConnectedGeneration Resource)
    (slot : state.current = some generation) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      current := none
      closing := generation :: state.closing
  }
  have generationIds : data.channelGenerationIds =
      state.channelGenerationIds := by
    simp [data, SharedStateData.channelGenerationIds, slot]
  apply ofData data
  · rw [generationIds]
    exact state.generation_ids_unique
  · intro candidate member
    exact state.generations_below candidate (by
      rw [← generationIds]
      exact member)
  · simpa [data] using state.initialization_generation_coherent
  · simpa [data, generationIds] using state.initialization_task_disjoint
  · simp [data, SharedStateData.currentExcludesInitializerTask]
  · simpa [data] using state.close_driver_phase_coherent
  · intro terminal phase
    apply state.terminal_nonaccepting
    · simpa [data, SharedStateData.hasTerminalEvidence] using terminal
    · exact phase
  · intro closed
    exact False.elim (state.not_closed_of_current generation slot closed)

end SharedState

/--
Atomically poison admission and retain an unexpected owner-bearing initializer
result without disturbing the authoritative generation slot.
-/
private def SharedState.quarantineInitializationOwner
    (state : SharedState Resource)
    (generation : Nat)
    (primary : PrimaryOpenFailure)
    (owner : ClaimedCleanupOwner Resource)
    (notClosed : state.model.phase ≠ .closed) :
    SharedState Resource × CloseClaim := by
  let transition :=
    ChannelLease.beginClose state.model
  let driver := state.closeDriver.publishClaim transition.decision
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      model := transition.state
      quarantinedInitializationOwners :=
        { generation, primary, owner } ::
          state.quarantinedInitializationOwners
      closeDriver := driver
  }
  let next : SharedState Resource := SharedState.ofData data
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique)
    (by
      intro candidate member
      exact state.generations_below candidate (by
        simpa [data, SharedStateData.channelGenerationIds] using member))
    (by simpa [data] using state.initialization_generation_coherent)
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.initialization_task_disjoint)
    (by simpa [data] using state.current_excludes_initializer_task)
    (by
      simpa [data, driver, transition] using
        SharedState.beginClose_driver_phaseCoherent state.closeDriver
          state.model state.close_driver_phase_coherent)
    (by
      intro _
      exact ChannelLease.beginClose_phase_nonaccepting state.model)
    (by
      intro closed
      have oldClosed := ChannelLease.beginClose_closed_implies_closed
        state.model (by simpa [data, transition] using closed)
      exact False.elim (notClosed oldClosed))
  exact (next, {
    decision := transition.decision
    drained := transition.state.activeCount == 0
  })

private def SharedState.quarantineInitializationUncertainty
    (state : SharedState Resource)
    (notClosed : state.model.phase ≠ .closed) :
    SharedState Resource × CloseClaim := by
  let transition :=
    ChannelLease.beginClose state.model
  let driver := state.closeDriver.publishClaim transition.decision
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      model := transition.state
      quarantinedInitializationUncertainty := true
      closeDriver := driver
  }
  let next : SharedState Resource := SharedState.ofData data
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique)
    (by
      intro candidate member
      exact state.generations_below candidate (by
        simpa [data, SharedStateData.channelGenerationIds] using member))
    (by simpa [data] using state.initialization_generation_coherent)
    (by simpa [data, SharedStateData.channelGenerationIds] using
      state.initialization_task_disjoint)
    (by simpa [data] using state.current_excludes_initializer_task)
    (by
      simpa [data, driver, transition] using
        SharedState.beginClose_driver_phaseCoherent state.closeDriver
          state.model state.close_driver_phase_coherent)
    (by
      intro _
      exact ChannelLease.beginClose_phase_nonaccepting state.model)
    (by
      intro closed
      have oldClosed := ChannelLease.beginClose_closed_implies_closed
        state.model (by simpa [data, transition] using closed)
      exact False.elim (notClosed oldClosed))
  exact (next, {
    decision := transition.decision
    drained := transition.state.activeCount == 0
  })

private abbrev TrustPreparationResult :=
  Except TrustAnchors.Error
    TrustAnchors.Bundle

/-!
Trust preparation is process-local policy, not part of a connection
generation. The shared owner therefore pins the first terminal value,
including a thrown `IO.Error`, behind a separate mutex. Holding that mutex
through the one action keeps both success and failure single-flight without
introducing a task whose custody would have to join shared close.
-/
private structure SharedTrustPreparation where
  state :
    Std.Mutex (Option (Except IO.Error TrustPreparationResult))
  action : IO TrustPreparationResult

private def SharedTrustPreparation.create
    (action : IO TrustPreparationResult) : IO SharedTrustPreparation := do
  pure { state := ← Std.Mutex.new none, action }

private def SharedTrustPreparation.load
    (preparation : SharedTrustPreparation) : IO TrustPreparationResult :=
  preparation.state.atomically do
    let captured ← match ← get with
      | some captured => pure captured
      | none =>
          let captured : Except IO.Error TrustPreparationResult ← try
            .ok <$> preparation.action
          catch error =>
            pure (.error error)
          set (some captured)
          pure captured
    match captured with
    | .ok result => pure result
    | .error error => throw error

/--
One lazily connected shared-channel owner.

Construction stores only refined configuration and connector capabilities.
DNS, trust loading, and socket/TLS setup start in a dedicated task only after
the first RPC acquires an outer call lease. A transport-dead generation is
retired after that RPC settles and the failed RPC is never replayed. Among
opening failures, only retryable transport or clean local setup admits a fresh
generation; endpoint/trust policy, supervisor invariant, and cleanup
uncertainty start terminal drain.
-/
structure ManagedChannel (Resource : Type) where
  private mk ::
  private dependencies : ManagedChannel.Dependencies Resource
  private configuration : ManagedChannel.Config
  private state : Std.Mutex (SharedState Resource)
  private drained : IO.Promise Unit
  /--
  Post-construction callback used by an initializer task to hand off a close
  claim. Its joining fallback first removes only an authoritative terminal
  task handle before any inline close, so the initializer cannot self-join.
  -/
  private closeHandoff : IO.Ref
    (Option Cancellation → IO Unit)
  /-- Authoritative terminal close result, independent of state-mutex writes. -/
  private closeCompletion : IO.Promise (Except CloseError Unit)
  /--
  Unregisterable wakeup published immediately after close completion.  Use the
  shared cancellation wrapper so selector callbacks are resolved only after
  its non-reentrant token mutex has been released.
  -/
  private closeSettled : Cancellation

namespace ManagedChannel

def endpoint (channel : ManagedChannel Resource) : Endpoint :=
  channel.configuration.endpoint

def phase (channel : ManagedChannel Resource) :
    IO ChannelLease.Phase := do
  channel.state.atomically do
    pure (← get).model.phase

private def acquire
    (channel : ManagedChannel Resource) :
    IO (Except ChannelLease.AcquireError
      ChannelLease.Lease) :=
  channel.state.atomically do
    let current ← get
    match accepted : ChannelLease.acquire current.model with
    | .error error => pure (.error error)
    | .ok grant =>
        set (current.withModelSamePhase grant.state
          (ChannelLease.acquire_preserves_phase current.model grant accepted))
        pure (.ok grant.lease)

private structure ReleaseOutcome where
  becameDrained : Bool
  ownsClaimedClose : Bool

private def release
    (channel : ManagedChannel Resource)
    (lease : ChannelLease.Lease) :
    IO (Except Unit ReleaseOutcome) := do
  channel.state.atomically do
    let current ← get
    match released : ChannelLease.release current.model lease with
    | .error _ => pure (.error ())
    | .ok next =>
        let becameDrained :=
          decide (next.phase = .draining) && next.activeCount == 0
        let ownsClaimedClose :=
          becameDrained &&
            current.closeDriver.isNeedsOwner
        let modeled := current.withModelSamePhase next
          (ChannelLease.release_preserves_phase current.model next lease released)
        let updated := if owns : ownsClaimedClose then
          modeled.withCloseDriver .inline (by
            have needs : current.closeDriver = .needsOwner := by
              have needed : current.closeDriver.isNeedsOwner = true := by
                simp [ownsClaimedClose] at owns
                exact owns.2
              cases driver : current.closeDriver <;>
                simp_all [CloseDriverState.isNeedsOwner]
            simpa [modeled, SharedState.withModelSamePhase, needs] using
              CloseDriverState.Transition.lastReleaseInline) (by
            have draining : next.phase = .draining := by
              simp [ownsClaimedClose, becameDrained] at owns
              exact owns.1.1
            change CloseDriverState.inline.phaseCoherent next.phase
            rw [draining]
            trivial)
        else
          modeled
        set updated
        pure (.ok { becameDrained, ownsClaimedClose })

private inductive InitializationClaim (Resource : Type) where
  | ready (generation : ConnectedGeneration Resource)
  | pending (initialization : PendingInitialization Resource)
  | failed (failure : OpeningFailure)
  | unavailable (failure : InitializationUnavailable)

private def pendingFailureCloseClaim?
    (state : SharedState Resource) : Option CloseClaim :=
  if state.closeDriver.isNeedsOwner then
    some {
      decision := .claimed
      drained := state.model.activeCount == 0
    }
  else
    none

private def failedInitializationOpeningFailure
    (state : SharedState Resource) :
    FailedInitialization Resource → OpeningFailure
  | .terminalPolicy _ _ =>
      .terminalPolicy (pendingFailureCloseClaim? state)
  | .cleanupUncertain _ _ _
  | .cleanupAuthorityMissing _ _
  | .taskUncertain _ =>
      .cleanupUncertain (pendingFailureCloseClaim? state)
  | .connectorInvariant _ =>
      .supervisorInvariant (pendingFailureCloseClaim? state)

/-- Every published failed-initialization state is terminal for cancellation. -/
private theorem failedInitializationOpeningFailure_cancellationMayMask
    (state : SharedState Resource)
    (failure : FailedInitialization Resource) :
    (failedInitializationOpeningFailure state failure).cancellationMayMask = false := by
  cases failure <;> rfl

private def openingFailureWithoutClaim
    (primary : PrimaryOpenFailure) : OpeningFailure :=
  match primary with
  | .transport _ => .retryableTransport
  | .localSetup => .retryableLocal
  | .policy _ => .terminalPolicy none
  | .invariant => .supervisorInvariant none

private def openingFailureFromDiagnosticWithoutClaim
    (failure : OpenFailure) : OpeningFailure :=
  if failure.hasCleanupUncertainty then
    .cleanupUncertain none
  else
    openingFailureWithoutClaim failure.primary

/-!
Transfer a direct owner-bearing failure into the generation-indexed shared
supervisor. The raw owner is taken while `ManagedChannel.state` is held and the
corresponding failure/close-claim state is published in the same transaction.
The initializer task calls this before returning its immutable `OpenFailure`,
so no waiter can ever receive or race to consume owner authority.
-/
private def transferOwnedInitializationFailure
    (channel : ManagedChannel Resource)
    (generation : Nat)
    (initializationOwner? : Option
      Cancellation)
    (failure : OwnedOpenFailure Resource) : IO OpeningFailure :=
  channel.state.atomically do
    let current ← get
    if closed : current.model.phase == .closed then
      -- A closed supervisor cannot accept new debt. In particular, do not
      -- consume an exact owner from the opaque wrapper: classify only its
      -- immutable diagnostic and leave that owner externally reachable.
      pure (openingFailureFromDiagnosticWithoutClaim failure.failure)
    else
      have notClosed : current.model.phase ≠ .closed := by
        intro phase
        have equal : (current.model.phase == .closed) = true := by
          rw [phase]
          simp
        rw [equal] at closed
        contradiction
      let custody ← failure.takeCustodyView
      match slot : current.initialization with
      | .pending active =>
          if same : active.generation == generation then
            let sameOwner ← match initializationOwner? with
              | some supplied => active.completion.same supplied
              | none => pure false
            if sameOwner then
              have generationEq : active.generation = generation := by
                exact eq_of_beq same
              match custody with
              | .ownerFree primary =>
                  match primary with
                  | .transport _ => pure .retryableTransport
                  | .localSetup => pure .retryableLocal
                  | .policy policy =>
                      let (next, claim) := current.failPendingInitialization
                        active (.terminalPolicy generation policy) slot
                        generationEq.symm
                      set next
                      pure (.terminalPolicy (some claim))
                  | .invariant =>
                      let (next, claim) := current.failPendingInitialization
                        active (.connectorInvariant generation) slot
                        generationEq.symm
                      set next
                      pure (.supervisorInvariant (some claim))
              | .cleanupUncertain primary owner =>
                  let (next, claim) := current.failPendingInitialization
                    active (.cleanupUncertain generation primary owner) slot
                    generationEq.symm
                  set next
                  pure (.cleanupUncertain (some claim))
              | .cleanupAliased primary =>
                  -- The task owns the wrapper exclusively. Seeing it already
                  -- transferred here is a supervisor contract failure.
                  -- Retain the exact task while publishing sticky containment.
                  let (next, claim) := current.failPendingInitialization
                    active (.cleanupAuthorityMissing generation primary) slot
                    generationEq.symm
                  set next
                  pure (.cleanupUncertain (some claim))
              | .cleanupQuarantined primary =>
                  -- A direct caller already made this raw value
                  -- observation-only. The shared supervisor must record the
                  -- missing cleanup authority without stealing or replaying it.
                  let (next, claim) := current.failPendingInitialization
                    active (.cleanupAuthorityMissing generation primary) slot
                    generationEq.symm
                  set next
                  pure (.cleanupUncertain (some claim))
            else
              match custody with
              | .ownerFree primary =>
                  pure (openingFailureWithoutClaim primary)
              | .cleanupUncertain primary owner =>
                  let (next, claim) := current.quarantineInitializationOwner
                    generation primary owner notClosed
                  set next
                  pure (.cleanupUncertain (some claim))
              | .cleanupAliased _ =>
                  let (next, claim) :=
                    current.quarantineInitializationUncertainty notClosed
                  set next
                  pure (.cleanupUncertain (some claim))
              | .cleanupQuarantined _ =>
                  let (next, claim) :=
                    current.quarantineInitializationUncertainty notClosed
                  set next
                  pure (.cleanupUncertain (some claim))
          else
            match custody with
            | .ownerFree primary =>
                pure (openingFailureWithoutClaim primary)
            | .cleanupUncertain primary owner =>
                let (next, claim) := current.quarantineInitializationOwner
                  generation primary owner notClosed
                set next
                pure (.cleanupUncertain (some claim))
            | .cleanupAliased _ =>
                let (next, claim) :=
                  current.quarantineInitializationUncertainty notClosed
                set next
                pure (.cleanupUncertain (some claim))
            | .cleanupQuarantined _ =>
                let (next, claim) :=
                  current.quarantineInitializationUncertainty notClosed
                set next
                pure (.cleanupUncertain (some claim))
      | .failed authoritative _ =>
          match custody with
          | .ownerFree _ =>
              pure (failedInitializationOpeningFailure current authoritative)
          | .cleanupAliased _ =>
              -- Re-presenting an owner wrapper after its one exact capability
              -- transferred is not a copied diagnostic observation. Preserve
              -- the ambiguity as one sticky owner-free bit.
              let (next, claim) :=
                current.quarantineInitializationUncertainty notClosed
              set next
              pure (.cleanupUncertain (some claim))
          | .cleanupQuarantined _ =>
              let (next, claim) :=
                current.quarantineInitializationUncertainty notClosed
              set next
              pure (.cleanupUncertain (some claim))
          | .cleanupUncertain primary owner =>
              -- A distinct direct wrapper is a distinct capability even when
              -- its diagnostic generation matches terminal evidence.
              let (next, claim) := current.quarantineInitializationOwner
                generation primary owner notClosed
              set next
              pure (.cleanupUncertain (some claim))
      | .idle =>
          match custody with
          | .ownerFree primary =>
              pure (openingFailureWithoutClaim primary)
          | .cleanupUncertain primary owner =>
              let (next, claim) := current.failIdleInitialization
                (.cleanupUncertain generation primary owner) notClosed
              set next
              pure (.cleanupUncertain (some claim))
          | .cleanupAliased primary =>
              let (next, claim) := current.failIdleInitialization
                (.cleanupAuthorityMissing generation primary) notClosed
              set next
              pure (.cleanupUncertain (some claim))
          | .cleanupQuarantined primary =>
              let (next, claim) := current.failIdleInitialization
                (.cleanupAuthorityMissing generation primary) notClosed
              set next
              pure (.cleanupUncertain (some claim))

private def claimInitialization
    (channel : ManagedChannel Resource) :
    IO (InitializationClaim Resource) :=
  channel.state.atomically do
    let current ← get
    match noCurrent : current.current with
    | some generation => pure (.ready generation)
    | none =>
        match idle : current.initialization with
        | .pending initialization => pure (.pending initialization)
        | .failed failure _ =>
            pure (.failed
              (failedInitializationOpeningFailure current failure))
        | .idle =>
            if !current.quarantinedInitializationOwners.isEmpty ||
                current.quarantinedInitializationUncertainty then
              -- Quarantine is terminal cleanup custody even when another
              -- generation subsequently settled owner-free. An already
              -- admitted lease must not use the empty primary slot to start
              -- more network work after containment began.
              return .failed (.cleanupUncertain none)
            let accepting ← match current.initializationAdmission with
              | .ok proof => pure proof
              | .error unavailable => return .unavailable unavailable
            let generation := current.nextGeneration
            let action :
                IO (Except (OwnedOpenFailure Resource) (Subchannel Resource)) := do
              try
                channel.dependencies.beforeInitializationOpen
              catch _ =>
                return Except.error localOpenFailure
              Subchannel.openWith channel.dependencies channel.configuration
            let spawned : Except IO.Error
                (InitializationTask Resource ×
                  Cancellation ×
                  Cancellation) ← try
              channel.dependencies.beforeInitializationTaskAllocation
              let completion ← Cancellation.create
              let published ← Cancellation.create
              let taskAction :
                  IO (Except OpenFailure (Subchannel Resource)) := do
                -- No opening effect may begin until the exact task handle is
                -- installed in `SharedState.initialization` below.
                published.wait
                channel.dependencies.beforeInitializationTaskBody
                match ← action with
                | .ok connected => pure (.ok connected)
                | .error owned =>
                    let diagnostic := owned.failure
                    -- Install exact cleanup authority and terminal/retry state
                    -- before this data-only diagnostic becomes task-visible.
                    let opening ←
                      channel.transferOwnedInitializationFailure
                        generation (some completion) owned
                    match opening.closeClaim? with
                    | some claim =>
                        if claim.decision == .claimed && claim.drained then
                          channel.drained.resolve ()
                    | none => pure ()
                    if !opening.cancellationMayMask then
                      -- Terminal publication always helps an existing close
                      -- claim. `beginClose` may have joined an earlier
                      -- transition whose detached allocation restored
                      -- `needsOwner`; gating this handoff on `.claimed` would
                      -- strand that exact custody. The joining fallback may
                      -- run inline only after atomically dropping this now
                      -- data-only terminal task handle, so it cannot self-join.
                      try
                        channel.dependencies.beforeInitializationCloseHandoff
                      catch _ =>
                        pure ()
                      (← channel.closeHandoff.get) (some completion)
                    pure (.error diagnostic)
              let task ← IO.asTask
                (try taskAction finally completion.cancel)
                Task.Priority.dedicated
              pure (Except.ok (task, completion, published))
            catch error =>
              pure (Except.error error)
            match spawned with
            | Except.error _ =>
                pure (.failed .retryableLocal)
            | Except.ok (task, completion, published) =>
                try
                  channel.dependencies.beforeInitializationTaskPublication
                catch _ =>
                  pure ()
                let initialization := { generation, task, completion }
                set (current.allocatePendingInitialization initialization
                  rfl noCurrent idle accepting.down)
                -- `set` is nonthrowing. Release only after supervisor custody
                -- exists; callbacks wake outside the signal's token mutex.
                published.cancel
                pure (.pending initialization)

private def sameInitialization
    (left right : PendingInitialization Resource) :
    BaseIO (Option (PLift (left.generation = right.generation))) := do
  if same : left.generation == right.generation then
    if ← left.completion.same right.completion then
      pure (some ⟨eq_of_beq same⟩)
    else
      pure none
  else
    pure none

private def settleUncertainInitializationTask
    (channel : ManagedChannel Resource)
    (initialization : PendingInitialization Resource) : IO OpeningFailure :=
  channel.state.atomically do
    let current ← get
    match slot : current.initialization with
    | .pending active =>
        if (← sameInitialization active initialization).isSome then
          let (next, claim) := current.failPendingInitializationWithoutTask
            active (.taskUncertain initialization.generation) slot
          set next
          pure (.cleanupUncertain (some claim))
        else
          pure (.cleanupUncertain none)
    | .failed authoritative (some pending) =>
        if (← sameInitialization pending initialization).isSome then
          set (current.clearFailedInitializationTask
            authoritative pending slot)
        pure (failedInitializationOpeningFailure current authoritative)
    | .failed authoritative none =>
        pure (failedInitializationOpeningFailure current authoritative)
    | .idle => pure (.cleanupUncertain none)

/-!
Observe the immutable failure published by an initializer task. Its owned
authority was already transferred before task completion, so this function
never consumes or mutates the diagnostic. Authoritative terminal state wins a
stale waiter's older diagnostic; an impossible still-pending same generation
is contained as uncertain task evidence.
-/
private def observeInitializationFailure
    (channel : ManagedChannel Resource)
    (initialization : PendingInitialization Resource)
    (failure : OpenFailure) : IO OpeningFailure :=
  channel.state.atomically do
    let current ← get
    match slot : current.initialization with
    | .failed authoritative (some pending) =>
        if (← sameInitialization pending initialization).isSome then
          set (current.clearFailedInitializationTask
            authoritative pending slot)
        pure (failedInitializationOpeningFailure current authoritative)
    | .failed authoritative none =>
        pure (failedInitializationOpeningFailure current authoritative)
    | .idle =>
        -- An aged-out task result is only a copied diagnostic. Its exact
        -- authority, if any, transferred before publication and is no longer
        -- represented by this value. Classify it without fabricating debt.
        pure (openingFailureFromDiagnosticWithoutClaim failure)
    | .pending active =>
        if (← sameInitialization active initialization).isSome then
          match failure.kind with
          | .ownerFree (.transport _) =>
              set (current.clearPendingInitialization active slot)
              pure .retryableTransport
          | .ownerFree .localSetup =>
              set (current.clearPendingInitialization active slot)
              pure .retryableLocal
          | .ownerFree (.policy policy) =>
              let (next, claim) := current.failPendingInitializationWithoutTask
                active (.terminalPolicy initialization.generation policy) slot
              set next
              pure (.terminalPolicy (some claim))
          | .ownerFree .invariant =>
              let (next, claim) := current.failPendingInitializationWithoutTask
                active (.connectorInvariant initialization.generation) slot
              set next
              pure (.supervisorInvariant (some claim))
          | .cleanupFailed primary =>
              let (next, claim) := current.failPendingInitializationWithoutTask
                active (.cleanupAuthorityMissing
                  initialization.generation primary) slot
              set next
              pure (.cleanupUncertain (some claim))
        else
          -- A result from another task generation is likewise data-only.
          -- Only an `OwnedOpenFailure` transfer may add exact or uncertain
          -- cleanup custody to supervisor state.
          pure (openingFailureFromDiagnosticWithoutClaim failure)

private def publishInitialization
    (shared : ManagedChannel Resource)
    (initialization : PendingInitialization Resource)
    (channel : Subchannel Resource) :
    IO (Except ConnectedError (ConnectedGeneration Resource)) := do
  let generation : ConnectedGeneration Resource := {
    generation := initialization.generation
    channel
  }
  shared.state.atomically do
    let current ← get
    -- Every waiter receives a copy of the same successful task value. Once
    -- one waiter has installed the generation, all later observers reuse that
    -- authoritative value rather than treating their alias as new custody.
    match current.current with
    | some authoritative =>
        if authoritative.generation == generation.generation then
          return .ok authoritative
    | none => pure ()
    match slot : current.initialization with
    | .pending active =>
        match ← sameInitialization active initialization with
        | some sameGeneration =>
          match phase : current.model.phase with
          | .accepting =>
              set (current.publishPendingGeneration active generation slot
                sameGeneration.down.symm phase)
              pure (.ok generation)
          | .draining | .closed =>
              set (current.stagePendingGeneration active generation slot
                sameGeneration.down.symm)
              if !current.quarantinedInitializationOwners.isEmpty ||
                  current.quarantinedInitializationUncertainty then
                pure (.error (.opening (.cleanupUncertain
                  (pendingFailureCloseClaim? current))))
              else
                pure (.error (.unavailable
                  (if current.model.phase == .closed then .closed
                    else .draining)))
        | none =>
          -- The private task handle proves this is a copied result from an
          -- older generation, not a newly acquired channel owner. Classify
          -- the stale observation without mutating supervisor custody.
          if !current.quarantinedInitializationOwners.isEmpty ||
              current.quarantinedInitializationUncertainty then
            pure (.error (.opening (.cleanupUncertain
              (pendingFailureCloseClaim? current))))
          else
            match current.model.phase with
            | .draining => pure (.error (.unavailable .draining))
            | .closed => pure (.error (.unavailable .closed))
            | .accepting =>
                pure (.error (.opening (.supervisorInvariant none)))
    | .failed authoritative (some pending) =>
        match ← sameInitialization pending initialization with
        | some sameGeneration =>
          set (current.stageFailedPendingGeneration authoritative pending
            generation slot sameGeneration.down.symm)
          pure (.error (.opening
            (failedInitializationOpeningFailure current authoritative)))
        | none =>
          pure (.error (.opening
            (failedInitializationOpeningFailure current authoritative)))
    | .failed authoritative none =>
        pure (.error (.opening
          (failedInitializationOpeningFailure current authoritative)))
    | .idle =>
        if !current.quarantinedInitializationOwners.isEmpty ||
            current.quarantinedInitializationUncertainty then
          pure (.error (.opening (.cleanupUncertain
            (pendingFailureCloseClaim? current))))
        else
          match current.model.phase with
          | .draining => pure (.error (.unavailable .draining))
          | .closed => pure (.error (.unavailable .closed))
          | .accepting =>
              pure (.error (.opening (.supervisorInvariant none)))

private def settleInitializationResult
    (channel : ManagedChannel Resource)
    (initialization : PendingInitialization Resource)
    (result : Except IO.Error
      (Except OpenFailure (Subchannel Resource))) :
    IO (Except ConnectedError (ConnectedGeneration Resource)) := do
  match result with
  | .error _ =>
      -- A task-level failure bypassed `openWith`'s fixed-shape cleanup result,
      -- so no proof remains that a partially acquired resource was released.
      pure (.error (.opening
        (← channel.settleUncertainInitializationTask initialization)))
  | .ok (.error failure) =>
      pure (.error (.opening
        (← channel.observeInitializationFailure initialization failure)))
  | .ok (.ok connected) =>
      channel.publishInitialization initialization connected

private def awaitInitialization
    (channel : ManagedChannel Resource)
    (initialization : PendingInitialization Resource) :
    IO (Except ConnectedError (ConnectedGeneration Resource)) := do
  channel.settleInitializationResult initialization
    (← IO.wait initialization.task)

private def authoritativeInitializationFailure?
    (channel : ManagedChannel Resource) : IO (Option OpeningFailure) :=
  channel.state.atomically do
    let current ← get
    match current.initialization with
    | .failed authoritative _ =>
        pure (some
          (failedInitializationOpeningFailure current authoritative))
    | .idle | .pending _ => pure none

private def awaitInitializationWithCancellation
    (channel : ManagedChannel Resource)
    (initialization : PendingInitialization Resource)
    (cancellation : Cancellation) :
    IO (Except ConnectedError (ConnectedGeneration Resource)) := do
  let raced : InitializationRace ← (Std.Async.Selectable.one #[
    .case initialization.completion.selector fun _ =>
      pure InitializationRace.completed,
    .case cancellation.selector fun _ =>
      pure InitializationRace.cancelled
  ]).block
  match raced with
  | .completed =>
      channel.settleInitializationResult initialization
        (← IO.wait initialization.task)
  | .cancelled =>
      -- Fair selection can observe cancellation while initialization becomes
      -- terminal concurrently. Settle any already-available result into
      -- supervisor state before returning: success and retryable failure keep
      -- the selected `ownerCancelled`, while policy, invariant, and cleanup
      -- uncertainty must not be masked. Otherwise leave the exact task staged
      -- for a later caller or close owner.
      try
        channel.dependencies.beforeCancelledInitializationSettlement
      catch _ =>
        pure ()
      -- Ownership/terminal evidence is installed before the task publishes
      -- its diagnostic. It therefore outranks cancellation even during the
      -- small interval in which `IO.hasFinished` is still false.
      match ← channel.authoritativeInitializationFailure? with
      | some failure =>
          if failure.cancellationMayMask then
            pure ()
          else
            return .error (.opening failure)
      | none => pure ()
      if ← IO.hasFinished initialization.task then
        match ← channel.settleInitializationResult initialization
            (← IO.wait initialization.task) with
        | .error (.opening failure) =>
            if failure.cancellationMayMask then
              pure (.error .ownerCancelled)
            else
              pure (.error (.opening failure))
        | .error .ownerCancelled => pure (.error .ownerCancelled)
        | .error (.unavailable error) => pure (.error (.unavailable error))
        | .ok _ => pure (.error .ownerCancelled)
      else
        pure (.error .ownerCancelled)

private def connected
    (channel : ManagedChannel Resource) :
    IO (Except ConnectedError (ConnectedGeneration Resource)) := do
  match ← channel.claimInitialization with
  | .ready generation => pure (.ok generation)
  | .pending initialization =>
      channel.awaitInitialization initialization
  | .failed failure => pure (.error (.opening failure))
  | .unavailable failure => pure (.error (.unavailable failure))

private def connectedWithCancellation
    (channel : ManagedChannel Resource)
    (cancellation : Cancellation) :
    IO (Except ConnectedError (ConnectedGeneration Resource)) := do
  -- An already-cancelled request must not start otherwise-lazy network work.
  if ← cancellation.isCancelled then
    return .error .ownerCancelled
  try
    channel.dependencies.beforeCancelledInitializationClaim
  catch _ =>
    pure ()
  let result ← match ← channel.claimInitialization with
    | .ready generation => pure (.ok generation)
    | .pending initialization =>
        channel.awaitInitializationWithCancellation initialization cancellation
    | .failed failure => pure (.error (.opening failure))
    | .unavailable failure => pure (.error (.unavailable failure))
  match result with
  | .error error => pure (.error error)
  | .ok generation =>
      -- Covers both a cached ready generation and cancellation concurrent
      -- with publishing a newly completed generation. The inner RPC performs
      -- its own immediate recheck after this boundary as well.
      if ← cancellation.isCancelled then
        pure (.error .ownerCancelled)
      else
        pure (.ok generation)

/-!
grpc-lean records a dead connection using the status that caused its reader or
writer to fail. Native `IO.Error` conversion can produce `CANCELLED`,
`DEADLINE_EXCEEDED`, `RESOURCE_EXHAUSTED`, or `UNKNOWN`; EOF/GOAWAY can produce
`UNAVAILABLE`; and HTTP/2/TLS protocol failure can produce `INTERNAL`.

Those codes can also be stream- or application-level outcomes. The current
grpc-lean call boundary deliberately exposes only `Grpc.Status`, not its
provenance, so all six are conservatively transport-ambiguous: retire the
generation after the exact call settles, but never replay that call.
-/

def transportAmbiguousRpcCodes : List Grpc.Code := [
  .cancelled,
  .unknown,
  .deadlineExceeded,
  .resourceExhausted,
  .internal,
  .unavailable
]

def rpcCodeRequiresGenerationRetirement : Grpc.Code → Bool
  | .cancelled
  | .unknown
  | .deadlineExceeded
  | .resourceExhausted
  | .internal
  | .unavailable => true
  | .ok
  | .invalidArgument
  | .notFound
  | .alreadyExists
  | .permissionDenied
  | .failedPrecondition
  | .aborted
  | .outOfRange
  | .unimplemented
  | .dataLoss
  | .unauthenticated => false

theorem rpcCodeRequiresGenerationRetirement_iff
    (code : Grpc.Code) :
    rpcCodeRequiresGenerationRetirement code = true ↔
      code ∈ transportAmbiguousRpcCodes := by
  cases code <;>
    simp [rpcCodeRequiresGenerationRetirement, transportAmbiguousRpcCodes]

def requiresGenerationRetirement : CallError → Bool
  | .channelDraining
  | .channelClosed
  | .actionFailed
  | .supervisorInvariant
  | .callActionFailed
  | .cleanupUncertain => true
  | .requestEncoding
  | .responseDecoding
  | .scopeClosed
  | .localDeadlineExceeded
  | .ownerCancelled => false
  | .rpc status _ => rpcCodeRequiresGenerationRetirement status.code

/--
Severity used when concurrently admitted calls publish generation-retirement
evidence. Exact cleanup uncertainty and supervisor failure must not be masked
by an earlier retryable peer status; equal severities remain first-wins.
-/
private def retirementPriority : CallError → Nat
  | .cleanupUncertain => 5
  | .supervisorInvariant => 4
  | .actionFailed
  | .callActionFailed
  | .channelDraining
  | .channelClosed => 3
  | .rpc _ _ => 2
  | _ => 0

private def mergeRetirement
    (current : Option CallError)
    (candidate : Except CallError Response) : Option CallError :=
  match current, candidate with
  | some retained, .error error =>
      if requiresGenerationRetirement error &&
          retirementPriority retained < retirementPriority error then
        some error
      else
        some retained
  | some retained, .ok _ => some retained
  | none, .error error =>
      if requiresGenerationRetirement error then some error else none
  | none, .ok _ => none

private def mergeRetirementResult
    (retirement : Option CallError)
    (callback : Except CallError Response) : Except CallError Response :=
  match mergeRetirement retirement callback with
  | some error => .error error
  | none => callback

private def takeGeneration
    (shared : ManagedChannel Resource)
    (generation : ConnectedGeneration Resource) :
    IO (Option (ConnectedGeneration Resource)) :=
  shared.state.atomically do
    let current ← get
    match slot : current.current with
    | some active =>
        if active.generation == generation.generation then
          -- Publish the exact cleanup capability before running its close
          -- effect. An exception can therefore leave debt, but not erase its
          -- owner.
          set (current.stageCurrentGeneration active slot)
          pure (some active)
        else
          pure none
    | none => pure none

private def awaitClose
    (shared : ManagedChannel Resource) : IO (Except CloseError Unit) := do
  let some result ← IO.wait shared.closeCompletion.result?
    | pure (.error .completionDropped)
  pure result

private def closeCompletion?
    (shared : ManagedChannel Resource) : IO (Option (Except CloseError Unit)) := do
  if ← shared.closeCompletion.isResolved then
    some <$> shared.awaitClose
  else
    pure none

private def observeClose
    (shared : ManagedChannel Resource) : IO CloseObservation := do
  match ← shared.closeCompletion? with
  | some result => pure (.settled result)
  | none =>
      try
        shared.dependencies.beforeCloseObservationFinalCheck
      catch _ =>
        pure ()
      -- Completion can publish after the first check but before custody is
      -- sampled. This second authoritative check gives terminal evidence
      -- precedence at the observation linearization boundary.
      match ← shared.closeCompletion? with
      | some result => pure (.settled result)
      | none =>
          -- Sample custody only at this final boundary. An earlier read could
          -- become stale while the observation seam is paused and incorrectly
          -- claim that a driver is still needed after another caller took it.
          let needsOwner ← shared.state.atomically do
            pure ((← get).closeDriver.isNeedsOwner)
          if needsOwner then pure .needsDriver else pure .stillClosing

private inductive CloseDeadlineRace where
  | completed
  | elapsed

/-- Largest millisecond interval representable by libuv's UInt64 timer. -/
private def maximumCloseTimerMilliseconds : Nat := (2 : Nat) ^ 64 - 1

private def awaitCloseOrDeadline
    (shared : ManagedChannel Resource) (remainingMilliseconds : Nat) :
    IO CloseDeadlineRace :=
  (do
    let timerMilliseconds :=
      min remainingMilliseconds maximumCloseTimerMilliseconds
    let timer ← Selector.sleep
      (Std.Time.Millisecond.Offset.ofNat timerMilliseconds)
    let completed : Selectable CloseDeadlineRace :=
      .case shared.closeSettled.selector fun _ => pure .completed
    let elapsed : Selectable CloseDeadlineRace :=
      .case timer fun _ => pure .elapsed
    -- Selector order is not semantic (pinned Std may shuffle it). The caller's
    -- authoritative completion recheck after `.elapsed` supplies boundary
    -- precedence instead.
    Selectable.one #[completed, elapsed]).block

private def takeClosingResources
    (shared : ManagedChannel Resource) :
    IO (Option (PendingInitialization Resource)) :=
  shared.state.atomically do
    let current ← get
    let next := match slot : current.current with
      | none => current
      | some generation => current.stageCurrentGeneration generation slot
    set next
    -- Keep the task itself reachable in `state.initialization` until its
    -- resource-bearing result has been transferred into supervisor state.
    match current.initialization with
    | .pending initialization => pure (some initialization)
    | .failed _ (some initialization) => pure (some initialization)
    | .idle | .failed _ none => pure none

/--
The elected close owner joins the exact staged task and settles its structural
result: successful channels are staged for exact close, cleanup ambiguity
retains its owner, invariant or outer-task failure records sticky generation
evidence, and clean owner-free failure creates no debt.
-/
private def settleInitializationDuringClose
    (shared : ManagedChannel Resource)
    (initialization : PendingInitialization Resource)
    (result : Except IO.Error
      (Except OpenFailure (Subchannel Resource))) : IO Unit :=
  shared.state.atomically do
    let current ← get
    match slot : current.initialization with
    | .pending active =>
      match ← sameInitialization active initialization with
      | some sameGeneration =>
          match result with
          | .ok (.ok channel) =>
              -- Success has no separate transfer step. The close owner moves
              -- the exact channel into its staged list while consuming pending.
              set (current.stagePendingGeneration active {
                generation := initialization.generation
                channel
              } slot sameGeneration.down.symm)
          | .error _ =>
              let (next, _) := current.failPendingInitializationWithoutTask
                active (.taskUncertain initialization.generation) slot
              set next
          | .ok (.error failure) =>
              -- Clean retryable transfer deliberately retains pending until
              -- the exact task is joined. Terminal diagnostics should already
              -- have transferred; if not, publish sanitized containment.
              match failure.kind with
              | .ownerFree (.transport _) | .ownerFree .localSetup =>
                  set (current.clearPendingInitialization active slot)
              | .ownerFree (.policy policy) =>
                  let (next, _) :=
                    current.failPendingInitializationWithoutTask active
                      (.terminalPolicy initialization.generation policy) slot
                  set next
              | .ownerFree .invariant =>
                  let (next, _) :=
                    current.failPendingInitializationWithoutTask active
                      (.connectorInvariant initialization.generation) slot
                  set next
              | .cleanupFailed primary =>
                  let (next, _) :=
                    current.failPendingInitializationWithoutTask active
                      (.cleanupAuthorityMissing
                        initialization.generation primary) slot
                  set next
      | none => pure ()
    | .failed authoritative (some pending) =>
        match ← sameInitialization pending initialization with
        | some sameGeneration =>
          match result with
          | .ok (.ok channel) =>
              set (current.stageFailedPendingGeneration authoritative pending {
                generation := initialization.generation
                channel
              } slot sameGeneration.down.symm)
          | .error _ | .ok (.error _) =>
              set (current.clearFailedInitializationTask
                authoritative pending slot)
        | none => pure ()
    | .failed _ none => pure ()
    | .idle => pure ()

private def initializedDuringClose
    (shared : ManagedChannel Resource)
    (initialization : PendingInitialization Resource) :
    IO Unit := do
  let result ← IO.wait initialization.task
  shared.settleInitializationDuringClose initialization result

private structure ClosingExtraction
    (Resource : Type)
    (closing : List (ConnectedGeneration Resource))
    (requested : Nat) where
  before : List (ConnectedGeneration Resource)
  authoritative : ConnectedGeneration Resource
  after : List (ConnectedGeneration Resource)
  reconstruct :
    closing = before ++ authoritative :: after
  requestedGeneration : authoritative.generation = requested

private def extractClosing
    (closing : List (ConnectedGeneration Resource))
    (requested : Nat) :
    Option (ClosingExtraction Resource closing requested) :=
  match closing with
  | [] => none
  | head :: tail =>
      if same : head.generation == requested then
        some {
          before := []
          authoritative := head
          after := tail
          reconstruct := rfl
          requestedGeneration := eq_of_beq same
        }
      else
        match extractClosing tail requested with
        | none => none
        | some extracted =>
            some {
              before := head :: extracted.before
              authoritative := extracted.authoritative
              after := extracted.after
              reconstruct := by
                change head :: tail =
                  head :: (extracted.before ++
                    extracted.authoritative :: extracted.after)
                congr
                exact extracted.reconstruct
              requestedGeneration := extracted.requestedGeneration
            }

namespace SharedState

private theorem not_closed_of_closingExtraction
    (state : SharedState Resource)
    (requested : Nat)
    (extracted : ClosingExtraction Resource state.closing requested) :
    state.model.phase ≠ .closed := by
  intro closed
  have drained := state.closed_drained closed
  rw [extracted.reconstruct] at drained
  simp at drained

private def settleClosingSuccess
    (state : SharedState Resource)
    (requested : Nat)
    (extracted : ClosingExtraction Resource state.closing requested) :
    SharedState Resource := by
  let closing := extracted.before ++ extracted.after
  let data : SharedStateData Resource := {
    state.toSharedStateData with closing
  }
  have closingSublist : List.Sublist closing state.closing := by
    rw [extracted.reconstruct]
    exact (List.Sublist.refl closing).middle extracted.authoritative
  have generationSublist : List.Sublist data.channelGenerationIds
      state.channelGenerationIds := by
    have mapped := closingSublist.map
      (fun generation : ConnectedGeneration Resource => generation.generation)
    have withCurrent := mapped.append_left
      (state.current.toList.map (fun generation => generation.generation))
    have withRetained := withCurrent.append_right
      (state.retained.map (fun generation => generation.generation))
    simpa [data, closing, SharedStateData.channelGenerationIds,
      List.append_assoc] using withRetained
  apply SharedState.ofData data
  · exact generationSublist.nodup state.generation_ids_unique
  · intro candidate member
    exact state.generations_below candidate
      (generationSublist.subset member)
  · simpa [data] using state.initialization_generation_coherent
  · cases task : state.initialization.taskGeneration? with
    | none =>
        change state.initialization.taskDisjoint
          data.channelGenerationIds
        simp [InitializationState.taskDisjoint, task]
    | some generation =>
        have disjoint :
            ¬ generation ∈ state.channelGenerationIds := by
          simpa [InitializationState.taskDisjoint, task] using
            state.initialization_task_disjoint
        change state.initialization.taskDisjoint
          data.channelGenerationIds
        simp only [InitializationState.taskDisjoint, task]
        intro member
        exact disjoint (generationSublist.subset member)
  · simpa [data] using state.current_excludes_initializer_task
  · simpa [data] using state.close_driver_phase_coherent
  · intro terminal phase
    apply state.terminal_nonaccepting
    · simpa [data, SharedStateData.hasTerminalEvidence] using terminal
    · exact phase
  · intro closed
    exact False.elim
      (not_closed_of_closingExtraction state requested extracted closed)

private def settleClosingFailure
    (state : SharedState Resource)
    (requested : Nat)
    (extracted : ClosingExtraction Resource state.closing requested) :
    SharedState Resource × CloseClaim := by
  let transition := ChannelLease.beginClose state.model
  let closing := extracted.before ++ extracted.after
  let retained := extracted.authoritative :: state.retained
  let driver := state.closeDriver.publishClaim transition.decision
  let data : SharedStateData Resource := {
    state.toSharedStateData with
      model := transition.state
      closing
      retained
      closeDriver := driver
  }
  let currentIds := state.current.toList.map
    (fun generation => generation.generation)
  let beforeIds := extracted.before.map
    (fun generation => generation.generation)
  let afterIds := extracted.after.map
    (fun generation => generation.generation)
  let retainedIds := state.retained.map
    (fun generation => generation.generation)
  let authoritativeId := extracted.authoritative.generation
  have movedCandidate :
      ((beforeIds ++ afterIds) ++ authoritativeId :: retainedIds).Perm
        (authoritativeId :: ((beforeIds ++ afterIds) ++ retainedIds)) :=
    List.perm_middle
  have movedOriginal :
      (beforeIds ++ authoritativeId :: (afterIds ++ retainedIds)).Perm
        (authoritativeId :: (beforeIds ++ (afterIds ++ retainedIds))) :=
    List.perm_middle
  have tailPermutation :
      ((beforeIds ++ afterIds) ++ authoritativeId :: retainedIds).Perm
        (beforeIds ++ authoritativeId :: (afterIds ++ retainedIds)) := by
    exact movedCandidate.trans (by
      simpa [List.append_assoc] using movedOriginal.symm)
  have generationPermutation :
      data.channelGenerationIds.Perm state.channelGenerationIds := by
    have withCurrent := tailPermutation.append_left currentIds
    simpa [data, closing, retained, currentIds, beforeIds, afterIds,
      retainedIds, authoritativeId, SharedStateData.channelGenerationIds,
      extracted.reconstruct, List.append_assoc] using withCurrent
  let next : SharedState Resource := SharedState.ofData data
    (generationPermutation.symm.nodup state.generation_ids_unique)
    (by
      intro generation member
      exact state.generations_below generation
        (generationPermutation.mem_iff.mp member))
    (by simpa [data] using state.initialization_generation_coherent)
    (by
      cases task : state.initialization.taskGeneration? with
      | none =>
          change state.initialization.taskDisjoint data.channelGenerationIds
          simp [InitializationState.taskDisjoint, task]
      | some generation =>
          have disjoint :
              ¬ generation ∈ state.channelGenerationIds := by
            simpa [InitializationState.taskDisjoint, task] using
              state.initialization_task_disjoint
          change state.initialization.taskDisjoint data.channelGenerationIds
          simp only [InitializationState.taskDisjoint, task]
          intro member
          exact disjoint (generationPermutation.mem_iff.mp member))
    (by simpa [data] using state.current_excludes_initializer_task)
    (by
      simpa [data, driver, transition] using
        SharedState.beginClose_driver_phaseCoherent state.closeDriver state.model
          state.close_driver_phase_coherent)
    (by
      intro _
      exact ChannelLease.beginClose_phase_nonaccepting state.model)
    (by
      intro closed
      have oldClosed := ChannelLease.beginClose_closed_implies_closed state.model (by
        simpa [data, transition] using closed)
      exact False.elim
        (not_closed_of_closingExtraction state requested extracted oldClosed))
  exact (next, {
    decision := transition.decision
    drained := transition.state.activeCount == 0
  })

end SharedState

private def settleStagedClose
    (shared : ManagedChannel Resource)
    (generation : ConnectedGeneration Resource)
    (failed : Bool) : IO (Option CloseClaim) :=
  shared.state.atomically do
    let current ← get
    match extractClosing current.closing generation.generation with
    | none => pure none
    | some extracted =>
        if failed then
          let (next, claim) :=
            SharedState.settleClosingFailure current
              generation.generation extracted
          set next
          pure (some claim)
        else
          set (SharedState.settleClosingSuccess current
            generation.generation extracted)
          pure none

private def closeStaged
    (shared : ManagedChannel Resource)
    (generation : ConnectedGeneration Resource) : IO Unit := do
  let failed ← try
    pure (!(← Subchannel.close generation.channel).isOk)
  catch _ =>
    pure true
  discard <| shared.settleStagedClose generation failed

private def closeStagedChannels
    (shared : ManagedChannel Resource) : IO Unit := do
  let staged ← shared.state.atomically do
    pure (← get).closing
  for generation in staged do
    shared.closeStaged generation

private def SharedState.publishClosed
    (state : SharedState Resource)
    (closed : ChannelLease.State)
    (finished : ChannelLease.finishClose state.model =
      .ok closed)
    (noCurrent : state.current = none)
    (clean : state.cleanupInventory.isClean = true)
    (driverClosed : state.closeDriver.phaseCoherent .closed) :
    SharedState Resource := by
  let data : SharedStateData Resource := {
    state.toSharedStateData with model := closed
  }
  have closedClean :=
    ChannelLease.finish_close_is_clean
      state.model closed finished
  have closedPhase : closed.phase = .closed := closedClean.1
  have closedActive : closed.activeCount = 0 := closedClean.2
  have cleanParts := (CleanupInventory.isClean_iff _).mp clean
  have channelLengths :
      state.closing.length + state.retained.length = 0 := by
    simpa [SharedState.cleanupInventory,
      SharedStateData.cleanupInventory] using cleanParts.1
  have closingNil : state.closing = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  have retainedNil : state.retained = [] := by
    apply List.eq_nil_of_length_eq_zero
    omega
  apply SharedState.ofData data
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.generation_ids_unique
  · intro generation member
    exact state.generations_below generation (by
      simpa [data, SharedStateData.channelGenerationIds] using member)
  · simpa [data] using state.initialization_generation_coherent
  · simpa [data, SharedStateData.channelGenerationIds] using
      state.initialization_task_disjoint
  · simpa [data] using state.current_excludes_initializer_task
  · simpa [data, closedPhase] using driverClosed
  · intro _ accepting
    have : closed.phase = .accepting := by
      simpa [data] using accepting
    rw [closedPhase] at this
    contradiction
  · intro _
    exact ⟨closedActive, by simpa [data] using noCurrent,
      by simpa [data] using closingNil,
      by simpa [data] using retainedNil,
      by simpa [data] using clean⟩

private def publishClosed
    (shared : ManagedChannel Resource) : IO (Except CloseError Unit) :=
  shared.state.atomically do
    let current ← get
    let driverClosed? : Option
        (PLift (current.closeDriver.phaseCoherent .closed)) :=
      match driverSlot : current.closeDriver with
      | .inline => some ⟨by trivial⟩
      | .detached _ _ => some ⟨by trivial⟩
      | .absent | .needsOwner | .startingBounded _ | .startingJoining _
      | .inlineTerminal => none
    match driverClosed? with
    | none => pure (.error .supervisorInvariant)
    | some driverClosed =>
      let inventory := current.cleanupInventory
      -- Broken supervisor/task evidence has diagnostic precedence over exact
      -- transport debt in the joined close result; neither class is erased.
      if supervisorDebt :
          inventory.uncertainInitializations ≠ 0 ∨
          inventory.invariantInitializations ≠ 0 ∨
          inventory.pendingInitializations ≠ 0 then
        pure (.error .supervisorInvariant)
      else
        match currentSlot : current.current with
        | some _ => pure (.error .transport)
        | none =>
          if exactDebt :
              inventory.channelOwners ≠ 0 ∨
              inventory.initializationOwners ≠ 0 then
            pure (.error .transport)
          else
            have clean : inventory.isClean = true := by
              apply (CleanupInventory.isClean_iff inventory).2
              simp_all
            match finished :
                ChannelLease.finishClose current.model with
            | .error _ => pure (.error .supervisorInvariant)
            | .ok closed =>
                set (SharedState.publishClosed current closed finished
                  currentSlot clean driverClosed.down)
                pure (.ok ())

private def finishClaimedClose
    (shared : ManagedChannel Resource) : IO Unit := do
  let result : Except CloseError Unit ← try
    let some () ← IO.wait shared.drained.result?
      | pure (.error .completionDropped)
    let initialization ← shared.takeClosingResources
    match initialization with
    | some pending => shared.initializedDuringClose pending
    | none => pure ()
    shared.closeStagedChannels
    shared.publishClosed
  catch _ =>
    pure (.error .transport)
  let published ← try
    shared.dependencies.beforeCloseCompletionPublication
    pure result
  catch _ =>
    pure (.error .completionDropped)
  shared.closeCompletion.resolve published
  shared.closeSettled.cancel

  -- Completion is authoritative. Detached task custody remains reachable in
  -- state after termination; only the task-free inline form becomes terminal.
  shared.state.atomically do
    let current ← get
    match slot : current.closeDriver with
    | .inline => set (current.markInlineCloseTerminal slot)
    | .absent | .needsOwner | .startingBounded _ | .startingJoining _
    | .detached _ _ | .inlineTerminal => pure ()

private inductive CloseDriverAvailability where
  | take (ticket : CloseStarterTicket)
  | startingBounded
  | startingJoining
  | driven

private inductive CloseDriverStartOutcome where
  | driven
  | needsDriver

private inductive CloseDriverStartAttempt where
  | driven
  | needsDriver
  | retry

private def takeClaimedCloseOwner
    (shared : ManagedChannel Resource)
    (allowInlineFallback : Bool) : IO CloseDriverAvailability := do
  let ticket ← CloseStarterTicket.create
  shared.state.atomically do
    let current ← get
    match slot : current.closeDriver with
    | .needsOwner =>
        if allowInlineFallback then
          set (current.takeJoiningCloseDriver ticket slot)
        else
          set (current.takeBoundedCloseDriver ticket slot)
        pure (.take ticket)
    | .startingBounded _ => pure .startingBounded
    | .startingJoining _ => pure .startingJoining
    | .absent | .detached _ _ | .inline | .inlineTerminal => pure .driven

/--
Start the unique owner of a previously published and atomically taken close
claim. A bounded request restores needs-owner custody if allocation fails. A
joining close preserves the original synchronous/last-releaser fallback and
therefore cannot strand the completion promise.
-/
private def startClaimedClose
    (shared : ManagedChannel Resource)
    (allowInlineFallback : Bool)
    (ticket : CloseStarterTicket)
    (initializationOwner? :
      Option Cancellation) :
    IO CloseDriverStartAttempt := do
  let spawned : Except IO.Error (CloseTask × IO.Promise Unit) ← try
    shared.dependencies.beforeClaimedCloseTask
    let publication : IO.Promise Unit ← IO.Promise.new
    let owner ← IO.asTask (do
      let some () ← IO.wait publication.result?
        | return
      -- State, rather than a publication-local flag, authorizes the effect.
      -- A delayed/stale task wakes, observes no exact detached ticket, and
      -- exits without touching transport custody.
      let approved ← shared.state.atomically do
        let current ← get
        match current.closeDriver with
        | .detached stored _ => stored.same ticket
        | .absent | .needsOwner | .startingBounded _ | .startingJoining _
        | .inline | .inlineTerminal => pure false
      if approved then shared.finishClaimedClose else pure ())
      Task.Priority.dedicated
    pure (Except.ok (owner, publication))
  catch error =>
    pure (Except.error error)
  match spawned with
  | Except.ok (owner, publication) =>
      try
        shared.dependencies.beforeClaimedCloseTaskPublication
      catch _ =>
        pure ()
      let approved ← try
        shared.state.atomically do
          let current ← get
          match slot : current.closeDriver with
          | .startingBounded stored =>
              if ← stored.same ticket then
                set (current.publishBoundedCloseDriver stored owner slot)
                pure true
              else
                pure false
          | .startingJoining stored =>
              if ← stored.same ticket then
                set (current.publishJoiningCloseDriver stored owner slot)
                pure true
              else
                pure false
          | .absent | .needsOwner | .detached _ _ | .inline
          | .inlineTerminal => pure false
      catch _ =>
        -- An interrupted publication may have committed, not started, or
        -- stopped between those points. Recover only this exact ticket.
        shared.state.atomically do
          let current ← get
          match slot : current.closeDriver with
          | .detached stored _ => stored.same ticket
          | .startingBounded stored =>
              if ← stored.same ticket then
                set (current.restoreBoundedCloseDriver stored slot)
              pure false
          | .startingJoining stored =>
              if ← stored.same ticket then
                set (current.restoreJoiningCloseDriver stored slot)
              pure false
          | .absent | .needsOwner | .inline | .inlineTerminal => pure false
      finally
        -- Even interruption of mutex acquisition/publication must wake the
        -- candidate. State identity below decides whether it may run.
        publication.resolve ()
      if !approved then
        -- Rejected publication has no state custody. Join its gate-only task
        -- before returning so even the allocated task handle is not leaked.
        discard <| IO.wait owner
      if approved then pure .driven else pure .retry
  | Except.error _ =>
      if !allowInlineFallback then
        -- A bounded caller must not turn allocation failure into unbounded
        -- cleanup. Restore exact custody for a later bounded request or the
        -- joining close path.
        let restored ← shared.state.atomically do
          let current ← get
          match slot : current.closeDriver with
          | .startingBounded stored =>
              if ← stored.same ticket then
                set (current.restoreBoundedCloseDriver stored slot)
                pure true
              else
                pure false
          | .absent | .needsOwner | .startingJoining _ | .detached _ _
          | .inline | .inlineTerminal => pure false
        if restored then pure .needsDriver else pure .retry
      else
        -- `retire` and most failed-initialization callers run under an admitted
        -- outer lease. They cannot synchronously wait for `drained`, because
        -- that lease is released only after they return. If leases remain,
        -- transfer fallback custody to the unique last releaser. With no
        -- leases, a terminal initializer may itself be this caller: its exact
        -- cleanup authority already lives in `FailedInitialization`, so drop
        -- only the data-only task handle before inline close to avoid self-join.
        let fallback? ← shared.state.atomically do
          let current ← get
          match driverSlot : current.closeDriver with
          | .startingJoining stored =>
              if ← stored.same ticket then
                if current.model.activeCount == 0 then
                  match initializationSlot : current.initialization with
                  | .failed failure (some initialization) =>
                      let isSelf ← match initializationOwner? with
                        | some owner =>
                            owner.same initialization.completion
                        | none => pure false
                      if isSelf then
                        let cleared := current.clearFailedInitializationTask
                          failure initialization initializationSlot
                        have clearedDriver :
                            cleared.closeDriver = .startingJoining stored := by
                          simpa [cleared,
                            SharedState.clearFailedInitializationTask] using
                            driverSlot
                        set (cleared.inlineJoiningCloseDriver
                          stored clearedDriver)
                      else
                        set (current.inlineJoiningCloseDriver
                          stored driverSlot)
                  | .idle | .pending _ | .failed _ none =>
                      set (current.inlineJoiningCloseDriver stored driverSlot)
                  pure (some true)
                else
                  set (current.restoreJoiningCloseDriver stored driverSlot)
                  pure (some false)
              else
                pure none
          | .absent | .needsOwner | .startingBounded _ | .detached _ _
          | .inline | .inlineTerminal => pure none
        match fallback? with
        | some true =>
            try
              shared.dependencies.afterInlineCloseDriverPublication
            catch _ =>
              pure ()
            shared.finishClaimedClose
            pure .driven
        | some false => pure .driven
        | none => pure .retry

/--
Ensure that the one close generation has an exact completion owner. Joining
callers wait through another caller's short allocation attempt so they can
retake custody restored by failure; bounded callers only observe that attempt.
-/
private partial def ensureClaimedCloseOwner
    (shared : ManagedChannel Resource)
    (allowInlineFallback : Bool)
    (initializationOwner? :
      Option Cancellation := none) :
    IO CloseDriverStartOutcome := do
  match ← shared.takeClaimedCloseOwner allowInlineFallback with
  | .take ticket =>
      match ← startClaimedClose shared
          allowInlineFallback ticket initializationOwner? with
      | .retry =>
          shared.ensureClaimedCloseOwner
            allowInlineFallback initializationOwner?
      | .driven => pure .driven
      | .needsDriver => pure .needsDriver
  | .driven => pure .driven
  | .startingJoining =>
      -- A joining starter either publishes a task, transfers fallback to the
      -- last lease, or completes inline. In particular, an initializer must
      -- return instead of waiting on an inline closer that joined its task.
      pure .driven
  | .startingBounded =>
      -- A bounded starter may restore `needsOwner` after allocation failure.
      -- Joining callers wait through only that recoverable publication window.
      if !allowInlineFallback then
        pure .driven
      else
        IO.sleep 1
        shared.ensureClaimedCloseOwner
          allowInlineFallback initializationOwner?

/--
Transfer an atomically staged close claim to its detached owner. If this caller
fails before reaching this function, the last exact lease still owns structural
custody; if task allocation fails here, `startClaimedClose` restores the same
fallback.
-/
private def startStagedClaimedClose
    (shared : ManagedChannel Resource) : IO Unit := do
  discard <| shared.ensureClaimedCloseOwner true

def createWith
    (dependencies : ManagedChannel.Dependencies Resource)
    (configuration : ManagedChannel.Config) :
    IO (ManagedChannel Resource) := do
  let trustPreparation ←
    SharedTrustPreparation.create dependencies.loadTrust
  let sharedDependencies := {
    dependencies with
    loadTrust := trustPreparation.load
  }
  let closeHandoff ← IO.mkRef
    (fun _ : Option Cancellation => pure ())
  let shared : ManagedChannel Resource :=
    .mk sharedDependencies configuration
      (← Std.Mutex.new SharedState.initial)
      (← IO.Promise.new)
      closeHandoff
      (← IO.Promise.new)
      (← Cancellation.create)
  closeHandoff.set fun initializationOwner? => do
    discard <| shared.ensureClaimedCloseOwner true initializationOwner?
  pure shared

/--
Create the production owner without performing DNS, trust-store, or network
effects. The first RPC performs connection initialization.
-/
def create
    (configuration : ManagedChannel.Config) :
    IO (ManagedChannel Grpc.Client.Connection) :=
  createWith ManagedChannel.Dependencies.production configuration

private def retire
    (shared : ManagedChannel Resource)
    (generation : ConnectedGeneration Resource) : IO Bool := do
  match ← shared.takeGeneration generation with
  | none => pure true
  | some staged =>
      let closed ← try
        Subchannel.close staged.channel
      catch _ =>
        pure (.error .transport)
      match closed with
      | .ok () =>
          discard <| shared.settleStagedClose staged false
          pure true
      | .error _ =>
          let claim? ← shared.settleStagedClose staged true
          match claim? with
          | some claim =>
              if claim.decision == .claimed && claim.drained then
                shared.drained.resolve ()
              if claim.decision == .claimed then
                shared.startStagedClaimedClose
          | none => pure ()
          pure false

private def useGeneration
    (shared : ManagedChannel Resource)
    (action : Subchannel Resource → IO (Except CallError Response))
    (cancellation : Option Cancellation := none) :
    IO (Except CallError Response) := do
  let connected ← match cancellation with
    | none => shared.connected
    | some cancellation =>
        shared.connectedWithCancellation cancellation
  match connected with
  | .error .ownerCancelled => pure (.error .ownerCancelled)
  | .error (.unavailable failure) => pure (.error failure.callError)
  | .error (.opening failure) =>
      match failure.closeClaim? with
      | some claim =>
          if claim.decision == .claimed && claim.drained then
            shared.drained.resolve ()
      | none => pure ()
      if !failure.cancellationMayMask then
        shared.startStagedClaimedClose
      pure (.error failure.callError)
  | .ok generation =>
      let result ← action generation.channel
      match result with
      | .ok response => pure (.ok response)
      | .error error =>
          if requiresGenerationRetirement error then
            if ← shared.retire generation then
              pure (.error error)
            else
              match error with
              | .rpc _ _ =>
                  -- The admitted call has already settled with this exact
                  -- peer status. Failed retirement is retained by the shared
                  -- close owner, but must not overwrite the caller's result.
                  pure (.error error)
              | _ => pure (.error .cleanupUncertain)
          else
            pure (.error error)

private def mapAcquireError :
    ChannelLease.AcquireError → CallError
  | .draining => .channelDraining
  | .closed => .channelClosed

private def withLease
    (shared : ManagedChannel Resource)
    (action : IO (Except CallError Response)) :
    IO (Except CallError Response) := do
  match ← shared.acquire with
  | .error .draining =>
      -- A terminal initializer may have restored `needsOwner` after its
      -- non-inline handoff allocation failed with no active lease. A later
      -- ordinary call cannot acquire, but it still helps recover that exact
      -- close claim before returning the public draining error.
      discard <| shared.ensureClaimedCloseOwner false
      pure (.error .channelDraining)
  | .error .closed => pure (.error .channelClosed)
  | .ok lease =>
      let result : Except IO.Error (Except CallError Response) ←
        try
          pure (Except.ok (← action))
        catch error =>
          pure (Except.error error)
      match ← shared.release lease with
      | .error () => pure (.error .supervisorInvariant)
      | .ok released =>
        if released.becameDrained then shared.drained.resolve ()
        if released.ownsClaimedClose then shared.finishClaimedClose
        match result with
        | .ok value => pure value
        | .error _ => pure (.error .actionFailed)

private inductive InvocationCancellationOutcome where
  | disarmed
  | deadline
  | ownerCancelled
  | monitorFailed
deriving BEq, Repr

private abbrev InvocationCancellationTask :=
  Task (Except IO.Error InvocationCancellationOutcome)

private inductive InvocationGatePhase where
  | pending
  | started
  | completed
  | cancelled (outcome : InvocationCancellationOutcome)
deriving BEq, Repr

/--
The authoritative linearization for one absolute invocation.  `started` means
the exact transport start was admitted while the optional owner token was
locked and still active; `cancelled` means no later start may be admitted; and
`completed` was likewise published before owner cancellation. Deadline-only
transitions take this mutex directly; owner-sensitive transitions use the
fixed token-then-gate lock order.
-/
private structure InvocationGate where
  absoluteDeadline : Nat
  phase : Std.Mutex InvocationGatePhase

private def InvocationGate.cancel
    (gate : InvocationGate)
    (candidate : InvocationCancellationOutcome) :
    IO InvocationCancellationOutcome :=
  gate.phase.atomically do
    match ← get with
    | .completed => pure .disarmed
    | .cancelled outcome => pure outcome
    | .pending | .started =>
        set (InvocationGatePhase.cancelled candidate)
        pure candidate

private def InvocationGate.observe
    (gate : InvocationGate) : IO InvocationCancellationOutcome :=
  gate.phase.atomically do
    match ← get with
    | .completed => pure .disarmed
    | .cancelled outcome => pure outcome
    | .pending | .started => pure .monitorFailed

/--
Atomically admit the one transport start and return its exact remaining local
budget. A delayed monitor cannot admit a call after wall-clock expiry because
the same mutex transaction checks the absolute monotonic deadline. When an
owner token exists, `InvocationBudget.claimStart` calls this while holding that
token's active-state lock.
-/
private def InvocationGate.claimStart
    (gate : InvocationGate) :
    IO (Except InvocationCancellationOutcome Nat) :=
  gate.phase.atomically do
    match ← get with
    | .pending =>
        let now ← IO.monoMsNow
        if gate.absoluteDeadline ≤ now then
          set (InvocationGatePhase.cancelled .deadline)
          pure (.error .deadline)
        else
          set InvocationGatePhase.started
          pure (.ok (gate.absoluteDeadline - now))
    | .cancelled outcome => pure (.error outcome)
    | .started | .completed => pure (.error .monitorFailed)

/--
Publish action completion against the same deadline/cancellation gate. The
clock check prevents a scheduler-delayed monitor from allowing a result that
actually crossed the absolute deadline. Owner-sensitive completion holds the
same token lock used by transport admission.
-/
private def InvocationGate.finish
    (gate : InvocationGate) : IO InvocationCancellationOutcome :=
  gate.phase.atomically do
    match ← get with
    | .cancelled outcome => pure outcome
    | .completed => pure .monitorFailed
    | .pending | .started =>
        let now ← IO.monoMsNow
        if gate.absoluteDeadline ≤ now then
          set (InvocationGatePhase.cancelled .deadline)
          pure .deadline
        else
          set InvocationGatePhase.completed
          pure .disarmed

private def runInvocationCancellation
    (gate : InvocationGate)
    (signal disarm : Cancellation)
    (ownerCancellation : Option Cancellation) :
    IO InvocationCancellationOutcome := do
  try
    let now ← IO.monoMsNow
    let candidate ← if gate.absoluteDeadline ≤ now then
      pure InvocationCancellationOutcome.deadline
    else
      let remaining := gate.absoluteDeadline - now
      let sleeper ← (Std.Async.Sleep.mk
        (Std.Time.Millisecond.Offset.ofNat remaining)).block
      let base := #[
        Std.Async.Selectable.case disarm.selector fun _ =>
          pure InvocationCancellationOutcome.disarmed,
        Std.Async.Selectable.case sleeper.selector fun _ =>
          pure InvocationCancellationOutcome.deadline
      ]
      let choices := match ownerCancellation with
        | none => base
        | some owner => base.push <|
            Std.Async.Selectable.case owner.selector fun _ =>
              pure InvocationCancellationOutcome.ownerCancelled
      (Std.Async.Selectable.one choices).block
    let outcome ← match candidate with
      | .disarmed => gate.observe
      | .deadline | .ownerCancelled | .monitorFailed =>
          gate.cancel candidate
    if outcome != .disarmed then signal.cancel
    pure outcome
  catch _ =>
    -- Fail closed: wake a blocked initializer/call and let the joined monitor
    -- result distinguish infrastructure failure from a real owner deadline.
    let outcome ← gate.cancel .monitorFailed
    if outcome != .disarmed then signal.cancel
    pure outcome

/-- Exact owner of one absolute invocation budget and its monitor task. -/
private structure InvocationBudget where
  startedAt : Nat
  declaredDeadline : RpcDeadline
  ownerCancellation : Option Cancellation
  signal : Cancellation
  disarm : Cancellation
  gate : InvocationGate
  owner : InvocationCancellationTask

private def InvocationBudget.startAt
    (startedAt : Nat)
    (deadline : RpcDeadline)
    (ownerCancellation : Option Cancellation) :
    IO (Except CallError InvocationBudget) := do
  match ownerCancellation with
  | some owner =>
      if ← owner.isCancelled then return .error .ownerCancelled
  | none => pure ()
  let signal ← Cancellation.create
  let disarm ← Cancellation.create
  let gate : InvocationGate := {
    absoluteDeadline := startedAt + deadline.seconds * 1_000
    phase := ← Std.Mutex.new .pending
  }
  let monitor : Except IO.Error InvocationCancellationTask ← try
    pure (Except.ok (← IO.asTask
      (runInvocationCancellation gate signal disarm ownerCancellation)
      Task.Priority.dedicated))
  catch error =>
    pure (Except.error error)
  match monitor with
  | .error _ => pure (.error .supervisorInvariant)
  | .ok owner => pure (.ok {
      startedAt
      declaredDeadline := deadline
      ownerCancellation
      signal
      disarm
      gate
      owner
    })

private def InvocationBudget.start
    (deadline : RpcDeadline)
    (ownerCancellation : Option Cancellation) :
    IO (Except CallError InvocationBudget) := do
  let startedAt ← try
    IO.monoMsNow
  catch _ =>
    return .error .supervisorInvariant
  InvocationBudget.startAt startedAt deadline ownerCancellation

/--
Claim the transport start for this invocation.  `none` is intentionally mapped
to the inner adapter's `ownerCancelled`; `finish` below restores the exact
deadline/owner/monitor provenance from the authoritative gate.
-/
private def InvocationBudget.claimStart
    (budget : InvocationBudget) : IO (Option Nat) := do
  let admitted ← try
    match budget.ownerCancellation with
    | none => budget.gate.claimStart
    | some owner =>
        match ← owner.linearizeIfActive budget.gate.claimStart with
        | some admitted => pure admitted
        | none => pure (.error .ownerCancelled)
  catch _ =>
    pure (.error .monitorFailed)
  match admitted with
  | .ok remaining => pure (some remaining)
  | .error candidate =>
      let outcome ← budget.gate.cancel candidate
      if outcome != .disarmed then budget.signal.cancel
      pure none

private def InvocationBudget.finishCore
    (budget : InvocationBudget)
    (result : Except CallError Response) :
    IO (Except CallError Response) := do
  let completion ← try
    match budget.ownerCancellation with
    | none => budget.gate.finish
    | some owner =>
        match ← owner.linearizeIfActive budget.gate.finish with
        | some outcome => pure outcome
        | none => budget.gate.cancel .ownerCancelled
  catch _ =>
    budget.gate.cancel .monitorFailed
  if completion != .disarmed then budget.signal.cancel
  budget.disarm.cancel
  let monitorFailed ← match ← IO.wait budget.owner with
    | .error _ => pure true
    | .ok _ => pure false
  let outcome ← if monitorFailed then
      pure InvocationCancellationOutcome.monitorFailed
    else
      budget.gate.observe
  match result with
  | .error .cleanupUncertain => pure (.error .cleanupUncertain)
  | .error .supervisorInvariant => pure (.error .supervisorInvariant)
  | .error (.rpc status statusDetails) =>
      pure (.error (.rpc status statusDetails))
  | .error .callActionFailed => pure (.error .callActionFailed)
  | .error .actionFailed => pure (.error .actionFailed)
  | result =>
      match outcome with
      | .disarmed => pure result
      | .deadline => pure (.error .localDeadlineExceeded)
      | .ownerCancelled => pure (.error .ownerCancelled)
      | .monitorFailed => pure (.error .supervisorInvariant)

/--
Finalization is a non-throwing ownership boundary.  Even an unexpected local
effect failure publishes cancellation to both waiters and joins the exact
monitor task before reporting a supervisor invariant.
-/
private def InvocationBudget.finish
    (budget : InvocationBudget)
    (result : Except CallError Response) :
    IO (Except CallError Response) := do
  try
    budget.finishCore result
  catch _ =>
    try budget.signal.cancel catch _ => pure ()
    try budget.disarm.cancel catch _ => pure ()
    try discard <| IO.wait budget.owner catch _ => pure ()
    pure (.error .supervisorInvariant)

/--
Own one absolute invocation budget from before lazy initialization through the
exact call and lease release. Native setup remains independently staged if it
cannot observe cancellation; expiration returns without erasing that task.
-/
private def withInvocationDeadline
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (ownerCancellation : Option Cancellation)
    (action : Subchannel Resource → InvocationBudget →
      IO (Except CallError Response)) : IO (Except CallError Response) := do
  let actionFinished ← try
    IO.mkRef false
  catch _ =>
    return .error .supervisorInvariant
  let budget ← match ← InvocationBudget.start deadline ownerCancellation with
    | .error error => return .error error
    | .ok budget => pure budget
  let result ← shared.withLease do
    let result ← shared.useGeneration (cancellation := some budget.signal)
      fun generation => do
        let raw : Except CallError Response ← try
          action generation budget
        catch _ =>
          pure (.error .actionFailed)
        let classified ← budget.finish raw
        actionFinished.set true
        pure classified
    pure result
  if ← actionFinished.get then
    pure result
  else
    budget.finish result

/-- Issue one exact typed call using an already-owned absolute budget. -/
private def unaryWithBudget
    (channel : Subchannel Grpc.Client.Connection)
    (budget : InvocationBudget)
    (deadline : RpcDeadline)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  Subchannel.unaryWith channel fun connection configuration =>
    (UnaryCall.unaryCancellableWithPermit connection
      { configuration with deadline } budget.signal budget.claimStart
      method encode decode request).block

/-- Runtime phase of one exact-generation callback capability. -/
private inductive GenerationScopePhase where
  | open
  | draining
  | closed
deriving BEq

/-- Unique ownership token for one invocation admitted by a generation. -/
private structure GenerationInvocationTicket where
  id : Nat
deriving BEq

/--
The mutex is the authoritative supervisor state for the scoped capability.
`active` contains every and only invocation that may still touch `resource`.
The first transport-class result is sticky so a detached, already-admitted
call cannot have its retirement evidence discarded when the callback returns.
-/
private structure GenerationScopeState where
  phase : GenerationScopePhase := .open
  nextTicket : Nat := 0
  active : List GenerationInvocationTicket := []
  retirement : Option CallError := none

private structure GenerationScope where
  state : Std.Mutex GenerationScopeState
  drained : IO.Promise Unit

namespace GenerationScope

private def create : IO GenerationScope := do
  pure {
    state := ← Std.Mutex.new {}
    drained := ← IO.Promise.new
  }

private def acquire
    (scope : GenerationScope) :
    IO (Except CallError GenerationInvocationTicket) :=
  scope.state.atomically do
    let current ← get
    match current.phase with
    | .draining | .closed => pure (.error .scopeClosed)
    | .open =>
        match current.retirement with
        | some error => pure (.error error)
        | none =>
            let ticket := { id := current.nextTicket }
            set { current with
              nextTicket := current.nextTicket + 1
              active := ticket :: current.active
            }
            pure (.ok ticket)

private def withoutTicket
    (ticket : GenerationInvocationTicket)
    (active : List GenerationInvocationTicket) :
    Option (List GenerationInvocationTicket) :=
  if active.contains ticket then
    some (active.erase ticket)
  else
    none

/--
Release exactly one invocation token and atomically publish its retirement
evidence before waking the callback's drain owner.
-/
private def release
    (scope : GenerationScope)
    (ticket : GenerationInvocationTicket)
    (result : Except CallError Response) : IO Bool := do
  let released : Except Unit Bool ← scope.state.atomically do
    let current ← get
    let some active := withoutTicket ticket current.active
      | pure (.error ())
    let retirement := mergeRetirement current.retirement result
    set { current with active, retirement }
    pure (.ok (current.phase == .draining && active.isEmpty))
  match released with
  | .error () => pure false
  | .ok becameDrained =>
      if becameDrained then scope.drained.resolve ()
      pure true

/--
Close admission at callback return, join every admitted invocation, then make
the escaped capability permanently inert. The sticky retirement result is
returned only after its reporting invocation has released its exact ticket.
-/
private def closeAndDrain
    (scope : GenerationScope) : IO (Except CallError (Option CallError)) := do
  let transition : Except Unit Bool ← scope.state.atomically do
    let current ← get
    match current.phase with
    | .open =>
        set { current with phase := .draining }
        pure (.ok current.active.isEmpty)
    | .draining | .closed => pure (.error ())
  let .ok alreadyDrained := transition
    | return .error .supervisorInvariant
  if alreadyDrained then scope.drained.resolve ()
  let some () ← IO.wait scope.drained.result?
    | return .error .supervisorInvariant
  scope.state.atomically do
    let current ← get
    if current.phase != .draining || !current.active.isEmpty then
      pure (.error .supervisorInvariant)
    else
      set { current with phase := .closed }
      pure (.ok current.retirement)

end GenerationScope

/-- Setup budget plus whether the callback declared its exact first policy. -/
private structure PreparedInvocationBudget where
  budget : InvocationBudget
  exactPolicy : Bool

/--
One exact connected generation retained for the whole scope of a compound
operation. Unlike selecting a `Subchannel` and issuing separate calls, this
capability keeps the inner `ChannelOwner.Owner` lease across every admitted
invocation. Its runtime gate makes capture safe: admission closes when the
callback returns, admitted invocations drain before lease release, and later
uses of an escaped value fail with `scopeClosed`.
-/
structure Generation (Resource : Type) where
  private mk ::
  private resource : Resource
  private configuration : ManagedChannel.Config
  private scope : GenerationScope
  /-- Serializes first-budget selection with authoritative scope admission. -/
  private admission : Std.Mutex Unit
  private beforeScopeAdmission : IO Unit
  /--
  The setup budget is consumed by exactly the first admitted invocation.  It
  is mutex-owned because a trusted callback may begin concurrent invocations.
  -/
  private firstBudget : Std.Mutex (Option PreparedInvocationBudget)

namespace Generation

private structure AdmittedInvocation where
  ticket : GenerationInvocationTicket
  budget : InvocationBudget

private def takeBudget
    (generation : Generation Resource)
    (requestedAt : Nat)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation) :
    IO (Except CallError InvocationBudget) := do
  let prepared ← generation.firstBudget.atomically do
    let current ← get
    set (none : Option PreparedInvocationBudget)
    pure current
  match prepared with
  | some prepared =>
      let budget := prepared.budget
      let sameCancellation ← match budget.ownerCancellation, cancellation with
        | none, none => pure true
        | some left, some right => left.same right
        | _, _ => pure false
      if budget.declaredDeadline == deadline && sameCancellation then
        pure (.ok budget)
      else if prepared.exactPolicy then
        match ← budget.finish
            (.error .supervisorInvariant : Except CallError Unit) with
        | .error error => pure (.error error)
        | .ok () => pure (.error .supervisorInvariant)
      else
        -- The setup owner starts with the channel's default cap because the
        -- callback has not yet supplied its first call policy.  Transfer it
        -- exactly once into that policy without restarting time: a longer,
        -- shorter, or cancellable first call remains anchored at setup entry.
        match ← budget.finish (.ok () : Except CallError Unit) with
        | .error error => pure (.error error)
        | .ok () =>
            InvocationBudget.startAt budget.startedAt deadline cancellation
  | none => InvocationBudget.startAt requestedAt deadline cancellation

private def rejectAdmission
    (generation : Generation Resource)
    (error : CallError) : IO (Except CallError AdmittedInvocation) := do
  match ← generation.scope.acquire with
  | .error scopeError => pure (.error scopeError)
  | .ok ticket =>
      if ← generation.scope.release ticket
          (.error error : Except CallError Unit) then
        pure (.error error)
      else
        pure (.error .supervisorInvariant)

private def admitAt
    (generation : Generation Resource)
    (requestedAt : Except CallError Nat)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation) :
    IO (Except CallError AdmittedInvocation) :=
  generation.admission.atomically do
    let .ok requestedAt := requestedAt
      | return ← generation.rejectAdmission .supervisorInvariant
    let selected ← generation.takeBudget requestedAt deadline cancellation
    let hookSucceeded ← try
      generation.beforeScopeAdmission
      pure true
    catch _ =>
      pure false
    if !hookSucceeded then
      let error ← match selected with
        | .error _ => pure CallError.supervisorInvariant
        | .ok budget =>
            match ← budget.finish
                (.error .supervisorInvariant : Except CallError Unit) with
            | .error error => pure error
            | .ok () => pure .supervisorInvariant
      generation.rejectAdmission error
    else match selected with
    | .error budgetError =>
        -- Publish a policy/setup invariant to the sticky generation state
        -- before a concurrent invocation may select another budget.
        generation.rejectAdmission budgetError
    | .ok budget =>
        match ← generation.scope.acquire with
        | .ok ticket => pure (.ok { ticket, budget })
        | .error error =>
            match ← budget.finish (.error error : Except CallError Unit) with
            | .error classified => pure (.error classified)
            | .ok () => pure (.error .supervisorInvariant)

private def admit
    (generation : Generation Resource)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation) :
    IO (Except CallError AdmittedInvocation) := do
  -- Queueing behind the serialized first-policy decision consumes this
  -- invocation's own budget and observes its owner cancellation.
  let requestedAt ← try
    pure (Except.ok (← IO.monoMsNow) : Except CallError Nat)
  catch _ =>
    pure (.error .supervisorInvariant)
  generation.admitAt requestedAt deadline cancellation

/--
Finish the absolute budget before publishing the invocation result to the
generation scope. Thus deadline provenance and monitor failures participate in
the same retirement decision as transport errors. Scope admission failure is
still used to disarm/join the budget before returning.
-/
private def invokeAdmitted
    (generation : Generation Resource)
    (admitted : AdmittedInvocation)
    (action : IO (Except CallError Response)) :
    IO (Except CallError Response) := do
  let raw : Except CallError Response ← try
    action
  catch _ =>
    pure (.error .actionFailed)
  let result ← admitted.budget.finish raw
  if ← generation.scope.release admitted.ticket result then
    pure result
  else
    pure (.error .supervisorInvariant)

private def invokeWithPolicy
    (generation : Generation Resource)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) := do
  let admitted ← match ← generation.admit deadline cancellation with
    | .error error => return .error error
    | .ok admitted => pure admitted
  generation.invokeAdmitted admitted do
    match ← admitted.budget.claimStart with
    | none => pure (.error .ownerCancelled)
    | some _ =>
        pure ((← action generation.resource generation.configuration)
          |>.mapError mapCallError)

/-- Deterministic test seam with an already-captured invocation timestamp. -/
private def invokeWithPolicyAt
    (generation : Generation Resource)
    (requestedAt : Nat)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) := do
  let admitted ← match ←
      generation.admitAt (.ok requestedAt) deadline cancellation with
    | .error error => return .error error
    | .ok admitted => pure admitted
  generation.invokeAdmitted admitted do
    match ← admitted.budget.claimStart with
    | none => pure (.error .ownerCancelled)
    | some _ =>
        pure ((← action generation.resource generation.configuration)
          |>.mapError mapCallError)

private def invokeWith
    (generation : Generation Resource)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) :=
  generation.invokeWithPolicy generation.configuration.deadline none action

/-- Issue one typed unary call on the exact retained generation. -/
def invoke
    (generation : Generation Grpc.Client.Connection)
    (method : Grpc.MethodName)
    (encode : Request → Except EncodeError ByteArray)
    (decode : ByteArray → Except DecodeError Response)
    (deadline : Option RpcDeadline)
    (cancellation : Option Cancellation)
    (request : Request) : IO (Except CallError Response) :=
  do
    let effectiveDeadline := deadline.getD generation.configuration.deadline
    let admitted ← match ← generation.admit effectiveDeadline cancellation with
      | .error error => return .error error
      | .ok admitted => pure admitted
    generation.invokeAdmitted admitted do
      let call ← (UnaryCall.unaryCancellableWithPermit
        generation.resource { generation.configuration with
          deadline := effectiveDeadline }
        admitted.budget.signal admitted.budget.claimStart
        method encode decode request).block
      pure (call.mapError mapCallError)

end Generation

/--
Consume the setup budget, if no invocation claimed it, and classify the
enclosing result before its current supervisor scope is released.
-/
private def finishPreparedBudget
    (prepared : Std.Mutex (Option PreparedInvocationBudget))
    (result : Except CallError Response) :
    IO (Except CallError Response) := do
  let leftover ← prepared.atomically do
    let current ← get
    set (none : Option PreparedInvocationBudget)
    pure current
  match leftover with
  | some prepared => prepared.budget.finish result
  | none => pure result

/--
Implementation shared by the legacy default-policy scope and the explicit
first-policy scope.
-/
private def withGenerationUsingPolicy
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation)
    (exactPolicy : Bool)
    (action : Generation Resource →
      IO (Except CallError Response)) : IO (Except CallError Response) := do
  let budget ← match ← InvocationBudget.start deadline cancellation with
    | .error error => return .error error
    | .ok budget => pure budget
  let prepared ← try
    Std.Mutex.new (some { budget, exactPolicy })
  catch _ =>
    return ← budget.finish (.error .supervisorInvariant)
  let result ← shared.withLease do
    let result ←
    shared.useGeneration (cancellation := some budget.signal) fun connected => do
      match ← connected.owner.withResourceChecked fun resource => do
          let scope ← GenerationScope.create
          let admission ← Std.Mutex.new ()
          let generation := Generation.mk resource connected.configuration
            scope admission shared.dependencies.beforeGenerationScopeAdmission
            prepared
          let callback : Except CallError Response ← try
            action generation
          catch _ =>
            pure (.error .actionFailed)
          let drained ← scope.closeAndDrain
          let result := match drained with
            | .error error => mergeRetirementResult (some error) callback
            | .ok retirement => mergeRetirementResult retirement callback
          let result ← finishPreparedBudget prepared result
          match result with
          | .error .cleanupUncertain => pure .cleanupUncertain
          | result => pure (.release result) with
      | Except.error error => pure (Except.error (mapUseError error))
      | Except.ok result => pure result
    finishPreparedBudget prepared result
  finishPreparedBudget prepared result

/--
Run a compound action while retaining one exact connection generation, with
an explicitly declared policy governing setup and the first invocation from
the same monotonic start.  That first invocation must present the same
deadline and cancellation capability; a mismatch is a sticky supervisor
invariant and never reaches the transport.
-/
def withGenerationWithFirstPolicy
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation)
    (action : Generation Resource →
      IO (Except CallError Response)) : IO (Except CallError Response) :=
  shared.withGenerationUsingPolicy deadline cancellation true action

/--
Run a compound action while retaining both the shared call lease and the exact
inner connection-generation lease.  Setup uses the channel default policy.
If the callback's first invocation selects another policy, its clock is
transferred without restarting, but cancellation selected only inside the
callback cannot retroactively govern setup.  Callers requiring that stronger
contract use `withGenerationWithFirstPolicy`.

Any transport-class error returned by the action is still visible to
`useGeneration`, so retirement semantics are unchanged and the ambiguous call
is never replayed.
-/
def withGeneration
    (shared : ManagedChannel Resource)
    (action : Generation Resource →
      IO (Except CallError Response)) : IO (Except CallError Response) :=
  shared.withGenerationUsingPolicy shared.configuration.deadline none false action

/-! Generic resource access exists only in an explicitly named test surface. -/

namespace TestSupport

/-!
`SupervisorSnapshot` is an intentionally white-box test observation surface.
Its sums expose lifecycle shape, but never the channel/resource, task,
cancellation, starter-ticket, lease, mutex, or promise capabilities carried by
the private supervisor state.
-/

inductive SupervisorInitializationFailureKind where
  | terminalPolicy
  | cleanupUncertain
  | cleanupAuthorityMissing
  | taskUncertain
  | connectorInvariant
deriving BEq, DecidableEq, Repr

inductive SupervisorInitialization where
  | idle
  | pending (generation : Nat)
  | failed
      (kind : SupervisorInitializationFailureKind)
      (failureGeneration : Nat)
      (taskGeneration? : Option Nat)
deriving BEq, DecidableEq, Repr

namespace SupervisorInitialization

def taskGeneration? : SupervisorInitialization → Option Nat
  | .idle | .failed _ _ none => none
  | .pending generation | .failed _ _ (some generation) => some generation

def isTerminal : SupervisorInitialization → Bool
  | .failed _ _ _ => true
  | .idle | .pending _ => false

def generationCoherent
    (initialization : SupervisorInitialization)
    (nextGeneration : Nat) : Prop :=
  match initialization with
  | .idle => True
  | .pending generation => generation < nextGeneration
  | .failed _ _ none => True
  | .failed _ failureGeneration (some taskGeneration) =>
      taskGeneration < nextGeneration ∧
        failureGeneration = taskGeneration

def taskDisjoint
    (initialization : SupervisorInitialization)
    (channelGenerations : List Nat) : Prop :=
  match initialization.taskGeneration? with
  | none => True
  | some generation => generation ∉ channelGenerations

end SupervisorInitialization

inductive SupervisorCloseDriver where
  | absent
  | needsOwner
  | startingBounded
  | startingJoining
  | detached
  | inline
  | inlineTerminal
deriving BEq, DecidableEq, Repr

namespace SupervisorCloseDriver

def phaseCoherent
    (driver : SupervisorCloseDriver)
    (phase : ChannelLease.Phase) : Prop :=
  match phase, driver with
  | .accepting, .absent => True
  | .draining, .needsOwner
  | .draining, .startingBounded
  | .draining, .startingJoining
  | .draining, .detached
  | .draining, .inline
  | .draining, .inlineTerminal => True
  | .closed, .detached
  | .closed, .inline
  | .closed, .inlineTerminal => True
  | _, _ => False

end SupervisorCloseDriver

private def supervisorChannelGenerationIds
    (currentGeneration? : Option Nat)
    (closingGenerations retainedGenerations : List Nat) : List Nat :=
  currentGeneration?.toList ++ closingGenerations ++ retainedGenerations

private def supervisorHasTerminalEvidence
    (initialization : SupervisorInitialization)
    (quarantinedInitializationOwnerCount : Nat)
    (quarantinedInitializationUncertainty : Bool)
    (retainedGenerations : List Nat) : Bool :=
  initialization.isTerminal ||
    quarantinedInitializationOwnerCount != 0 ||
    quarantinedInitializationUncertainty ||
    !retainedGenerations.isEmpty

private structure SupervisorSnapshotCertificate
    (phase : ChannelLease.Phase)
    (activeCount nextGeneration : Nat)
    (currentGeneration? : Option Nat)
    (closingGenerations retainedGenerations : List Nat)
    (initialization : SupervisorInitialization)
    (quarantinedInitializationOwnerCount : Nat)
    (quarantinedInitializationUncertainty : Bool)
    (cleanupInventory : CleanupInventory)
    (closeDriver : SupervisorCloseDriver) : Prop where
  generationIdsUnique :
    (supervisorChannelGenerationIds currentGeneration?
      closingGenerations retainedGenerations).Nodup
  generationsBelow : ∀ generation,
    generation ∈ supervisorChannelGenerationIds currentGeneration?
      closingGenerations retainedGenerations →
        generation < nextGeneration
  initializationGenerationCoherent :
    initialization.generationCoherent nextGeneration
  initializationTaskDisjoint :
    initialization.taskDisjoint
      (supervisorChannelGenerationIds currentGeneration?
        closingGenerations retainedGenerations)
  currentExcludesInitializerTask :
    currentGeneration?.isSome = true →
      initialization.taskGeneration? = none
  closeDriverPhaseCoherent : closeDriver.phaseCoherent phase
  terminalNonaccepting :
    supervisorHasTerminalEvidence initialization
      quarantinedInitializationOwnerCount
      quarantinedInitializationUncertainty retainedGenerations = true →
        phase ≠ .accepting
  inventoryChannelOwners :
    cleanupInventory.channelOwners =
      closingGenerations.length + retainedGenerations.length
  inventoryPendingInitialization :
    cleanupInventory.pendingInitializations =
      if initialization.taskGeneration?.isSome then 1 else 0
  closedDrained : phase = .closed →
    activeCount = 0 ∧
      currentGeneration? = none ∧
      closingGenerations = [] ∧
      retainedGenerations = [] ∧
      cleanupInventory.isClean = true

structure SupervisorSnapshot where
  private mk ::
  phase : ChannelLease.Phase
  activeCount : Nat
  nextGeneration : Nat
  currentGeneration? : Option Nat
  closingGenerations : List Nat
  retainedGenerations : List Nat
  initialization : SupervisorInitialization
  quarantinedInitializationOwnerCount : Nat
  quarantinedInitializationUncertainty : Bool
  cleanupInventory : CleanupInventory
  closeDriver : SupervisorCloseDriver
  private certified : SupervisorSnapshotCertificate phase activeCount
    nextGeneration currentGeneration? closingGenerations retainedGenerations
    initialization quarantinedInitializationOwnerCount
    quarantinedInitializationUncertainty cleanupInventory closeDriver

namespace SupervisorSnapshot

def channelGenerationIds (snapshot : SupervisorSnapshot) : List Nat :=
  supervisorChannelGenerationIds snapshot.currentGeneration?
    snapshot.closingGenerations snapshot.retainedGenerations

def hasTerminalEvidence (snapshot : SupervisorSnapshot) : Bool :=
  supervisorHasTerminalEvidence snapshot.initialization
    snapshot.quarantinedInitializationOwnerCount
    snapshot.quarantinedInitializationUncertainty
    snapshot.retainedGenerations

/--
The capability-free clauses certified by the private supervisor state.  The
certificate stored in `SupervisorSnapshot` remains private; this public
structure makes every production invariant independently usable by tests.
-/
structure Invariant (snapshot : SupervisorSnapshot) : Prop where
  generationIdsUnique : snapshot.channelGenerationIds.Nodup
  generationsBelow : ∀ generation,
    generation ∈ snapshot.channelGenerationIds →
      generation < snapshot.nextGeneration
  initializationGenerationCoherent :
    snapshot.initialization.generationCoherent snapshot.nextGeneration
  initializationTaskDisjoint :
    snapshot.initialization.taskDisjoint snapshot.channelGenerationIds
  currentExcludesInitializerTask :
    snapshot.currentGeneration?.isSome = true →
      snapshot.initialization.taskGeneration? = none
  closeDriverPhaseCoherent :
    snapshot.closeDriver.phaseCoherent snapshot.phase
  terminalNonaccepting :
    snapshot.hasTerminalEvidence = true → snapshot.phase ≠ .accepting
  inventoryChannelOwners :
    snapshot.cleanupInventory.channelOwners =
      snapshot.closingGenerations.length +
        snapshot.retainedGenerations.length
  inventoryPendingInitialization :
    snapshot.cleanupInventory.pendingInitializations =
      if snapshot.initialization.taskGeneration?.isSome then 1 else 0
  closedDrained : snapshot.phase = .closed →
    snapshot.activeCount = 0 ∧
      snapshot.currentGeneration? = none ∧
      snapshot.closingGenerations = [] ∧
      snapshot.retainedGenerations = [] ∧
      snapshot.cleanupInventory.isClean = true

/-- Every atomic supervisor snapshot carries the public production invariant. -/
theorem invariant (snapshot : SupervisorSnapshot) : snapshot.Invariant := by
  have certified := snapshot.certified
  exact {
    generationIdsUnique := certified.generationIdsUnique
    generationsBelow := certified.generationsBelow
    initializationGenerationCoherent :=
      certified.initializationGenerationCoherent
    initializationTaskDisjoint := certified.initializationTaskDisjoint
    currentExcludesInitializerTask :=
      certified.currentExcludesInitializerTask
    closeDriverPhaseCoherent := certified.closeDriverPhaseCoherent
    terminalNonaccepting := certified.terminalNonaccepting
    inventoryChannelOwners := certified.inventoryChannelOwners
    inventoryPendingInitialization :=
      certified.inventoryPendingInitialization
    closedDrained := certified.closedDrained
  }

end SupervisorSnapshot

private def supervisorFailureKind :
    FailedInitialization Resource → SupervisorInitializationFailureKind
  | .terminalPolicy _ _ => .terminalPolicy
  | .cleanupUncertain _ _ _ => .cleanupUncertain
  | .cleanupAuthorityMissing _ _ => .cleanupAuthorityMissing
  | .taskUncertain _ => .taskUncertain
  | .connectorInvariant _ => .connectorInvariant

private def supervisorInitializationView :
    InitializationState Resource → SupervisorInitialization
  | .idle => .idle
  | .pending initialization => .pending initialization.generation
  | .failed failure pending? =>
      .failed (supervisorFailureKind failure) failure.generation
        (pending?.map fun initialization => initialization.generation)

private theorem supervisorInitialization_taskGeneration
    (state : InitializationState Resource) :
    (supervisorInitializationView state).taskGeneration? =
      state.taskGeneration? := by
  cases state with
  | idle => rfl
  | pending _ => rfl
  | failed failure pending? => cases pending? <;> rfl

private theorem supervisorInitialization_isTerminal
    (state : InitializationState Resource) :
    (supervisorInitializationView state).isTerminal = state.isTerminal := by
  cases state <;> rfl

private theorem supervisorInitialization_generationCoherent
    (state : InitializationState Resource)
    (nextGeneration : Nat) :
    (supervisorInitializationView state).generationCoherent nextGeneration ↔
      state.generationCoherent nextGeneration := by
  cases state with
  | idle => rfl
  | pending _ => rfl
  | failed failure pending? => cases pending? <;> rfl

private theorem supervisorInitialization_taskDisjoint
    (state : InitializationState Resource)
    (channelGenerations : List Nat) :
    (supervisorInitializationView state).taskDisjoint channelGenerations ↔
      state.taskDisjoint channelGenerations := by
  unfold SupervisorInitialization.taskDisjoint
  unfold InitializationState.taskDisjoint
  rw [supervisorInitialization_taskGeneration state]

private theorem supervisorInitialization_hasTask
    (state : InitializationState Resource) :
    (supervisorInitializationView state).taskGeneration?.isSome =
      state.hasReachableTask := by
  cases state with
  | idle => rfl
  | pending _ => rfl
  | failed failure pending? => cases pending? <;> rfl

private def supervisorCloseDriverView :
    CloseDriverState → SupervisorCloseDriver
  | .absent => .absent
  | .needsOwner => .needsOwner
  | .startingBounded _ => .startingBounded
  | .startingJoining _ => .startingJoining
  | .detached _ _ => .detached
  | .inline => .inline
  | .inlineTerminal => .inlineTerminal

private theorem supervisorCloseDriver_phaseCoherent
    (driver : CloseDriverState)
    (phase : ChannelLease.Phase) :
    (supervisorCloseDriverView driver).phaseCoherent phase ↔
      driver.phaseCoherent phase := by
  cases driver <;> cases phase <;> rfl

private theorem supervisorChannelGenerationIds_eq
    (state : SharedState Resource) :
    supervisorChannelGenerationIds
        (state.current.map fun generation => generation.generation)
        (state.closing.map fun generation => generation.generation)
        (state.retained.map fun generation => generation.generation) =
      state.channelGenerationIds := by
  cases current : state.current <;>
    simp [supervisorChannelGenerationIds,
      SharedStateData.channelGenerationIds, current]

private theorem supervisorHasTerminalEvidence_eq
    (state : SharedState Resource) :
    supervisorHasTerminalEvidence
        (supervisorInitializationView state.initialization)
        state.quarantinedInitializationOwners.length
        state.quarantinedInitializationUncertainty
        (state.retained.map fun generation => generation.generation) =
      state.hasTerminalEvidence := by
  rw [supervisorHasTerminalEvidence,
    supervisorInitialization_isTerminal state.initialization]
  cases owners : state.quarantinedInitializationOwners <;>
    simp [SharedStateData.hasTerminalEvidence, owners]

private theorem supervisorPendingInventory
    (state : SharedState Resource) :
    state.cleanupInventory.pendingInitializations =
      if (supervisorInitializationView
          state.initialization).taskGeneration?.isSome then
        1
      else
        0 := by
  rw [show state.cleanupInventory.pendingInitializations =
      state.initialization.cleanupInventory.pendingInitializations by rfl]
  rw [state.initialization.pendingInventory_eq_reachableTask]
  rw [supervisorInitialization_hasTask state.initialization]

private def supervisorSnapshotOfState
    (state : SharedState Resource) : SupervisorSnapshot := by
  let currentGeneration? :=
    state.current.map fun generation => generation.generation
  let closingGenerations :=
    state.closing.map fun generation => generation.generation
  let retainedGenerations :=
    state.retained.map fun generation => generation.generation
  let initialization := supervisorInitializationView state.initialization
  let quarantinedInitializationOwnerCount :=
    state.quarantinedInitializationOwners.length
  let cleanupInventory := state.cleanupInventory
  let closeDriver := supervisorCloseDriverView state.closeDriver
  have channelIds :
      supervisorChannelGenerationIds currentGeneration?
          closingGenerations retainedGenerations =
        state.channelGenerationIds := by
    simpa [currentGeneration?, closingGenerations, retainedGenerations] using
      supervisorChannelGenerationIds_eq state
  have terminalEvidence :
      supervisorHasTerminalEvidence initialization
          quarantinedInitializationOwnerCount
          state.quarantinedInitializationUncertainty retainedGenerations =
        state.hasTerminalEvidence := by
    simpa [initialization, quarantinedInitializationOwnerCount,
      retainedGenerations] using supervisorHasTerminalEvidence_eq state
  refine {
    phase := state.model.phase
    activeCount := state.model.activeCount
    nextGeneration := state.nextGeneration
    currentGeneration?
    closingGenerations
    retainedGenerations
    initialization
    quarantinedInitializationOwnerCount
    quarantinedInitializationUncertainty :=
      state.quarantinedInitializationUncertainty
    cleanupInventory
    closeDriver
    certified := ?_
  }
  constructor
  · rw [channelIds]
    exact state.generation_ids_unique
  · intro generation member
    rw [channelIds] at member
    exact state.generations_below generation member
  · exact (supervisorInitialization_generationCoherent
      state.initialization state.nextGeneration).2
        state.initialization_generation_coherent
  · rw [channelIds]
    exact (supervisorInitialization_taskDisjoint state.initialization
      state.channelGenerationIds).2 state.initialization_task_disjoint
  · intro present
    have statePresent : state.current.isSome = true := by
      simpa [currentGeneration?] using present
    have noTask := state.current_excludes_initializer_task statePresent
    simpa [initialization,
      supervisorInitialization_taskGeneration state.initialization] using noTask
  · exact (supervisorCloseDriver_phaseCoherent state.closeDriver
      state.model.phase).2 state.close_driver_phase_coherent
  · intro terminal
    apply state.terminal_nonaccepting
    rw [← terminalEvidence]
    exact terminal
  · simp [cleanupInventory, closingGenerations, retainedGenerations,
      SharedState.cleanupInventory, SharedStateData.cleanupInventory]
  · simpa [cleanupInventory, initialization] using
      supervisorPendingInventory state
  · intro closed
    have drained := state.closed_drained closed
    refine ⟨drained.1, ?_, ?_, ?_, ?_⟩
    · simpa [currentGeneration?] using drained.2.1
    · simpa [closingGenerations] using drained.2.2.1
    · simpa [retainedGenerations] using drained.2.2.2.1
    · simpa [cleanupInventory] using drained.2.2.2.2

/--
Read the entire certified supervisor projection under one state-mutex
linearization point. The returned value is capability-free.
-/
def supervisorSnapshot
    (shared : ManagedChannel Resource) : IO SupervisorSnapshot :=
  shared.state.atomically do
    pure (supervisorSnapshotOfState (← get))

/-- Read bounded terminal custody/evidence without exposing channel internals. -/
def cleanupInventory
    (shared : ManagedChannel Resource) : IO CleanupInventory :=
  shared.state.atomically do
    pure (← get).cleanupInventory

/-- Next lazy-initialization generation, exposed only to prove publication. -/
def nextInitializationGeneration
    (shared : ManagedChannel Resource) : IO Nat :=
  shared.state.atomically do
    pure (← get).nextGeneration

/--
Sanitized view of the one terminal initialization state. The cleanup variant
exposes the exact generic test resource together with its generation; production
code cannot extract a `ClaimedCleanupOwner`.
-/
inductive FailedInitializationEvidence (Resource : Type) where
  | terminalPolicy
      (generation : Nat)
      (error : OpenError)
  | cleanupUncertain
      (generation : Nat)
      (primaryError : OpenError)
      (primaryDisposition : OpenFailureDisposition)
      (resource : Resource)
  | cleanupAuthorityMissing
      (generation : Nat)
      (primaryError : OpenError)
      (primaryDisposition : OpenFailureDisposition)
  | taskUncertain (generation : Nat)
  | connectorInvariant (generation : Nat)
deriving BEq, Repr

/-- Test-only sanitized view of an unexpected quarantined cleanup owner. -/
structure QuarantinedInitializationEvidence (Resource : Type) where
  generation : Nat
  primaryError : OpenError
  primaryDisposition : OpenFailureDisposition
  resource : Resource
deriving BEq, Repr

/-- Test-only proof of the structural, generation-indexed failure state. -/
def failedInitializationEvidence?
    (shared : ManagedChannel Resource) :
    IO (Option (FailedInitializationEvidence Resource)) :=
  shared.state.atomically do
    match (← get).initialization with
    | .idle | .pending _ => pure none
    | .failed (.terminalPolicy generation policy) _ =>
        pure (some (.terminalPolicy generation
          (PrimaryOpenFailure.policy policy).error))
    | .failed (.cleanupUncertain generation primary owner) _ =>
        pure (some
          (.cleanupUncertain generation primary.error
            primary.disposition owner.resource))
    | .failed (.cleanupAuthorityMissing generation primary) _ =>
        pure (some (.cleanupAuthorityMissing generation primary.error
          primary.disposition))
    | .failed (.taskUncertain generation) _ =>
        pure (some (.taskUncertain generation))
    | .failed (.connectorInvariant generation) _ =>
        pure (some (.connectorInvariant generation))

/-- Exact generation/resource evidence for permanently quarantined owners. -/
def quarantinedInitializationEvidence
    (shared : ManagedChannel Resource) :
    IO (List (QuarantinedInitializationEvidence Resource)) :=
  shared.state.atomically do
    pure ((← get).quarantinedInitializationOwners.map fun retained => {
      generation := retained.generation
      primaryError := retained.primary.error
      primaryDisposition := retained.primary.disposition
      resource := retained.owner.resource
    })

/--
White-box settlement seam for generation-mismatch custody tests. It performs
the same claim publication/start handoff as a real shared caller while avoiding
fabricating a `PendingInitialization` task handle.
-/
def settleInitializationFailureForGeneration
    (shared : ManagedChannel Resource)
    (generation : Nat)
    (failure : OwnedOpenFailure Resource) : IO CallError := do
  let opening ←
    shared.transferOwnedInitializationFailure generation none failure
  match opening.closeClaim? with
  | some claim =>
      if claim.decision == .claimed && claim.drained then
        shared.drained.resolve ()
  | none => pure ()
  if !opening.cancellationMayMask then
    shared.startStagedClaimedClose
  pure opening.callError

/--
Present only a copied, data-only task diagnostic at an arbitrary generation.
The synthetic task is joined locally and carries no cleanup authority; this
seam proves that stale observations classify without changing supervisor
custody or lifecycle.
-/
def observeInitializationDiagnosticForGeneration
    (shared : ManagedChannel Resource)
    (generation : Nat) (failure : OpenFailure) : IO CallError := do
  let completion ← Cancellation.create
  let task : InitializationTask Resource ← IO.asTask
    (pure (.error failure) : IO (Except OpenFailure (Subchannel Resource)))
  let initialization : PendingInitialization Resource := {
    generation
    task
    completion
  }
  let opening ← shared.observeInitializationFailure initialization failure
  discard <| IO.wait task
  completion.cancel
  pure opening.callError

/-- Whether supervisor state retains the exact detached close-task owner. -/
def hasRetainedCloseTask
    (shared : ManagedChannel Resource) : IO Bool :=
  shared.state.atomically do
    pure (← get).closeDriver.hasDetachedTask

/-- Whether the one authoritative close result was published. -/
def closeCompletionResolved
    (shared : ManagedChannel Resource) : IO Bool :=
  shared.closeCompletion.isResolved

/-- Number of currently registered bounded close-completion selectors. -/
def closeSettlementWaiters
    (shared : ManagedChannel Resource) : IO Nat :=
  Cancellation.TestSupport.registeredWaiters
    shared.closeSettled

/-- Whether the close generation explicitly still needs a completion owner. -/
def closeNeedsOwner
    (shared : ManagedChannel Resource) : IO Bool :=
  shared.state.atomically do
    pure (← get).closeDriver.isNeedsOwner

/-- Whether one caller currently owns close-driver allocation or inline close. -/
def closeOwnerStarting
    (shared : ManagedChannel Resource) : IO Bool :=
  shared.state.atomically do
    pure (← get).closeDriver.starting

/--
Number of callers registered on the single completion signal for the current
initializer. `none` means that no initializer is staged. The signal itself is
copied out under the supervisor lock before its waiter count is inspected.
-/
def initializationCompletionWaiters
    (shared : ManagedChannel Resource) : IO (Option Nat) := do
  let completion? ← shared.state.atomically do
    match (← get).initialization with
    | .pending initialization => pure (some initialization.completion)
    | .failed _ (some initialization) =>
        pure (some initialization.completion)
    | .idle | .failed _ none => pure none
  match completion? with
  | none => pure none
  | some completion =>
      some <$>
        Cancellation.TestSupport.registeredWaiters
          completion

/-- Whether the exact staged initializer has reached a terminal task result. -/
def initializationTaskFinished
    (shared : ManagedChannel Resource) : IO (Option Bool) := do
  let task? ← shared.state.atomically do
    match (← get).initialization with
    | .pending initialization => pure (some initialization.task)
    | .failed _ (some initialization) => pure (some initialization.task)
    | .idle | .failed _ none => pure none
  match task? with
  | none => pure none
  | some task => some <$> IO.hasFinished task

/--
Generic deterministic seam for exercising cancellation while the shared owner
is still awaiting lazy initialization. Production callers use the typed RPC
functions below, which pass the same cancellation capability to the inner
call after initialization succeeds.
-/
def unaryWithInitializationCancellation
    (shared : ManagedChannel Resource)
    (cancellation : Cancellation)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) :=
  shared.withLease <|
    shared.useGeneration (cancellation := some cancellation) fun generation =>
      Subchannel.unaryWith generation action

/-- Exercise the production absolute budget across generic lazy setup. -/
def unaryWithInvocationDeadline
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) :=
  shared.withInvocationDeadline deadline none fun generation _ =>
    Subchannel.unaryWith generation action

/--
Deterministic seam exposing only the atomic transport-start permit.  It cannot
render credentials or release the leased resource; tests use it to prove that
expiry prevents start and that setup is deducted from the peer-call budget.
-/
def unaryWithInvocationPermit
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (action :
      Resource → ManagedChannel.Config → IO (Option Nat) →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) :=
  shared.withInvocationDeadline deadline none fun generation budget =>
    Subchannel.unaryWith generation fun resource configuration =>
      action resource configuration budget.claimStart

/-- Exercise owner cancellation combined with the production absolute budget. -/
def unaryWithInvocationDeadlineAndCancellation
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (cancellation : Cancellation)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) :=
  shared.withInvocationDeadline deadline (some cancellation)
    fun generation _ =>
      Subchannel.unaryWith generation action

/-- Revocable generic invoker for deterministic lifecycle tests. -/
structure GenerationInvoker (Resource InvocationResponse : Type) where
  invoke :
    (Resource → ManagedChannel.Config →
      IO (Except UnaryCall.Error InvocationResponse)) →
    IO (Except CallError InvocationResponse)
  invokeWithDeadline :
    RpcDeadline →
      (Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error InvocationResponse)) →
      IO (Except CallError InvocationResponse)
  invokeWithPolicy :
    RpcDeadline →
      Option Cancellation →
      (Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error InvocationResponse)) →
      IO (Except CallError InvocationResponse)
  invokeWithDeadlineAt :
    Nat → RpcDeadline →
      (Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error InvocationResponse)) →
      IO (Except CallError InvocationResponse)

private def generationInvoker
    (generation : Generation Resource) :
    GenerationInvoker Resource InvocationResponse := {
  invoke := generation.invokeWith
  invokeWithDeadline := fun deadline =>
    generation.invokeWithPolicy deadline none
  invokeWithPolicy := generation.invokeWithPolicy
  invokeWithDeadlineAt := fun requestedAt deadline =>
    generation.invokeWithPolicyAt requestedAt deadline none
}

/-- Exercise an exact-generation scope without exposing its production type. -/
def withGeneration
    (shared : ManagedChannel Resource)
    (action : GenerationInvoker Resource InvocationResponse →
      IO (Except CallError Response)) : IO (Except CallError Response) :=
  ManagedChannel.withGeneration shared fun generation =>
    action (generationInvoker generation)

/-- Exercise setup and first-call ownership under one explicitly matched policy. -/
def withGenerationWithFirstPolicy
    (shared : ManagedChannel Resource)
    (deadline : RpcDeadline)
    (cancellation : Option Cancellation)
    (action : GenerationInvoker Resource InvocationResponse →
      IO (Except CallError Response)) : IO (Except CallError Response) :=
  ManagedChannel.withGenerationWithFirstPolicy shared deadline cancellation
    fun generation => action (generationInvoker generation)

end TestSupport

/--
Trusted generic seam used by deterministic lazy/reconnection tests. The outer
lease covers initialization, the exact inner call lease, and any retirement
close. Production callers use the typed functions below.
-/
def unaryWith
    (shared : ManagedChannel Resource)
    (action :
      Resource → ManagedChannel.Config →
        IO (Except UnaryCall.Error Response)) :
    IO (Except CallError Response) :=
  shared.withLease <| shared.useGeneration fun generation =>
    Subchannel.unaryWith generation action

def unaryWithDeadline
    (shared : ManagedChannel Grpc.Client.Connection)
    (deadline : RpcDeadline)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  shared.withInvocationDeadline deadline none fun generation budget =>
    unaryWithBudget generation budget deadline method encode decode request

def unaryWithDeadlineAndCancellation
    (shared : ManagedChannel Grpc.Client.Connection)
    (deadline : RpcDeadline)
    (cancellation : Cancellation)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  shared.withInvocationDeadline deadline (some cancellation)
    fun generation budget =>
      unaryWithBudget generation budget deadline method encode decode request

def unaryWithCancellation
    (shared : ManagedChannel Grpc.Client.Connection)
    (cancellation : Cancellation)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  shared.unaryWithDeadlineAndCancellation shared.configuration.deadline
    cancellation method encode decode request

def unary
    (shared : ManagedChannel Grpc.Client.Connection)
    (method : Grpc.MethodName)
    (encode : Request → Except ε ByteArray)
    (decode : ByteArray → Except δ Response)
    (request : Request) :
    IO (Except CallError Response) :=
  shared.unaryWithDeadline shared.configuration.deadline
    method encode decode request

private def claimClose
    (shared : ManagedChannel Resource) :
    IO ChannelLease.BeginCloseDecision := do
  let (decision, drained) ← shared.state.atomically do
    let current ← get
    let (next, claim) := SharedState.beginClose current
    set next
    pure (claim.decision, claim.drained)
  if decision == .claimed && drained then shared.drained.resolve ()
  pure decision

/--
Request the one shared close generation without waiting for transport cleanup.
The first caller publishes its claim and takes needs-owner custody before task
allocation. If that allocation fails, `needsDriver` returns only after that
custody is restored; no resource, task, or completion custody leaves the
supervisor.
-/
def requestClose
    (shared : ManagedChannel Resource) : IO CloseObservation := do
  discard <| shared.claimClose
  match ← shared.ensureClaimedCloseOwner false with
  | .needsDriver => pure .needsDriver
  | .driven => shared.observeClose

private partial def awaitClaimedCloseUntil
    (shared : ManagedChannel Resource)
    (absoluteDeadlineMilliseconds : Nat) : IO CloseObservation := do
  let now ← IO.monoMsNow
  if absoluteDeadlineMilliseconds ≤ now then
    shared.observeClose
  else
    let remaining := absoluteDeadlineMilliseconds - now
    let timerChunk := min remaining maximumCloseTimerMilliseconds
    let raced : Except IO.Error CloseDeadlineRace ← try
      pure (Except.ok (← shared.awaitCloseOrDeadline timerChunk))
    catch error =>
      pure (Except.error error)
    match raced with
    | Except.ok .completed =>
        pure (.settled (← shared.awaitClose))
    | Except.error _ =>
        -- Selector infrastructure failure returns conservatively without
        -- changing close ownership or spinning on the same failure.
        shared.observeClose
    | Except.ok .elapsed =>
        -- Completion/custody are authoritative after timer selection. If an
        -- absolute Nat exceeds one UInt64 timer interval, re-arm the remainder
        -- rather than allowing the native conversion to wrap.
        match ← shared.observeClose with
        | .settled result => pure (.settled result)
        | .needsDriver => pure .needsDriver
        | .stillClosing =>
            -- Re-read the monotonic clock even after the final-sized chunk.
            -- libuv may saturate `loop time + timeout` near UInt64.max, and
            -- early/spurious timer wakeups never authorize a timeout result.
            shared.awaitClaimedCloseUntil absoluteDeadlineMilliseconds

/--
Request close and observe its authoritative completion until one absolute
monotonic millisecond deadline. Deadline expiry only observes the current
nonterminal state (`stillClosing` or `needsDriver`); it never resolves the
completion promise, removes a detached driver, or changes exact resource
custody. Completion is checked both before and after deadline selection, so
already-published terminal evidence wins boundary races.
-/
def awaitCloseUntil
    (shared : ManagedChannel Resource)
    (absoluteDeadlineMilliseconds : Nat) : IO CloseObservation := do
  match ← shared.requestClose with
  | .settled result => pure (.settled result)
  | .needsDriver => pure .needsDriver
  | .stillClosing =>
      shared.awaitClaimedCloseUntil absoluteDeadlineMilliseconds

/-- Request close with one relative monotonic observation budget. -/
def closeWithin
    (shared : ManagedChannel Resource)
    (milliseconds : Nat) : IO CloseObservation := do
  let startedAt ← IO.monoMsNow
  shared.awaitCloseUntil (startedAt + milliseconds)

/--
Stop new calls, join every admitted initialization/call/retirement, then close
all acquired generations. The elected close owner is a dedicated task, so a
cancelled close caller cannot abandon transport ownership. Initialization is
settled by structural disposition; sticky invariant or uncertain-task evidence
makes the joined close fail closed.
-/
def close
    (shared : ManagedChannel Resource) : IO (Except CloseError Unit) := do
  discard <| shared.claimClose
  -- Unlike bounded observation, the joining API retains its original inline
  -- fallback when task allocation fails. It also waits through a racing
  -- bounded allocation attempt and retakes any custody that attempt restores.
  discard <| shared.ensureClaimedCloseOwner true
  shared.awaitClose

end ManagedChannel

end Grpc
