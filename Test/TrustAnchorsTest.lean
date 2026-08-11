import Grpc
import Test.CertificateFixtures

namespace TrustAnchorsTest

open Grpc.TrustAnchors

private def fail (detail : String) : IO α :=
  throw (IO.userError detail)

private def expect (condition : Bool) (detail : String) : IO Unit := do
  unless condition do fail detail

private def validPem : String :=
  CertificateFixtures.validCertificatePem

private def unusedProbe (_ : System.FilePath) : IO (Except IO.Error Bool) :=
  pure (.error (IO.userError "unexpected trust path probe"))

private def unusedRead (_ : System.FilePath) :
    IO (Except ReadFailure ByteArray) :=
  pure (.error (.io (IO.userError "unexpected trust path read")))

private def testValidation : IO Unit := do
  match validateBundle ByteArray.empty with
  | .error .empty => pure ()
  | _ => fail "empty trust bundle was accepted"
  match validateBundle (ByteArray.empty.push 0xff) with
  | .error .invalidUtf8 => pure ()
  | _ => fail "non-UTF-8 trust bundle was accepted"
  match validateBundle "not PEM".toUTF8 with
  | .error (.invalidPem _) => pure ()
  | _ => fail "non-PEM trust bundle was accepted"
  match validateBundle CertificateFixtures.wellArmoredInvalidDer.toUTF8 with
  | .error (.invalidPem _) => pure ()
  | _ => fail "well-armored invalid certificate DER was accepted"
  match validateBundle validPem.toUTF8 with
  | .ok text => expect (text == validPem) "valid PEM bytes changed"
  | .error error => fail s!"valid PEM was rejected: {repr error}"
  let mixed := CertificateFixtures.wellArmoredInvalidDer ++ validPem
  match validateBundle mixed.toUTF8 with
  | .ok text =>
      expect (text == validPem)
        "unsupported certificate was not removed from a usable bundle"
      match TLS13.X509.Chain.TrustStore.decodePEM text with
      | .ok store =>
          expect (store.anchors.size == 1)
            "normalized mixed bundle changed its usable anchor count"
      | .error error =>
          fail s!"normalized mixed bundle failed transport parsing: {error}"
  | .error error =>
      fail s!"usable mixed certificate bundle was rejected: {repr error}"

private def testExplicitPrecedence : IO Unit := do
  let calls ← IO.mkRef (#[] : Array String)
  let backend : Backend := {
    platform := .linux
    getEnvironment := fun name => do
      calls.modify (·.push s!"env:{name}")
      if name == sslCertFileVariable then pure (some "/explicit.pem")
      else if name == nixSslCertFileVariable then pure (some "/ignored.pem")
      else pure none
    probe := fun path => do
      calls.modify (·.push s!"probe:{path}")
      unusedProbe path
    read := fun path => do
      calls.modify (·.push s!"read:{path}")
      pure (.ok validPem.toUTF8)
  }
  match ← loadWith backend with
  | .error error => fail s!"explicit trust bundle failed: {error}"
  | .ok bundle =>
      expect (bundle.source == .sslCertFile)
        "SSL_CERT_FILE did not win precedence"
      expect (bundle.path.toString == "/explicit.pem")
        "SSL_CERT_FILE path changed"
  expect ((← calls.get) == #[
      "env:SSL_CERT_FILE",
      "read:/explicit.pem"
    ]) "explicit trust path consulted a fallback"

private def testInvalidExplicitNeverFallsBack : IO Unit := do
  let calls ← IO.mkRef (#[] : Array String)
  let backend : Backend := {
    platform := .linux
    getEnvironment := fun name => do
      calls.modify (·.push s!"env:{name}")
      if name == sslCertFileVariable then pure (some "/broken.pem")
      else pure (some "/must-not-be-used.pem")
    probe := fun path => do
      calls.modify (·.push s!"probe:{path}")
      pure (.ok true)
    read := fun path => do
      calls.modify (·.push s!"read:{path}")
      pure (.ok "not PEM".toUTF8)
  }
  match ← loadWith backend with
  | .error (.validation path (.invalidPem _)) =>
      expect (path.toString == "/broken.pem")
        "invalid explicit path changed"
  | .error error => fail s!"invalid explicit failure changed: {error}"
  | .ok _ => fail "invalid explicit trust bundle was accepted"
  expect ((← calls.get) == #[
      "env:SSL_CERT_FILE",
      "read:/broken.pem"
    ]) "invalid explicit trust bundle silently fell back"

private def testResourceFailuresRemainSpecific : IO Unit := do
  let unreadable : Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == sslCertFileVariable then pure (some "/unreadable.pem")
      else pure (some "/must-not-be-used.pem")
    probe := unusedProbe
    read := fun _ =>
      pure (.error (.io
        (.permissionDenied (some "/unreadable.pem") 13 "injected denial")))
  }
  match ← loadWith unreadable with
  | .error (.read path
      (.permissionDenied (some "/unreadable.pem") 13 "injected denial")) =>
      expect (path.toString == "/unreadable.pem")
        "trust read error lost its selected path"
  | .error error => fail s!"trust read error changed shape: {error}"
  | .ok _ => fail "unreadable explicit trust file was accepted"

  let oversized : Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == sslCertFileVariable then pure (some "/oversized.pem")
      else pure none
    probe := unusedProbe
    read := fun _ => pure (.error (.tooLarge maximumBundleBytes))
  }
  match ← loadWith oversized with
  | .error (.tooLarge path limit) =>
      expect (path.toString == "/oversized.pem" &&
        limit == maximumBundleBytes)
        "trust size failure lost its path or bound"
  | .error error => fail s!"trust size error changed shape: {error}"
  | .ok _ => fail "oversized explicit trust file was accepted"

  let delayedClose : Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == sslCertFileVariable then pure (some "/close-error.pem")
      else pure none
    probe := unusedProbe
    read := fun _ =>
      pure (.error (.closeDiagnostic Grpc.Posix.Errno.io))
  }
  match ← loadWith delayedClose with
  | .error (.closeDiagnostic path error) =>
      expect (path.toString == "/close-error.pem" &&
        error == Grpc.Posix.Errno.io)
        "trust close diagnostic lost its selected path or errno"
  | .error error => fail s!"trust close diagnostic changed shape: {error}"
  | .ok _ => fail "trust close diagnostic was ignored"

  let paths := defaultPaths .linux
  let some first := paths.head?
    | fail "Linux trust path fixture is incomplete"
  let probeFailure : Backend := {
    platform := .linux
    getEnvironment := fun _ => pure none
    probe := fun _ =>
      pure (.error
        (.permissionDenied (some first.toString) 13 "injected probe denial"))
    read := unusedRead
  }
  match ← loadWith probeFailure with
  | .error (.probe path
      (.permissionDenied (some deniedPath) 13 "injected probe denial")) =>
      expect (path.toString == first.toString &&
        deniedPath == first.toString)
        "trust probe error lost structured details"
  | .error error => fail s!"trust probe error changed shape: {error}"
  | .ok _ => fail "failed system trust probe was ignored"

private def testExplicitPathRefinement : IO Unit := do
  let backendFor value : Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == sslCertFileVariable then pure (some value) else pure none
    probe := unusedProbe
    read := unusedRead
  }
  match ← loadWith (backendFor "") with
  | .error (.emptyExplicitPath environmentName) =>
      expect (environmentName == sslCertFileVariable)
        "empty explicit path lost its variable"
  | _ => fail "empty explicit trust path was accepted"
  let nulPath := "/tmp/" ++ String.singleton (Char.ofNat 0) ++ "anchors.pem"
  match ← loadWith (backendFor nulPath) with
  | .error (.explicitPathContainsNul environmentName) =>
      expect (environmentName == sslCertFileVariable)
        "NUL explicit path lost its variable"
  | _ => fail "NUL explicit trust path crossed into filesystem IO"

private def testNixAndSystemSelection : IO Unit := do
  let nixBackend : Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == sslCertFileVariable then pure none
      else if name == nixSslCertFileVariable then pure (some "/nix.pem")
      else pure none
    probe := unusedProbe
    read := fun path =>
      if path.toString == "/nix.pem" then pure (.ok validPem.toUTF8)
      else unusedRead path
  }
  match ← loadWith nixBackend with
  | .ok bundle =>
      expect (bundle.source == .nixSslCertFile)
        "NIX_SSL_CERT_FILE source changed"
  | .error error => fail s!"NIX_SSL_CERT_FILE failed: {error}"

  let paths := defaultPaths .linux
  let some selected := paths[1]?
    | fail "Linux trust path fixture is incomplete"
  let probes ← IO.mkRef (#[] : Array String)
  let systemBackend : Backend := {
    platform := .linux
    getEnvironment := fun _ => pure none
    probe := fun path => do
      probes.modify (·.push path.toString)
      pure (.ok (path.toString == selected.toString))
    read := fun path =>
      if path.toString == selected.toString then pure (.ok validPem.toUTF8)
      else unusedRead path
  }
  match ← loadWith systemBackend with
  | .ok bundle =>
      expect (bundle.source == .system)
        "default trust path had the wrong source"
      expect (bundle.path.toString == selected.toString)
        "default trust path selection changed"
  | .error error => fail s!"default trust path failed: {error}"
  expect ((← probes.get).toList == (paths.take 2).map toString)
    "default trust paths were not probed in order"

private def testBoundedRead : IO Unit :=
  IO.FS.withTempFile fun handle path => do
    handle.write "12345".toUTF8
    handle.flush
    match ← readFileBounded path 4 with
    | .error (.tooLarge 4) => pure ()
    | .error _ => fail "bounded trust read failed for the wrong reason"
    | .ok _ => fail "bounded trust read accepted an oversized file"
    match ← readFileBounded path 5 with
    | .ok bytes => do
      expect (bytes == "12345".toUTF8)
        "bounded trust read changed bytes at the exact limit"
    | .error _ => fail "bounded trust read rejected its exact limit"

private def testLinuxDescriptorCustody : IO Unit := do
  let path : System.FilePath := "/injected/anchors.pem"
  let descriptor : Grpc.Posix.Fd := 41
  let readStep ← IO.mkRef 0
  let closes ← IO.mkRef (#[] : Array Grpc.Posix.Fd)
  let successful : LinuxReadBackend := {
    openFile := fun actual => do
      expect (actual.toString == path.toString)
        "Linux trust open changed its path"
      pure (.ok (descriptor, 5))
    read := fun actual _ => do
      expect (actual == descriptor) "Linux trust read changed its descriptor"
      let step ← readStep.get
      readStep.set (step + 1)
      match step with
      | 0 => pure (.error Grpc.Posix.Errno.interrupted)
      | 1 => pure (.ok "12".toUTF8)
      | 2 => pure (.ok "345".toUTF8)
      | _ => pure (.ok ByteArray.empty)
    close := fun actual => do
      closes.modify (·.push actual)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith successful path 5 with
  | .ok bytes =>
      expect (bytes == "12345".toUTF8)
        "descriptor trust read changed exact-limit bytes"
  | .error _ =>
      fail "descriptor trust read failed"
  expect ((← closes.get) == #[descriptor])
    "descriptor trust read did not consume exactly one close"
  expect ((← readStep.get) == 4)
    "descriptor trust read did not retry EINTR or observe EOF"

  let overflowReads ← IO.mkRef 0
  let overflowCloses ← IO.mkRef 0
  let initialOverflow : LinuxReadBackend := {
    openFile := fun _ => pure (.ok (descriptor, 6))
    read := fun _ _ => do
      overflowReads.modify (· + 1)
      pure (.ok ByteArray.empty)
    close := fun _ => do
      overflowCloses.modify (· + 1)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith initialOverflow path 5 with
  | .error (.tooLarge 5) => pure ()
  | _ => fail "initial descriptor overflow changed"
  expect ((← overflowReads.get) == 0 && (← overflowCloses.get) == 1)
    "initial descriptor overflow read or lost its consuming close"

  let dynamicCloses ← IO.mkRef 0
  let dynamicOverflow : LinuxReadBackend := {
    openFile := fun _ => pure (.ok (descriptor, 0))
    read := fun _ _ => pure (.ok "12345".toUTF8)
    close := fun _ => do
      dynamicCloses.modify (· + 1)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith dynamicOverflow path 4 with
  | .error (.tooLarge 4) => pure ()
  | _ => fail "dynamic descriptor overflow changed"
  expect ((← dynamicCloses.get) == 1)
    "dynamic descriptor overflow lost its consuming close"

  let openCloseCalls ← IO.mkRef 0
  let failedOpen : LinuxReadBackend := {
    openFile := fun _ => pure (.error Grpc.Posix.Errno.accessDenied)
    read := fun _ _ => fail "failed Linux trust open attempted a read"
    close := fun _ => do
      openCloseCalls.modify (· + 1)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith failedOpen path 5 with
  | .error (.descriptor .open error) =>
      expect (error == Grpc.Posix.Errno.accessDenied)
        "Linux trust open lost its errno"
  | _ => fail "Linux trust open failure changed"
  expect ((← openCloseCalls.get) == 0)
    "failed Linux trust open fabricated descriptor custody"

  let outOfRangeCloseCalls ← IO.mkRef 0
  let outOfRangeDescriptor : Grpc.Posix.Fd :=
    Grpc.Posix.Constants.cIntMax + 1
  let outOfRangeOpen : LinuxReadBackend := {
    openFile := fun _ => pure (.ok (outOfRangeDescriptor, 0))
    read := fun _ _ => fail "out-of-range Linux descriptor attempted a read"
    close := fun _ => do
      outOfRangeCloseCalls.modify (· + 1)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith outOfRangeOpen path 5 with
  | .error (.descriptor .open error) =>
      expect (error == Grpc.Posix.Errno.invalidArgument)
        "out-of-range Linux descriptor lost its validation error"
  | _ => fail "out-of-range Linux descriptor was accepted"
  expect ((← outOfRangeCloseCalls.get) == 0)
    "out-of-range Linux descriptor fabricated accepted custody"

  let readCloses ← IO.mkRef 0
  let failedRead : LinuxReadBackend := {
    openFile := fun _ => pure (.ok (descriptor, 1))
    read := fun _ _ => pure (.error Grpc.Posix.Errno.io)
    close := fun _ => do
      readCloses.modify (· + 1)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith failedRead path 5 with
  | .error (.descriptor .read error) =>
      expect (error == Grpc.Posix.Errno.io)
        "Linux trust read lost its errno"
  | _ => fail "Linux trust read failure changed"
  expect ((← readCloses.get) == 1)
    "failed Linux trust read lost its consuming close"

  let thrownReadCloses ← IO.mkRef 0
  let thrownRead : LinuxReadBackend := {
    openFile := fun _ => pure (.ok (descriptor, 1))
    read := fun _ _ => throw (IO.userError "injected read exception")
    close := fun _ => do
      thrownReadCloses.modify (· + 1)
      pure (.consumed none)
  }
  match ← readFileBoundedLinuxWith thrownRead path 5 with
  | .error (.io (.userError message)) =>
      expect (message == "injected read exception")
        "thrown Linux trust read changed its IO error"
  | _ => fail "thrown Linux trust read changed"
  expect ((← thrownReadCloses.get) == 1)
    "thrown Linux trust read lost its consuming close"

private def testLinuxCloseDiagnosticsAndValidation : IO Unit := do
  let path : System.FilePath := "/injected/anchors.pem"
  let descriptor : Grpc.Posix.Fd := 42
  let backendFor closeResult contents : LinuxReadBackend := {
    openFile := fun _ => do
      let current ← contents.get
      pure (.ok (descriptor, UInt64.ofNat current.size))
    read := fun _ _ => do
      let emitted ← contents.get
      contents.set ByteArray.empty
      pure (.ok emitted)
    close := fun _ => pure closeResult
  }

  let diagnosticContents ← IO.mkRef "ok".toUTF8
  match ← readFileBoundedLinuxWith
      (backendFor (.consumed (some Grpc.Posix.Errno.io))
        diagnosticContents) path 8 with
  | .error (.closeDiagnostic error) =>
      expect (error == Grpc.Posix.Errno.io)
        "consumed Linux close lost its diagnostic"
  | _ => fail "consumed close diagnostic changed"

  let closeCalls ← IO.mkRef 0
  let invalidContents ← IO.mkRef "not PEM".toUTF8
  let invalidLinux : LinuxReadBackend := {
    (backendFor (.consumed none) invalidContents) with
    close := fun _ => do
      closeCalls.modify (· + 1)
      pure (.consumed none)
  }
  let loadBackend : Backend := {
    platform := .linux
    getEnvironment := fun name =>
      if name == sslCertFileVariable then pure (some path.toString)
      else pure none
    probe := unusedProbe
    read := fun selected => readFileBoundedLinuxWith invalidLinux selected
      maximumBundleBytes
  }
  match ← loadWith loadBackend with
  | .error (.validation actual (.invalidPem _)) =>
      expect (actual.toString == path.toString)
        "descriptor-backed validation lost its selected path"
  | _ => fail "descriptor-backed validation changed"
  expect ((← closeCalls.get) == 1)
    "descriptor-backed invalid PEM path did not consume exactly one close"

private def testHostSystemBundleIsTransportDecodable : IO Unit := do
  let backend := {
    productionBackend with
    getEnvironment := fun _ => pure none
  }
  match ← loadWith backend with
  | .error (.noSystemBundle _) =>
      -- Some hermetic builders intentionally provide no host trust store.
      pure ()
  | .error error =>
      fail s!"host system trust bundle was unusable: {error}"
  | .ok bundle =>
      match TLS13.X509.Chain.TrustStore.decodePEM bundle.pem with
      | .error error =>
          fail s!"normalized host trust bundle failed transport parsing: {error}"
      | .ok store =>
          expect (!store.anchors.isEmpty)
            "normalized host trust bundle contained no usable anchors"

def run : IO Unit := do
  testValidation
  testExplicitPrecedence
  testInvalidExplicitNeverFallsBack
  testResourceFailuresRemainSpecific
  testExplicitPathRefinement
  testNixAndSystemSelection
  testBoundedRead
  testLinuxDescriptorCustody
  testLinuxCloseDiagnosticsAndValidation
  testHostSystemBundleIsTransportDecodable
  IO.println "trust-anchor tests passed"

end TrustAnchorsTest

def main : IO Unit :=
  TrustAnchorsTest.run
