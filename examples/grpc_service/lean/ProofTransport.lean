import Lean

/-
  ProofTransport.lean - Generic, application-agnostic proof verifier.

  This module is the trust boundary for the proof-carrying-message
  protocol. Clients hand it two Lean source strings:

    * `proofTerm` - the proof term shipped on the wire
    * `propTerm`  - the proposition the client expects the proof to attest

  The verifier wraps them as

    def __proof_transport_check : (propTerm) := (proofTerm)

  and elaborates that declaration in-process with `Lean.Elab.process`.
  Success means the frontend and kernel accepted the proof against the
  expected type.

  The verifier imports `Init` once at module initialization and reuses
  that immutable environment for every check. The embedding executable
  must initialize Lean the same way Lean's generated `main` does:
  `lean_initialize`, module initializers, `lean_io_mark_end_initialization`,
  and `lean_init_task_manager`.

  This module knows nothing about RPCs, traits, or message types. Both
  `proofTerm` and `propTerm` are opaque transport - Lean source strings
  that the verifier hands verbatim to the kernel. No per-RPC validation
  logic, no shared trait registry.
-/

namespace ProofTransport

open Lean

private def checkName : Name := `__proof_transport_check

private def checkFileName : String := "<proof-transport>"

private initialize verifierEnv : IO.Ref (Except String Environment) ← do
  let result ←
    try
      let sysroot ← Lean.findSysroot
      Lean.initSearchPath sysroot
      let env ← Lean.importModules
        (imports := #[{ module := `Init }])
        (opts := {})
        (trustLevel := 1024)
      pure (Except.ok env)
    catch e =>
      pure (Except.error (toString e))
  IO.mkRef result

private def checkSource (proofTerm propTerm : String) : String :=
  s!"def {checkName} : ({propTerm}) := ({proofTerm})\n"

private def logMessages (messages : MessageLog) : IO Unit := do
  for message in messages.toList do
    let text ← message.toString
    IO.eprintln s!"[ProofTransport] lean message: {text}"

/-- Verify that `proofTerm` is a valid proof of `propTerm`. Returns
    true iff `Lean.Elab.process` accepts
    `def __proof_transport_check : (propTerm) := (proofTerm)`. -/
def verifyProof (proofTerm propTerm : String) : IO Bool := do
  let envResult ← verifierEnv.get
  match envResult with
  | Except.error err =>
      IO.eprintln s!"[ProofTransport] verifier initialization failed: {err}"
      return false
  | Except.ok env =>
      let source := checkSource proofTerm propTerm
      let result : Except String MessageLog ←
        try
          let (_, messages) ← Lean.Elab.process source env {} (some checkFileName)
          pure (Except.ok messages)
        catch e =>
          pure (Except.error (toString e))

      match result with
      | Except.error err =>
          IO.eprintln s!"[ProofTransport] verification failed: {err}"
          IO.eprintln s!"[ProofTransport] source:\n{source}"
          return false
      | Except.ok messages =>
          if messages.hasErrors then
            IO.eprintln "[ProofTransport] verification failed"
            IO.eprintln s!"[ProofTransport] source:\n{source}"
            logMessages messages
            return false
          else
            return true

end ProofTransport
