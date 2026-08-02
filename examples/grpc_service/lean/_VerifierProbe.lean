import Lean
import ProofTransport

open Lean

def main : IO Unit := do
  IO.println "Probe: starting"

  IO.println "Probe: calling Lean.findSysroot..."
  let sysroot ← try Lean.findSysroot
                catch e => do
                  IO.eprintln s!"findSysroot failed: {e}"
                  pure (System.FilePath.mk ".")
  IO.println s!"Probe: sysroot = {sysroot}"

  IO.println "Probe: initializing search path..."
  try Lean.initSearchPath sysroot
  catch e => IO.eprintln s!"initSearchPath failed: {e}"

  IO.println "Probe: importing modules..."
  let env ← try
    Lean.importModules
      (imports := #[{ module := `Init }])
      (opts := {})
      (trustLevel := 1024)
  catch e => do
    IO.eprintln s!"importModules failed: {e}"
    pure (← Lean.mkEmptyEnvironment)
  IO.println s!"Probe: env loaded"

  IO.println "Probe: elaborating trivial proof..."
  let source := "def __test : ((1 : UInt64) = (1 : UInt64)) := (@Eq.refl UInt64 (1 : UInt64))"
  let (_, msgs) ← try
    Lean.Elab.process source env {} (some "<probe>")
  catch e => do
    IO.eprintln s!"Lean.Elab.process failed: {e}"
    pure (env, MessageLog.empty)
  IO.println s!"Probe: messages.hasErrors = {msgs.hasErrors}"
  for m in msgs.toList do
    let txt ← m.toString
    IO.println s!"Probe:   {txt}"

  IO.println "Probe: checking ProofTransport.verifyProof..."
  let accepted ← ProofTransport.verifyProof
    "(@Eq.refl UInt64 (1 : UInt64))"
    "((1 : UInt64) = (1 : UInt64))"
  IO.println s!"Probe: accepted valid proof = {accepted}"
  let rejected ← ProofTransport.verifyProof
    "(@Eq.refl UInt64 (2 : UInt64))"
    "((2 : UInt64) = (1 : UInt64))"
  IO.println s!"Probe: accepted invalid proof = {rejected}"
  unless accepted && !rejected do
    throw (IO.userError "ProofTransport regression check failed")

  IO.println "Probe: done"
