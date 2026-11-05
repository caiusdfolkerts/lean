module
import all paper_verification
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`paper_verification, `paper_verification.lattice001, `paper_verification.lattice002, `paper_verification.lattice003, `paper_verification.lattice004, `paper_verification.lattice005, `paper_verification.lattice006, `paper_verification.lattice007, `paper_verification.lattice008]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := env.header.moduleNames[idx.toNat]? | continue
    unless localModules.contains owner do continue
    let shouldCheck ← match info with
      | .thmInfo _ | .axiomInfo _ => pure true
      | _ => liftTermElabM <| Lean.Meta.isProp info.type
    unless shouldCheck do continue
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    count := count + 1
  if count == 0 then throwError "No local theorems were checked"
  logInfo m!"Checked axiom dependencies of {count} local theorems."
