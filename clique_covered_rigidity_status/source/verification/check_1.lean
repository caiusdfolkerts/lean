module
import all rigidity
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`rigidity, `verification.internal.extract, `consolidated.pair_pin_progress01, `verification.internal.checkpoint, `consolidated.pair_pin_progress02, `papers.rigidity_mode_splitting, `consolidated.rigidity_generic_tools, `consolidated.rigidity_foundations01, `consolidated.rigidity_foundations02, `consolidated.rigidity_combined_prepared, `consolidated.rigidity_combined02, `consolidated.rigidity_combined03, `consolidated.rigidity_combined04, `consolidated.rigidity_combined05, `consolidated.rigidity_combined06, `consolidated.rigidity_combined07, `consolidated.rigidity_main_recovery01, `consolidated.rigidity_priority_expectation01]
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
