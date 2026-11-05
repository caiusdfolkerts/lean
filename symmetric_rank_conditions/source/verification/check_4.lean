module
import all symmetric_rank_verification
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`symmetric_local, `symmetric_next, `matching_row_bump, `matching_insertion_core, `matching_median_audit, `matching_foundation, `paper_verification, `combinatorics_verification, `verified_theorems, `obstruction_verification, `applications_verification, `schur_tableau_bridge, `schur_quotient_count, `schur_row_counts, `schur_theory, `rank_stratum_verification, `ideal_integrality_foundation, `ideal_integral_closure, `determinantal_transfer, `determinantal_transfer_scores, `rational_polyhedra, `rational_polytope_certificates, `ideal_real_weight, `integral_closure_theory, `gram_assignment, `gram_foundation, `gram_bitableaux, `corollary_seven_two, `supplementary_verification, `complete_verification, `extension_dependency_audit, `foundation_dependency_audit, `paper_statements, `reader_dependency_audit, `symmetric_rank_verification]
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
