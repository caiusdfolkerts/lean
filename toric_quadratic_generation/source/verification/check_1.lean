module
import all toric_quadratic
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`toric_quadratic, `paper_verification.toric028, `paper_verification.toric001, `paper_verification.toric002, `paper_verification.toric009, `paper_verification.toric005, `paper_verification.toric017, `paper_verification.toric018, `paper_verification.toric019, `paper_verification.toric020, `paper_verification.toric021, `paper_verification.toric013, `paper_verification.toric010, `paper_verification.toric022, `paper_verification.toric029, `paper_verification.toric023, `paper_verification.toric016, `paper_verification.toric024, `paper_verification.toric025, `paper_verification.toric030, `paper_verification.toric032, `paper_verification.toric033, `paper_verification.toric026, `paper_verification.toric040, `paper_verification.toric027, `paper_verification.toric038, `paper_verification.toric031, `paper_verification.toric037, `paper_verification.toric034, `paper_verification.toric035, `paper_verification.toric036, `paper_verification.toric039, `paper_verification.toric042, `paper_verification.toric041, `paper_verification.toric043, `toric_quadratic.real_slices, `toric_quadratic.real_support, `toric_quadratic.fan_basics]
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
