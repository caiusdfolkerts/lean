module
import all stress_flex
import all torus_period
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let modules : Array Name :=
    #[`stress_flex, `torus_period]
  let names := env.checked.get.constants.fold (fun names name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if modules.contains env.header.moduleNames[idx.toNat]! then names.push name
      else names
    | none => names) (#[] : Array Name)
  unless !names.isEmpty do
    throwError "Audit found no declarations in the checked bundles"
  for moduleName in modules do
    unless names.any (fun name => match env.getModuleIdxFor? name with
        | some idx => env.header.moduleNames[idx.toNat]! == moduleName
        | none => false) do
      throwError "Audit found no declarations in {moduleName}"
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Missing declaration {name}"
    if info.isUnsafe || info.isPartial then
      throwError "Unsafe or partial local declaration is forbidden: {name}"
    match info with
    | .axiomInfo _ => throwError "Local axiom is forbidden: {name}"
    | _ => pure ()
    let axioms ← collectAxioms name
    let rejected := axioms.filter (fun axiomName => !allowed.contains axiomName)
    unless rejected.isEmpty do
      throwError "{name} depends on forbidden axioms: {rejected}"
  logInfo m!"AUDIT_COMPLETE: {names.size} bundle declarations; only propext, Classical.choice, Quot.sound are permitted."
