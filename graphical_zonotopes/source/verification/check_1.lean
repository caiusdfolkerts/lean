module
import all verified.appendix_newton
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`verified.appendix_newton, `verified.appendix_a2, `verified.extensions, `verified.main, `verified.parts.part041, `verified.parts.part040, `verified.parts.part039, `verified.parts.part038, `verified.parts.part037, `verified.parts.part036, `verified.parts.part035, `verified.parts.part034, `verified.parts.part033, `verified.parts.part032, `verified.parts.part031, `verified.parts.part030, `verified.parts.part029, `verified.parts.part028, `verified.parts.part027, `verified.parts.part026, `verified.parts.part025, `verified.parts.part024, `verified.parts.part023, `verified.parts.part022, `verified.parts.part021, `verified.parts.part020, `verified.parts.part019, `verified.parts.part018, `verified.parts.part017, `verified.parts.part016, `verified.parts.part015, `verified.parts.part014, `verified.parts.part013, `verified.parts.part012, `verified.parts.part011, `verified.parts.part010, `verified.parts.part009, `verified.parts.part008, `verified.parts.part007, `verified.parts.part006, `verified.parts.part005, `verified.parts.part004, `verified.parts.part003, `verified.parts.part002, `verified.parts.part001, `verified.parts.part000]
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
