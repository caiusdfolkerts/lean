module
import all verification.internal.axioms
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`volume_polynomials, `volume_polynomials.all, `volume_polynomials.assembly_part01, `volume_polynomials.assembly_part02, `volume_polynomials.assembly_part03, `volume_polynomials.assembly_part04, `volume_polynomials.assembly_part05, `volume_polynomials.assembly_part06, `volume_polynomials.assembly_part07, `volume_polynomials.assembly_part08, `volume_polynomials.assembly_part09, `volume_polynomials.assembly_part10, `verification.internal.axioms, `verification.internal.executable_rational_smoke]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some owner := env.header.moduleNames[idx.toNat]? | continue
    unless localModules.contains owner do continue
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    count := count + 1
  if count == 0 then throwError "No local declarations were checked"
  logInfo m!"Checked axiom dependencies of {count} local declarations."
