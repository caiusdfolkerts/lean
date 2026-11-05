module
import all verification.internal.ellipsoid_full21_inspection
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`ellipsoid, `ellipsoid.verified.complete, `ellipsoid.verified.main, `ellipsoid.verified.main_remainder03, `ellipsoid.verified.main_remainder02, `ellipsoid.verified.main_remainder01, `ellipsoid.verified.reconstruction_complete, `ellipsoid.verified.reconstruction, `ellipsoid.verified.reconstruction01, `ellipsoid.verified.main04, `ellipsoid.verified.main03, `ellipsoid.verified.main02, `ellipsoid.verified.main01, `tau_ceti.ring_theory.polynomial.roots, `tau_ceti.data.multiset.rel, `tau_ceti.ring_theory.polynomial.vieta, `tau_ceti.topology.algebra.polynomial.basic, `tau_ceti.ring_theory.polynomial.monic.of_coeff, `tau_ceti.measure_theory.constructions.haar_to_sphere, `tau_ceti.analysis.calculus.parametric_integral, `tau_ceti.topology.compactness.normed, `tau_ceti.analysis.special_functions.beta, `tau_ceti.analysis.calculus.real_charts, `tau_ceti.analysis.real.sqrt, `tau_ceti.analysis.special_functions.gamma, `tau_ceti.analysis.special_functions.pow.real, `tau_ceti.analysis.convex.stiemke, `ellipsoid.verified.affine, `ellipsoid.verified.affine01, `tau_ceti.analysis.polynomial.continuity_of_roots.basic, `tau_ceti.analysis.polynomial.symmetric_power, `tau_ceti.ring_theory.polynomial.symmetric_power, `tau_ceti.data.sym.basic, `tau_ceti.ring_theory.mv_polynomial.symmetric.substitution, `tau_ceti.topology.sym.disjoint, `tau_ceti.data.sym.disjoint, `tau_ceti.topology.sym.basic, `tau_ceti.topology.metric_space.separated_balls, `ellipsoid.coefficient_corners, `ellipsoid.sharpness_neighborhood, `verification.internal.ellipsoid_remaining_statements, `verification.internal.ellipsoid_full20_inspection, `verification.internal.ellipsoid_full21_inspection]
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
