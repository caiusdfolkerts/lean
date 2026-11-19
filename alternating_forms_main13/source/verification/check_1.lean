module
import all verified
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`verified, `paper_verification.literal000, `paper_verification.literal001, `paper_verification.literal002, `paper_verification.literal003, `paper_verification.literal004, `paper_verification.literal005, `paper_verification.literal006, `paper_verification.literal007, `paper_verification.literal008, `paper_verification.literal009, `paper_verification.literal010, `paper_verification.literal011, `paper_verification.literal012, `paper_verification.literal013, `paper_verification.literal014, `paper_verification.literal015, `paper_verification.literal016, `paper_verification.ambient_base2, `paper_verification.ambient_zero6, `paper_verification.ambient_generic1, `paper_verification.ambient_intrinsic5, `paper_verification.ambient_polarization2, `paper_verification.coefficient_grading3, `paper_verification.rees_grading4, `paper_verification.graded_degenerations3, `paper_verification.graded_characteristic1, `paper_verification.final_theorem_one_three1, `paper_verification.schubert_rank3, `paper_verification.richardson_chart6, `paper_verification.global_comparisons4, `paper_verification.one_plane_boundary6, `paper_verification.richardson_intrinsic2, `paper_verification.tensor_multiplicity2, `paper_verification.fixed_plane_count3, `paper_verification.ce_integrated1, `paper_verification.oai_base000_run4, `paper_verification.oai_base001_run2, `paper_verification.oai_base002_run3, `paper_verification.oai_sheaf_api8, `paper_verification.oai_chow000_run4, `paper_verification.oai_chow001_run2, `paper_verification.oai_chow002_run2, `paper_verification.oai_analytic000_run5, `paper_verification.oai_chow003_run1, `paper_verification.oai_chow004_run1, `paper_verification.oai_flasque_low_degree1, `paper_verification.oai_groth_zero_outside1, `paper_verification.oai_groth_flasque2, `paper_verification.oai_module_map_gluing2, `paper_verification.relative_projective_geometry2, `paper_verification.oai_projective_boundary000_run1, `paper_verification.oai_thom000_run1, `paper_verification.oai_thom001_run1, `paper_verification.oai_thom002_run2, `paper_verification.oai_thom003_run1, `paper_verification.oai_thom004_run1, `paper_verification.oai_thom005_run1, `paper_verification.oai_thom006_run2, `paper_verification.oai_thom007_run1, `paper_verification.oai_thom008_run1, `paper_verification.section_four_geometry1, `paper_verification.actual_odd_affine_paving6, `paper_verification.derived_comparison1, `paper_verification.projective_universal6, `paper_verification.twisting_coherence2, `paper_verification.symmetric_basis_degree2, `paper_verification.symmetric_projective_geometry3, `paper_verification.relative_twisting2, `paper_verification.direct_sum_concentration2, `paper_verification.empty_singular_cohomology3, `paper_verification.exact_sequence_rank2, `paper_verification.finite_exact_filtration3, `paper_verification.main_statements1, `paper_verification.relative_cohomology_whole2, `paper_verification.singular_pair_cohomology_rank1, `paper_verification.total_singular_cohomology2, `paper_verification.isotropic_projective_geometry3, `paper_verification.direct_sum_shift4, `paper_verification.actual_chow_rank5, `paper_verification.all_odd_chow_rank2, `paper_verification.projective_line_algebra, `tau_ceti.algebra.homology.short_complex.biproduct, `tau_ceti.category_theory.exact.kernel_cokernel_pair, `tau_ceti.algebra.homology.short_complex.short_exact, `geometry_verified.stage000, `geometry_verified.stage001, `geometry_verified.stage002, `geometry_verified.stage003, `geometry_verified.stage004, `geometry_verified.stage005, `tau_ceti.algebra.category.module_cat.sheaf.exactness]
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
