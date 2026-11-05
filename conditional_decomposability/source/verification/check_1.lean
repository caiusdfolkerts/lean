module
import all conditional_decomposability
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`main, `consolidated_dev.conditional_complete_integration, `consolidated.all_rigid_cover_cases, `consolidated.low_dimensional_rigid_covers, `consolidated.nonsimple_rigid_covers, `consolidated.four_tail_rigid_cover, `consolidated.actual_four_tail_geometry, `consolidated.actual_rigid_seeds, `consolidated.rigid_tail_sets, `consolidated.deletion_fields, `consolidated.deletion_geometry, `consolidated.root_graph, `consolidated.root_generic, `consolidated_dev.intrinsic_figure_geometry, `consolidated_dev.actual_geometry, `consolidated_dev.no_simple_ten_intrinsic, `consolidated_dev.simple_vertex_duality, `consolidated_dev.simple_four_ridges, `consolidated_dev.abstract_lower_bound, `consolidated_dev.simple_four_combinatorics, `papers.simple_four_finite_obstruction, `consolidated_dev.simple_four_no_ten, `consolidated.actual_rigid_five_seeds, `consolidated.actual_sigma_tail, `consolidated.actual_facet_hitting, `consolidated.homothety_uniform_cover, `consolidated.homothety_shared_central_impossible, `consolidated.homothety_fiber_comparison, `consolidated.homothety_fiber_rows, `consolidated.dense_cone_rigidity, `consolidated.small_order_rigidity, `consolidated.homothety_unowned_facet, `consolidated.homothety_unowned_class, `consolidated.homothety_central_clique, `consolidated.homothety_minimum_class, `consolidated_dev.minkowski_map_core, `consolidated.three_dimensional_incidences, `consolidated.incidence_core_geometry, `consolidated.relative_facet_halfspaces, `consolidated.homothety_shared_class_neighbors, `consolidated.homothety_boundary_cover, `consolidated.universal_shephard, `consolidated_dev.exact_shephard_criterion, `consolidated_dev.codim_two_extra_base, `consolidated_dev.minkowski_homothetic_core, `consolidated_dev.minkowski_fiber_geometry, `papers.finite_fiber_saturation, `consolidated_dev.affine_interpolation, `consolidated_dev.projective_crossing_geometry, `consolidated.minkowski_codimension_two_deletion, `consolidated.minkowski_deletion_summand, `consolidated.proper_image_exact_summand, `consolidated_dev.conditional_upper_canonical, `supplementary.dense_matching_concurrence, `supplementary.proper_image_map, `supplementary.two_homotheties, `supplementary.intrinsic_small_order_covers, `supplementary.paper_interfaces, `conditional_decomposability, `conditional_decomposability_audit, `verification.internal.extract]
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
