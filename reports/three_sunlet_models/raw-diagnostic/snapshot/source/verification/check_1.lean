module
import all sunlet
public meta import Lean.Util.CollectAxioms
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
open Lean Elab Command
run_cmd do
  let env := (← getEnv).setExporting false
  let localModules := #[`sunlet, `sunlet.modular_final_audit, `sunlet.all_loop_contact_supports, `sunlet.generic_pair_geometry, `sunlet.contact_development, `sunlet.latin_orbits, `sunlet.permutation_families, `sunlet.punctured_differences, `sunlet.ordinary_edge_rigidity, `sunlet.punctured_both_endpoints, `sunlet.two_ratio_rigidity, `sunlet.normalized_variations, `sunlet.toric_differential, `sunlet.contact_coefficient, `sunlet.sparse_tangent_pair, `sunlet.one_hole_field, `sunlet.matrix_specialization, `sunlet.rational_partials, `sunlet.etale_derivations, `sunlet.contact_equations, `sunlet.ratio_correction, `sunlet.ratio_solution_spaces, `sunlet.invariant_functions, `sunlet.contact_linear, `sunlet.jacobian_finite, `sunlet.sparse_contact, `sunlet.contact_completion, `sunlet.contact_torus, `sunlet.latin_sparse_contact, `sunlet.exceptional_contact_transport, `sunlet.support_transport, `sunlet.contact_exceptions, `sunlet.sparse_contact_entries, `sunlet.arbitrary_orbit_classification, `sunlet.fine_invariant_kernel, `sunlet.fine_odd_kernel, `sunlet.coarse_selection, `sunlet.orbit_models, `sunlet.partition_subgroups, `sunlet.one_level_obstructions, `sunlet.height_obstructions, `sunlet.orbit_height_completion, `sunlet.orbit_height, `sunlet.height_elimination, `sunlet.class_dimension, `sunlet.class_kernel, `sunlet.class_selection, `sunlet.identified_normalization, `sunlet.group_coordinates, `sunlet.polynomial_image, `sunlet.basic, `sunlet.dimension_upper_bound, `sunlet.normalized_algebra, `sunlet.normalization, `sunlet.dimension_algebra, `sunlet.weighted_initial, `sunlet.selected_exponents, `sunlet.selected_relations, `sunlet.exponent_independence, `sunlet.initial_independence, `sunlet.exponent_rank, `sunlet.dimension_lower_bound, `sunlet.main_dimension, `sunlet.latin_split, `sunlet.generated_action, `sunlet.negation_coarsening, `sunlet.index_two_orbit_rigidity, `sunlet.cyclic_orbit_models, `sunlet.cyclic_sparse_witness, `sunlet.distinct_derangements, `sunlet.paper_statements, `sunlet.extended_rational_derivations, `sunlet.generic_toric_embeddings, `sunlet.loop_field_actions, `sunlet.loop_point_fibers, `sunlet.rational_diagonal_actions, `sunlet.verified_complex_statements, `sunlet.verified_cyclic_paper, `sunlet.verified_cyclic_field, `sunlet.verified_generic_open, `sunlet.verified_field_core, `sunlet.verified_normalized_model, `sunlet.verified_generic_conclusions, `sunlet.verified_model_fibers, `sunlet.verified_fiber_geometry, `sunlet.verified_toric_geometry, `sunlet.verified_network_conclusion, `sunlet.verified_network_algebra, `sunlet.verified_network_graph, `sunlet.verified_normalized_generic_fiber]
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
