module

/-
# Strict final modular proof audit

This is an explicit alternative to the additional one-file source-only gate.
Every local import must have an exact completed ordinary source/object record.
Private local proof bodies are loaded and traversed; no theorem is postulated.
Only the pinned library frontier may use its compiled axiom metadata.
The independent finalizer recomputes every local axiom set from actual edges,
checks all source/object bindings again, and requires this audit's exit-0 record.
Until that finalizer succeeds, the complete project remains unverified.
-/

public import Lean.Elab.BuiltinEvalCommand
public import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import sunlet.all_loop_contact_supports
import all sunlet.all_loop_contact_supports
public import sunlet.arbitrary_orbit_classification
import all sunlet.arbitrary_orbit_classification
public import sunlet.basic
import all sunlet.basic
public import sunlet.class_dimension
import all sunlet.class_dimension
public import sunlet.class_kernel
import all sunlet.class_kernel
public import sunlet.class_selection
import all sunlet.class_selection
public import sunlet.coarse_selection
import all sunlet.coarse_selection
public import sunlet.contact_coefficient
import all sunlet.contact_coefficient
public import sunlet.contact_completion
import all sunlet.contact_completion
public import sunlet.contact_development
import all sunlet.contact_development
public import sunlet.contact_equations
import all sunlet.contact_equations
public import sunlet.contact_exceptions
import all sunlet.contact_exceptions
public import sunlet.contact_linear
import all sunlet.contact_linear
public import sunlet.contact_torus
import all sunlet.contact_torus
public import sunlet.cyclic_orbit_models
import all sunlet.cyclic_orbit_models
public import sunlet.cyclic_sparse_witness
import all sunlet.cyclic_sparse_witness
public import sunlet.dimension_algebra
import all sunlet.dimension_algebra
public import sunlet.dimension_lower_bound
import all sunlet.dimension_lower_bound
public import sunlet.dimension_upper_bound
import all sunlet.dimension_upper_bound
public import sunlet.distinct_derangements
import all sunlet.distinct_derangements
public import sunlet.etale_derivations
import all sunlet.etale_derivations
public import sunlet.exceptional_contact_transport
import all sunlet.exceptional_contact_transport
public import sunlet.exponent_independence
import all sunlet.exponent_independence
public import sunlet.exponent_rank
import all sunlet.exponent_rank
public import sunlet.extended_rational_derivations
import all sunlet.extended_rational_derivations
public import sunlet.fine_invariant_kernel
import all sunlet.fine_invariant_kernel
public import sunlet.fine_odd_kernel
import all sunlet.fine_odd_kernel
public import sunlet.generated_action
import all sunlet.generated_action
public import sunlet.generic_pair_geometry
import all sunlet.generic_pair_geometry
public import sunlet.generic_toric_embeddings
import all sunlet.generic_toric_embeddings
public import sunlet.group_coordinates
import all sunlet.group_coordinates
public import sunlet.height_elimination
import all sunlet.height_elimination
public import sunlet.height_obstructions
import all sunlet.height_obstructions
public import sunlet.identified_normalization
import all sunlet.identified_normalization
public import sunlet.index_two_orbit_rigidity
import all sunlet.index_two_orbit_rigidity
public import sunlet.initial_independence
import all sunlet.initial_independence
public import sunlet.invariant_functions
import all sunlet.invariant_functions
public import sunlet.jacobian_finite
import all sunlet.jacobian_finite
public import sunlet.latin_orbits
import all sunlet.latin_orbits
public import sunlet.latin_sparse_contact
import all sunlet.latin_sparse_contact
public import sunlet.latin_split
import all sunlet.latin_split
public import sunlet.loop_field_actions
import all sunlet.loop_field_actions
public import sunlet.loop_point_fibers
import all sunlet.loop_point_fibers
public import sunlet.main_dimension
import all sunlet.main_dimension
public import sunlet.matrix_specialization
import all sunlet.matrix_specialization
public import sunlet.negation_coarsening
import all sunlet.negation_coarsening
public import sunlet.normalization
import all sunlet.normalization
public import sunlet.normalized_algebra
import all sunlet.normalized_algebra
public import sunlet.normalized_variations
import all sunlet.normalized_variations
public import sunlet.one_hole_field
import all sunlet.one_hole_field
public import sunlet.one_level_obstructions
import all sunlet.one_level_obstructions
public import sunlet.orbit_height
import all sunlet.orbit_height
public import sunlet.orbit_height_completion
import all sunlet.orbit_height_completion
public import sunlet.orbit_models
import all sunlet.orbit_models
public import sunlet.ordinary_edge_rigidity
import all sunlet.ordinary_edge_rigidity
public import sunlet.paper_statements
import all sunlet.paper_statements
public import sunlet.partition_subgroups
import all sunlet.partition_subgroups
public import sunlet.permutation_families
import all sunlet.permutation_families
public import sunlet.polynomial_image
import all sunlet.polynomial_image
public import sunlet.punctured_both_endpoints
import all sunlet.punctured_both_endpoints
public import sunlet.punctured_differences
import all sunlet.punctured_differences
public import sunlet.ratio_correction
import all sunlet.ratio_correction
public import sunlet.ratio_solution_spaces
import all sunlet.ratio_solution_spaces
public import sunlet.rational_diagonal_actions
import all sunlet.rational_diagonal_actions
public import sunlet.rational_partials
import all sunlet.rational_partials
public import sunlet.selected_exponents
import all sunlet.selected_exponents
public import sunlet.selected_relations
import all sunlet.selected_relations
public import sunlet.sparse_contact
import all sunlet.sparse_contact
public import sunlet.sparse_contact_entries
import all sunlet.sparse_contact_entries
public import sunlet.sparse_tangent_pair
import all sunlet.sparse_tangent_pair
public import sunlet.support_transport
import all sunlet.support_transport
public import sunlet.toric_differential
import all sunlet.toric_differential
public import sunlet.two_ratio_rigidity
import all sunlet.two_ratio_rigidity
public import sunlet.verified_complex_statements
import all sunlet.verified_complex_statements
public import sunlet.verified_cyclic_field
import all sunlet.verified_cyclic_field
public import sunlet.verified_cyclic_paper
import all sunlet.verified_cyclic_paper
public import sunlet.verified_fiber_geometry
import all sunlet.verified_fiber_geometry
public import sunlet.verified_field_core
import all sunlet.verified_field_core
public import sunlet.verified_generic_conclusions
import all sunlet.verified_generic_conclusions
public import sunlet.verified_generic_open
import all sunlet.verified_generic_open
public import sunlet.verified_model_fibers
import all sunlet.verified_model_fibers
public import sunlet.verified_network_algebra
import all sunlet.verified_network_algebra
public import sunlet.verified_network_conclusion
import all sunlet.verified_network_conclusion
public import sunlet.verified_network_graph
import all sunlet.verified_network_graph
public import sunlet.verified_normalized_generic_fiber
import all sunlet.verified_normalized_generic_fiber
public import sunlet.verified_normalized_model
import all sunlet.verified_normalized_model
public import sunlet.verified_toric_geometry
import all sunlet.verified_toric_geometry
public import sunlet.weighted_initial
import all sunlet.weighted_initial

-- Generated verification output directories.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit/final"


section SunletModularFinalAudit

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs false

-- Theorem 1.1, all normalized Latin systems
#check @Sunlet.paper_theorem_1_1
#print axioms Sunlet.paper_theorem_1_1

-- Theorem 1.1, literal original group coordinates
#check @Sunlet.GroupCoordinates.paper_theorem_1_1_original_coordinates
#print axioms Sunlet.GroupCoordinates.paper_theorem_1_1_original_coordinates

-- Theorem 2.3, literal distinct-derangement hypotheses
#check @Sunlet.paper_theorem_2_3_literal
#print axioms Sunlet.paper_theorem_2_3_literal

-- Theorem 4.2, generic unordered decomposition including toric boundary
#check @Sunlet.NormalizedLatinSystem.generic_unique_unordered_decomposition
#print axioms Sunlet.NormalizedLatinSystem.generic_unique_unordered_decomposition

-- Theorem 4.2, actual torus decompositions on a dense open
#check @Sunlet.NormalizedLatinSystem.generic_unique_torus_decomposition
#print axioms Sunlet.NormalizedLatinSystem.generic_unique_torus_decomposition

-- Theorem 4.2, literal normalized degree
#check @Sunlet.NormalizedLatinSystem.normalized_generic_degree
#print axioms Sunlet.NormalizedLatinSystem.normalized_generic_degree

-- Theorem 4.2, Galois property
#check @Sunlet.NormalizedLatinSystem.normalized_isGalois
#print axioms Sunlet.NormalizedLatinSystem.normalized_isGalois

-- Theorem 4.2, exact character wreath Galois group
#check @Sunlet.NormalizedLatinSystem.normalizedGaloisEquiv
#print axioms Sunlet.NormalizedLatinSystem.normalizedGaloisEquiv

-- Theorem 4.2, literal homomorphisms from the universal abelianization
#check @Sunlet.NormalizedLatinSystem.normalizedGaloisUniversalEquiv
#print axioms Sunlet.NormalizedLatinSystem.normalizedGaloisUniversalEquiv

-- Equivalence of the two complete semidirect-product presentations
#check @Sunlet.LoopData.abelianCharacterWreathEquiv
#print axioms Sunlet.LoopData.abelianCharacterWreathEquiv

-- Theorem 4.2, whole affine five-family algebraic fibers
#check @Sunlet.NormalizedLatinSystem.paper_theorem_4_2_algebraic_fibers
#print axioms Sunlet.NormalizedLatinSystem.paper_theorem_4_2_algebraic_fibers

-- Theorem 4.2, scheme-theoretic normalized geometric generic fiber
#check @Sunlet.NormalizedLatinSystem.normalizedGeometricGenericFiber_split
#print axioms Sunlet.NormalizedLatinSystem.normalizedGeometricGenericFiber_split

-- Theorem 4.2, rationality of the actual model over Q
#check @Sunlet.NormalizedLatinSystem.model_rational
#print axioms Sunlet.NormalizedLatinSystem.model_rational

-- Theorem 4.2, rationality of the actual secant over Q
#check @Sunlet.NormalizedLatinSystem.secant_rational
#print axioms Sunlet.NormalizedLatinSystem.secant_rational

-- Section 5, literal original six-family algebraic fibers
#check @Sunlet.GroupCoordinates.six_family_general_fiber
#print axioms Sunlet.GroupCoordinates.six_family_general_fiber

-- Corollary 5.1, exact degree two
#check @Sunlet.LoopData.paper_corollary_5_1_degree
#print axioms Sunlet.LoopData.paper_corollary_5_1_degree

-- Corollary 5.1, explicit interchange is the only nonidentity field symmetry
#check @Sunlet.LoopData.paper_corollary_5_1_automorphisms
#print axioms Sunlet.LoopData.paper_corollary_5_1_automorphisms

-- Corollary 5.1, every general normalized preimage is the point or its interchange
#check @Sunlet.LoopData.paper_corollary_5_1_point_ambiguity
#print axioms Sunlet.LoopData.paper_corollary_5_1_point_ambiguity

-- Theorem 6.1, all orders and exact coordinate set
#check @Sunlet.CyclicSelectedField.paper_theorem_6_1_all_orders
#print axioms Sunlet.CyclicSelectedField.paper_theorem_6_1_all_orders

-- Theorem 6.1, natural coordinate projection function fields over Q
#check @Sunlet.CyclicSelectedField.paper_projectionFunctionFieldEquiv
#print axioms Sunlet.CyclicSelectedField.paper_projectionFunctionFieldEquiv

-- Theorem 6.1, coordinate compatibility of the function-field isomorphism
#check @Sunlet.CyclicSelectedField.originalProjectionFieldEquiv_coordinate
#print axioms Sunlet.CyclicSelectedField.originalProjectionFieldEquiv_coordinate

-- Theorem 6.1, reconstruction in constrained-triple coordinates
#check @Sunlet.CyclicSelectedField.original_flow_reconstruction
#print axioms Sunlet.CyclicSelectedField.original_flow_reconstruction

-- Theorem 7.1, arbitrary automorphism subgroup
#check @Sunlet.OrbitClasses.paper_theorem_7_1
#print axioms Sunlet.OrbitClasses.paper_theorem_7_1

-- Theorem 7.1, exact exceptional orbit cardinalities
#check @Sunlet.OrbitClasses.orbit_index_two_exception_card
#print axioms Sunlet.OrbitClasses.orbit_index_two_exception_card

-- Theorem 7.1, index-two exception forces exponent two
#check @Sunlet.OrbitClasses.index_two_orbit_partition_exponent_two
#print axioms Sunlet.OrbitClasses.index_two_orbit_partition_exponent_two

-- Corollary 7.4, all cyclic orbit models
#check @Sunlet.OrbitClasses.paper_corollary_7_4
#print axioms Sunlet.OrbitClasses.paper_corollary_7_4

-- Corollary 8.1, arbitrary binary level-one identified model
#check @Sunlet.NetworkTheorem.paper_corollary_8_1
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1

-- Corollary 8.1, literal unrestricted model
#check @Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted

-- Network faithfulness, every reticulation choice gives a spanning tree
#check @Sunlet.NetworkDisplayedTrees.displayedGraph_isTree
#print axioms Sunlet.NetworkDisplayedTrees.displayedGraph_isTree

-- Network faithfulness, one monomial per displayed choice
#check @Sunlet.NetworkFlowUniqueness.coordinate_eq_displayed_sum
#print axioms Sunlet.NetworkFlowUniqueness.coordinate_eq_displayed_sum

-- Network faithfulness, the literal Fourier formula from displayed-tree leaf cuts
#check @Sunlet.NetworkDisplayedFlowCuts.coordinate_eq_leaf_cut_formula
#print axioms Sunlet.NetworkDisplayedFlowCuts.coordinate_eq_leaf_cut_formula

-- Original normalization, equality of defining ideals
#check @Sunlet.Normalization.definingIdeal_eq_normalizedKernel
#print axioms Sunlet.Normalization.definingIdeal_eq_normalizedKernel

-- Original normalization, faithful generic evaluation
#check @Sunlet.NormalizedLatinSystem.genericNormalizedEvaluation_injective
#print axioms Sunlet.NormalizedLatinSystem.genericNormalizedEvaluation_injective

-- Original normalization, actual coordinate fraction-field equivalence
#check @Sunlet.NormalizedLatinSystem.modelFunctionFieldEquivNormalizedImage
#print axioms Sunlet.NormalizedLatinSystem.modelFunctionFieldEquivNormalizedImage

-- Original normalization, every coordinate preserved
#check @Sunlet.NormalizedLatinSystem.modelFunctionFieldEquiv_coordinate
#print axioms Sunlet.NormalizedLatinSystem.modelFunctionFieldEquiv_coordinate

-- Geometric generic fiber, literal localized source retained
#check @Sunlet.NormalizedLatinSystem.normalizedLocalizedRingEquivSourceAlgebra
#print axioms Sunlet.NormalizedLatinSystem.normalizedLocalizedRingEquivSourceAlgebra

-- Geometric generic fiber, actual generic tensor algebra
#check @Sunlet.NormalizedLatinSystem.normalizedGenericFiberEquiv
#print axioms Sunlet.NormalizedLatinSystem.normalizedGenericFiberEquiv

-- Original Fourier coordinates, exact six/five family images
#check @Sunlet.GroupCoordinates.range_eq_fiveFamily
#print axioms Sunlet.GroupCoordinates.range_eq_fiveFamily

-- Original Fourier coordinates, constrained-triple coordinate ring
#check @Sunlet.GroupCoordinates.flowCoordinateRingEquiv
#print axioms Sunlet.GroupCoordinates.flowCoordinateRingEquiv

-- All orders, actual sparse tangent/contact witness
#check @Sunlet.NormalizedLatinSystem.exists_sparseWitness
#print axioms Sunlet.NormalizedLatinSystem.exists_sparseWitness

-- All cyclic orders, exact observation index range
#check @Sunlet.CyclicSelectedField.fullObservationFlowIndex_range
#print axioms Sunlet.CyclicSelectedField.fullObservationFlowIndex_range

-- Cyclic recovery, full field generated by retained coordinates
#check @Sunlet.CyclicSelectedField.observedField_eq_fullImageField
#print axioms Sunlet.CyclicSelectedField.observedField_eq_fullImageField

-- Cyclic recovery, source field algebraic over actual retained field
#check @Sunlet.CyclicSelectedField.full_isAlgebraic
#print axioms Sunlet.CyclicSelectedField.full_isAlgebraic

-- Cyclic recovery, determinant nonzero including order-two colors
#check @Sunlet.CyclicSelectedField.rowDeterminant_ne_zero
#print axioms Sunlet.CyclicSelectedField.rowDeterminant_ne_zero

-- Theorem 7.1, the full arbitrary inverse-stable partition clause
#check @Sunlet.OrbitHeight.inverse_stable_original_coordinates_order_free
#print axioms Sunlet.OrbitHeight.inverse_stable_original_coordinates_order_free

-- Network faithfulness, the unique conserved flow for each displayed choice
#check @Sunlet.NetworkFlowUniqueness.graph_eachChoiceUnique
#print axioms Sunlet.NetworkFlowUniqueness.graph_eachChoiceUnique

-- Corollary 8.1, exact displayed-tree leaf-cut coordinates with arbitrary orbit constraints
#check @Sunlet.NetworkTheorem.paper_corollary_8_1_leaf_cut
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1_leaf_cut

-- Corollary 8.1, exact unrestricted displayed-tree leaf-cut coordinates
#check @Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted_leaf_cut
#print axioms Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted_leaf_cut


-- Literal statements and actual complex-field instances.
#check @Sunlet.paper_theorem_1_1_fin
#print axioms Sunlet.paper_theorem_1_1_fin
#check @Sunlet.injective_iff_distinct_nonidentity
#print axioms Sunlet.injective_iff_distinct_nonidentity
#check @Sunlet.ComplexGroundField.complex_isAlgClosed
#print axioms Sunlet.ComplexGroundField.complex_isAlgClosed
#check @Sunlet.ComplexGroundField.complex_charZero
#print axioms Sunlet.ComplexGroundField.complex_charZero
#check @Sunlet.ComplexPaper.paper_theorem_1_1
#print axioms Sunlet.ComplexPaper.paper_theorem_1_1
#check @Sunlet.ComplexPaper.paper_theorem_2_3
#print axioms Sunlet.ComplexPaper.paper_theorem_2_3
#check @Sunlet.ComplexPaper.generic_unique_unordered_decomposition
#print axioms Sunlet.ComplexPaper.generic_unique_unordered_decomposition
#check @Sunlet.ComplexPaper.normalized_generic_degree
#print axioms Sunlet.ComplexPaper.normalized_generic_degree
#check @Sunlet.ComplexPaper.normalized_isGalois
#print axioms Sunlet.ComplexPaper.normalized_isGalois
#check @Sunlet.ComplexPaper.normalizedGaloisEquiv
#print axioms Sunlet.ComplexPaper.normalizedGaloisEquiv
#check @Sunlet.ComplexPaper.paper_theorem_4_2_algebraic_fibers
#print axioms Sunlet.ComplexPaper.paper_theorem_4_2_algebraic_fibers
#check @Sunlet.ComplexPaper.six_family_general_algebraic_fiber
#print axioms Sunlet.ComplexPaper.six_family_general_algebraic_fiber
#check @Sunlet.ComplexPaper.paper_corollary_5_1_point_ambiguity
#print axioms Sunlet.ComplexPaper.paper_corollary_5_1_point_ambiguity
#check @Sunlet.ComplexPaper.paper_theorem_6_1
#print axioms Sunlet.ComplexPaper.paper_theorem_6_1
#check @Sunlet.ComplexPaper.paper_theorem_7_1
#print axioms Sunlet.ComplexPaper.paper_theorem_7_1
#check @Sunlet.ComplexPaper.paper_theorem_7_1_inverse_stable
#print axioms Sunlet.ComplexPaper.paper_theorem_7_1_inverse_stable
#check @Sunlet.ComplexPaper.paper_corollary_7_4
#print axioms Sunlet.ComplexPaper.paper_corollary_7_4
#check @Sunlet.ComplexPaper.paper_corollary_8_1
#print axioms Sunlet.ComplexPaper.paper_corollary_8_1
#check @Sunlet.ComplexPaper.paper_corollary_8_1_unrestricted
#print axioms Sunlet.ComplexPaper.paper_corollary_8_1_unrestricted

section RationalGroundFieldChecks
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]
variable (L : Sunlet.NormalizedLatinSystem ι Ω) (o : Ω)
#check L.model_rational (k := ℚ) o
#check L.secant_rational (k := ℚ) o
#check Sunlet.CyclicSelectedField.paper_projectionFunctionFieldEquiv
end RationalGroundFieldChecks

-- Definitions that fix the mathematical meaning of the principal statements.
#print Sunlet.NormalizedLatinSystem
#print Sunlet.coordinatePolynomial
#print Sunlet.GroupCoordinates.coordinate
#print Sunlet.GroupCoordinates.FlowIndex
#print Sunlet.GroupCoordinates.tripleParameterMap
#print Sunlet.Normalization.Parameters
#print Sunlet.Normalization.interchangeParameters
#print Sunlet.Normalization.LocalizedRing
#print Sunlet.Normalization.normalizedComorphism
#print Sunlet.LoopData.AbelianGroup
#print Sunlet.LoopData.characterSubgroup
#print Sunlet.LoopData.characterEquiv
#print Sunlet.LoopData.swapCharacters
#print Sunlet.LoopData.CharacterWreath
#print Sunlet.LoopData.abelianCharacterSwap
#print Sunlet.LoopData.AbelianCharacterWreath
#print Sunlet.AlgebraicSets.PolynomialEquiv
#print Sunlet.FiberAlgebraic.gaugeSpace
#print Sunlet.NormalizedLatinSystem.ModelCoordinateRing
#print Sunlet.NormalizedLatinSystem.ModelFunctionField
#print Sunlet.NormalizedLatinSystem.NormalizedGenericFiber
#print Sunlet.NormalizedLatinSystem.NormalizedGeometricGenericFiber
#print PolynomialImage.RationalCoordinateInverse
#print PolynomialImage.RationalCoordinateInverse.inverseOpen
#print PolynomialImage.OriginalFunctionField
#print Sunlet.CyclicSelectedField.LiteralRetained
#print Sunlet.CyclicSelectedField.fullObservationIndex
#print Sunlet.OrbitClasses.OrbitIndexTwoException
#print Sunlet.NetworkGraphDecomposition.IsBinaryCactus
#print Sunlet.NetworkGraphModel.Orientation
#print Sunlet.NetworkGraphModel.ReticulationData
#print Sunlet.NetworkFlowGluing.Flow
#print Sunlet.NetworkGraphModel.coordinate
#print Sunlet.NetworkTriangleIncidence.defect

#print Sunlet.OrbitHeight.InverseStablePartition

#print Sunlet.OrbitHeight.InverseStablePartition.IndexTwoException

#print Sunlet.ClassGroupCoordinates.coordinate

#print Sunlet.ClassGroupCoordinates.tripleImageClosure

#print Sunlet.NetworkDisplayedFlowCuts.leafCutCoordinate

-- The exhaustive audit traverses all local proof bodies; the enclosing
-- compiler/job wall-time bound remains in force. No proof check is skipped.
set_option maxHeartbeats 0 in
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let approvedModules : Array Name := #[
    `sunlet.all_loop_contact_supports,
    `sunlet.arbitrary_orbit_classification,
    `sunlet.basic,
    `sunlet.class_dimension,
    `sunlet.class_kernel,
    `sunlet.class_selection,
    `sunlet.coarse_selection,
    `sunlet.contact_coefficient,
    `sunlet.contact_completion,
    `sunlet.contact_development,
    `sunlet.contact_equations,
    `sunlet.contact_exceptions,
    `sunlet.contact_linear,
    `sunlet.contact_torus,
    `sunlet.cyclic_orbit_models,
    `sunlet.cyclic_sparse_witness,
    `sunlet.dimension_algebra,
    `sunlet.dimension_lower_bound,
    `sunlet.dimension_upper_bound,
    `sunlet.distinct_derangements,
    `sunlet.etale_derivations,
    `sunlet.exceptional_contact_transport,
    `sunlet.exponent_independence,
    `sunlet.exponent_rank,
    `sunlet.extended_rational_derivations,
    `sunlet.fine_invariant_kernel,
    `sunlet.fine_odd_kernel,
    `sunlet.generated_action,
    `sunlet.generic_pair_geometry,
    `sunlet.generic_toric_embeddings,
    `sunlet.group_coordinates,
    `sunlet.height_elimination,
    `sunlet.height_obstructions,
    `sunlet.identified_normalization,
    `sunlet.index_two_orbit_rigidity,
    `sunlet.initial_independence,
    `sunlet.invariant_functions,
    `sunlet.jacobian_finite,
    `sunlet.latin_orbits,
    `sunlet.latin_sparse_contact,
    `sunlet.latin_split,
    `sunlet.loop_field_actions,
    `sunlet.loop_point_fibers,
    `sunlet.main_dimension,
    `sunlet.matrix_specialization,
    `sunlet.negation_coarsening,
    `sunlet.normalization,
    `sunlet.normalized_algebra,
    `sunlet.normalized_variations,
    `sunlet.one_hole_field,
    `sunlet.one_level_obstructions,
    `sunlet.orbit_height,
    `sunlet.orbit_height_completion,
    `sunlet.orbit_models,
    `sunlet.ordinary_edge_rigidity,
    `sunlet.paper_statements,
    `sunlet.partition_subgroups,
    `sunlet.permutation_families,
    `sunlet.polynomial_image,
    `sunlet.punctured_both_endpoints,
    `sunlet.punctured_differences,
    `sunlet.ratio_correction,
    `sunlet.ratio_solution_spaces,
    `sunlet.rational_diagonal_actions,
    `sunlet.rational_partials,
    `sunlet.selected_exponents,
    `sunlet.selected_relations,
    `sunlet.sparse_contact,
    `sunlet.sparse_contact_entries,
    `sunlet.sparse_tangent_pair,
    `sunlet.support_transport,
    `sunlet.toric_differential,
    `sunlet.two_ratio_rigidity,
    `sunlet.verified_complex_statements,
    `sunlet.verified_cyclic_field,
    `sunlet.verified_cyclic_paper,
    `sunlet.verified_fiber_geometry,
    `sunlet.verified_field_core,
    `sunlet.verified_generic_conclusions,
    `sunlet.verified_generic_open,
    `sunlet.verified_model_fibers,
    `sunlet.verified_network_algebra,
    `sunlet.verified_network_conclusion,
    `sunlet.verified_network_graph,
    `sunlet.verified_normalized_generic_fiber,
    `sunlet.verified_normalized_model,
    `sunlet.verified_toric_geometry,
    `sunlet.weighted_initial]
  unless env.header.trustLevel == 0 do
    throwError "Final audit requires the ordinary trust-level-zero environment"
  for mod in env.header.moduleNames do
    if mod == `sunlet || (mod.toString.startsWith "Sunlet." || mod.toString.startsWith "sunlet.") then
      unless approvedModules.contains mod do
        throwError "Unbound imported project module: {mod}"
  for mod in approvedModules do
    unless env.header.moduleNames.contains mod do
      throwError "Required project module is absent: {mod}"
    unless env.header.imports.any (fun imp => imp.module == mod && imp.importAll) do
      throwError "Private proof bodies were not explicitly requested for: {mod}"
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => env.mainModule
  let isLocal (n : Name) : Bool :=
    moduleOf n == env.mainModule || approvedModules.contains (moduleOf n)
  let allowed (n : Name) : Bool :=
    n == ``propext || n == ``Classical.choice || n == ``Quot.sound
  let principals : Array Name := #[
    ``Sunlet.paper_theorem_1_1_fin,
    ``Sunlet.injective_iff_distinct_nonidentity,
    ``Sunlet.ComplexGroundField.complex_isAlgClosed,
    ``Sunlet.ComplexGroundField.complex_charZero,
    ``Sunlet.ComplexPaper.paper_theorem_1_1,
    ``Sunlet.ComplexPaper.paper_theorem_2_3,
    ``Sunlet.ComplexPaper.generic_unique_unordered_decomposition,
    ``Sunlet.ComplexPaper.normalized_generic_degree,
    ``Sunlet.ComplexPaper.normalized_isGalois,
    ``Sunlet.ComplexPaper.normalizedGaloisEquiv,
    ``Sunlet.ComplexPaper.paper_theorem_4_2_algebraic_fibers,
    ``Sunlet.ComplexPaper.six_family_general_algebraic_fiber,
    ``Sunlet.ComplexPaper.paper_corollary_5_1_point_ambiguity,
    ``Sunlet.ComplexPaper.paper_theorem_6_1,
    ``Sunlet.ComplexPaper.paper_theorem_7_1,
    ``Sunlet.ComplexPaper.paper_theorem_7_1_inverse_stable,
    ``Sunlet.ComplexPaper.paper_corollary_7_4,
    ``Sunlet.ComplexPaper.paper_corollary_8_1,
    ``Sunlet.ComplexPaper.paper_corollary_8_1_unrestricted,

    ``Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted_leaf_cut,
    ``Sunlet.NetworkTheorem.paper_corollary_8_1_leaf_cut,
    ``Sunlet.paper_theorem_1_1,
    ``Sunlet.GroupCoordinates.paper_theorem_1_1_original_coordinates,
    ``Sunlet.paper_theorem_2_3_literal,
    ``Sunlet.NormalizedLatinSystem.generic_unique_unordered_decomposition,
    ``Sunlet.NormalizedLatinSystem.generic_unique_torus_decomposition,
    ``Sunlet.NormalizedLatinSystem.normalized_generic_degree,
    ``Sunlet.NormalizedLatinSystem.normalized_isGalois,
    ``Sunlet.NormalizedLatinSystem.normalizedGaloisEquiv,
    ``Sunlet.NormalizedLatinSystem.normalizedGaloisUniversalEquiv,
    ``Sunlet.LoopData.abelianCharacterWreathEquiv,
    ``Sunlet.NormalizedLatinSystem.paper_theorem_4_2_algebraic_fibers,
    ``Sunlet.NormalizedLatinSystem.normalizedGeometricGenericFiber_split,
    ``Sunlet.NormalizedLatinSystem.model_rational,
    ``Sunlet.NormalizedLatinSystem.secant_rational,
    ``Sunlet.GroupCoordinates.six_family_general_fiber,
    ``Sunlet.LoopData.paper_corollary_5_1_degree,
    ``Sunlet.LoopData.paper_corollary_5_1_automorphisms,
    ``Sunlet.LoopData.paper_corollary_5_1_point_ambiguity,
    ``Sunlet.CyclicSelectedField.paper_theorem_6_1_all_orders,
    ``Sunlet.CyclicSelectedField.paper_projectionFunctionFieldEquiv,
    ``Sunlet.CyclicSelectedField.originalProjectionFieldEquiv_coordinate,
    ``Sunlet.CyclicSelectedField.original_flow_reconstruction,
    ``Sunlet.OrbitClasses.paper_theorem_7_1,
    ``Sunlet.OrbitClasses.orbit_index_two_exception_card,
    ``Sunlet.OrbitClasses.index_two_orbit_partition_exponent_two,
    ``Sunlet.OrbitClasses.paper_corollary_7_4,
    ``Sunlet.NetworkTheorem.paper_corollary_8_1,
    ``Sunlet.NetworkTheorem.paper_corollary_8_1_unrestricted,
    ``Sunlet.NetworkDisplayedTrees.displayedGraph_isTree,
    ``Sunlet.NetworkFlowUniqueness.coordinate_eq_displayed_sum,
    ``Sunlet.NetworkDisplayedFlowCuts.coordinate_eq_leaf_cut_formula,
    ``Sunlet.Normalization.definingIdeal_eq_normalizedKernel,
    ``Sunlet.NormalizedLatinSystem.genericNormalizedEvaluation_injective,
    ``Sunlet.NormalizedLatinSystem.modelFunctionFieldEquivNormalizedImage,
    ``Sunlet.NormalizedLatinSystem.modelFunctionFieldEquiv_coordinate,
    ``Sunlet.NormalizedLatinSystem.normalizedLocalizedRingEquivSourceAlgebra,
    ``Sunlet.NormalizedLatinSystem.normalizedGenericFiberEquiv,
    ``Sunlet.GroupCoordinates.range_eq_fiveFamily,
    ``Sunlet.GroupCoordinates.flowCoordinateRingEquiv,
    ``Sunlet.NormalizedLatinSystem.exists_sparseWitness,
    ``Sunlet.CyclicSelectedField.fullObservationFlowIndex_range,
    ``Sunlet.CyclicSelectedField.observedField_eq_fullImageField,
    ``Sunlet.CyclicSelectedField.full_isAlgebraic,
    ``Sunlet.OrbitHeight.inverse_stable_original_coordinates_order_free,
    ``Sunlet.NetworkFlowUniqueness.graph_eachChoiceUnique,
    ``Sunlet.CyclicSelectedField.rowDeterminant_ne_zero]
  for n in principals do
    unless isLocal n do
      throwError "Principal endpoint is outside the exact source-bound project closure: {n}"
  let names := env.constants.fold (init := (#[] : Array Name)) fun ns n _ =>
    if isLocal n then ns.push n else ns
  let names := names.qsort Name.lt
  let mut records : Array Json := #[]
  let mut boundaries : NameSet := {}
  for n in names do
    let some ci := env.find? n | throwError "Missing source-bound project declaration {n}"
    if ci.isUnsafe then
      throwError "Unsafe local declaration is forbidden: {n}"
    match ci with
    | .defnInfo _ | .thmInfo _ | .opaqueInfo _ =>
        unless (ci.value? true).isSome do
          throwError "Local proof or definition body unavailable: {n}"
    | .axiomInfo _ => throwError "Local axiom declaration is forbidden: {n}"
    | _ => pure ()
    let axs := (← collectAxioms n).qsort Name.lt
    for ax in axs do
      unless allowed ax do
        throwError "Unapproved transitive axiom {ax} in {n}"
    let typeDeps := ci.type.getUsedConstants
    let valueDeps := (ci.value? true).map Expr.getUsedConstants |>.getD #[]
    let kernelDeps : Array Name := match ci with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    let deps := (typeDeps ++ valueDeps ++ kernelDeps).foldl (fun s x => s.insert x) ({} : NameSet)
    for d in deps.toArray do
      unless (env.find? d).isSome do
        throwError "Missing actual dependency {d} of {n}"
    for d in deps.toArray do
      unless isLocal d do boundaries := boundaries.insert d
    let typeString ← liftTermElabM <| return (← Meta.ppExpr ci.type).pretty
    records := records.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("universe_parameters", toJson (ci.levelParams.map Name.toString)),
      ("type", toJson typeString),
      ("proof_or_definition_body_available", toJson (ci.value? true).isSome),
      ("unsafe_declaration", toJson ci.isUnsafe),
      ("direct_type_dependencies", toJson (typeDeps.qsort Name.lt |>.map Name.toString)),
      ("direct_body_dependencies", toJson (valueDeps.qsort Name.lt |>.map Name.toString)),
      ("direct_kernel_dependencies", toJson (kernelDeps.qsort Name.lt |>.map Name.toString)),
      ("direct_dependencies", toJson (deps.toArray.qsort Name.lt |>.map Name.toString)),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let mut boundaryRecords : Array Json := #[]
  for n in boundaries.toArray.qsort Name.lt do
    let some ci := env.find? n | throwError "Missing pinned-library boundary {n}"
    if ci.isUnsafe then
      throwError "Unsafe pinned-library dependency is forbidden: {n}"
    let axs := (← collectAxioms n).qsort Name.lt
    for ax in axs do
      unless allowed ax do
        throwError "Unapproved axiom {ax} at pinned-library boundary {n}"
    boundaryRecords := boundaryRecords.push <| Json.mkObj [
      ("name", toJson n.toString), ("module", toJson (moduleOf n).toString),
      ("transitive_axioms", toJson (axs.map Name.toString))]
  let result := Json.mkObj [
    (".lake/reports/audit", toJson "all source-bound project declarations, actual bodies, and transitive axioms"),
    ("audit_mode", toJson "ordinary modular source-object-bound proof chain"),
    ("body_audit_passed", toJson true),
    ("complete", toJson false),
    ("required_input_modules", toJson (approvedModules.map Name.toString)),
    ("expected_lean_version", toJson "4.35.0"),
    ("expected_lean_commit", toJson "eb6cafb7290e8bd5f2937522d8d804f58f02bafc"),
    ("mathlib_commit", toJson "56a005855ea17e0b0958f73ec801ae140b0a1679"),
    ("main_module", toJson env.mainModule.toString),
    ("environment_trust_level", toJson env.header.trustLevel.toNat),
    ("direct_imports", toJson (env.header.imports.map fun imp => imp.module.toString)),
    ("imported_local_proof_objects", toJson (approvedModules.map Name.toString)),
    ("axiom_whitelist", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("principal_endpoints", toJson (principals.map Name.toString)),
    ("local_declarations", Json.arr records),
    ("pinned_library_boundary", Json.arr boundaryRecords),
    ("unapproved_axioms", Json.arr #[])]
  IO.FS.createDirAll ".lake/reports/audit/final"
  IO.FS.writeFile ".lake/reports/audit/final/modular_dependencies.json" result.pretty
  logInfo m!"MODULAR BODY AUDIT PASSED (source/object binding and independent closure verification still required): {records.size} source-bound project declarations; {principals.size} principal/semantic endpoints; {boundaryRecords.size} pinned-library boundaries."

end SunletModularFinalAudit
