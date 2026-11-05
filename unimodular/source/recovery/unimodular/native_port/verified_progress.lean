module

public import Recovery.Unimodular.PriorExtensions.LiteralA3Projectivity
public import Recovery.Unimodular.NativePort.A3PrimitiveReplacement
public import Recovery.Unimodular.PriorExtensions.FlowLattice

@[expose] public section

/-!
Joint entry point for the presently verified native results.

This is explicitly NOT a completed formalization of the whole unimodular
paper. In particular, no missing Seymour, Fano, divisor, Koszul or syzygy
claim is imported as an axiom or packaged as a proved statement here.
The fresh check of this module verifies that these exact independently
checked proof components coexist under one pinned Lean environment.
-/

#print axioms Unimodular.AllowedBlocks.theorem_1_1
#print axioms Unimodular.AllowedBlocks.theorem_3_1_bijection
#print axioms Unimodular.FlowOrientations.proposition_2_3_integral_relation
#print axioms Unimodular.FlowOrientations.proposition_2_3
#print axioms Unimodular.FlowOrientations.positive_configuration_flow_normal_form
#print axioms Unimodular.LiteralRootCoordinates.a3_literal_complete_fan_count
#print axioms Unimodular.LiteralRootCoordinates.a3_literal_regular_complete_fan_count
#print axioms Unimodular.LiteralA3Projectivity.literal_projective_fan_count
#print axioms Unimodular.LiteralA3Projectivity.literal_lattice_projective_fan_count
#print axioms Unimodular.LiteralA3Projectivity.literal_projective_regular_fan_count
#print axioms Unimodular.LiteralA3Projectivity.literal_nonprojective_regular_fan_count
#print axioms Unimodular.A3ProjectiveCounts.smooth_exceptions_exact
#print axioms Unimodular.A3PrimitiveReplacement.one_square_nonprojective_primitive
#print axioms Unimodular.A3ReplacementCones.removed_full_cone_iff
#print axioms Unimodular.A3ReplacementCones.inserted_full_cone_iff

set_option pp.universes true in
#check Unimodular.AllowedBlocks.theorem_1_1
#check Unimodular.AllowedBlocks.theorem_3_1_bijection
#check Unimodular.FlowOrientations.proposition_2_3
#check Unimodular.FlowOrientations.positive_configuration_flow_normal_form
#check Unimodular.LiteralRootCoordinates.a3_literal_complete_fan_count
#check Unimodular.LiteralRootCoordinates.a3_literal_regular_complete_fan_count
#check Unimodular.LiteralA3Projectivity.literal_projective_fan_count
#check Unimodular.LiteralA3Projectivity.literal_lattice_projective_fan_count
#check Unimodular.LiteralA3Projectivity.literal_projective_regular_fan_count
#check Unimodular.LiteralA3Projectivity.literal_nonprojective_regular_fan_count
#check Unimodular.A3PrimitiveReplacement.one_square_nonprojective_primitive
#check Unimodular.A3ReplacementCones.removed_full_cone_iff
#check Unimodular.A3ReplacementCones.inserted_full_cone_iff

#check "UNIMODULAR_VERIFIED_PROGRESS_EOF_V1"
