import bier.general_construction
import bier.realization_from_faces
import bier.audit_support

-- Create directories for generated verification output.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


/-! Checked-environment guards for the principal statements and geometric foundations. -/

audit_standard_axioms Bier.principal_example
audit_standard_axioms Bier.self_dual_example
audit_standard_axioms Bier.three_dimensional_example
audit_standard_axioms Bier.general_allSign_construction
audit_standard_axioms Bier.ghost_signRank_bound_fixedCard
audit_standard_axioms Bier.ghost_signRank_bound_arbitrary
audit_standard_axioms Bier.exists_core_schur_realization
audit_standard_axioms Bier.paddedPrincipalInverse_span_finrank
audit_standard_axioms Bier.Complex.bier_isSphere
audit_standard_axioms Bier.principalSigns_signRank_gt
audit_standard_axioms Bier.explicitHadamard_hadamard
audit_standard_axioms Bier.allColumnSigns_signRank
audit_standard_axioms Bier.Complex.isolated_bier_stellar
audit_standard_axioms Bier.allLabelsSphere_vertex_count
audit_standard_axioms Bier.allLabelsSphere_dimension
audit_standard_axioms Bier.allLabelsSphere_isSphere
audit_standard_axioms Bier.Complex.selfDualSuspension_link_eq_map
audit_standard_axioms Bier.Complex.selfDualSuspension_nonpolytopal
audit_standard_axioms Bier.PolytopeRealization.link_polytopal
audit_standard_axioms Bier.realization_of_proper_faces
audit_standard_axioms Bier.all_labels_example
audit_standard_axioms Bier.Complex.isolated_bier_nonpolytopal
audit_standard_axioms Bier.StellarFacetData.inverseRealization
audit_standard_axioms Bier.StellarFacetData.polytopal_of_stellar
audit_standard_axioms Bier.general_allSign_construction_unrestricted

export_proof_dependencies ".lake/reports/audit/principal_dependencies.json" [
  Bier.principal_example,
  Bier.self_dual_example,
  Bier.three_dimensional_example,
  Bier.general_allSign_construction,
  Bier.ghost_signRank_bound_fixedCard,
  Bier.ghost_signRank_bound_arbitrary,
  Bier.exists_core_schur_realization,
  Bier.paddedPrincipalInverse_span_finrank,
  Bier.Complex.bier_isSphere,
  Bier.principalSigns_signRank_gt,
  Bier.explicitHadamard_hadamard,
  Bier.allColumnSigns_signRank,
  Bier.Complex.isolated_bier_stellar,
  Bier.allLabelsSphere_vertex_count,
  Bier.allLabelsSphere_dimension,
  Bier.allLabelsSphere_isSphere,
  Bier.Complex.selfDualSuspension_link_eq_map,
  Bier.Complex.selfDualSuspension_nonpolytopal,
  Bier.PolytopeRealization.link_polytopal,
  Bier.realization_of_proper_faces,
  Bier.all_labels_example,
  Bier.Complex.isolated_bier_nonpolytopal,
  Bier.StellarFacetData.inverseRealization,
  Bier.StellarFacetData.polytopal_of_stellar,
  Bier.general_allSign_construction_unrestricted
]
