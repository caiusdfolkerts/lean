module

public import cubical.polytope.main
public import cubical.polytope.face_bounds
public import cubical.polytope.generic_theorems
public import cubical.polytope.stacking_sharpness_real
public import cubical.audit_support

@[expose] public section

-- Optional audit-report filesystem output is disabled in the read-only verifier.


/-! # Transitive axiom audit of every principal convex claim -/

open LeanEval.Geometry.PlatonicClassification

audit_standard_axioms IsCubical.edge_bound
audit_standard_axioms IsCubical.strengthened_edge_bound
audit_standard_axioms IsCubical.bipartite
audit_standard_axioms IsCubical.generic_local_propagation
audit_standard_axioms IsCubical.generic_facet_determination
audit_standard_axioms IsCubical.face_lower_bound
audit_standard_axioms IsCubical.facet_lower_bound
audit_standard_axioms IsCubical.strengthened_face_lower_bound
audit_standard_axioms IsCubical.strengthened_facet_lower_bound
audit_standard_axioms standardCube_isCubical
audit_standard_axioms standardCube_faceNumber
audit_standard_axioms IsStackedCubical.isCubical
audit_standard_axioms IsStackedCubical.edge_equality
audit_standard_axioms IsStackedCubical.face_equality
audit_standard_axioms IsStackedCubical.facet_equality
audit_standard_axioms IsStackedCubical.edge_equality_real
audit_standard_axioms IsStackedCubical.face_equality_real
audit_standard_axioms IsStackedCubical.facet_equality_real
audit_standard_axioms Cubical.Simplicial.IsFacetCircuit.genericallyRigid

export_proof_dependencies ".lake/reports/audit/convex_dependencies.json" [
  IsCubical.edge_bound,
  IsCubical.strengthened_edge_bound,
  IsCubical.bipartite,
  IsCubical.generic_local_propagation,
  IsCubical.generic_facet_determination,
  IsCubical.face_lower_bound,
  IsCubical.facet_lower_bound,
  IsCubical.strengthened_face_lower_bound,
  IsCubical.strengthened_facet_lower_bound,
  standardCube_isCubical,
  standardCube_faceNumber,
  IsStackedCubical.isCubical,
  IsStackedCubical.edge_equality,
  IsStackedCubical.face_equality,
  IsStackedCubical.facet_equality,
  IsStackedCubical.edge_equality_real,
  IsStackedCubical.face_equality_real,
  IsStackedCubical.facet_equality_real,
  Cubical.Simplicial.IsFacetCircuit.genericallyRigid
]
