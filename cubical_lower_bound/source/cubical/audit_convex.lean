import cubical.polytope.main
import cubical.polytope.face_bounds
import cubical.polytope.generic_theorems
import cubical.polytope.stacking_sharpness_real
import cubical.audit_support

-- Create directories for generated verification output.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


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
