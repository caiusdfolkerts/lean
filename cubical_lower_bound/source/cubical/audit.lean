import cubical
import cubical.audit_convex

-- Create directories for generated verification output.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


/-! # Final audit of the complete paper -/

open Cubical.PL.CubeComplex

audit_standard_axioms strengthened_edge_bound
audit_standard_axioms strengthened_edge_bound_nat
audit_standard_axioms cubical_pl_lower_bound
audit_standard_axioms exists_coloring
audit_standard_axioms neighborGraph_genericallyRigid_dim
audit_standard_axioms facetStep_connected
audit_standard_axioms Cubical.PL.sphere_edgeGraph_genericallyRigid
audit_standard_axioms Cubical.PL.isPLSphere_barycentric_iff

export_proof_dependencies ".lake/reports/audit/pl_dependencies.json" [
  strengthened_edge_bound,
  strengthened_edge_bound_nat,
  cubical_pl_lower_bound,
  exists_coloring,
  neighborGraph_genericallyRigid_dim,
  facetStep_connected,
  Cubical.PL.sphere_edgeGraph_genericallyRigid,
  Cubical.PL.isPLSphere_barycentric_iff
]
