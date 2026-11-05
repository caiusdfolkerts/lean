import bier.forster.operator_norm
import bier.forster.hadamard
import bier.audit_support

-- Create directories for generated verification output.
run_cmd Lean.Elab.Command.liftIO do
  IO.FS.createDirAll ".lake/reports/audit"


/-! Kernel-environment audit of the complete Forster dependency chain. -/

audit_standard_axioms Bier.Forster.exists_exponentialSum_minimum
audit_standard_axioms Bier.Forster.CauchyBinet.det_mul_eq_sum_minors
audit_standard_axioms Bier.Forster.exists_equal_leverage
audit_standard_axioms Bier.Forster.exists_balancedProjection
audit_standard_axioms Bier.Forster.exists_generic_sign_factor
audit_standard_axioms Bier.Forster.exists_rank_factorization
audit_standard_axioms Bier.Forster.forster_bound
audit_standard_axioms Bier.Forster.signRank_spectral
audit_standard_axioms Bier.Forster.hadamard_columnRestriction_signRank

export_proof_dependencies ".lake/reports/audit/forster_dependencies.json" [
  Bier.Forster.exists_exponentialSum_minimum,
  Bier.Forster.CauchyBinet.det_mul_eq_sum_minors,
  Bier.Forster.exists_equal_leverage,
  Bier.Forster.exists_balancedProjection,
  Bier.Forster.exists_generic_sign_factor,
  Bier.Forster.exists_rank_factorization,
  Bier.Forster.forster_bound,
  Bier.Forster.signRank_spectral,
  Bier.Forster.hadamard_columnRestriction_signRank
]
