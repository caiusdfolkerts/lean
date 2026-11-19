module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_candidate " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidate⟪0⟫ : Description := ⟨⟪1⟫, ⟨⟪2⟫, (certNat% ⟪3⟫)⟩⟩"### args

elab "cert_candidate_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem candidate⟪0⟫_checked : Checked candidate⟪0⟫ SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota ⟪1⟫)) ⟪2⟫ := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩"### args

elab "cert_candidate_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem candidate⟪0⟫_checked : Checked candidate⟪0⟫ SharedSmallGraph.graphRows
    (SharedSmallGraph.allowedMask (quota 14)) ⟪1⟫ := ⟨by decide +kernel, by decide +kernel⟩"### args

elab "cert_candidate_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem candidate⟪0⟫_checked : Checked candidate⟪0⟫ SharedSix0Incidence.graphRows
    (GraphEmbeddingCoverage.sixAllowed (quota 30)) ⟪1⟫ := ⟨nodup_of_increasing _ (by decide +kernel), by decide +kernel⟩"### args

