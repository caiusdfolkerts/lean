module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_r_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem r⟪0⟫_checked : check r⟪0⟫ = true := by decide +kernel"### args

