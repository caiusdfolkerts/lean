module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_chunkTree " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def chunkTree⟪0⟫ : TargetTree :=
  .branch 64 chunkPart⟪0⟫A chunkPart⟪0⟫B"### args

