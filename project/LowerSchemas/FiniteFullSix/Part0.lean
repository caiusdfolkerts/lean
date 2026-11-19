module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_inverse " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem inverse_⟪0⟫ : Interval inverseTest ⟪1⟫ ⟪2⟫ :=
  interval_of_check inverseTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_inverse_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem inverse_join_⟪0⟫_⟪1⟫ : Interval inverseTest ⟪2⟫ ⟪3⟫ :=
  interval_append inverseTest ⟪2⟫ ⟪4⟫ ⟪3⟫ inverse_⟪0⟫ inverse_⟪5⟫"### args

elab "cert_inverse_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem inverse_join_⟪0⟫_⟪1⟫ : Interval inverseTest ⟪2⟫ ⟪3⟫ :=
  interval_append inverseTest ⟪2⟫ ⟪4⟫ ⟪3⟫ inverse_join_⟪0⟫_⟪5⟫ inverse_join_⟪5⟫_⟪1⟫"### args

elab "cert_inverse_part " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem inverse_part_⟪0⟫ : Interval inverseTest ⟪1⟫ ⟪2⟫ := inverse_join_⟪3⟫_⟪4⟫"### args

elab "cert_lookup " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : Nat := table.get i"### args

elab "cert_part " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem part_⟪0⟫ : Interval embeddingTest ⟪1⟫ ⟪2⟫ :=
  interval_of_check embeddingTest ⟪1⟫ 8 (by decide +kernel)"### args

elab "cert_part_join " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem part_join_⟪0⟫_⟪1⟫ : Interval embeddingTest ⟪0⟫ ⟪1⟫ :=
  interval_append embeddingTest ⟪0⟫ ⟪2⟫ ⟪1⟫ part_⟪0⟫ part_join_⟪2⟫_⟪1⟫"### args

elab "cert_part_join_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem part_join_⟪0⟫_⟪1⟫ : Interval embeddingTest ⟪2⟫ ⟪3⟫ :=
  interval_append embeddingTest ⟪2⟫ ⟪4⟫ ⟪3⟫ part_join_⟪0⟫_⟪5⟫ part_join_⟪5⟫_⟪1⟫"### args

elab "cert_part_join_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem part_join_⟪0⟫_⟪1⟫ : Interval embeddingTest ⟪2⟫ ⟪3⟫ :=
  interval_append embeddingTest ⟪2⟫ ⟪4⟫ ⟪3⟫ part_⟪0⟫ part_⟪5⟫"### args

elab "cert_part_part " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem part_part_⟪0⟫ : Interval embeddingTest ⟪1⟫ ⟪2⟫ := part_join_⟪3⟫_⟪4⟫"### args

elab "cert_table " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def table : Table Nat :=
  integerTable% 0 ⟪0⟫"### args

