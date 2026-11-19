module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_checked_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : Interval test ⟪0⟫ ⟪1⟫ :=
  interval_of_check test ⟪0⟫ ⟪2⟫ (by decide +kernel)"### args

elab "cert_lookup_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : Nat × Nat := records.get i"### args

elab "cert_quota_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def quota (j : Nat) : Nat := ([0,⟪0⟫,⟪1⟫,⟪2⟫,0] : List Nat).getD j 0"### args

elab "cert_test_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool :=
  let r := lookup i
  decide (r.1 < GraphCatalogue.Generated.Graph13.Level⟪0⟫.count) &&
  (decide (SharedSmallRootReplay.complement r.2 =
    (GraphCatalogue.Generated.Graph13.Level⟪0⟫.lookup r.1).mask) &&
  SharedSmallRootReplay.check quota ⟪1⟫ r.2)"### args

