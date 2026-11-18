module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : Interval test ⟪0⟫ ⟪1⟫ :=
  interval_of_check test ⟪0⟫ ⟪2⟫ (by decide +kernel)"### args

elab "cert_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked : Interval test 0 ⟪0⟫ := by
  intro i hlo hhi
  have hlocal := Part000.checked i (by omega) (by omega)
  simpa only [test, lookup, dispatch, Table.get, Part000.test] using hlocal"### args

elab "cert_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : Interval test ⟪0⟫ ⟪1⟫ :=
  fast_interval ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_choices " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def choices (i : Fin ⟪0⟫) (edge : Fin 45) :
    Choice 10 ⟪1⟫ 24505 := choiceAt (lookup i.val) edge"### args

elab "cert_choices_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem choices_checked (i : Fin ⟪0⟫) (edge : Fin 45) :
    extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪1⟫.entry i) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪2⟫.entry edge (choices i edge) = true := by
  have hi := checked i.val (Nat.zero_le _) i.isLt
  have he := List.all_eq_true.mp hi edge (List.mem_finRange edge)
  simpa only [choices, Fin.ofNat_val_eq_self, FastGraphCatalogueCheck.extensionCheck_eq] using he"### args

elab "cert_covers_step " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem covers_step (hprevious : Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪0⟫.entry i).edges) ⟪1⟫) :
    Covers TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
      (fun i => (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪2⟫.entry i).edges) ⟪3⟫ :=
  covers_step_of_checks TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪0⟫.entry Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪2⟫.entry choices
    Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪0⟫.entry_checked Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪2⟫.entry_checked choices_checked hprevious"### args

elab "cert_entry " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def entry (i : Fin count) : (State 45) := lookup i.val"### args

elab "cert_entry_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def entry (i : Fin count) : Nat := lookup i.val"### args

elab "cert_entry_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem entry_checked (i : Fin count) : stateCheck (entry i) = true :=
  checked i.val (Nat.zero_le _) i.isLt"### args

elab "cert_fastTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def fastTest (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  Graph13FastEdgeMaps.extensionCheck
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪0⟫.entry (Fin.ofNat ⟪1⟫ i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪2⟫.entry edge
    (choiceAt (lookup i) edge)"### args

elab "cert_fastTest_eq " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fastTest_eq (i : Nat) : fastTest i = test i := by
  unfold fastTest test
  apply congrArg (fun f : Fin 45 → Bool => (List.finRange 45).all f)
  funext edge
  exact Graph13FastEdgeMaps.extensionCheck_eq _ _ _ _"### args

elab "cert_fast_interval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fast_interval (lo count : Nat)
    (h : checkRange fastTest lo count = true) : Interval test lo (lo+count) := by
  intro i hlo hhi
  rw [← fastTest_eq]
  exact checkRange_sound fastTest lo count h i hlo hhi"### args

elab "cert_level_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem level⟪0⟫_complete :
    Covers TenGraphEdges.incidence 4 Frames.renamings
      (fun i => (Level⟪0⟫.entry i).edges) ⟪1⟫ :=
  Step⟪2⟫.covers_step level⟪2⟫_complete"### args

elab "cert_lookup_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : (State 45) := table.get i"### args

elab "cert_lookup_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : (State 45) := (dispatch.get i) i"### args

elab "cert_lookup_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : (Nat × Nat) := table.get i"### args

elab "cert_lookup_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : Nat := table.get i"### args

elab "cert_lookup_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def lookup (i : Nat) : Nat := (dispatch.get i) i"### args

elab "cert_table_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def table : Table Nat :=
  integerTable% 0 ⟪0⟫"### args

elab "cert_test " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool := (List.finRange 45).all fun edge =>
  FastGraphCatalogueCheck.extensionCheck TenGraphEdges.incidence 4 Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Frames.renamings
    (Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪0⟫.entry (Fin.ofNat ⟪1⟫ i)) Papers.RationalityTen.GraphCatalogue.Generated.Graph13.Level⟪2⟫.entry edge
    (choiceAt (lookup i) edge)"### args

elab "cert_test_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool := TenGraphEdges.permutationCheck (lookup i).1 (lookup i).2"### args

elab "cert_test_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool := stateCheck (lookup i)"### args

