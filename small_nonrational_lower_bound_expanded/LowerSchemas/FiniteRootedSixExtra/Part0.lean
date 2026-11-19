module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_badMasksBlock_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_badMasksBlock_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_badMasksBlock_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_badMasksBlock_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := 0x0"### args

elab "cert_badTest_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_⟪0⟫_block_⟪1⟫ : Interval badTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check badTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_block_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem block_⟪0⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪1⟫)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount ⟪1⟫)) 0 8 24
  check_⟪0⟫_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount ⟪1⟫)) 8 16 24
  check_⟪0⟫_0008
  check_⟪0⟫_0016))"### args

elab "cert_block_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem block_⟪0⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪1⟫)) 0 ⟪2⟫ :=
  check_⟪0⟫_0000"### args

elab "cert_candidateMasksBlock_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_candidateMasksBlock_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_candidateMasksBlock_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_cellTest_block_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_⟪0⟫_block_⟪1⟫ : Interval cellTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check cellTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_check_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem check_⟪0⟫_⟪1⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪2⟫)) ⟪3⟫ ⟪4⟫ :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount ⟪2⟫)) ⟪3⟫ ⟪5⟫ (by decide +kernel)"### args

elab "cert_checked_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : Interval test ⟪0⟫ ⟪1⟫ :=
  interval_of_check test ⟪0⟫ 64 (by decide +kernel)"### args

elab "cert_checked_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : FiniteChecks.Interval test ⟪0⟫ ⟪1⟫ :=
  FiniteChecks.interval_of_check test ⟪0⟫ ⟪2⟫ (by decide +kernel)"### args

elab "cert_faceTable_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def faceTable : Table Nat :=
  integerTable% 0 ⟪0⟫"### args

elab "cert_faceWitness_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))"### args

elab "cert_fastGenerator_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def fastGenerator⟪0⟫ (i : Nat) := fastCellTest ⟪0⟫ i"### args

elab "cert_fastGenerator_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fastGenerator⟪0⟫_block_⟪1⟫ : Interval fastGenerator⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check fastGenerator⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_kindSupport_checked_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_checked_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_code_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_code : Nat := (certNat% 0)"### args

elab "cert_kindSupport_decode_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
      (kindSupport⟪0⟫_⟪1⟫, kindSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_kindSupport_eq_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_eq : kindRows ⟪0⟫ = kindSupport⟪0⟫_suffix_000 := by
  change kindSupports ⟪0⟫ = kindSupport⟪0⟫_suffix_000
  rw [kindSupport⟪0⟫_source]
  exact congrArg Prod.fst kindSupport⟪0⟫_suffix_decode_000"### args

elab "cert_kindSupport_mask_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask kindSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_kindSupport_rest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_rest_⟪1⟫ : Nat := PackedRawNatGrowth.drop ⟪2⟫ kindSupport⟪0⟫_code"### args

elab "cert_kindSupport_source_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_source : kindSupports ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ kindSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_kindSupport_suffix_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_suffix_⟪1⟫ : List Nat := []"### args

elab "cert_kindSupport_suffix_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_suffix_⟪1⟫ : List Nat := kindSupport⟪0⟫_⟪1⟫ ++ kindSupport⟪0⟫_suffix_⟪2⟫"### args

elab "cert_kindSupport_suffix_decode_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
    (kindSupport⟪0⟫_suffix_⟪1⟫, kindSupport⟪0⟫_rest_⟪5⟫) :=
  PackedRawNatGrowth.readList_append_of_eq ⟪2⟫ ⟪4⟫ ⟪7⟫
    kindSupport⟪0⟫_rest_⟪1⟫ kindSupport⟪0⟫_rest_⟪6⟫ kindSupport⟪0⟫_rest_⟪5⟫
    kindSupport⟪0⟫_⟪1⟫ kindSupport⟪0⟫_suffix_⟪6⟫ kindSupport⟪0⟫_⟪1⟫_decode kindSupport⟪0⟫_suffix_decode_⟪6⟫"### args

elab "cert_kindSupport_suffix_decode_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ 0 kindSupport⟪0⟫_rest_⟪1⟫ =
    (kindSupport⟪0⟫_suffix_⟪1⟫, kindSupport⟪0⟫_rest_⟪1⟫) := by rfl"### args

elab "cert_kindTest_block_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ :=
  interval_of_check kindTest_0 ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_kindTest_block_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact kindTest_large_⟪0⟫"### args

elab "cert_lookup_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def lookup (i : Nat) : Nat := table.get i"### args

elab "cert_maskTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def maskTest⟪0⟫ (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode ⟪0⟫) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode ⟪0⟫)) j)"### args

elab "cert_maskTest_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem maskTest⟪0⟫_block_⟪1⟫ : Interval maskTest⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check maskTest⟪0⟫ ⟪2⟫ 16 (by decide +kernel)"### args

elab "cert_metadata_normalizers_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck ⟪0⟫ template root raw faceWitness = true := by decide +kernel"### args

elab "cert_metadata_root_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel"### args

elab "cert_metadata_symmetry_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 64 ⟪0⟫
  (FiniteChecks.interval_append (symmetry) 0 32 64
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 64
  metadata_symmetry_0032
  metadata_symmetry_0048))
  (FiniteChecks.interval_append (symmetry) 64 96 ⟪0⟫
  (FiniteChecks.interval_append (symmetry) 64 80 96
  metadata_symmetry_0064
  metadata_symmetry_0080)
  (FiniteChecks.interval_append (symmetry) 96 112 ⟪0⟫
  metadata_symmetry_0096
  metadata_symmetry_0112)))"### args

elab "cert_metadata_symmetry_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_symmetry_⟪0⟫ : FiniteChecks.Interval symmetry ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check symmetry ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_metadata_validity_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_validity_⟪0⟫ : FiniteChecks.Interval validity ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check validity ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_metadata_validity_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 64 ⟪0⟫
  (FiniteChecks.interval_append (validity) 0 32 64
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 64
  metadata_validity_0032
  metadata_validity_0048))
  (FiniteChecks.interval_append (validity) 64 96 ⟪0⟫
  (FiniteChecks.interval_append (validity) 64 80 96
  metadata_validity_0064
  metadata_validity_0080)
  (FiniteChecks.interval_append (validity) 96 112 ⟪0⟫
  metadata_validity_0096
  metadata_validity_0112)))"### args

elab "cert_placement_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check ⟪0⟫ (raw b) template root FacetUniverses.RootedSixExtra⟪1⟫.cells
    code 0 (witness b code)"### args

elab "cert_raw_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1"### args

elab "cert_ridgeSupport_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_⟪1⟫ : List Nat := [⟪2⟫,⟪3⟫,⟪4⟫,⟪5⟫,⟪6⟫,⟪7⟫,⟪8⟫]"### args

elab "cert_ridgeSupport_checked_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_checked :
    (ridgeSupport⟪0⟫_⟪1⟫.all (fun c => hasNat (rawCells c).ridgeMasks ⟪0⟫)) = true := by decide +kernel"### args

elab "cert_ridgeSupport_checked_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_checked :
    (ridgeSupport⟪0⟫_⟪1⟫.all (fun c => hasNat (rawCells c).ridgeMasks ⟪0⟫)) = true := by decide +kernel"### args

elab "cert_ridgeSupport_code_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_code : Nat := (certNat% 0)"### args

elab "cert_ridgeSupport_decode_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ ridgeSupport⟪0⟫_rest_⟪1⟫ =
      (ridgeSupport⟪0⟫_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_ridgeSupport_eq_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_eq : candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 := by
  change candidateSupports ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000
  rw [ridgeSupport⟪0⟫_source]
  exact congrArg Prod.fst ridgeSupport⟪0⟫_suffix_decode_000"### args

elab "cert_ridgeSupport_mask_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask ridgeSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_ridgeSupport_rest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_rest_⟪1⟫ : Nat := PackedRawNatGrowth.drop ⟪2⟫ ridgeSupport⟪0⟫_code"### args

elab "cert_ridgeSupport_source_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_source : candidateSupports ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ ridgeSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_ridgeSupport_suffix_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_suffix_⟪1⟫ : List Nat := ridgeSupport⟪0⟫_⟪1⟫ ++ ridgeSupport⟪0⟫_suffix_⟪2⟫"### args

elab "cert_ridgeSupport_suffix_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_suffix_⟪1⟫ : List Nat := []"### args

elab "cert_ridgeSupport_suffix_decode_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ 0 ridgeSupport⟪0⟫_rest_⟪1⟫ =
    (ridgeSupport⟪0⟫_suffix_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪1⟫) := by rfl"### args

elab "cert_ridgeSupport_suffix_decode_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ ridgeSupport⟪0⟫_rest_⟪1⟫ =
    (ridgeSupport⟪0⟫_suffix_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪5⟫) :=
  PackedRawNatGrowth.readList_append_of_eq ⟪2⟫ ⟪4⟫ ⟪7⟫
    ridgeSupport⟪0⟫_rest_⟪1⟫ ridgeSupport⟪0⟫_rest_⟪6⟫ ridgeSupport⟪0⟫_rest_⟪5⟫
    ridgeSupport⟪0⟫_⟪1⟫ ridgeSupport⟪0⟫_suffix_⟪6⟫ ridgeSupport⟪0⟫_⟪1⟫_decode ridgeSupport⟪0⟫_suffix_decode_⟪6⟫"### args

elab "cert_ridgeTestInterval_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTestInterval⟪0⟫ : Interval ridgeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := ridgeTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_ridgeTest_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeTest_⟪0⟫ (i : Nat) := ridgeTest (i+⟪0⟫)"### args

elab "cert_ridgeTest_block_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ := by
  intro i hlo hhi
  by_cases h : i = ⟪2⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪4⟫
  · subst i
    exact ridgeTest_large_⟪5⟫
  by_cases h : i = ⟪6⟫
  · subst i
    exact ridgeTest_large_⟪7⟫
  by_cases h : i = ⟪8⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪9⟫
  · subst i
    exact ridgeTest_large_⟪10⟫
  by_cases h : i = ⟪11⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪12⟫
  · subst i
    decide +kernel
  have h : i = ⟪13⟫ := by omega
  subst i
  decide +kernel"### args

elab "cert_ridgeTest_block_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check ridgeTest_⟪0⟫ ⟪2⟫ 8 (by decide +kernel)"### args

elab "cert_ridgeTest_block_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪4⟫ := by
  intro i hlo hhi
  by_cases h : i = ⟪2⟫
  · subst i
    exact ridgeTest_large_⟪3⟫
  by_cases h : i = ⟪5⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪6⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪7⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪8⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪9⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪10⟫
  · subst i
    decide +kernel
  have h : i = ⟪11⟫ := by omega
  subst i
  decide +kernel"### args

elab "cert_ridgeTest_complete_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_complete : Interval ridgeTest_⟪0⟫ 0 128 :=
  (interval_append ridgeTest_⟪0⟫ 0 64 128
  (interval_append ridgeTest_⟪0⟫ 0 32 64
  (interval_append ridgeTest_⟪0⟫ 0 16 32
  (interval_append ridgeTest_⟪0⟫ 0 8 16
  ridgeTest_⟪0⟫_block_0
  ridgeTest_⟪0⟫_block_1)
  (interval_append ridgeTest_⟪0⟫ 16 24 32
  ridgeTest_⟪0⟫_block_2
  ridgeTest_⟪0⟫_block_3))
  (interval_append ridgeTest_⟪0⟫ 32 48 64
  (interval_append ridgeTest_⟪0⟫ 32 40 48
  ridgeTest_⟪0⟫_block_4
  ridgeTest_⟪0⟫_block_5)
  (interval_append ridgeTest_⟪0⟫ 48 56 64
  ridgeTest_⟪0⟫_block_6
  ridgeTest_⟪0⟫_block_7)))
  (interval_append ridgeTest_⟪0⟫ 64 96 128
  (interval_append ridgeTest_⟪0⟫ 64 80 96
  (interval_append ridgeTest_⟪0⟫ 64 72 80
  ridgeTest_⟪0⟫_block_8
  ridgeTest_⟪0⟫_block_9)
  (interval_append ridgeTest_⟪0⟫ 80 88 96
  ridgeTest_⟪0⟫_block_10
  ridgeTest_⟪0⟫_block_11))
  (interval_append ridgeTest_⟪0⟫ 96 112 128
  (interval_append ridgeTest_⟪0⟫ 96 104 112
  ridgeTest_⟪0⟫_block_12
  ridgeTest_⟪0⟫_block_13)
  (interval_append ridgeTest_⟪0⟫ 112 120 128
  ridgeTest_⟪0⟫_block_14
  ridgeTest_⟪0⟫_block_15))))"### args

elab "cert_ridgeTest_large_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask, ridgeSupport⟪0⟫_011_mask, ridgeSupport⟪0⟫_012_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, ridgeSupport⟪0⟫_011_checked, ridgeSupport⟪0⟫_012_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, ridgeSupport⟪0⟫_suffix_014, ridgeSupport⟪0⟫_suffix_015, ridgeSupport⟪0⟫_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask, ridgeSupport⟪0⟫_011_mask, ridgeSupport⟪0⟫_012_mask, ridgeSupport⟪0⟫_013_mask, ridgeSupport⟪0⟫_014_mask, ridgeSupport⟪0⟫_015_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, ridgeSupport⟪0⟫_suffix_014, ridgeSupport⟪0⟫_suffix_015, ridgeSupport⟪0⟫_suffix_016, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, ridgeSupport⟪0⟫_011_checked, ridgeSupport⟪0⟫_012_checked, ridgeSupport⟪0⟫_013_checked, ridgeSupport⟪0⟫_014_checked, ridgeSupport⟪0⟫_015_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, Bool.and_self]"### args

elab "cert_root_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def root : Cell := FacetUniverses.RootedSixExtra⟪0⟫.cells 0"### args

elab "cert_signatureMasksBlock_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_signatureMasksBlock_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_symmetry_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixExtra⟪0⟫.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))"### args

elab "cert_test_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)"### args

elab "cert_validity_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck ⟪0⟫ (raw (Fin.ofNat blockCount i))"### args

elab "cert_wellFormedTest_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_block_⟪1⟫ : Interval wellFormedTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check wellFormedTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_witness_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin ⟪0⟫ :=
  Fin.ofNat ⟪0⟫ (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)"### args

