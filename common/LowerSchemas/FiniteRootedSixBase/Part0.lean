module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_badMasksBlock_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_badMasksBlock_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_badMasksBlock_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_badTestInterval_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTestInterval⟪0⟫ : Interval badTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := badTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [badTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_badTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badTest_⟪0⟫ (i : Nat) := badTest (i+⟪0⟫)"### args

elab "cert_badTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_⟪0⟫_block_⟪1⟫ : Interval badTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check badTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem block_⟪0⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪1⟫)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount ⟪1⟫)) 0 8 24
  check_⟪0⟫_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount ⟪1⟫)) 8 16 24
  check_⟪0⟫_0008
  check_⟪0⟫_0016))"### args

elab "cert_block_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem block_⟪0⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪1⟫)) 0 ⟪2⟫ :=
  check_⟪0⟫_0000"### args

elab "cert_candidateMasksBlock_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_candidateMasksBlock_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_candidateMasksBlock_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_cellTestInterval_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTestInterval⟪0⟫ : Interval cellTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := cellTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [cellTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_cellTest_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cellTest_⟪0⟫ (i : Nat) := cellTest (i+⟪0⟫)"### args

elab "cert_cellTest_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_⟪0⟫_block_⟪1⟫ : Interval cellTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check cellTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_check_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem check_⟪0⟫_⟪1⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪2⟫)) ⟪3⟫ ⟪4⟫ :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount ⟪2⟫)) ⟪3⟫ ⟪5⟫ (by decide +kernel)"### args

elab "cert_checked_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : FiniteChecks.Interval test ⟪0⟫ ⟪1⟫ :=
  FiniteChecks.interval_of_check test ⟪0⟫ ⟪2⟫ (by decide +kernel)"### args

elab "cert_checked_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : Interval test ⟪0⟫ ⟪1⟫ :=
  interval_of_check test ⟪0⟫ 64 (by decide +kernel)"### args

elab "cert_faceTable_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def faceTable : Table Nat :=
  integerTable% 0 ⟪0⟫"### args

elab "cert_faceWitness_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))"### args

elab "cert_fastGenerator_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def fastGenerator⟪0⟫ (i : Nat) := fastCellTest ⟪0⟫ i"### args

elab "cert_fastGenerator_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fastGenerator⟪0⟫_block_⟪1⟫ : Interval fastGenerator⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check fastGenerator⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_kindSupport_checked_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_checked_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_code_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_code : Nat := (certNat% 0)"### args

elab "cert_kindSupport_decode_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
      (kindSupport⟪0⟫_⟪1⟫, kindSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_kindSupport_eq_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_eq : kindRows ⟪0⟫ = kindSupport⟪0⟫_suffix_000 := by
  rw [kindSupport⟪0⟫_source]
  exact congrArg Prod.fst kindSupport⟪0⟫_suffix_decode_000"### args

elab "cert_kindSupport_mask_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask kindSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_kindSupport_rest_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_rest_⟪1⟫ : Nat := PackedRawNatGrowth.drop ⟪2⟫ kindSupport⟪0⟫_code"### args

elab "cert_kindSupport_source_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_source : kindRows ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ kindSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_kindSupport_source_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_source : kindSupports ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ kindSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_kindSupport_suffix_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_suffix_⟪1⟫ : List Nat := []"### args

elab "cert_kindSupport_suffix_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_suffix_⟪1⟫ : List Nat := kindSupport⟪0⟫_⟪1⟫ ++ kindSupport⟪0⟫_suffix_⟪2⟫"### args

elab "cert_kindSupport_suffix_decode_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
    (kindSupport⟪0⟫_suffix_⟪1⟫, kindSupport⟪0⟫_rest_⟪5⟫) :=
  PackedRawNatGrowth.readList_append_of_eq ⟪2⟫ ⟪4⟫ ⟪7⟫
    kindSupport⟪0⟫_rest_⟪1⟫ kindSupport⟪0⟫_rest_⟪6⟫ kindSupport⟪0⟫_rest_⟪5⟫
    kindSupport⟪0⟫_⟪1⟫ kindSupport⟪0⟫_suffix_⟪6⟫ kindSupport⟪0⟫_⟪1⟫_decode kindSupport⟪0⟫_suffix_decode_⟪6⟫"### args

elab "cert_kindSupport_suffix_decode_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ 0 kindSupport⟪0⟫_rest_⟪1⟫ =
    (kindSupport⟪0⟫_suffix_⟪1⟫, kindSupport⟪0⟫_rest_⟪1⟫) := by rfl"### args

elab "cert_kindTest_block_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ :=
  interval_of_check kindTest_0 ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_kindTest_block_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact kindTest_large_⟪0⟫"### args

elab "cert_lookup_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def lookup (i : Nat) : Nat := table.get i"### args

elab "cert_maskTest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def maskTest⟪0⟫ (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode ⟪0⟫) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode ⟪0⟫)) j)"### args

elab "cert_maskTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem maskTest⟪0⟫_block_⟪1⟫ : Interval maskTest⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check maskTest⟪0⟫ ⟪2⟫ 16 (by decide +kernel)"### args

elab "cert_metadata_normalizers_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck ⟪0⟫ template root raw faceWitness = true := by decide +kernel"### args

elab "cert_metadata_root_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel"### args

elab "cert_metadata_symmetry_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_symmetry_⟪0⟫ : FiniteChecks.Interval symmetry ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check symmetry ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_metadata_validity_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_validity_⟪0⟫ : FiniteChecks.Interval validity ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check validity ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_placement_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check ⟪0⟫ (raw b) template root FacetUniverses.RootedSixBase⟪1⟫.cells
    code 0 (witness b code)"### args

elab "cert_raw_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1"### args

elab "cert_ridgeSupport " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_⟪1⟫ : List Nat := [⟪2⟫,⟪3⟫,⟪4⟫,⟪5⟫,⟪6⟫,⟪7⟫,⟪8⟫,⟪9⟫,⟪10⟫,⟪11⟫,⟪12⟫,⟪13⟫,⟪14⟫,⟪15⟫,⟪16⟫]"### args

elab "cert_ridgeSupport_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_009 : List Nat := [⟪1⟫,⟪2⟫,⟪3⟫,⟪4⟫,⟪5⟫,⟪6⟫,⟪7⟫,⟪8⟫,⟪9⟫,⟪10⟫,⟪11⟫,⟪12⟫,⟪13⟫,⟪14⟫,⟪15⟫,⟪16⟫,⟪17⟫]"### args

elab "cert_ridgeSupport_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_020 : List Nat := [⟪1⟫,⟪2⟫,⟪3⟫,⟪4⟫,⟪5⟫,⟪6⟫,⟪7⟫,⟪8⟫,⟪9⟫,⟪10⟫,⟪11⟫,⟪12⟫,⟪13⟫]"### args

elab "cert_ridgeSupport_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_⟪1⟫ : List Nat := [⟪2⟫,⟪3⟫,⟪4⟫]"### args

elab "cert_ridgeSupport_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_⟪1⟫ : List Nat := [⟪2⟫,⟪3⟫,⟪4⟫,⟪5⟫,⟪6⟫]"### args

elab "cert_ridgeSupport_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_059 : List Nat := [⟪1⟫]"### args

elab "cert_ridgeSupport_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_checked :
    (ridgeSupport⟪0⟫_⟪1⟫.all (fun c => hasNat (rawCells c).ridgeMasks ⟪0⟫)) = true := by decide +kernel"### args

elab "cert_ridgeSupport_checked_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_checked :
    (ridgeSupport⟪0⟫_⟪1⟫.all (fun c => hasNat (rawCells c).ridgeMasks ⟪0⟫)) = true := by decide +kernel"### args

elab "cert_ridgeSupport_code " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_code : Nat := ((certNat% 0))"### args

elab "cert_ridgeSupport_code_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_code : Nat := (certNat% 0)"### args

elab "cert_ridgeSupport_decode_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ ridgeSupport⟪0⟫_rest_⟪1⟫ =
      (ridgeSupport⟪0⟫_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_ridgeSupport_eq " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_eq : candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 := by
  change candidateSupports ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000
  rw [ridgeSupport⟪0⟫_source]
  exact congrArg Prod.fst ridgeSupport⟪0⟫_suffix_decode_000"### args

elab "cert_ridgeSupport_eq_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_eq : candidateSupports ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 := by
  rw [ridgeSupport⟪0⟫_source]
  exact congrArg Prod.fst ridgeSupport⟪0⟫_suffix_decode_000"### args

elab "cert_ridgeSupport_eq_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_eq : candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 := by
  rw [ridgeSupport⟪0⟫_source]
  exact congrArg Prod.fst ridgeSupport⟪0⟫_suffix_decode_000"### args

elab "cert_ridgeSupport_mask_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask ridgeSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_ridgeSupport_rest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_rest_⟪1⟫ : Nat := PackedRawNatGrowth.drop ⟪2⟫ ridgeSupport⟪0⟫_code"### args

elab "cert_ridgeSupport_source " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_source : candidateSupports ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ ridgeSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_ridgeSupport_source_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_source : candidateRows ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ ridgeSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_ridgeSupport_suffix " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_suffix_⟪1⟫ : List Nat := ridgeSupport⟪0⟫_⟪1⟫ ++ ridgeSupport⟪0⟫_suffix_⟪2⟫"### args

elab "cert_ridgeSupport_suffix_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeSupport⟪0⟫_suffix_⟪1⟫ : List Nat := []"### args

elab "cert_ridgeSupport_suffix_decode " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ 0 ridgeSupport⟪0⟫_rest_⟪1⟫ =
    (ridgeSupport⟪0⟫_suffix_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪1⟫) := by rfl"### args

elab "cert_ridgeSupport_suffix_decode_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ ridgeSupport⟪0⟫_rest_⟪1⟫ =
    (ridgeSupport⟪0⟫_suffix_⟪1⟫, ridgeSupport⟪0⟫_rest_⟪5⟫) :=
  PackedRawNatGrowth.readList_append_of_eq ⟪2⟫ ⟪4⟫ ⟪7⟫
    ridgeSupport⟪0⟫_rest_⟪1⟫ ridgeSupport⟪0⟫_rest_⟪6⟫ ridgeSupport⟪0⟫_rest_⟪5⟫
    ridgeSupport⟪0⟫_⟪1⟫ ridgeSupport⟪0⟫_suffix_⟪6⟫ ridgeSupport⟪0⟫_⟪1⟫_decode ridgeSupport⟪0⟫_suffix_decode_⟪6⟫"### args

elab "cert_ridgeTestInterval_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTestInterval⟪0⟫ : Interval ridgeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := ridgeTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_ridgeTest_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeTest_⟪0⟫ (i : Nat) := ridgeTest (i+⟪0⟫)"### args

elab "cert_ridgeTest_block_10 " args:num* : command =>
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

elab "cert_ridgeTest_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ := by
  intro i hlo hhi
  by_cases h : i = ⟪2⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪4⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪5⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪6⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪7⟫
  · subst i
    exact ridgeTest_large_⟪8⟫
  by_cases h : i = ⟪9⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪10⟫
  · subst i
    decide +kernel
  have h : i = ⟪11⟫ := by omega
  subst i
  decide +kernel"### args

elab "cert_ridgeTest_block_6 " args:num* : command =>
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

elab "cert_ridgeTest_block_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ := by
  intro i hlo hhi
  by_cases h : i = ⟪2⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪4⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪5⟫
  · subst i
    decide +kernel
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
    exact ridgeTest_large_⟪12⟫
  have h : i = ⟪13⟫ := by omega
  subst i
  decide +kernel"### args

elab "cert_ridgeTest_block_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ := by
  intro i hlo hhi
  by_cases h : i = ⟪2⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪4⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪5⟫
  · subst i
    exact ridgeTest_large_⟪6⟫
  by_cases h : i = ⟪7⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪8⟫
  · subst i
    exact ridgeTest_large_⟪9⟫
  by_cases h : i = ⟪10⟫
  · subst i
    decide +kernel
  by_cases h : i = ⟪11⟫
  · subst i
    decide +kernel
  have h : i = ⟪12⟫ := by omega
  subst i
  decide +kernel"### args

elab "cert_ridgeTest_block_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check ridgeTest_⟪0⟫ ⟪2⟫ 8 (by decide +kernel)"### args

elab "cert_ridgeTest_complete_6 " args:num* : command =>
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

elab "cert_ridgeTest_large " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, ridgeSupport⟪0⟫_suffix_014, ridgeSupport⟪0⟫_suffix_015, ridgeSupport⟪0⟫_suffix_016, ridgeSupport⟪0⟫_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask, ridgeSupport⟪0⟫_011_mask, ridgeSupport⟪0⟫_012_mask, ridgeSupport⟪0⟫_013_mask, ridgeSupport⟪0⟫_014_mask, ridgeSupport⟪0⟫_015_mask, ridgeSupport⟪0⟫_016_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, ridgeSupport⟪0⟫_suffix_014, ridgeSupport⟪0⟫_suffix_015, ridgeSupport⟪0⟫_suffix_016, ridgeSupport⟪0⟫_suffix_017, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, ridgeSupport⟪0⟫_011_checked, ridgeSupport⟪0⟫_012_checked, ridgeSupport⟪0⟫_013_checked, ridgeSupport⟪0⟫_014_checked, ridgeSupport⟪0⟫_015_checked, ridgeSupport⟪0⟫_016_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 from ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask, ridgeSupport⟪0⟫_011_mask]
    decide +kernel
  · rw [show candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 from ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, ridgeSupport⟪0⟫_011_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, ridgeSupport⟪0⟫_suffix_014, ridgeSupport⟪0⟫_suffix_015, ridgeSupport⟪0⟫_suffix_016, ridgeSupport⟪0⟫_suffix_017, ridgeSupport⟪0⟫_suffix_018, ridgeSupport⟪0⟫_suffix_019, ridgeSupport⟪0⟫_suffix_020, ridgeSupport⟪0⟫_suffix_021, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask, ridgeSupport⟪0⟫_011_mask, ridgeSupport⟪0⟫_012_mask, ridgeSupport⟪0⟫_013_mask, ridgeSupport⟪0⟫_014_mask, ridgeSupport⟪0⟫_015_mask, ridgeSupport⟪0⟫_016_mask, ridgeSupport⟪0⟫_017_mask, ridgeSupport⟪0⟫_018_mask, ridgeSupport⟪0⟫_019_mask, ridgeSupport⟪0⟫_020_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, ridgeSupport⟪0⟫_suffix_013, ridgeSupport⟪0⟫_suffix_014, ridgeSupport⟪0⟫_suffix_015, ridgeSupport⟪0⟫_suffix_016, ridgeSupport⟪0⟫_suffix_017, ridgeSupport⟪0⟫_suffix_018, ridgeSupport⟪0⟫_suffix_019, ridgeSupport⟪0⟫_suffix_020, ridgeSupport⟪0⟫_suffix_021, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, ridgeSupport⟪0⟫_011_checked, ridgeSupport⟪0⟫_012_checked, ridgeSupport⟪0⟫_013_checked, ridgeSupport⟪0⟫_014_checked, ridgeSupport⟪0⟫_015_checked, ridgeSupport⟪0⟫_016_checked, ridgeSupport⟪0⟫_017_checked, ridgeSupport⟪0⟫_018_checked, ridgeSupport⟪0⟫_019_checked, ridgeSupport⟪0⟫_020_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_4 " args:num* : command =>
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

elab "cert_ridgeTest_large_5 " args:num* : command =>
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

elab "cert_ridgeTest_large_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 from ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask]
    decide +kernel
  · rw [show candidateRows ⟪0⟫ = ridgeSupport⟪0⟫_suffix_000 from ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_large_⟪0⟫ : ridgeTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport⟪0⟫_000_mask, ridgeSupport⟪0⟫_001_mask, ridgeSupport⟪0⟫_002_mask, ridgeSupport⟪0⟫_003_mask, ridgeSupport⟪0⟫_004_mask, ridgeSupport⟪0⟫_005_mask, ridgeSupport⟪0⟫_006_mask, ridgeSupport⟪0⟫_007_mask, ridgeSupport⟪0⟫_008_mask, ridgeSupport⟪0⟫_009_mask, ridgeSupport⟪0⟫_010_mask, ridgeSupport⟪0⟫_011_mask]
    decide +kernel
  · rw [ridgeSupport⟪0⟫_eq]
    simp only [ridgeSupport⟪0⟫_suffix_000, ridgeSupport⟪0⟫_suffix_001, ridgeSupport⟪0⟫_suffix_002, ridgeSupport⟪0⟫_suffix_003, ridgeSupport⟪0⟫_suffix_004, ridgeSupport⟪0⟫_suffix_005, ridgeSupport⟪0⟫_suffix_006, ridgeSupport⟪0⟫_suffix_007, ridgeSupport⟪0⟫_suffix_008, ridgeSupport⟪0⟫_suffix_009, ridgeSupport⟪0⟫_suffix_010, ridgeSupport⟪0⟫_suffix_011, ridgeSupport⟪0⟫_suffix_012, List.all_append, List.all_nil, ridgeSupport⟪0⟫_000_checked, ridgeSupport⟪0⟫_001_checked, ridgeSupport⟪0⟫_002_checked, ridgeSupport⟪0⟫_003_checked, ridgeSupport⟪0⟫_004_checked, ridgeSupport⟪0⟫_005_checked, ridgeSupport⟪0⟫_006_checked, ridgeSupport⟪0⟫_007_checked, ridgeSupport⟪0⟫_008_checked, ridgeSupport⟪0⟫_009_checked, ridgeSupport⟪0⟫_010_checked, ridgeSupport⟪0⟫_011_checked, Bool.and_self]"### args

elab "cert_ridgeTest_large_8 " args:num* : command =>
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

elab "cert_root_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def root : Cell := FacetUniverses.RootedSixBase⟪0⟫.cells 0"### args

elab "cert_signatureMasksBlock_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasksBlock⟪0⟫ : Nat := ((certNat% ⟪1⟫))"### args

elab "cert_symmetry_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSixBase⟪0⟫.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))"### args

elab "cert_test_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)"### args

elab "cert_validity_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck ⟪0⟫ (raw (Fin.ofNat blockCount i))"### args

elab "cert_wellFormedTestInterval_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTestInterval⟪0⟫ : Interval wellFormedTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := wellFormedTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_wellFormedTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def wellFormedTest_⟪0⟫ (i : Nat) := wellFormedTest (i+⟪0⟫)"### args

elab "cert_wellFormedTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_block_⟪1⟫ : Interval wellFormedTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check wellFormedTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_wellFormedTest_complete_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_complete : Interval wellFormedTest_⟪0⟫ 0 256 :=
  (interval_append wellFormedTest_⟪0⟫ 0 128 256
  (interval_append wellFormedTest_⟪0⟫ 0 64 128
  (interval_append wellFormedTest_⟪0⟫ 0 32 64
  (interval_append wellFormedTest_⟪0⟫ 0 16 32
  wellFormedTest_⟪0⟫_block_0
  wellFormedTest_⟪0⟫_block_1)
  (interval_append wellFormedTest_⟪0⟫ 32 48 64
  wellFormedTest_⟪0⟫_block_2
  wellFormedTest_⟪0⟫_block_3))
  (interval_append wellFormedTest_⟪0⟫ 64 96 128
  (interval_append wellFormedTest_⟪0⟫ 64 80 96
  wellFormedTest_⟪0⟫_block_4
  wellFormedTest_⟪0⟫_block_5)
  (interval_append wellFormedTest_⟪0⟫ 96 112 128
  wellFormedTest_⟪0⟫_block_6
  wellFormedTest_⟪0⟫_block_7)))
  (interval_append wellFormedTest_⟪0⟫ 128 192 256
  (interval_append wellFormedTest_⟪0⟫ 128 160 192
  (interval_append wellFormedTest_⟪0⟫ 128 144 160
  wellFormedTest_⟪0⟫_block_8
  wellFormedTest_⟪0⟫_block_9)
  (interval_append wellFormedTest_⟪0⟫ 160 176 192
  wellFormedTest_⟪0⟫_block_10
  wellFormedTest_⟪0⟫_block_11))
  (interval_append wellFormedTest_⟪0⟫ 192 224 256
  (interval_append wellFormedTest_⟪0⟫ 192 208 224
  wellFormedTest_⟪0⟫_block_12
  wellFormedTest_⟪0⟫_block_13)
  (interval_append wellFormedTest_⟪0⟫ 224 240 256
  wellFormedTest_⟪0⟫_block_14
  wellFormedTest_⟪0⟫_block_15))))"### args

elab "cert_witness_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin ⟪0⟫ :=
  Fin.ofNat ⟪0⟫ (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)"### args

