module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_badMasksBlock_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := 0x0"### args

elab "cert_badMasksBlock_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := 0x0"### args

elab "cert_badMasksBlock_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_badMasksBlocks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlocks : Table Nat :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf badMasksBlock0000)
 (.leaf badMasksBlock0001))
 (.branch 3
 (.leaf badMasksBlock0002)
 (.leaf badMasksBlock0003)))
 (.branch 6
 (.branch 5
 (.leaf badMasksBlock0004)
 (.leaf badMasksBlock0005))
 (.branch 7
 (.leaf badMasksBlock0006)
 (.leaf badMasksBlock0007))))"### args

elab "cert_badMasksBlocks_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasksBlocks : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf badMasksBlock0000)
 (.leaf badMasksBlock0001))
 (.branch 3
 (.leaf badMasksBlock0002)
 (.branch 4
 (.leaf badMasksBlock0003)
 (.leaf badMasksBlock0004))))
 (.branch 7
 (.branch 6
 (.leaf badMasksBlock0005)
 (.leaf badMasksBlock0006))
 (.branch 8
 (.leaf badMasksBlock0007)
 (.branch 9
 (.leaf badMasksBlock0008)
 (.leaf badMasksBlock0009)))))"### args

elab "cert_badMasks_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasks (i : Nat) := PackedRawNatGrowth.take ⟪0⟫
  (PackedRawNatGrowth.drop (⟪0⟫*(i%64)) (badMasksBlocks.get (i/64)))"### args

elab "cert_badTestInterval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTestInterval⟪0⟫ : Interval badTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := badTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [badTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_badTest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badTest_⟪0⟫ (i : Nat) := badTest (i+⟪0⟫)"### args

elab "cert_badTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badTest (i : Nat) := if badMasks i = 0 then true else
  decide (Nat.land (badMasks i) (SignatureCompatibility.cover (SignatureCompatibility.allMask ⟪0⟫)
    vertexMasks signatureIndex signatureMasks (rawCells i)) = 0)"### args

elab "cert_badTest_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_⟪0⟫_block_⟪1⟫ : Interval badTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check badTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_badTest_complete_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_complete : Interval badTest 0 ⟪0⟫ := (interval_append badTest 0 256 ⟪0⟫ badTestInterval0 badTestInterval256)"### args

elab "cert_badTest_complete_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem badTest_complete : Interval badTest 0 ⟪0⟫ := (interval_append badTest 0 256 ⟪0⟫ badTestInterval0 (interval_append badTest 256 512 ⟪0⟫ badTestInterval256 badTestInterval512))"### args

elab "cert_bad_disjoint_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem bad_disjoint (a : Fin ⟪0⟫) : Nat.land (badMasks a.val)
    (SignatureCompatibility.cover (SignatureCompatibility.allMask ⟪0⟫) vertexMasks signatureIndex signatureMasks (rawCells a.val)) = 0 := by
  have h := badTest_complete a.val (Nat.zero_le _) a.isLt
  by_cases hz : badMasks a.val = 0
  · rw [hz]; exact Nat.zero_and _
  · exact of_decide_eq_true (by simpa only [badTest, hz, ite_false] using h)"### args

elab "cert_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem block_⟪0⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪1⟫)) 0 24 :=
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount ⟪1⟫)) 0 8 24
  check_⟪0⟫_0000
  (FiniteChecks.interval_append (placement (Fin.ofNat blockCount ⟪1⟫)) 8 16 24
  check_⟪0⟫_0008
  check_⟪0⟫_0016))"### args

elab "cert_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem block_⟪0⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪1⟫)) 0 ⟪2⟫ :=
  check_⟪0⟫_0000"### args

elab "cert_cache_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cache : BatchedGrowthPruning.Cache ridgeList literalCompatible kind :=
  SignatureCompatibility.ofChecks rawCells candidateMasks badMasks kindMasks candidateRows kindRows keys
    vertexMasks signatureIndex signatureMasks
    (fun c => (cell_facts c).1)
    (fun q => (ridge_facts q).1)
    (fun c => (cell_facts c).2.1)
    (fun q => (ridge_facts q).2)
    (by
      intro j hj
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).1)
    (by
      intro j hj
      exact (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).2)
    (fun c => of_decide_eq_true (cell_facts c).2.2.2.1)
    (by
      intro c v hv
      exact of_decide_eq_true (List.all_eq_true.mp (cell_facts c).2.2.2.2.1 v (List.mem_range.mpr hv)))
    (fun c => (cell_facts c).2.2.2.2.2) bad_disjoint"### args

elab "cert_candidateMasksBlock_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_candidateMasksBlock_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlock0015 : Nat := (certNat% 15)"### args

elab "cert_candidateMasksBlocks_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasksBlocks : Table Nat :=
(.branch 8
 (.branch 4
 (.branch 2
 (.branch 1
 (.leaf candidateMasksBlock0000)
 (.leaf candidateMasksBlock0001))
 (.branch 3
 (.leaf candidateMasksBlock0002)
 (.leaf candidateMasksBlock0003)))
 (.branch 6
 (.branch 5
 (.leaf candidateMasksBlock0004)
 (.leaf candidateMasksBlock0005))
 (.branch 7
 (.leaf candidateMasksBlock0006)
 (.leaf candidateMasksBlock0007))))
 (.branch 12
 (.branch 10
 (.branch 9
 (.leaf candidateMasksBlock0008)
 (.leaf candidateMasksBlock0009))
 (.branch 11
 (.leaf candidateMasksBlock0010)
 (.leaf candidateMasksBlock0011)))
 (.branch 14
 (.branch 13
 (.leaf candidateMasksBlock0012)
 (.leaf candidateMasksBlock0013))
 (.branch 15
 (.leaf candidateMasksBlock0014)
 (.leaf candidateMasksBlock0015)))))"### args

elab "cert_candidateMasks_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasks (i : Nat) := PackedRawNatGrowth.take ⟪0⟫
  (PackedRawNatGrowth.drop (⟪0⟫*(i%64)) (candidateMasksBlocks.get (i/64)))"### args

elab "cert_candidateRows_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateRows := decodeRow candidateRowTable"### args

elab "cert_candidateSupports_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateSupports := candidateRows"### args

elab "cert_cellTestInterval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTestInterval⟪0⟫ : Interval cellTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := cellTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [cellTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_cellTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cellTest_⟪0⟫ (i : Nat) := cellTest (i+⟪0⟫)"### args

elab "cert_cellTest_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cellTest (i : Nat) := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (rawKind i = (rawCells i).kind) && (decide ((rawCells i).vertices < 1024) && ((List.range 10).all (fun v => decide ((vertexMasks v).testBit i = (rawCells i).vertices.testBit v)) && (SignatureCompatibility.faces (rawCells i)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask ⟪0⟫) signatureIndex signatureMasks (rawCells i) q).testBit i))))))"### args

elab "cert_cellTest_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cellTest (g i : Nat) : Bool :=
  let generator := Fin.ofNat generatorCount g
  let cell := Fin.ofNat cellCount i
  inverseCheckAt (forward generator) (forward generator) cell &&
    cellRelabelCheck (TenGraphEdges.vertexMap (vertexCode generator))
      (cells cell) (cells (forward generator cell))"### args

elab "cert_cellTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_⟪0⟫_block_⟪1⟫ : Interval cellTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check cellTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_cellTest_complete_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_complete : Interval cellTest 0 ⟪0⟫ := (interval_append cellTest 0 256 ⟪0⟫ cellTestInterval0 (interval_append cellTest 256 512 ⟪0⟫ cellTestInterval256 cellTestInterval512))"### args

elab "cert_cellTest_complete_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_complete : Interval cellTest 0 ⟪0⟫ := (interval_append cellTest 0 256 ⟪0⟫ cellTestInterval0 cellTestInterval256)"### args

elab "cert_cell_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cell_checked (g : Fin generatorCount) (i : Fin ⟪0⟫) :
    cellTest g.val i.val = true := by
  rw [← Papers.RationalityTen.FacetUniverses.RootedSevenPure⟪1⟫.Outside.Verified.fastCellTest_eq]
  exact Papers.RationalityTen.FacetUniverses.RootedSevenPure⟪1⟫.Outside.Verified.fast_checked g i"### args

elab "cert_cell_facts_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cell_facts (a : Fin ⟪0⟫) : (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) ∧ (decide ((rawCells a.val).vertices < 1024) = true) ∧ ((List.range 10).all (fun v => decide ((vertexMasks v).testBit a.val = (rawCells a.val).vertices.testBit v)) = true) ∧ ((SignatureCompatibility.faces (rawCells a.val)).all (fun q => (SignatureCompatibility.profileMask (SignatureCompatibility.allMask ⟪0⟫) signatureIndex signatureMasks (rawCells a.val) q).testBit a.val) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt"### args

elab "cert_cells_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cells (i : Fin cellCount) : Cell := rawCells i.val"### args

elab "cert_cells_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cells (c : Fin ⟪0⟫) := rawCells c.val"### args

elab "cert_check_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem check_⟪0⟫_⟪1⟫ : FiniteChecks.Interval (placement (Fin.ofNat blockCount ⟪2⟫)) ⟪3⟫ ⟪4⟫ :=
  FiniteChecks.interval_of_check (placement (Fin.ofNat blockCount ⟪2⟫)) ⟪3⟫ ⟪5⟫ (by decide +kernel)"### args

elab "cert_checked_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checked_⟪0⟫ : FiniteChecks.Interval test ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check test ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_decodeRow_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def decodeRow (table : Table Nat) (i : Nat) : List Nat :=
  let code := table.get i
  (PackedRawNatGrowth.readList ⟪0⟫ (PackedRawNatGrowth.take 16 code)
    (PackedRawNatGrowth.drop 16 code)).1"### args

elab "cert_dispatch_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispatch : Table (Nat → Nat) :=
(.leaf Data.Part000.lookup)"### args

elab "cert_dispatch_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispatch : Table (Nat → Nat) :=
(.branch 512
 (.leaf Data.Part000.lookup)
 (.leaf Data.Part001.lookup))"### args

elab "cert_faceTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def faceTable : Table Nat :=
  integerTable% 0 ⟪0⟫"### args

elab "cert_faceWitness_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def faceWitness (s r : Nat) : Fin blockCount :=
  Fin.ofNat blockCount (faceTable.get (s * 1024 + r))"### args

elab "cert_facts_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem facts.kindExact (c : Fin ⟪0⟫) : fastKind c.val = (cells c).kind := raw_kind_exact c"### args

elab "cert_fastCellTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def fastCellTest (g i : Nat) : Bool :=
  let gen := Fin.ofNat generatorCount g
  let cell := Fin.ofNat ⟪0⟫ i
  inverseCheckAt (forward gen) (forward gen) cell &&
    CachedCellRelabel.bitsetCellCheck (CachedCellRelabel.lookup (renameCode gen))
      (cells cell) (cells (forward gen cell))"### args

elab "cert_fastCellTest_eq_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fastCellTest_eq (g i : Nat) : fastCellTest g i = cellTest g i := by
  simp only [fastCellTest, cellTest,
    CachedCellRelabel.cached_bitsetCellCheck_eq _ _ (mask_checked _)]"### args

elab "cert_fastGenerator_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def fastGenerator⟪0⟫ (i : Nat) := fastCellTest ⟪0⟫ i"### args

elab "cert_fastGenerator_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fastGenerator⟪0⟫_block_⟪1⟫ : Interval fastGenerator⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check fastGenerator⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_fastKind_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def fastKind := rawKind"### args

elab "cert_fast_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fast_checked (g : Fin generatorCount) (i : Fin ⟪0⟫) :
    fastCellTest g.val i.val = true := by
  have hg : g.val < 2 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 := by omega
  rcases hc with h | h
  · have hg : g = (⟨0, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator0_complete i.val (Nat.zero_le _) i.isLt
  · have hg : g = (⟨1, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact fastGenerator1_complete i.val (Nat.zero_le _) i.isLt"### args

elab "cert_forward_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def forward (g : Fin generatorCount) : Fin cellCount → Fin cellCount :=
  packedCellMap (by decide) ⟪0⟫ (mapTable.get g.val)"### args

elab "cert_keys_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def keys := List.range 5"### args

elab "cert_kindMaskTable_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindMaskTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf (certNat% ⟪0⟫)))
 (.branch 3
 (.leaf (certNat% ⟪1⟫))
 (.branch 4
 (.leaf (certNat% ⟪2⟫))
 (.leaf 0x0))))"### args

elab "cert_kindMaskTable_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindMaskTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf 0x0))
 (.branch 3
 (.leaf (certNat% ⟪0⟫))
 (.branch 4
 (.leaf (certNat% ⟪1⟫))
 (.leaf 0x0))))"### args

elab "cert_kindMasks_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindMasks := kindMaskTable.get"### args

elab "cert_kindRowTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindRowTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf 0x0))
 (.branch 3
 (.leaf (certNat% ⟪0⟫))
 (.branch 4
 (.leaf (certNat% ⟪1⟫))
 (.leaf 0x0))))"### args

elab "cert_kindRowTable_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindRowTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf 0x1)
 (.leaf (certNat% ⟪0⟫)))
 (.branch 3
 (.leaf (certNat% ⟪1⟫))
 (.branch 4
 (.leaf (certNat% ⟪2⟫))
 (.leaf 0x0))))"### args

elab "cert_kindRows_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindRows := decodeRow kindRowTable"### args

elab "cert_kindSupport " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_008 : List Nat := [⟪1⟫,⟪2⟫,⟪3⟫,⟪4⟫,⟪5⟫,⟪6⟫,⟪7⟫,⟪8⟫,⟪9⟫,⟪10⟫,⟪11⟫,⟪12⟫,⟪13⟫,⟪14⟫]"### args

elab "cert_kindSupport_checked_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_checked_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_checked :
    (kindSupport⟪0⟫_⟪1⟫.all (fun c => decide ((rawCells c).kind = ⟪0⟫))) = true := by decide +kernel"### args

elab "cert_kindSupport_code " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_code : Nat := (certNat% 0)"### args

elab "cert_kindSupport_decode_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_decode :
    PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
      (kindSupport⟪0⟫_⟪1⟫, kindSupport⟪0⟫_rest_⟪4⟫) := by decide +kernel"### args

elab "cert_kindSupport_eq " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_eq : kindRows ⟪0⟫ = kindSupport⟪0⟫_suffix_000 := by
  rw [kindSupport⟪0⟫_source]
  exact congrArg Prod.fst kindSupport⟪0⟫_suffix_decode_000"### args

elab "cert_kindSupport_mask_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_⟪1⟫_mask : RawNatGrowthCheck.mask kindSupport⟪0⟫_⟪1⟫ = (certNat% ⟪2⟫) := by decide +kernel"### args

elab "cert_kindSupport_rest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_rest_⟪1⟫ : Nat := PackedRawNatGrowth.drop ⟪2⟫ kindSupport⟪0⟫_code"### args

elab "cert_kindSupport_source " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_source : kindRows ⟪0⟫ =
    (PackedRawNatGrowth.readList ⟪1⟫ ⟪2⟫ kindSupport⟪0⟫_code).1 := by rfl"### args

elab "cert_kindSupport_suffix_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_suffix_⟪1⟫ : List Nat := []"### args

elab "cert_kindSupport_suffix_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupport⟪0⟫_suffix_⟪1⟫ : List Nat := kindSupport⟪0⟫_⟪1⟫ ++ kindSupport⟪0⟫_suffix_⟪2⟫"### args

elab "cert_kindSupport_suffix_decode_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ ⟪3⟫ kindSupport⟪0⟫_rest_⟪1⟫ =
    (kindSupport⟪0⟫_suffix_⟪1⟫, kindSupport⟪0⟫_rest_⟪5⟫) :=
  PackedRawNatGrowth.readList_append_of_eq ⟪2⟫ ⟪4⟫ ⟪7⟫
    kindSupport⟪0⟫_rest_⟪1⟫ kindSupport⟪0⟫_rest_⟪6⟫ kindSupport⟪0⟫_rest_⟪5⟫
    kindSupport⟪0⟫_⟪1⟫ kindSupport⟪0⟫_suffix_⟪6⟫ kindSupport⟪0⟫_⟪1⟫_decode kindSupport⟪0⟫_suffix_decode_⟪6⟫"### args

elab "cert_kindSupport_suffix_decode_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindSupport⟪0⟫_suffix_decode_⟪1⟫ : PackedRawNatGrowth.readList ⟪2⟫ 0 kindSupport⟪0⟫_rest_⟪1⟫ =
    (kindSupport⟪0⟫_suffix_⟪1⟫, kindSupport⟪0⟫_rest_⟪1⟫) := by rfl"### args

elab "cert_kindSupports_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindSupports := kindRows"### args

elab "cert_kindTestInterval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTestInterval0 : Interval kindTest 0 5 := by
  intro i hlo hhi
  have h := kindTest_0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [kindTest_0, Nat.sub_add_cancel hlo] using h"### args

elab "cert_kindTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindTest_0 (i : Nat) := kindTest (i+0)"### args

elab "cert_kindTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindTest (i : Nat) := decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) &&
  (kindRows i).all (fun c => decide ((rawCells c).kind = i))"### args

elab "cert_kindTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ :=
  interval_of_check kindTest_0 ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_kindTest_block_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_block_⟪0⟫ : Interval kindTest_0 ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact kindTest_large_⟪0⟫"### args

elab "cert_kindTest_complete_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_0_complete : Interval kindTest_0 0 5 :=
  (interval_append kindTest_0 0 2 5
  (interval_append kindTest_0 0 1 2
  kindTest_0_block_0
  kindTest_0_block_1)
  (interval_append kindTest_0 2 3 5
  kindTest_0_block_2
  (interval_append kindTest_0 3 4 5
  kindTest_0_block_3
  kindTest_0_block_4)))"### args

elab "cert_kindTest_complete_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_complete : Interval kindTest 0 5 := kindTestInterval0"### args

elab "cert_kindTest_large " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_large_⟪0⟫ : kindTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport⟪0⟫_eq]
    simp only [kindSupport⟪0⟫_suffix_000, kindSupport⟪0⟫_suffix_001, kindSupport⟪0⟫_suffix_002, kindSupport⟪0⟫_suffix_003, kindSupport⟪0⟫_suffix_004, kindSupport⟪0⟫_suffix_005, kindSupport⟪0⟫_suffix_006, kindSupport⟪0⟫_suffix_007, kindSupport⟪0⟫_suffix_008, kindSupport⟪0⟫_suffix_009, kindSupport⟪0⟫_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport⟪0⟫_000_mask, kindSupport⟪0⟫_001_mask, kindSupport⟪0⟫_002_mask, kindSupport⟪0⟫_003_mask, kindSupport⟪0⟫_004_mask, kindSupport⟪0⟫_005_mask, kindSupport⟪0⟫_006_mask, kindSupport⟪0⟫_007_mask, kindSupport⟪0⟫_008_mask, kindSupport⟪0⟫_009_mask]
    decide +kernel
  · rw [kindSupport⟪0⟫_eq]
    simp only [kindSupport⟪0⟫_suffix_000, kindSupport⟪0⟫_suffix_001, kindSupport⟪0⟫_suffix_002, kindSupport⟪0⟫_suffix_003, kindSupport⟪0⟫_suffix_004, kindSupport⟪0⟫_suffix_005, kindSupport⟪0⟫_suffix_006, kindSupport⟪0⟫_suffix_007, kindSupport⟪0⟫_suffix_008, kindSupport⟪0⟫_suffix_009, kindSupport⟪0⟫_suffix_010, List.all_append, List.all_nil, kindSupport⟪0⟫_000_checked, kindSupport⟪0⟫_001_checked, kindSupport⟪0⟫_002_checked, kindSupport⟪0⟫_003_checked, kindSupport⟪0⟫_004_checked, kindSupport⟪0⟫_005_checked, kindSupport⟪0⟫_006_checked, kindSupport⟪0⟫_007_checked, kindSupport⟪0⟫_008_checked, kindSupport⟪0⟫_009_checked, Bool.and_self]"### args

elab "cert_kindTest_large_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_large_⟪0⟫ : kindTest ⟪0⟫ = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport⟪0⟫_eq]
    simp only [kindSupport⟪0⟫_suffix_000, kindSupport⟪0⟫_suffix_001, kindSupport⟪0⟫_suffix_002, kindSupport⟪0⟫_suffix_003, kindSupport⟪0⟫_suffix_004, kindSupport⟪0⟫_suffix_005, kindSupport⟪0⟫_suffix_006, kindSupport⟪0⟫_suffix_007, kindSupport⟪0⟫_suffix_008, kindSupport⟪0⟫_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport⟪0⟫_000_mask, kindSupport⟪0⟫_001_mask, kindSupport⟪0⟫_002_mask, kindSupport⟪0⟫_003_mask, kindSupport⟪0⟫_004_mask, kindSupport⟪0⟫_005_mask, kindSupport⟪0⟫_006_mask, kindSupport⟪0⟫_007_mask, kindSupport⟪0⟫_008_mask]
    decide +kernel
  · rw [kindSupport⟪0⟫_eq]
    simp only [kindSupport⟪0⟫_suffix_000, kindSupport⟪0⟫_suffix_001, kindSupport⟪0⟫_suffix_002, kindSupport⟪0⟫_suffix_003, kindSupport⟪0⟫_suffix_004, kindSupport⟪0⟫_suffix_005, kindSupport⟪0⟫_suffix_006, kindSupport⟪0⟫_suffix_007, kindSupport⟪0⟫_suffix_008, kindSupport⟪0⟫_suffix_009, List.all_append, List.all_nil, kindSupport⟪0⟫_000_checked, kindSupport⟪0⟫_001_checked, kindSupport⟪0⟫_002_checked, kindSupport⟪0⟫_003_checked, kindSupport⟪0⟫_004_checked, kindSupport⟪0⟫_005_checked, kindSupport⟪0⟫_006_checked, kindSupport⟪0⟫_007_checked, kindSupport⟪0⟫_008_checked, Bool.and_self]"### args

elab "cert_kind_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kind (i : Fin cellCount) := (cells i).kind"### args

elab "cert_kind_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kind (c : Fin ⟪0⟫) := (cells c).kind"### args

elab "cert_literalCompatible_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def literalCompatible (a b : Fin cellCount) :=
  Papers.RationalityTen.ConcreteGrowth.compatible (cells a) (cells b)"### args

elab "cert_literalCompatible_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def literalCompatible (a b : Fin ⟪0⟫) := ConcreteGrowth.compatible (cells a) (cells b)"### args

elab "cert_lookup_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def lookup (i : Nat) : Nat :=
  Papers.RationalityTen.PackedFacetCells.take ⟪0⟫
    (Papers.RationalityTen.PackedFacetCells.drop (⟪0⟫ * (i % 128)) (table.get (i / 128)))"### args

elab "cert_mapTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def mapTable : Table Nat :=
(.branch 1
 (.leaf ⟪0⟫)
 (.leaf ⟪1⟫))"### args

elab "cert_maskTest_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def maskTest⟪0⟫ (j : Nat) : Bool :=
  decide (CachedCellRelabel.lookup (renameCode ⟪0⟫) j =
    RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode ⟪0⟫)) j)"### args

elab "cert_maskTest_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem maskTest⟪0⟫_block_⟪1⟫ : Interval maskTest⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check maskTest⟪0⟫ ⟪2⟫ 16 (by decide +kernel)"### args

elab "cert_mask_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem mask_checked (g : Fin generatorCount) (i : Fin 1024) :
    CachedCellRelabel.lookup (renameCode g) i.val =
      RawBoundaryMatch.renameMask (TenGraphEdges.vertexMap (vertexCode g)) i.val := by
  have hg : g.val < 2 := g.isLt
  have hc : g.val = 0 ∨ g.val = 1 := by omega
  rcases hc with h | h
  · have hg : g = (⟨0, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest0_complete i.val (Nat.zero_le _) i.isLt)
  · have hg : g = (⟨1, by decide⟩ : Fin generatorCount) := Fin.ext h
    subst g
    exact of_decide_eq_true (maskTest1_complete i.val (Nat.zero_le _) i.isLt)"### args

elab "cert_metadata_normalizers_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_normalizers :
    RawFaceNormalizers.completeCheck ⟪0⟫ template root raw faceWitness = true := by decide +kernel"### args

elab "cert_metadata_root_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_root : RawFacetEmbedding.wellFormedCheck root = true := by decide +kernel"### args

elab "cert_metadata_symmetry_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_symmetry_⟪0⟫ : FiniteChecks.Interval symmetry ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check symmetry ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_metadata_symmetry_6 " args:num* : command =>
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
  (FiniteChecks.interval_append (symmetry) 112 128 ⟪0⟫
  metadata_symmetry_0112
  metadata_symmetry_0128))))"### args

elab "cert_metadata_symmetry_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 174
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 128 174
  (FiniteChecks.interval_append (symmetry) 80 96 128
  metadata_symmetry_0080
  (FiniteChecks.interval_append (symmetry) 96 112 128
  metadata_symmetry_0096
  metadata_symmetry_0112))
  (FiniteChecks.interval_append (symmetry) 128 144 174
  metadata_symmetry_0128
  (FiniteChecks.interval_append (symmetry) 144 160 174
  metadata_symmetry_0144
  metadata_symmetry_0160))))"### args

elab "cert_metadata_symmetry_8 " args:num* : command =>
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

elab "cert_metadata_symmetry_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_symmetry : FiniteChecks.Interval symmetry 0 blockCount :=
  (FiniteChecks.interval_append (symmetry) 0 80 ⟪0⟫
  (FiniteChecks.interval_append (symmetry) 0 32 80
  (FiniteChecks.interval_append (symmetry) 0 16 32
  metadata_symmetry_0000
  metadata_symmetry_0016)
  (FiniteChecks.interval_append (symmetry) 32 48 80
  metadata_symmetry_0032
  (FiniteChecks.interval_append (symmetry) 48 64 80
  metadata_symmetry_0048
  metadata_symmetry_0064)))
  (FiniteChecks.interval_append (symmetry) 80 112 ⟪0⟫
  (FiniteChecks.interval_append (symmetry) 80 96 112
  metadata_symmetry_0080
  metadata_symmetry_0096)
  (FiniteChecks.interval_append (symmetry) 112 128 ⟪0⟫
  metadata_symmetry_0112
  (FiniteChecks.interval_append (symmetry) 128 144 ⟪0⟫
  metadata_symmetry_0128
  metadata_symmetry_0144))))"### args

elab "cert_metadata_validity_10 " args:num* : command =>
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
  (FiniteChecks.interval_append (validity) 112 128 ⟪0⟫
  metadata_validity_0112
  metadata_validity_0128))))"### args

elab "cert_metadata_validity_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 174
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 128 174
  (FiniteChecks.interval_append (validity) 80 96 128
  metadata_validity_0080
  (FiniteChecks.interval_append (validity) 96 112 128
  metadata_validity_0096
  metadata_validity_0112))
  (FiniteChecks.interval_append (validity) 128 144 174
  metadata_validity_0128
  (FiniteChecks.interval_append (validity) 144 160 174
  metadata_validity_0144
  metadata_validity_0160))))"### args

elab "cert_metadata_validity_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_validity : FiniteChecks.Interval validity 0 blockCount :=
  (FiniteChecks.interval_append (validity) 0 80 ⟪0⟫
  (FiniteChecks.interval_append (validity) 0 32 80
  (FiniteChecks.interval_append (validity) 0 16 32
  metadata_validity_0000
  metadata_validity_0016)
  (FiniteChecks.interval_append (validity) 32 48 80
  metadata_validity_0032
  (FiniteChecks.interval_append (validity) 48 64 80
  metadata_validity_0048
  metadata_validity_0064)))
  (FiniteChecks.interval_append (validity) 80 112 ⟪0⟫
  (FiniteChecks.interval_append (validity) 80 96 112
  metadata_validity_0080
  metadata_validity_0096)
  (FiniteChecks.interval_append (validity) 112 128 ⟪0⟫
  metadata_validity_0112
  (FiniteChecks.interval_append (validity) 128 144 ⟪0⟫
  metadata_validity_0128
  metadata_validity_0144))))"### args

elab "cert_metadata_validity_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem metadata_validity_⟪0⟫ : FiniteChecks.Interval validity ⟪1⟫ ⟪2⟫ :=
  FiniteChecks.interval_of_check validity ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_metadata_validity_9 " args:num* : command =>
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

elab "cert_placement_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def placement (b : Fin blockCount) (code : Nat) : Bool :=
  RawKindedFacePlacement.check ⟪0⟫ (raw b) template root FacetUniverses.RootedSevenPure⟪1⟫.cells
    code 0 (witness b code)"### args

elab "cert_rawCells_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenPure⟪0⟫.rawCells"### args

elab "cert_rawCells_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawCells (i : Nat) : Cell :=
  Papers.RationalityTen.PackedFacetCells.unpack ((dispatch.get i) i)"### args

elab "cert_rawKindCode_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawKindCode : Nat := ⟪0⟫"### args

elab "cert_rawKind_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawKind (i : Nat) := PackedRawNatGrowth.take 3
  (PackedRawNatGrowth.drop (3*i) rawKindCode)"### args

elab "cert_rawMap_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawMap (g c : Nat) : Nat :=
  ((mapTable.get g >>> (⟪0⟫ * c)) % ⟪1⟫) % ⟪2⟫"### args

elab "cert_rawMap_exact_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem rawMap_exact (g : Fin generatorCount) (c : Fin cellCount) :
    rawMap g.val c.val = (forward g c).val := rfl"### args

elab "cert_raw_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def raw (i : Fin blockCount) : RawFacePlacement.Block := (records.get i.val).1"### args

elab "cert_raw_kind_exact_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem raw_kind_exact (c : Fin ⟪0⟫) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.1"### args

elab "cert_renameCodeTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def renameCodeTable : Table Nat :=
(.branch 1
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031146030589498667320720657435786943876640617635033896965876224008760669254716045618505484360510611417475693317113244219394193022105682971070419849199805181521194122771861778347860674360904551003493259609466268914802112140802300264465436082758351468504083373030676834124164682495780213699535577237315851059241084800838922155445364026793605174776615498923969614649496735348018722058196192487243910623735724470863359775349714596491429202506130480662860453138401345954923622846667820257670784995350262766293930925262961314679420913259255841326080175338145883663219025173565117717273879342072550721130914408767511662895790267567177070806880835070107453164803403956517654221581528467672390149160760716233637473551690622457008937732986412141241351717100422413538757004990784127801436831448112910522884917242759320209960034561886783184510595812861900846950287523659622407826097891042737232751435405421070551440298182578648095534765877454648846008789148608941422244798999240989422143250887421321361250440622713919721284568169679345968750190644328424171188217616002190444482894308609128219023995855596014152592844791940243540031853302824513879696100797901649256152720045576225569153128866394419163629051667838870256967010007519061451266853692170175909090495758570291293038726158930619226207444250597969704010733100037326017967858988847358235912648583681140018841611980192216793705944182229757372736255376586131033535068352362439279233470050569015898315722269653505203200921626363009966699069042727008593869087684643952573661641968533434329079974310940935055221728227459653094506741259618673571897291973266234502042650275013270633901289439544244588339581007081650397235098468052099652950655617964422632011071372421959923924990771888033290333161266283970073059282016551093661143289596941286400091463928105164728049142377301595276392189206671338018865820178273915705429814451336545903117809252212866273450408548489120134951729980532537016019253735998892133821531532164760095277863671016459608522210103254819955090643430949265338298769491610610737785720861711696321699361454823239605697746463113144576549414177367093848125498322689985305652860449603085402312893215891109052745472397891324038637548926152365026960023769347510008900831893564307685285990527026659461170788862745508434094073554805763083438724864631859987985818768190209667622603606151886783400470715399568263225608366941993467362144689430583904095830212025530145497587776043257144483604876568700026935092924997384515854941321534072055684908078774533887286672259798344258343524955275535042027409507394805925827313593461562518242369037733858273458667762855863946294742167580824887029554745403732393639504546460188465876511991658077863309149223932287975852616561217772846967545797026085294276099935141912653727616657142269508196639620678821511488701268219352389696261292565606237236830384048991402477975840910780167754675329602244500462807352869888)
 (.leaf 35249680438582795941688988118499430462336567258297231157368092862797424165690819025087024830184343190345767742441471585323948831355805519780526390854815185373806422518676728957320469458865031146030589498667320720657435786943876640617635033896965876224008760669254716045618505484360510611417475693317113244219394193022105682971070419849199805181521194122771861778347860674360904551003493471492159798365977693560546646479025542718964713745284361464244356982126907626488107970066061452013137519401013935588845305467961265247145220072294543368037087371529177491384137169726733007090447205874059034157368417435975012489809584639678566423444637272269780656971790160146024174047151729913203233321669897850452700466606927559250713256933784280915065580872203402047231272167528503202925913053875735844940907796331800714006563552686986237930878565671009834360245129043182133995172589349104307785570271449736307787247422555947763980195740648518052247437638806246987204201503043026646764243530349958188087304060068444676635882939208192031432851205894448065854247934539000548113206570945398377155531688130710685494231999373792204285144836261240020985980666050342747214621695671661050964103766725726223808441025376929828612291146655324922653674067001619855784915927204111533068260239916672023297009996535563496337134223823969861744393130674137350943748913317837702952430739992017784743378622029626536537719924809404789703043837566527728587492294490294363932781963328291360585720142743560342948562384723155796498787015242077320027892735722235229527534578097192387065900760259072304217968176474370538996611131010132069592739645335972383847845354206349221486746374592655832522148253796962239556415962412041040665244145325911720126104161911635337034468844527643242910688600191820212892555514319833145774774262198134511576730618547545257860759270433551615420730436006550170516832050187450227969901968566267665615513701949603364998372989186681022647989056998931444208579787726914161540378863374289631332505101137266975299884295510326412243747235161983238646638075599811599603809642248026605966244618136990805673984420085711595434808025800283368753816682786363780121255368833602608540909412124546482332328311318365977024541724209091408565047629100920831955385651069793623996481856335988214260846383308056328676818466540656986732289284172425322280077525299081472540070563200460404560388010764851365993882681307196636112064488421143305403059629657526175956622777906966255645102900132850175359836080229673025312953977614795411434631585276635215917133702193218407506615028969853972340940578945225269009487975852120035196798822494401340479189191889226428280791320430361516459088235587944535546485014636119591473795168390685708762196502229642133837906644647082185694972109213015811374267349875440787126083457770002997860877530005184567091171340731106470899528456290464346818554058416569620352042088088456262178609541493871229301871835520030357815462155516773013264843524684624051989113111296146895765811940274361227265439273237301529974142061374326598431564754674237442977517272949915229587246678216803681829888))"### args

elab "cert_renameCode_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def renameCode (g : Fin generatorCount) := renameCodeTable.get g.val"### args

elab "cert_ridgeList_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeList := Papers.RationalityTen.ConcreteGrowth.ridgeList cells"### args

elab "cert_ridgeList_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeList := ConcreteGrowth.ridgeList cells"### args

elab "cert_ridgeTestInterval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTestInterval⟪0⟫ : Interval ridgeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := ridgeTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [ridgeTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_ridgeTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeTest_⟪0⟫ (i : Nat) := ridgeTest (i+⟪0⟫)"### args

elab "cert_ridgeTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeTest (i : Nat) := decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) &&
  (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i)"### args

elab "cert_ridgeTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_⟪0⟫_block_⟪1⟫ : Interval ridgeTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check ridgeTest_⟪0⟫ ⟪2⟫ 8 (by decide +kernel)"### args

elab "cert_ridgeTest_complete_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_complete : Interval ridgeTest 0 1024 := (interval_append ridgeTest 0 512 1024 (interval_append ridgeTest 0 256 512 (interval_append ridgeTest 0 128 256 ridgeTestInterval0 ridgeTestInterval128) (interval_append ridgeTest 256 384 512 ridgeTestInterval256 ridgeTestInterval384)) (interval_append ridgeTest 512 768 1024 (interval_append ridgeTest 512 640 768 ridgeTestInterval512 ridgeTestInterval640) (interval_append ridgeTest 768 896 1024 ridgeTestInterval768 ridgeTestInterval896)))"### args

elab "cert_ridgeTest_complete_5 " args:num* : command =>
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

elab "cert_ridge_facts_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridge_facts (q : Fin 1024) :
    candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val) ∧
    (candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true := by
  obtain ⟨hm, hs⟩ := Bool.and_eq_true_iff.mp (ridgeTest_complete q.val (Nat.zero_le _) q.isLt)
  exact ⟨of_decide_eq_true hm, hs⟩"### args

elab "cert_root_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def root : Cell := FacetUniverses.RootedSevenPure⟪0⟫.cells 0"### args

elab "cert_signatureIndex_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureIndex (q signature : Nat) : Nat := (signatureIndexTable.get q).get signature"### args

elab "cert_signatureMasksBlock_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasksBlock0003 : Nat := (certNat% 3)"### args

elab "cert_signatureMasksBlock_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasksBlock⟪0⟫ : Nat := (certNat% ⟪1⟫)"### args

elab "cert_signatureMasksBlocks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasksBlocks : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf signatureMasksBlock0000)
 (.leaf signatureMasksBlock0001))
 (.branch 3
 (.leaf signatureMasksBlock0002)
 (.leaf signatureMasksBlock0003)))"### args

elab "cert_signatureMasks_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def signatureMasks (i : Nat) := PackedRawNatGrowth.take ⟪0⟫
  (PackedRawNatGrowth.drop (⟪0⟫*(i%64)) (signatureMasksBlocks.get (i/64)))"### args

elab "cert_symmetry_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def symmetry (i : Nat) : Bool :=
  RawOutsidePlacement.blockCheck FacetUniverses.RootedSevenPure⟪0⟫.Outside.vertexCode root.vertices
    (raw (Fin.ofNat blockCount i))"### args

elab "cert_table_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def table : Table Nat :=
(.leaf ⟪0⟫)"### args

elab "cert_table_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def table : Table Nat :=
(.branch 5
 (.leaf ⟪0⟫)
 (.leaf ⟪1⟫))"### args

elab "cert_template_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def template : Cell := ⟨1, 15, [3, 5, 6, 9, 10, 12], [7, 11, 13, 14]⟩"### args

elab "cert_template_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def template : Cell := ⟨2, 31, [3, 5, 6, 9, 10, 12, 17, 18, 24], [7, 13, 14, 19, 25, 26]⟩"### args

elab "cert_template_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def template : Cell := ⟨3, 31, [3, 5, 6, 10, 12, 17, 20, 24], [7, 14, 21, 27, 28]⟩"### args

elab "cert_test_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def test (i : Nat) : Bool :=
  let b := Fin.ofNat blockCount i
  FiniteChecks.checkRange (placement b)
    0 (RawFacePlacement.count (raw b).shared (raw b).shared)"### args

elab "cert_validity_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def validity (i : Nat) : Bool :=
  RawFaceNormalizers.blockValidCheck ⟪0⟫ (raw (Fin.ofNat blockCount i))"### args

elab "cert_vertexCode_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def vertexCode (g : Fin generatorCount) : Nat := vertexTable.get g.val"### args

elab "cert_vertexMaskTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def vertexMaskTable : Table Nat :=
(.branch 5
 (.branch 2
 (.branch 1
 (.leaf ⟪0⟫)
 (.leaf ⟪1⟫))
 (.branch 3
 (.leaf ⟪2⟫)
 (.branch 4
 (.leaf ⟪3⟫)
 (.leaf ⟪4⟫))))
 (.branch 7
 (.branch 6
 (.leaf ⟪5⟫)
 (.leaf ⟪6⟫))
 (.branch 8
 (.leaf ⟪7⟫)
 (.branch 9
 (.leaf ⟪8⟫)
 (.leaf ⟪9⟫)))))"### args

elab "cert_vertexMasks_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def vertexMasks := vertexMaskTable.get"### args

elab "cert_vertexTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def vertexTable : Table Nat :=
(.branch 1
 (.leaf 650793726480)
 (.leaf 590395748880))"### args

elab "cert_vertex_checks_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem vertex_checks (g : Fin generatorCount) :
    TenGraphEdges.permutationCheck (vertexCode g) (vertexCode g) = true := by
  have h : ∀ g : Fin generatorCount,
      TenGraphEdges.permutationCheck (vertexCode g) (vertexCode g) = true := by decide +kernel
  exact h g"### args

elab "cert_wellFormedTestInterval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTestInterval⟪0⟫ : Interval wellFormedTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := wellFormedTest_⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [wellFormedTest_⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_wellFormedTest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def wellFormedTest (i : Nat) : Bool := RawFacetEmbedding.wellFormedCheck (rawCells i)"### args

elab "cert_wellFormedTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def wellFormedTest_⟪0⟫ (i : Nat) := wellFormedTest (i+⟪0⟫)"### args

elab "cert_wellFormedTest_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_block_⟪1⟫ : Interval wellFormedTest_⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check wellFormedTest_⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_wellFormedTest_complete_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_512_complete : Interval wellFormedTest_512 0 74 :=
  (interval_append wellFormedTest_512 0 32 74
  (interval_append wellFormedTest_512 0 16 32
  wellFormedTest_512_block_0
  wellFormedTest_512_block_1)
  (interval_append wellFormedTest_512 32 48 74
  wellFormedTest_512_block_2
  (interval_append wellFormedTest_512 48 64 74
  wellFormedTest_512_block_3
  wellFormedTest_512_block_4)))"### args

elab "cert_wellFormedTest_complete_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_⟪0⟫_complete : Interval wellFormedTest_⟪0⟫ 0 ⟪1⟫ :=
  (interval_append wellFormedTest_⟪0⟫ 0 128 ⟪1⟫
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
  (interval_append wellFormedTest_⟪0⟫ 128 192 ⟪1⟫
  (interval_append wellFormedTest_⟪0⟫ 128 160 192
  (interval_append wellFormedTest_⟪0⟫ 128 144 160
  wellFormedTest_⟪0⟫_block_8
  wellFormedTest_⟪0⟫_block_9)
  (interval_append wellFormedTest_⟪0⟫ 160 176 192
  wellFormedTest_⟪0⟫_block_10
  wellFormedTest_⟪0⟫_block_11))
  (interval_append wellFormedTest_⟪0⟫ 192 224 ⟪1⟫
  (interval_append wellFormedTest_⟪0⟫ 192 208 224
  wellFormedTest_⟪0⟫_block_12
  wellFormedTest_⟪0⟫_block_13)
  (interval_append wellFormedTest_⟪0⟫ 224 240 ⟪1⟫
  wellFormedTest_⟪0⟫_block_14
  wellFormedTest_⟪0⟫_block_15))))"### args

elab "cert_wellFormedTest_complete_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_complete : Interval wellFormedTest 0 ⟪0⟫ := (interval_append wellFormedTest 0 256 ⟪0⟫ wellFormedTestInterval0 (interval_append wellFormedTest 256 512 ⟪0⟫ wellFormedTestInterval256 wellFormedTestInterval512))"### args

elab "cert_wellFormedTest_complete_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem wellFormedTest_complete : Interval wellFormedTest 0 ⟪0⟫ := (interval_append wellFormedTest 0 256 ⟪0⟫ wellFormedTestInterval0 wellFormedTestInterval256)"### args

elab "cert_well_formed_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem well_formed (c : Fin ⟪0⟫) : RawFacetEmbedding.wellFormedCheck (cells c) = true :=
  wellFormedTest_complete c.val (Nat.zero_le _) c.isLt"### args

elab "cert_witness_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def witness (i : Fin blockCount) (code : Nat) : Fin ⟪0⟫ :=
  Fin.ofNat ⟪0⟫ (Nat.land (Nat.shiftRight (records.get i.val).2 (16 * code)) 65535)"### args

