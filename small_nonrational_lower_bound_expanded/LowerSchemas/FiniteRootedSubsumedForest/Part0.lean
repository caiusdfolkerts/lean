module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_blocks_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 nodeBlocks001)"### args

elab "cert_blocks_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 50
 nodeBlocks000
 (.branch 100
 nodeBlocks001
 nodeBlocks002))"### args

elab "cert_blocks_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))"### args

elab "cert_blocks_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨((certNat% 8)),(certNat% 9)⟩))))"### args

elab "cert_blocks_14 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.leaf ⟨(certNat% 6),(certNat% 7)⟩)))"### args

elab "cert_blocks_15 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)))"### args

elab "cert_blocks_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 2
 (.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))
 (.branch 3
 (.leaf ⟨((certNat% 4)),(certNat% 5)⟩)
 (.branch 4
 (.leaf ⟨((certNat% 6)),(certNat% 7)⟩)
 (.leaf ⟨(certNat% 8),(certNat% 9)⟩))))"### args

elab "cert_blocks_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨((certNat% 2)),(certNat% 3)⟩))"### args

elab "cert_blocks_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨((certNat% 0)),(certNat% 1)⟩)"### args

elab "cert_blocks_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 1
 (.leaf ⟨((certNat% 0)),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))"### args

elab "cert_blocks_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨⟪0⟫,⟪1⟫⟩)"### args

elab "cert_blocks_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.leaf ⟨(certNat% 0),(certNat% 1)⟩)"### args

elab "cert_boundary_classification_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification
    (renamings : Fin ⟪0⟫ → Renaming (fun c => has (FacetUniverses.RootedSixExtra⟪1⟫.ridgeList c))
      FacetUniverses.RootedSixExtra⟪1⟫.literalCompatible FacetUniverses.RootedSixExtra⟪1⟫.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixExtra⟪1⟫.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixExtra⟪1⟫.ridgeList c))
      FacetUniverses.RootedSixExtra⟪1⟫.literalCompatible FacetUniverses.RootedSixExtra⟪1⟫.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin ⟪0⟫)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.badMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixExtra⟪1⟫.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixExtra⟪1⟫.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
  · intro j
    exact (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  · intro j
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).2).1
  · intro j
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).2).2
  · intro i
    exact (nodeTest_sound i.val (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).1
  · intro i
    exact (nodeTest_sound i.val (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).2
  · intro c hc
    change has (nodes root).cells c = true at hc
    rw [hrootCells] at hc
    have heq : c = 0 := List.eq_of_mem_singleton ((has_true [0] c).mp hc)
    subst c
    exact (has_true B 0).mpr hroot
  · refine ⟨0, ?_⟩
    change has (nodes root).cells 0 = true
    rw [hrootCells]
    rfl"### args

elab "cert_boundary_classification_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification
    (renamings : Fin ⟪0⟫ → Renaming (fun c => has (FacetUniverses.RootedSixBase⟪1⟫.ridgeList c))
      FacetUniverses.RootedSixBase⟪1⟫.literalCompatible FacetUniverses.RootedSixBase⟪1⟫.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixBase⟪1⟫.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixBase⟪1⟫.ridgeList c))
      FacetUniverses.RootedSixBase⟪1⟫.literalCompatible FacetUniverses.RootedSixBase⟪1⟫.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin ⟪0⟫)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.badMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixBase⟪1⟫.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixBase⟪1⟫.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
  · intro j
    exact (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1
  · intro j
    exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).2).1
  · intro j
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).2).2
  · intro i
    exact (nodeTest_sound i.val (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).1
  · intro i
    exact (nodeTest_sound i.val (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).2
  · intro c hc
    change has (nodes root).cells c = true at hc
    rw [hrootCells] at hc
    have heq : c = 0 := List.eq_of_mem_singleton ((has_true [0] c).mp hc)
    subst c
    exact (has_true B 0).mpr hroot
  · refine ⟨0, ?_⟩
    change has (nodes root).cells 0 = true
    rw [hrootCells]
    rfl"### args

elab "cert_codes_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload"### args

elab "cert_counterTable_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf (certNat% ⟪0⟫))
 (.leaf (certNat% ⟪1⟫)))
 (.branch 3
 (.leaf (certNat% ⟪2⟫))
 (.leaf (certNat% ⟪3⟫))))"### args

elab "cert_counterTable_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 nodeCounters001)"### args

elab "cert_counterTable_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.leaf ⟪0⟫)"### args

elab "cert_counterTable_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 1
 (.leaf (certNat% 6))
 (.branch 2
 (.leaf (certNat% 7))
 (.leaf (certNat% 8))))"### args

elab "cert_counterTable_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 50
 nodeCounters000
 (.branch 100
 nodeCounters001
 nodeCounters002))"### args

elab "cert_counterTable_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf (certNat% 10))
 (.leaf (certNat% 11)))
 (.branch 3
 (.leaf (certNat% 12))
 (.branch 4
 (.leaf (certNat% 13))
 (.leaf (certNat% 14)))))"### args

elab "cert_counterTable_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 4
 (.branch 2
 (.branch 1
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))
 (.branch 3
 (.leaf (certNat% 18))
 (.leaf (certNat% 19))))
 (.branch 6
 (.branch 5
 (.leaf (certNat% 20))
 (.leaf (certNat% 21)))
 (.branch 7
 (.leaf (certNat% 22))
 (.leaf (certNat% 23)))))"### args

elab "cert_counterTable_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.leaf (certNat% 2))"### args

elab "cert_counterTable_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 1
 (.leaf (certNat% ⟪0⟫))
 (.leaf (certNat% ⟪1⟫)))"### args

elab "cert_counterTable_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 3
 (.branch 1
 (.leaf (certNat% 12))
 (.branch 2
 (.leaf (certNat% 13))
 (.leaf (certNat% 14))))
 (.branch 4
 (.leaf (certNat% 15))
 (.branch 5
 (.leaf (certNat% 16))
 (.leaf (certNat% 17)))))"### args

elab "cert_counterTable_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 3
 (.branch 1
 (.leaf (certNat% ⟪0⟫))
 (.branch 2
 (.leaf (certNat% ⟪1⟫))
 (.leaf (certNat% ⟪2⟫))))
 (.branch 5
 (.branch 4
 (.leaf (certNat% ⟪3⟫))
 (.leaf (certNat% ⟪4⟫)))
 (.branch 6
 (.leaf (certNat% ⟪5⟫))
 (.leaf (certNat% ⟪6⟫)))))"### args

elab "cert_counters_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take ⟪0⟫ (PackedRawNatGrowth.drop (⟪0⟫*(i%128)) (counterTable.get (i/128)))"### args

elab "cert_dispositionTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (RawLeafCertificate.Certificate.quota ⟪0⟫))"### args

elab "cert_dispositionTest_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase⟪0⟫.rawCells) (dispositionTable.get i)"### args

elab "cert_dispositionTest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixExtra⟪0⟫.rawCells) (dispositionTable.get i)"### args

elab "cert_dispositionTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSixBase⟪0⟫.rawCells) (dispositionTable.get i)"### args

elab "cert_dispositionTest_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem dispositionTest_block_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check dispositionTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_dispositionTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem dispositionTest_complete : Interval dispositionTest 0 1 :=
  dispositionTest_block_0"### args

elab "cert_dispositionTest_complete_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem dispositionTest_complete : Interval dispositionTest 0 2 :=
  (interval_append dispositionTest 0 1 2
  dispositionTest_block_0
  dispositionTest_block_1)"### args

elab "cert_disposition_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def disposition (j : Fin leafCount) := dispositionTable.get j.val"### args

elab "cert_disposition_at_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.rawCells) Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫) = true
  rw [Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_at_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by decide +kernel"### args

elab "cert_disposition_at_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.rawCells) Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫) = true
  rw [Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_at_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.rawCells) Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫) = true
  rw [Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_at_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by decide +kernel"### args

elab "cert_disposition_at_9 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.rawCells) Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫) = true
  rw [Nonrational.OldTerminalMatches.M⟪2⟫.r⟪3⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_checked_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixExtra⟪0⟫.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt"### args

elab "cert_disposition_checked_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSixBase⟪0⟫.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt"### args

elab "cert_disposition_interval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_interval_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact disposition_at_⟪0⟫"### args

elab "cert_disposition_interval_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_interval_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact disposition_at_⟪0⟫"### args

elab "cert_leafInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafInterval⟪0⟫ : Interval leafTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := leafTestAt⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_leafTable_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTable : Table (List Nat) :=
(.leaf [])"### args

elab "cert_leafTestAt " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTestAt⟪0⟫ (i : Nat) := leafTest (i+⟪0⟫)"### args

elab "cert_leafTestAt_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTestAt⟪0⟫_block_⟪1⟫ : Interval leafTestAt⟪0⟫ ⟪1⟫ ⟪2⟫ :=
  interval_of_check leafTestAt⟪0⟫ ⟪1⟫ 1 (by decide +kernel)"### args

elab "cert_leafTest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixBase⟪0⟫.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))"### args

elab "cert_leafTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSixExtra⟪0⟫.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))"### args

elab "cert_leafTest_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_block_⟪0⟫ : Interval leafTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check leafTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_leafTest_complete_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_complete : Interval leafTest 0 1 :=
  leafTest_block_0"### args

elab "cert_leaves_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves"### args

elab "cert_nodeInterval_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeInterval⟪0⟫ : Interval nodeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := test⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [test⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_nodeTest_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 ⟪0⟫ leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.keys Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra⟪1⟫.Generators.FastWords.rawMaps rawLeaves codes counters i"### args

elab "cert_nodeTest_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 ⟪0⟫ leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.keys Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase⟪1⟫.Generators.FastWords.rawMaps rawLeaves codes counters i"### args

elab "cert_nodeTest_complete_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 640 ⟪0⟫ nodeInterval0 nodeInterval640)"### args

elab "cert_nodeTest_complete_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_complete : Interval nodeTest 0 nodeCount := nodeInterval0"### args

elab "cert_nodeTest_complete_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 1280 ⟪0⟫ (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 ⟪0⟫ nodeInterval1280 nodeInterval1920))"### args

elab "cert_nodeTest_sound_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 ⟪0⟫ leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.keys Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixExtra⟪1⟫.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 ⟪0⟫ leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.keys Papers.RationalityTen.RootedCaches.RootedSixExtra⟪1⟫.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixExtra⟪1⟫.Generators.FastWords.rawMaps rawLeaves codes counters i h"### args

elab "cert_nodeTest_sound_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 ⟪0⟫ leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.badMasks
        Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.keys Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.fastKind quota
        Papers.RationalityTen.FacetUniverses.RootedSixBase⟪1⟫.Generators.FastWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 ⟪0⟫ leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.keys Papers.RationalityTen.RootedCaches.RootedSixBase⟪1⟫.fastKind quota
    Papers.RationalityTen.FacetUniverses.RootedSixBase⟪1⟫.Generators.FastWords.rawMaps rawLeaves codes counters i h"### args

elab "cert_nodes_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 ⟪0⟫ leafCount nodeCount :=
  decodedNodes rawNodes"### args

elab "cert_quota_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def quota : Nat → Nat
  | 0 => 1
  | 1 => ⟪1⟫
  | 2 => ⟪9⟫
  | 3 => ⟪8⟫
  | 4 => ⟪7⟫
  | 5 => ⟪6⟫
  | 6 => ⟪3⟫
  | 7 => ⟪5⟫
  | 8 => ⟪4⟫
  | 9 => ⟪2⟫
  | 10 => ⟪0⟫
  | _ => 0"### args

elab "cert_rawLeaves_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawLeaves := leafTable.get"### args

elab "cert_rawLeaves_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawLeaves (i : Nat) : List Nat :=
  let code := leafTable.get i
  (PackedRawNatGrowth.readList ⟪0⟫ (PackedRawNatGrowth.take 5 code)
    (PackedRawNatGrowth.drop 5 code)).1"### args

elab "cert_rawNodes_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)"### args

elab "cert_root_7 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def root : Fin nodeCount := ⟨⟪0⟫, by decide⟩"### args

elab "cert_test_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def test⟪0⟫ (i : Nat) := nodeTest (i+⟪0⟫)"### args

elab "cert_test_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_block_⟪1⟫ : Interval test⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check test⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_test_complete_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_complete : Interval test⟪0⟫ 0 ⟪1⟫ :=
  test⟪0⟫_block_0"### args

elab "cert_test_complete_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_complete : Interval test⟪0⟫ 0 ⟪1⟫ :=
  (interval_append test⟪0⟫ 0 48 ⟪1⟫
  (interval_append test⟪0⟫ 0 16 48
  test⟪0⟫_block_0
  (interval_append test⟪0⟫ 16 32 48
  test⟪0⟫_block_1
  test⟪0⟫_block_2))
  (interval_append test⟪0⟫ 48 64 ⟪1⟫
  test⟪0⟫_block_3
  (interval_append test⟪0⟫ 64 80 ⟪1⟫
  test⟪0⟫_block_4
  test⟪0⟫_block_5)))"### args

elab "cert_widths_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def widths : PackedRawNatGrowth.Widths := ⟨⟪0⟫,⟪1⟫,⟪2⟫,⟪3⟫⟩"### args

