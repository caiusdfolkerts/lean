module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_blocks_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩))"### args

elab "cert_blocks_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 1
 (.leaf ⟨(certNat% 0),(certNat% 1)⟩)
 (.branch 2
 (.leaf ⟨(certNat% 2),(certNat% 3)⟩)
 (.leaf ⟨(certNat% 4),(certNat% 5)⟩)))"### args

elab "cert_boundary_classification_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification
    (renamings : Fin 1 → Renaming (fun c => has (FacetUniverses.RootedSevenMixed⟪0⟫.ridgeList c))
      FacetUniverses.RootedSevenMixed⟪0⟫.literalCompatible FacetUniverses.RootedSevenMixed⟪0⟫.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.IdentityRawMaps.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSevenMixed⟪0⟫.ridgeList c))
      FacetUniverses.RootedSevenMixed⟪0⟫.literalCompatible FacetUniverses.RootedSevenMixed⟪0⟫.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 1)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine RawClosedGrowthClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.badMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.fastKind
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.facts.kindExact c) hmaps ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

elab "cert_boundary_classification_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification
    (renamings : Fin 1 → Renaming (fun c => has (FacetUniverses.RootedSevenPure⟪0⟫.ridgeList c))
      FacetUniverses.RootedSevenPure⟪0⟫.literalCompatible FacetUniverses.RootedSevenPure⟪0⟫.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.IdentityRawMaps.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSevenPure⟪0⟫.ridgeList c))
      FacetUniverses.RootedSevenPure⟪0⟫.literalCompatible FacetUniverses.RootedSevenPure⟪0⟫.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 1)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine RawClosedGrowthClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.badMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.fastKind
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.facts.kindExact c) hmaps ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

elab "cert_codes_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload"### args

elab "cert_counterTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 1
 (.leaf (certNat% 4))
 (.leaf (certNat% 5)))"### args

elab "cert_counterTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counterTable : Table Nat :=
(.branch 1
 (.leaf (certNat% 6))
 (.branch 2
 (.leaf (certNat% 7))
 (.leaf (certNat% 8))))"### args

elab "cert_counters_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))"### args

elab "cert_dispositionTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTable : Table RawLeafCertificate.Certificate :=
(.leaf (RawLeafCertificate.Certificate.quota ⟪0⟫))"### args

elab "cert_dispositionTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.rawCells) (dispositionTable.get i)"### args

elab "cert_dispositionTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def dispositionTest (i : Nat) : Bool := RawLeafCertificate.check quota
  ((rawLeaves i).map Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.rawCells) (dispositionTable.get i)"### args

elab "cert_dispositionTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem dispositionTest_block_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check dispositionTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_dispositionTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem dispositionTest_complete : Interval dispositionTest 0 1 :=
  dispositionTest_block_0"### args

elab "cert_disposition_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def disposition (j : Fin leafCount) := dispositionTable.get j.val"### args

elab "cert_disposition_at " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map Papers.RationalityTen.RootedCaches.RootedSevenPure064.rawCells) Nonrational.OldTerminalMatches.M000.r⟪1⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M000.r⟪1⟫) = true
  rw [Nonrational.OldTerminalMatches.M000.r⟪1⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_at_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by decide +kernel"### args

elab "cert_disposition_at_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by decide +kernel"### args

elab "cert_disposition_checked_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt"### args

elab "cert_disposition_checked_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt"### args

elab "cert_disposition_interval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_interval_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact disposition_at_⟪0⟫"### args

elab "cert_disposition_interval_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_interval_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact disposition_at_⟪0⟫"### args

elab "cert_leafTable_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTable : Table (List Nat) :=
(.leaf [])"### args

elab "cert_leafTestAt_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTestAt⟪0⟫_block_⟪1⟫ : Interval leafTestAt⟪0⟫ ⟪1⟫ ⟪2⟫ :=
  interval_of_check leafTestAt⟪0⟫ ⟪1⟫ 1 (by decide +kernel)"### args

elab "cert_leafTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSevenPure⟪0⟫.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))"### args

elab "cert_leafTest_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.RootedSevenMixed⟪0⟫.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))"### args

elab "cert_leafTest_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_block_⟪0⟫ : Interval leafTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check leafTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_leafTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_complete : Interval leafTest 0 1 :=
  leafTest_block_0"### args

elab "cert_leaves_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves"### args

elab "cert_nodeInterval_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeInterval⟪0⟫ : Interval nodeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := test⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [test⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_nodeTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodeTest (i : Nat) : Bool :=
  CounterGrowthReplay.check widths cellCount 1024 1 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.keys Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.fastKind quota
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves codes counters i"### args

elab "cert_nodeTest_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodeTest (i : Nat) : Bool :=
  CounterGrowthReplay.check widths cellCount 1024 1 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.keys Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.fastKind quota
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves codes counters i"### args

elab "cert_nodeTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 640 ⟪0⟫ nodeInterval0 (interval_append nodeTest 640 1280 ⟪0⟫ nodeInterval640 nodeInterval1280))"### args

elab "cert_nodeTest_complete_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_complete : Interval nodeTest 0 nodeCount := nodeInterval0"### args

elab "cert_nodeTest_sound " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1 leafCount nodeCount (rawNodes i) = true ∧
      RawNatGrowthCheck.nodeCheck Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.badMasks
        Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.keys Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.fastKind quota
        Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves rawNodes i = true :=
  CounterGrowthReplay.check_sound widths cellCount 1024 1 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.keys Papers.RationalityTen.RootedCaches.RootedSevenMixed⟪0⟫.fastKind quota
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves codes counters i h"### args

elab "cert_nodeTest_sound_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1 leafCount nodeCount (rawNodes i) = true ∧
      RawNatGrowthCheck.nodeCheck Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.badMasks
        Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.keys Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.fastKind quota
        Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves rawNodes i = true :=
  CounterGrowthReplay.check_sound widths cellCount 1024 1 leafCount nodeCount
    Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.badMasks
    Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.kindMasks Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.keys Papers.RationalityTen.RootedCaches.RootedSevenPure⟪0⟫.fastKind quota
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves codes counters i h"### args

elab "cert_nodes_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 1 leafCount nodeCount :=
  decodedNodes rawNodes"### args

elab "cert_quota_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def quota : Nat → Nat
  | 0 => 1
  | 1 => ⟪0⟫
  | 2 => ⟪2⟫
  | 3 => ⟪3⟫
  | 4 => ⟪1⟫
  | _ => 0"### args

elab "cert_rawLeaves_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawLeaves := leafTable.get"### args

elab "cert_rawNodes_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)"### args

elab "cert_root_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def root : Fin nodeCount := ⟨⟪0⟫, by decide⟩"### args

elab "cert_test_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def test⟪0⟫ (i : Nat) := nodeTest (i+⟪0⟫)"### args

elab "cert_test_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_block_⟪1⟫ : Interval test⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check test⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_test_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_complete : Interval test⟪0⟫ 0 640 :=
  (interval_append test⟪0⟫ 0 320 640
  (interval_append test⟪0⟫ 0 160 320
  (interval_append test⟪0⟫ 0 64 160
  (interval_append test⟪0⟫ 0 32 64
  test⟪0⟫_block_0
  test⟪0⟫_block_1)
  (interval_append test⟪0⟫ 64 96 160
  test⟪0⟫_block_2
  (interval_append test⟪0⟫ 96 128 160
  test⟪0⟫_block_3
  test⟪0⟫_block_4)))
  (interval_append test⟪0⟫ 160 224 320
  (interval_append test⟪0⟫ 160 192 224
  test⟪0⟫_block_5
  test⟪0⟫_block_6)
  (interval_append test⟪0⟫ 224 256 320
  test⟪0⟫_block_7
  (interval_append test⟪0⟫ 256 288 320
  test⟪0⟫_block_8
  test⟪0⟫_block_9))))
  (interval_append test⟪0⟫ 320 480 640
  (interval_append test⟪0⟫ 320 384 480
  (interval_append test⟪0⟫ 320 352 384
  test⟪0⟫_block_10
  test⟪0⟫_block_11)
  (interval_append test⟪0⟫ 384 416 480
  test⟪0⟫_block_12
  (interval_append test⟪0⟫ 416 448 480
  test⟪0⟫_block_13
  test⟪0⟫_block_14)))
  (interval_append test⟪0⟫ 480 544 640
  (interval_append test⟪0⟫ 480 512 544
  test⟪0⟫_block_15
  test⟪0⟫_block_16)
  (interval_append test⟪0⟫ 544 576 640
  test⟪0⟫_block_17
  (interval_append test⟪0⟫ 576 608 640
  test⟪0⟫_block_18
  test⟪0⟫_block_19)))))"### args

elab "cert_test_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_complete : Interval test⟪0⟫ 0 ⟪1⟫ :=
  (interval_append test⟪0⟫ 0 128 ⟪1⟫
  (interval_append test⟪0⟫ 0 64 128
  (interval_append test⟪0⟫ 0 32 64
  test⟪0⟫_block_0
  test⟪0⟫_block_1)
  (interval_append test⟪0⟫ 64 96 128
  test⟪0⟫_block_2
  test⟪0⟫_block_3))
  (interval_append test⟪0⟫ 128 192 ⟪1⟫
  (interval_append test⟪0⟫ 128 160 192
  test⟪0⟫_block_4
  test⟪0⟫_block_5)
  (interval_append test⟪0⟫ 192 224 ⟪1⟫
  test⟪0⟫_block_6
  test⟪0⟫_block_7)))"### args

elab "cert_widths_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def widths : PackedRawNatGrowth.Widths := ⟨⟪0⟫,⟪1⟫,0,⟪2⟫⟩"### args

