module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_boundary_classification_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification
    (renamings : Fin 1440 → Renaming (fun c => has (FacetUniverses.Small.ridgeList c))
      FacetUniverses.Small.literalCompatible FacetUniverses.Small.kind)
    (hmaps : ∀ f c, RootedSmallGeneratorWords.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.Small.ridgeList c))
      FacetUniverses.Small.literalCompatible FacetUniverses.Small.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 1440)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks RootedSmallCache.fastKind
    RootedSmallGeneratorWords.rawMaps rawLeaves rawNodes RootedSmallCache.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => RootedSmallCache.facts.kindExact c) hmaps ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

elab "cert_codes_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def codes (i : Nat) : Nat :=
  let b := blocks.get (i / 128)
  PackedRawNatGrowth.drop
    (PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) b.offsets)) b.payload"### args

elab "cert_counters_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counters (i : Nat) : Nat :=
  PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (counterTable.get (i/128)))"### args

elab "cert_dispositionTest_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem dispositionTest_block_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check dispositionTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_disposition_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def disposition (j : Fin leafCount) := dispositionTable.get j.val"### args

elab "cert_disposition_at_10 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M⟪1⟫.r⟪2⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M⟪1⟫.r⟪2⟫) = true
  rw [Nonrational.OldTerminalMatches.M⟪1⟫.r⟪2⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_at_11 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by
  change (RawLeafCertificate.boundaryCheck
    ((rawLeaves ⟪0⟫).map RootedSmallCache.rawCells) Nonrational.OldTerminalMatches.M⟪1⟫.r⟪2⟫.boundary &&
    Nonrational.InducedTerminalMatches.check Nonrational.OldTerminalMatches.M⟪1⟫.r⟪2⟫) = true
  rw [Nonrational.OldTerminalMatches.M⟪1⟫.r⟪2⟫_checked, Bool.and_true]
  decide +kernel"### args

elab "cert_disposition_at_12 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by decide +kernel"### args

elab "cert_disposition_at_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_at_⟪0⟫ : dispositionTest ⟪0⟫ = true := by decide +kernel"### args

elab "cert_disposition_checked_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map RootedSmallCache.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt"### args

elab "cert_disposition_interval_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_interval_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact disposition_at_⟪0⟫"### args

elab "cert_disposition_interval_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_interval_⟪0⟫ : Interval dispositionTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h : i = ⟪0⟫ := by omega
  subst i
  exact disposition_at_⟪0⟫"### args

elab "cert_leafInterval_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafInterval⟪0⟫ : Interval leafTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := leafTestAt⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_leafTestAt_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTestAt⟪0⟫ (i : Nat) := leafTest (i+⟪0⟫)"### args

elab "cert_leafTestAt_block_3 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTestAt⟪0⟫_block_⟪1⟫ : Interval leafTestAt⟪0⟫ ⟪1⟫ ⟪2⟫ :=
  interval_of_check leafTestAt⟪0⟫ ⟪1⟫ 1 (by decide +kernel)"### args

elab "cert_leafTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTest (i : Nat) : Bool :=
  listBounds cellCount (rawLeaves i) &&
    (WitnessGrowthDAG.closedCheck FacetUniverses.Small.ridgeList
      ((rawLeaves i).map (Fin.ofNat cellCount)) &&
      decide (((rawLeaves i).map (Fin.ofNat cellCount)).Nodup))"### args

elab "cert_leafTest_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_block_⟪0⟫ : Interval leafTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check leafTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_leaves_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leaves : Fin leafCount → List (Fin cellCount) := decodedLeaves rawLeaves"### args

elab "cert_nodeInterval_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeInterval⟪0⟫ : Interval nodeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := test⟪0⟫_complete (i-⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [test⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_nodeTest_6 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodeTest (i : Nat) : Bool :=
  SubsumedCounterReplay.check widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i"### args

elab "cert_nodeTest_sound_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_sound (i : Nat) (h : nodeTest i = true) :
    nodeBounds cellCount 1024 1440 leafCount nodeCount (rawNodes i) = true ∧
      SubsumedRawGrowth.nodeCheck RootedSmallCache.candidateMasks RootedSmallCache.badMasks
        RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
        RootedSmallGeneratorWords.rawMaps rawLeaves rawNodes i = true :=
  SubsumedCounterReplay.check_sound widths cellCount 1024 1440 leafCount nodeCount
    RootedSmallCache.candidateMasks RootedSmallCache.badMasks
    RootedSmallCache.kindMasks RootedSmallCache.keys RootedSmallCache.fastKind quota
    RootedSmallGeneratorWords.rawMaps rawLeaves codes counters i h"### args

elab "cert_nodes_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 1440 leafCount nodeCount :=
  decodedNodes rawNodes"### args

elab "cert_quota_5 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def quota : Nat → Nat
  | 0 => 1
  | 1 => ⟪0⟫
  | 2 => ⟪2⟫
  | 3 => ⟪1⟫
  | 4 => 0
  | _ => 0"### args

elab "cert_rawNodes_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawNodes (i : Nat) := PackedRawNatGrowth.decodeNode widths (codes i)"### args

elab "cert_root_8 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def root : Fin nodeCount := ⟨⟪0⟫, by decide⟩"### args

elab "cert_test_13 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def test⟪0⟫ (i : Nat) := nodeTest (i+⟪0⟫)"### args

elab "cert_test_block_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_block_⟪1⟫ : Interval test⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check test⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_widths_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def widths : PackedRawNatGrowth.Widths := ⟨12,⟪0⟫,11,⟪1⟫⟩"### args

