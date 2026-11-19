module
public meta import NumericProofSchema
public meta section
open Lean Elab Command

elab "cert_badMasks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badMasks (i : Nat) := PackedRawNatGrowth.take ⟪0⟫ (PackedRawNatGrowth.drop (⟪0⟫*(i%64)) (badMasksTable.get (i/64)))"### args

elab "cert_badRows " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def badRows := badRowTable.get"### args

elab "cert_blocks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def blocks : Table PackedRawNatGrowth.Block :=
(.branch 1
 (.leaf ⟨⟪0⟫,⟪1⟫⟩)
 (.branch 2
 (.leaf ⟨⟪2⟫,⟪3⟫⟩)
 (.leaf ⟨⟪4⟫,⟪5⟫⟩)))"### args

elab "cert_boundary_classification " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification (B : List (Fin ⟪0⟫))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin ⟪0⟫) ∈ B) : ∃ j, Same (family (leaves j)) (family B) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  obtain ⟨j, word, hsub, hne⟩ := complete_of_raw_checks candidateMasks badMasks rawKind
    (fun _ c => c) rawLeaves rawNodes cache quota renamings
    (fun _ => rfl) (fun _ => rfl) raw_kind_exact (fun _ _ => rfl)
    (fun j => (Bool.and_eq_true_iff.mp
      (leafTest_complete j.val (Nat.zero_le _) j.isLt)).1)
    (fun i => (Bool.and_eq_true_iff.mp
      (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).1)
    (fun i => (Bool.and_eq_true_iff.mp
      (nodeTest_complete i.val (Nat.zero_le _) i.isLt)).2)
    B hB root
    (by
      intro c hc
      change has (nodes root).cells c = true at hc
      rw [hrootCells] at hc
      have heq : c = 0 := List.eq_of_mem_singleton ((has_true [0] c).mp hc)
      subst c
      exact (has_true B 0).mpr hroot)
    (by
      refine ⟨0, ?_⟩
      change has (nodes root).cells 0 = true
      rw [hrootCells]
      rfl)
  have hw : OrbitGrowthDAG.applyWord renamings word B = B :=
    applyWord_identity (fun c => has (ridgeList c)) literalCompatible kind word B
  rw [hw] at hsub
  refine ⟨j, closed_leaf_eq_target ridgeList B (leaves j) hsub hne hB.no_three hB.connected ?_⟩
  exact (Bool.and_eq_true_iff.mp (leafTest_complete j.val (Nat.zero_le _) j.isLt)).2"### args

elab "cert_boundary_classification_nodup " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification_nodup (B : List (Fin ⟪0⟫))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin ⟪0⟫) ∈ B) :
    ∃ j, (leaves j).Nodup ∧ Same (family (leaves j)) (family B) := by
  obtain ⟨j, hj⟩ := boundary_classification B hB hroot
  exact ⟨j, leaves_nodup j, hj⟩"### args

elab "cert_boundary_classification_word " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem boundary_classification_word (B : List (Fin ⟪0⟫))
    (hB : Target (fun c => has (ridgeList c)) literalCompatible kind quota B)
    (hroot : (0 : Fin ⟪0⟫) ∈ B) :
    ∃ (j : Fin ⟪1⟫) (word : List (Fin 1)), (leaves j).Nodup ∧
      Same (family (leaves j)) (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  obtain ⟨j, hnodup, hj⟩ := boundary_classification_nodup B hB hroot
  exact ⟨j, [], hnodup, hj⟩"### args

elab "cert_cache " args:num* : command =>
  NumericProofSchema.elaborate
    r###"noncomputable def cache : Cache ridgeList literalCompatible kind :=
  FastRawCacheCertificate.ofChecks rawCells candidateMasks badMasks kindMasks
    candidateRows badRows kindRows keys
    (fun c => (cell_facts c).1)
    (fun q => of_decide_eq_true (ridge_facts q).1)
    (fun c => (cell_facts c).2.1)
    (fun q => (ridge_facts q).2)
    (fun c => of_decide_eq_true (cell_facts c).2.2.1)
    (fun c => (cell_facts c).2.2.2.1)
    (by
      intro j hj
      exact of_decide_eq_true (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).1)
    (by
      intro j hj
      exact (Bool.and_eq_true_iff.mp
        (kindTest_complete j (Nat.zero_le _) (List.mem_range.mp hj))).2)"### args

elab "cert_candidateMasks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateMasks (i : Nat) := PackedRawNatGrowth.take ⟪0⟫ (PackedRawNatGrowth.drop (⟪0⟫*(i%64)) (candidateMasksTable.get (i/64)))"### args

elab "cert_candidateRows " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def candidateRows := candidateRowTable.get"### args

elab "cert_cellTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cellTest (i : Nat) : Bool := (listBounds 1024 (rawCells i).ridgeMasks && ((rawCells i).ridgeMasks.all (fun q => (candidateMasks q).testBit i) && (decide (badMasks i = RawNatGrowthCheck.mask (badRows i)) && ((badRows i).all (fun c => !(ConcreteGrowth.compatible (rawCells i) (rawCells c))) && decide (rawKind i = (rawCells i).kind)))))"### args

elab "cert_cellTest_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cellTest_block_⟪0⟫ : Interval cellTest ⟪1⟫ ⟪2⟫ :=
  interval_of_check cellTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_cell_facts " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem cell_facts (a : Fin ⟪0⟫) :
    (listBounds 1024 (rawCells a.val).ridgeMasks = true) ∧ ((rawCells a.val).ridgeMasks.all (fun q => (candidateMasks q).testBit a.val) = true) ∧ (decide (badMasks a.val = RawNatGrowthCheck.mask (badRows a.val)) = true) ∧ ((badRows a.val).all (fun c => !(ConcreteGrowth.compatible (rawCells a.val) (rawCells c))) = true) ∧ (decide (rawKind a.val = (rawCells a.val).kind) = true) := by
  simpa only [cellTest, Bool.and_eq_true_iff] using cellTest_complete a.val (Nat.zero_le _) a.isLt"### args

elab "cert_cells " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def cells (c : Fin ⟪0⟫) := rawCells c.val"### args

elab "cert_checkedInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem checkedInterval⟪0⟫ : Interval nodeTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  exact fastTest_sound i (nodeInterval⟪0⟫ i hlo hhi)"### args

elab "cert_codes " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def codes (i : Nat) : Nat :=
  let block := blocks.get (i / 128)
  let offset := PackedRawNatGrowth.take 32 (PackedRawNatGrowth.drop (32*(i%128)) block.offsets)
  PackedRawNatGrowth.drop offset block.payload"### args

elab "cert_counters " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def counters (i : Nat) := PackedRawNatGrowth.take 25 (PackedRawNatGrowth.drop (25*(i%128)) (countersTable.get (i/128)))"### args

elab "cert_countersTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def countersTable : Table Nat :=
(.branch 1
 (.leaf ⟪0⟫)
 (.branch 2
 (.leaf ⟪1⟫)
 (.leaf ⟪2⟫)))"### args

elab "cert_disposition " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def disposition (_j : Fin ⟪0⟫) : RawLeafCertificate.Certificate := .quota ⟪1⟫"### args

elab "cert_disposition_checked " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem disposition_checked : ∀ j : Fin ⟪0⟫,
    RawLeafCertificate.check quota ((rawLeaves j.val).map rawCells)
      (disposition j) = true := by decide +kernel"### args

elab "cert_fastTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def fastTest (i : Nat) : Bool :=
  CachedMaskGrowth.countedCheck widths ⟪0⟫ 1024 1 ⟪1⟫ ⟪2⟫
    candidateMasks badMasks kindMasks keys rawKind quota (fun _ c => c)
    rawLeaves codes counters selectedMasks i"### args

elab "cert_fastTest_sound " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem fastTest_sound (i : Nat) (h : fastTest i = true) : nodeTest i = true := by
  have checked := CachedMaskGrowth.countedCheck_sound widths ⟪0⟫ 1024 1 ⟪1⟫ ⟪2⟫
    candidateMasks badMasks kindMasks keys rawKind quota (fun _ c => c)
    rawLeaves codes counters selectedMasks (fun _ => rfl) selectedMasks_exact i h
  exact Bool.and_eq_true_iff.mpr checked"### args

elab "cert_keys " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def keys := List.range 5"### args

elab "cert_kind " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kind (c : Fin ⟪0⟫) := (cells c).kind"### args

elab "cert_kindMaskTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindMaskTable : Table (Nat) :=
(.branch 2
 (.branch 1
 (.leaf 1)
 (.leaf ⟪0⟫))
 (.branch 3
 (.leaf ⟪1⟫)
 (.branch 4
 (.leaf ⟪2⟫)
 (.leaf ⟪3⟫))))"### args

elab "cert_kindMasks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindMasks := kindMaskTable.get"### args

elab "cert_kindRows " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindRows := kindRowTable.get"### args

elab "cert_kindTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def kindTest (i : Nat) : Bool := (decide (kindMasks i = RawNatGrowthCheck.mask (kindRows i)) && (kindRows i).all (fun c => decide ((rawCells c).kind = i)))"### args

elab "cert_kindTest_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_block_⟪0⟫ : Interval kindTest ⟪0⟫ ⟪1⟫ :=
  interval_of_check kindTest ⟪0⟫ 1 (by decide +kernel)"### args

elab "cert_kindTest_complete_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem kindTest_complete : Interval kindTest 0 5 :=
  (interval_append kindTest 0 2 5
  (interval_append kindTest 0 1 2
  kindTest_block_0
  kindTest_block_1)
  (interval_append kindTest 2 3 5
  kindTest_block_2
  (interval_append kindTest 3 4 5
  kindTest_block_3
  kindTest_block_4)))"### args

elab "cert_leafTable " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTable : Table (List Nat) :=
(.leaf [])"### args

elab "cert_leafTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leafTest (i : Nat) : Bool :=
  listBounds ⟪0⟫ (rawLeaves i) &&
    WitnessGrowthDAG.closedCheck ridgeList ((rawLeaves i).map (Fin.ofNat ⟪0⟫))"### args

elab "cert_leafTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_block_⟪0⟫ : Interval leafTest ⟪1⟫ ⟪2⟫ :=
  interval_of_check leafTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_leafTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leafTest_complete : Interval leafTest 0 1 :=
  leafTest_block_0"### args

elab "cert_leaves " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def leaves : Fin ⟪0⟫ → List (Fin ⟪1⟫) := decodedLeaves rawLeaves"### args

elab "cert_leaves_nodup " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem leaves_nodup : ∀ j, (leaves j).Nodup := by decide +kernel"### args

elab "cert_literalCompatible " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def literalCompatible (a b : Fin ⟪0⟫) := ConcreteGrowth.compatible (cells a) (cells b)"### args

elab "cert_maskLookup " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def maskLookup (i : Nat) := PackedRawNatGrowth.take ⟪0⟫ (PackedRawNatGrowth.drop (⟪0⟫*(i%64)) (maskLookupTable.get (i/64)))"### args

elab "cert_maskTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def maskTest (i : Nat) := decide (selectedMasks i = StreamingRawGrowth.nodeMask widths (codes i))"### args

elab "cert_maskTest_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem maskTest_block_⟪0⟫ : Interval maskTest ⟪1⟫ ⟪2⟫ :=
  interval_of_check maskTest ⟪1⟫ ⟪3⟫ (by decide +kernel)"### args

elab "cert_nodeInterval " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeInterval⟪0⟫ : Interval fastTest ⟪0⟫ ⟪1⟫ := by
  intro i hlo hhi
  have h := test⟪0⟫_complete (i - ⟪0⟫) (Nat.zero_le _) (by omega)
  simpa only [test⟪0⟫, Nat.sub_add_cancel hlo] using h"### args

elab "cert_nodeTest " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodeTest (i : Nat) : Bool :=
  nodeBounds ⟪0⟫ 1024 1 ⟪1⟫ ⟪2⟫ (rawNodes i) &&
    RawNatGrowthCheck.nodeCheck candidateMasks badMasks kindMasks keys rawKind quota
      (fun _ c => c) rawLeaves rawNodes i"### args

elab "cert_nodeTest_complete " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem nodeTest_complete : Interval nodeTest 0 ⟪0⟫ := checkedInterval0"### args

elab "cert_nodes " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def nodes : Fin ⟪0⟫ → BatchedOrbitGrowth.Node ⟪1⟫ 1024 1 ⟪2⟫ ⟪0⟫ := decodedNodes rawNodes"### args

elab "cert_quota " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def quota : Nat → Nat
  | 0 => 1
  | 1 => ⟪0⟫
  | 2 => ⟪1⟫
  | 3 => ⟪2⟫
  | 4 => 1
  | _ => 0"### args

elab "cert_rawCells " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawCells := Papers.RationalityTen.FacetUniverses.RootedSevenMixed⟪0⟫.rawCells"### args

elab "cert_rawKind " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawKind (i : Nat) := PackedRawNatGrowth.take 3 (PackedRawNatGrowth.drop (3*i) rawKindCode)"### args

elab "cert_rawKindCode " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawKindCode : Nat := ⟪0⟫"### args

elab "cert_rawLeaves " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawLeaves := leafTable.get"### args

elab "cert_rawNodes " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def rawNodes := PackedRawNatGrowth.nodes blocks widths 128"### args

elab "cert_raw_kind_exact " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem raw_kind_exact (c : Fin ⟪0⟫) : rawKind c.val = kind c :=
  of_decide_eq_true (cell_facts c).2.2.2.2"### args

elab "cert_renamings " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def renamings (_ : Fin 1) := Renaming.identity
  (fun c : Fin ⟪0⟫ => has (ridgeList c)) literalCompatible kind"### args

elab "cert_ridgeList " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeList := ConcreteGrowth.ridgeList cells"### args

elab "cert_ridgeTest_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def ridgeTest (i : Nat) : Bool := (decide (candidateMasks i = RawNatGrowthCheck.mask (candidateRows i)) && (candidateRows i).all (fun c => hasNat (rawCells c).ridgeMasks i))"### args

elab "cert_ridgeTest_block_2 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridgeTest_block_⟪0⟫ : Interval ridgeTest ⟪1⟫ ⟪2⟫ :=
  interval_of_check ridgeTest ⟪1⟫ 16 (by decide +kernel)"### args

elab "cert_ridge_facts " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem ridge_facts (q : Fin 1024) :
    (decide (candidateMasks q.val = RawNatGrowthCheck.mask (candidateRows q.val)) = true) ∧ ((candidateRows q.val).all (fun c => hasNat (rawCells c).ridgeMasks q.val) = true) := by
  simpa only [ridgeTest, Bool.and_eq_true_iff] using ridgeTest_complete q.val (Nat.zero_le _) q.isLt"### args

elab "cert_root " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def root : Fin ⟪0⟫ := ⟨⟪1⟫, by decide⟩"### args

elab "cert_selectedMasks " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def selectedMasks (i : Nat) : Nat :=
  if i < ⟪0⟫ then maskLookup i else StreamingRawGrowth.nodeMask widths (codes i)"### args

elab "cert_selectedMasks_exact " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem selectedMasks_exact (i : Nat) : selectedMasks i = StreamingRawGrowth.nodeMask widths (codes i) := by
  by_cases hi : i < ⟪0⟫
  · exact of_decide_eq_true (maskTest_complete i (Nat.zero_le _) hi)
  · simp only [selectedMasks, hi, ite_false]"### args

elab "cert_test_4 " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def test⟪0⟫ (i : Nat) := fastTest (i + ⟪0⟫)"### args

elab "cert_test_block " args:num* : command =>
  NumericProofSchema.elaborate
    r###"theorem test⟪0⟫_block_⟪1⟫ : Interval test⟪0⟫ ⟪2⟫ ⟪3⟫ :=
  interval_of_check test⟪0⟫ ⟪2⟫ ⟪4⟫ (by decide +kernel)"### args

elab "cert_widths " args:num* : command =>
  NumericProofSchema.elaborate
    r###"def widths : PackedRawNatGrowth.Widths := ⟨⟪0⟫,⟪1⟫,1,⟪2⟫⟩"### args

