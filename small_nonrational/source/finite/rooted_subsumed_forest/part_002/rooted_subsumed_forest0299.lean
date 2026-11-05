module
prelude
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0299Leaves
public import RootedSubsumedForest0299Proof000
public import RootedSubsumedForest0299Proof001
public import RootedSubsumedForest0299Proof002
public import RootedSubsumedForest0299Proof003
public import RootedSubsumedForest0299Proof004
public import RootedSubsumedForest0299Proof005
public import RootedSubsumedForest0299Proof006
public import RootedSubsumedForest0299Proof007
public import RootedSubsumedForest0299Proof008
public import RootedSubsumedForest0299Proof009
public import RootedSubsumedForest0299Proof010
public import RootedSubsumedForest0299Proof011
public import RootedSubsumedForest0299Proof012
public import RootedSubsumedForest0299Proof013
public import RootedSubsumedForest0299Proof014
public import RootedSubsumedForest0299Proof015
public import RootedSubsumedForest0299Proof016
public import RootedSubsumedForest0299Proof017
public import RootedSubsumedForest0299Proof018
public import RootedSubsumedForest0299Proof019
public import RootedSubsumedForest0299Proof020
public import RootedSubsumedForest0299Proof021
public import RootedSubsumedForest0299Proof022
public import RootedSubsumedForest0299Proof023

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 7680 15088 (interval_append nodeTest 0 3840 7680 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 7680 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 6400 7680 nodeInterval5760 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)))) (interval_append nodeTest 7680 11520 15088 (interval_append nodeTest 7680 9600 11520 (interval_append nodeTest 7680 8320 9600 nodeInterval7680 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))) (interval_append nodeTest 11520 13440 15088 (interval_append nodeTest 11520 12160 13440 nodeInterval11520 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800)) (interval_append nodeTest 13440 14080 15088 nodeInterval13440 (interval_append nodeTest 14080 14720 15088 nodeInterval14080 nodeInterval14720)))))
def root : Fin nodeCount := ⟨15087, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 96 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
    (renamings : Fin 96 → Renaming (fun c => has (FacetUniverses.RootedSixBase00.ridgeList c))
      FacetUniverses.RootedSixBase00.literalCompatible FacetUniverses.RootedSixBase00.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixBase00.ridgeList c))
      FacetUniverses.RootedSixBase00.literalCompatible FacetUniverses.RootedSixBase00.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 96)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixBase00.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.badMasks Papers.RationalityTen.RootedCaches.RootedSixBase00.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixBase00.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixBase00.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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
    rfl
#print axioms boundary_classification

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
