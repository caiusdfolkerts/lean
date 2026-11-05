module
prelude
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0339Leaves
public import RootedSubsumedForest0339Proof000
public import RootedSubsumedForest0339Proof001
public import RootedSubsumedForest0339Proof002
public import RootedSubsumedForest0339Proof003
public import RootedSubsumedForest0339Proof004
public import RootedSubsumedForest0339Proof005
public import RootedSubsumedForest0339Proof006
public import RootedSubsumedForest0339Proof007
public import RootedSubsumedForest0339Proof008
public import RootedSubsumedForest0339Proof009
public import RootedSubsumedForest0339Proof010
public import RootedSubsumedForest0339Proof011
public import RootedSubsumedForest0339Proof012
public import RootedSubsumedForest0339Proof013
public import RootedSubsumedForest0339Proof014
public import RootedSubsumedForest0339Proof015
public import RootedSubsumedForest0339Proof016
public import RootedSubsumedForest0339Proof017
public import RootedSubsumedForest0339Proof018
public import RootedSubsumedForest0339Proof019
public import RootedSubsumedForest0339Proof020
public import RootedSubsumedForest0339Proof021
public import RootedSubsumedForest0339Proof022

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 7040 14699 (interval_append nodeTest 0 3200 7040 (interval_append nodeTest 0 1280 3200 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 3200 nodeInterval1280 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560))) (interval_append nodeTest 3200 5120 7040 (interval_append nodeTest 3200 3840 5120 nodeInterval3200 (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480)) (interval_append nodeTest 5120 5760 7040 nodeInterval5120 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)))) (interval_append nodeTest 7040 10880 14699 (interval_append nodeTest 7040 8960 10880 (interval_append nodeTest 7040 7680 8960 nodeInterval7040 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320)) (interval_append nodeTest 8960 9600 10880 nodeInterval8960 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240))) (interval_append nodeTest 10880 12800 14699 (interval_append nodeTest 10880 11520 12800 nodeInterval10880 (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160)) (interval_append nodeTest 12800 13440 14699 nodeInterval12800 (interval_append nodeTest 13440 14080 14699 nodeInterval13440 nodeInterval14080)))))
def root : Fin nodeCount := ⟨14698, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
