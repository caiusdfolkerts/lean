module
prelude
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0303Leaves
public import RootedSubsumedForest0303Proof000
public import RootedSubsumedForest0303Proof001
public import RootedSubsumedForest0303Proof002
public import RootedSubsumedForest0303Proof003
public import RootedSubsumedForest0303Proof004
public import RootedSubsumedForest0303Proof005
public import RootedSubsumedForest0303Proof006
public import RootedSubsumedForest0303Proof007
public import RootedSubsumedForest0303Proof008
public import RootedSubsumedForest0303Proof009
public import RootedSubsumedForest0303Proof010
public import RootedSubsumedForest0303Proof011
public import RootedSubsumedForest0303Proof012
public import RootedSubsumedForest0303Proof013
public import RootedSubsumedForest0303Proof014
public import RootedSubsumedForest0303Proof015
public import RootedSubsumedForest0303Proof016
public import RootedSubsumedForest0303Proof017
public import RootedSubsumedForest0303Proof018
public import RootedSubsumedForest0303Proof019
public import RootedSubsumedForest0303Proof020
public import RootedSubsumedForest0303Proof021
public import RootedSubsumedForest0303Proof022
public import RootedSubsumedForest0303Proof023
public import RootedSubsumedForest0303Proof024
public import RootedSubsumedForest0303Proof025
public import RootedSubsumedForest0303Proof026
public import RootedSubsumedForest0303Proof027
public import RootedSubsumedForest0303Proof028

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 8960 18357 (interval_append nodeTest 0 4480 8960 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 6400 8960 (interval_append nodeTest 4480 5120 6400 nodeInterval4480 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760)) (interval_append nodeTest 6400 7680 8960 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040) (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320)))) (interval_append nodeTest 8960 13440 18357 (interval_append nodeTest 8960 10880 13440 (interval_append nodeTest 8960 9600 10880 nodeInterval8960 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240)) (interval_append nodeTest 10880 12160 13440 (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520) (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800))) (interval_append nodeTest 13440 16000 18357 (interval_append nodeTest 13440 14720 16000 (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080) (interval_append nodeTest 14720 15360 16000 nodeInterval14720 nodeInterval15360)) (interval_append nodeTest 16000 17280 18357 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640) (interval_append nodeTest 17280 17920 18357 nodeInterval17280 nodeInterval17920)))))
def root : Fin nodeCount := ⟨18356, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 48 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
    (renamings : Fin 48 → Renaming (fun c => has (FacetUniverses.RootedSixBase01.ridgeList c))
      FacetUniverses.RootedSixBase01.literalCompatible FacetUniverses.RootedSixBase01.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixBase01.ridgeList c))
      FacetUniverses.RootedSixBase01.literalCompatible FacetUniverses.RootedSixBase01.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 48)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixBase01.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixBase01.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
