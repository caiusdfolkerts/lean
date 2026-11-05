module
prelude
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0302Leaves
public import RootedSubsumedForest0302Proof000
public import RootedSubsumedForest0302Proof001
public import RootedSubsumedForest0302Proof002
public import RootedSubsumedForest0302Proof003
public import RootedSubsumedForest0302Proof004
public import RootedSubsumedForest0302Proof005
public import RootedSubsumedForest0302Proof006
public import RootedSubsumedForest0302Proof007
public import RootedSubsumedForest0302Proof008
public import RootedSubsumedForest0302Proof009
public import RootedSubsumedForest0302Proof010
public import RootedSubsumedForest0302Proof011
public import RootedSubsumedForest0302Proof012
public import RootedSubsumedForest0302Proof013
public import RootedSubsumedForest0302Proof014
public import RootedSubsumedForest0302Proof015
public import RootedSubsumedForest0302Proof016
public import RootedSubsumedForest0302Proof017
public import RootedSubsumedForest0302Proof018
public import RootedSubsumedForest0302Proof019
public import RootedSubsumedForest0302Proof020
public import RootedSubsumedForest0302Proof021
public import RootedSubsumedForest0302Proof022
public import RootedSubsumedForest0302Proof023
public import RootedSubsumedForest0302Proof024
public import RootedSubsumedForest0302Proof025
public import RootedSubsumedForest0302Proof026
public import RootedSubsumedForest0302Proof027
public import RootedSubsumedForest0302Proof028
public import RootedSubsumedForest0302Proof029
public import RootedSubsumedForest0302Proof030

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 9600 19838 (interval_append nodeTest 0 4480 9600 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 7040 9600 (interval_append nodeTest 4480 5760 7040 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120) (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)) (interval_append nodeTest 7040 8320 9600 (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680) (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)))) (interval_append nodeTest 9600 14720 19838 (interval_append nodeTest 9600 12160 14720 (interval_append nodeTest 9600 10880 12160 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240) (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520)) (interval_append nodeTest 12160 13440 14720 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800) (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080))) (interval_append nodeTest 14720 17280 19838 (interval_append nodeTest 14720 16000 17280 (interval_append nodeTest 14720 15360 16000 nodeInterval14720 nodeInterval15360) (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)) (interval_append nodeTest 17280 18560 19838 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920) (interval_append nodeTest 18560 19200 19838 nodeInterval18560 nodeInterval19200)))))
def root : Fin nodeCount := ⟨19837, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
