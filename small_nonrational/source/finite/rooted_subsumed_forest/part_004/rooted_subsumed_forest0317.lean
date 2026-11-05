module
prelude
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0317Leaves
public import RootedSubsumedForest0317Proof000
public import RootedSubsumedForest0317Proof001
public import RootedSubsumedForest0317Proof002
public import RootedSubsumedForest0317Proof003
public import RootedSubsumedForest0317Proof004
public import RootedSubsumedForest0317Proof005
public import RootedSubsumedForest0317Proof006
public import RootedSubsumedForest0317Proof007
public import RootedSubsumedForest0317Proof008
public import RootedSubsumedForest0317Proof009
public import RootedSubsumedForest0317Proof010
public import RootedSubsumedForest0317Proof011
public import RootedSubsumedForest0317Proof012
public import RootedSubsumedForest0317Proof013
public import RootedSubsumedForest0317Proof014

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 4480 9003 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 7040 9003 (interval_append nodeTest 4480 5760 7040 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120) (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)) (interval_append nodeTest 7040 8320 9003 (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680) (interval_append nodeTest 8320 8960 9003 nodeInterval8320 nodeInterval8960))))
def root : Fin nodeCount := ⟨9002, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
