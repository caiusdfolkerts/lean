module
prelude
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import RawClosedGrowthClassification
public import SmallRawForest02Leaves
public import SmallRawForest02Proof000
public import SmallRawForest02Proof001
public import SmallRawForest02Proof002
public import SmallRawForest02Proof003
public import SmallRawForest02Proof004
public import SmallRawForest02Proof005
public import SmallRawForest02Proof006
public import SmallRawForest02Proof007

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallRawForest02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 2560 4925 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 4925 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 4925 nodeInterval3840 nodeInterval4480)))
def root : Fin nodeCount := ⟨4924, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 1440 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
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
  refine RawClosedGrowthClassification.complete_of_raw_closed_checks
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
    rfl
#print axioms boundary_classification

end Papers.RationalityTen.SmallRawForests.SmallRawForest02
