module
prelude
public import RootedSevenPure018GrowthCache
public import IdentityRawMaps
public import RawClosedGrowthClassification
public import RootedRawForest0052Leaves
public import RootedRawForest0052Proof000
public import RootedRawForest0052Proof001
public import RootedRawForest0052Proof002

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0052
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 640 1477 nodeInterval0 (interval_append nodeTest 640 1280 1477 nodeInterval640 nodeInterval1280))
def root : Fin nodeCount := ⟨1476, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 1 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
    (renamings : Fin 1 → Renaming (fun c => has (FacetUniverses.RootedSevenPure018.ridgeList c))
      FacetUniverses.RootedSevenPure018.literalCompatible FacetUniverses.RootedSevenPure018.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.IdentityRawMaps.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSevenPure018.ridgeList c))
      FacetUniverses.RootedSevenPure018.literalCompatible FacetUniverses.RootedSevenPure018.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 1)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine RawClosedGrowthClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSevenPure018.candidateMasks Papers.RationalityTen.RootedCaches.RootedSevenPure018.badMasks Papers.RationalityTen.RootedCaches.RootedSevenPure018.fastKind
    Papers.RationalityTen.IdentityRawMaps.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSevenPure018.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSevenPure018.facts.kindExact c) hmaps ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

end Papers.RationalityTen.RootedForests.RootedRawForest0052
