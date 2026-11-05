module
prelude
public import RootedSixBase02GrowthCache
public import RootedSixBase02FastWords
public import SubsumedClassification
public import RootedSubsumedForest0306Leaves
public import RootedSubsumedForest0306Proof000
public import RootedSubsumedForest0306Proof001
public import RootedSubsumedForest0306Proof002
public import RootedSubsumedForest0306Proof003
public import RootedSubsumedForest0306Proof004
public import RootedSubsumedForest0306Proof005
public import RootedSubsumedForest0306Proof006
public import RootedSubsumedForest0306Proof007
public import RootedSubsumedForest0306Proof008
public import RootedSubsumedForest0306Proof009
public import RootedSubsumedForest0306Proof010
public import RootedSubsumedForest0306Proof011
public import RootedSubsumedForest0306Proof012
public import RootedSubsumedForest0306Proof013
public import RootedSubsumedForest0306Proof014
public import RootedSubsumedForest0306Proof015
public import RootedSubsumedForest0306Proof016
public import RootedSubsumedForest0306Proof017
public import RootedSubsumedForest0306Proof018

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 5760 11719 (interval_append nodeTest 0 2560 5760 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5760 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)))) (interval_append nodeTest 5760 8960 11719 (interval_append nodeTest 5760 7040 8960 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8960 nodeInterval7040 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320))) (interval_append nodeTest 8960 10240 11719 (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600) (interval_append nodeTest 10240 10880 11719 nodeInterval10240 (interval_append nodeTest 10880 11520 11719 nodeInterval10880 nodeInterval11520)))))
def root : Fin nodeCount := ⟨11718, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 48 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
    (renamings : Fin 48 → Renaming (fun c => has (FacetUniverses.RootedSixBase02.ridgeList c))
      FacetUniverses.RootedSixBase02.literalCompatible FacetUniverses.RootedSixBase02.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixBase02.ridgeList c))
      FacetUniverses.RootedSixBase02.literalCompatible FacetUniverses.RootedSixBase02.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 48)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixBase02.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.badMasks Papers.RationalityTen.RootedCaches.RootedSixBase02.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixBase02.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixBase02.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
