module
prelude
public import RootedSixExtra05GrowthCache
public import RootedSixExtra05FastWords
public import SubsumedClassification
public import RootedSubsumedForest0870Leaves
public import RootedSubsumedForest0870Proof000
public import RootedSubsumedForest0870Proof001
public import RootedSubsumedForest0870Proof002
public import RootedSubsumedForest0870Proof003
public import RootedSubsumedForest0870Proof004
public import RootedSubsumedForest0870Proof005
public import RootedSubsumedForest0870Proof006
public import RootedSubsumedForest0870Proof007
public import RootedSubsumedForest0870Proof008
public import RootedSubsumedForest0870Proof009
public import RootedSubsumedForest0870Proof010
public import RootedSubsumedForest0870Proof011
public import RootedSubsumedForest0870Proof012
public import RootedSubsumedForest0870Proof013
public import RootedSubsumedForest0870Proof014
public import RootedSubsumedForest0870Proof015
public import RootedSubsumedForest0870Proof016
public import RootedSubsumedForest0870Proof017
public import RootedSubsumedForest0870Proof018
public import RootedSubsumedForest0870Proof019
public import RootedSubsumedForest0870Proof020
public import RootedSubsumedForest0870Proof021
public import RootedSubsumedForest0870Proof022
public import RootedSubsumedForest0870Proof023
public import RootedSubsumedForest0870Proof024
public import RootedSubsumedForest0870Proof025
public import RootedSubsumedForest0870Proof026
public import RootedSubsumedForest0870Proof027
public import RootedSubsumedForest0870Proof028
public import RootedSubsumedForest0870Proof029
public import RootedSubsumedForest0870Proof030
public import RootedSubsumedForest0870Proof031
public import RootedSubsumedForest0870Proof032
public import RootedSubsumedForest0870Proof033
public import RootedSubsumedForest0870Proof034
public import RootedSubsumedForest0870Proof035

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 11520 22983 (interval_append nodeTest 0 5760 11520 (interval_append nodeTest 0 2560 5760 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5760 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)))) (interval_append nodeTest 5760 8320 11520 (interval_append nodeTest 5760 7040 8320 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680)) (interval_append nodeTest 8320 9600 11520 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))))) (interval_append nodeTest 11520 17280 22983 (interval_append nodeTest 11520 14080 17280 (interval_append nodeTest 11520 12800 14080 (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160) (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440)) (interval_append nodeTest 14080 15360 17280 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720) (interval_append nodeTest 15360 16000 17280 nodeInterval15360 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)))) (interval_append nodeTest 17280 19840 22983 (interval_append nodeTest 17280 18560 19840 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920) (interval_append nodeTest 18560 19200 19840 nodeInterval18560 nodeInterval19200)) (interval_append nodeTest 19840 21120 22983 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480) (interval_append nodeTest 21120 21760 22983 nodeInterval21120 (interval_append nodeTest 21760 22400 22983 nodeInterval21760 nodeInterval22400))))))
def root : Fin nodeCount := ⟨22982, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 288 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
    (renamings : Fin 288 → Renaming (fun c => has (FacetUniverses.RootedSixExtra05.ridgeList c))
      FacetUniverses.RootedSixExtra05.literalCompatible FacetUniverses.RootedSixExtra05.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixExtra05.ridgeList c))
      FacetUniverses.RootedSixExtra05.literalCompatible FacetUniverses.RootedSixExtra05.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 288)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixExtra05.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.badMasks Papers.RationalityTen.RootedCaches.RootedSixExtra05.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixExtra05.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixExtra05.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
