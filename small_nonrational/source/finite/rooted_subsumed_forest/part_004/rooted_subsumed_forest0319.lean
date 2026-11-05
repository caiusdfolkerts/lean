module
prelude
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0319Leaves
public import RootedSubsumedForest0319Proof000
public import RootedSubsumedForest0319Proof001
public import RootedSubsumedForest0319Proof002
public import RootedSubsumedForest0319Proof003
public import RootedSubsumedForest0319Proof004
public import RootedSubsumedForest0319Proof005
public import RootedSubsumedForest0319Proof006
public import RootedSubsumedForest0319Proof007
public import RootedSubsumedForest0319Proof008
public import RootedSubsumedForest0319Proof009
public import RootedSubsumedForest0319Proof010
public import RootedSubsumedForest0319Proof011
public import RootedSubsumedForest0319Proof012
public import RootedSubsumedForest0319Proof013
public import RootedSubsumedForest0319Proof014
public import RootedSubsumedForest0319Proof015
public import RootedSubsumedForest0319Proof016
public import RootedSubsumedForest0319Proof017
public import RootedSubsumedForest0319Proof018
public import RootedSubsumedForest0319Proof019
public import RootedSubsumedForest0319Proof020
public import RootedSubsumedForest0319Proof021
public import RootedSubsumedForest0319Proof022
public import RootedSubsumedForest0319Proof023
public import RootedSubsumedForest0319Proof024
public import RootedSubsumedForest0319Proof025
public import RootedSubsumedForest0319Proof026
public import RootedSubsumedForest0319Proof027
public import RootedSubsumedForest0319Proof028
public import RootedSubsumedForest0319Proof029
public import RootedSubsumedForest0319Proof030
public import RootedSubsumedForest0319Proof031
public import RootedSubsumedForest0319Proof032
public import RootedSubsumedForest0319Proof033
public import RootedSubsumedForest0319Proof034
public import RootedSubsumedForest0319Proof035
public import RootedSubsumedForest0319Proof036
public import RootedSubsumedForest0319Proof037
public import RootedSubsumedForest0319Proof038
public import RootedSubsumedForest0319Proof039
public import RootedSubsumedForest0319Proof040
public import RootedSubsumedForest0319Proof041
public import RootedSubsumedForest0319Proof042
public import RootedSubsumedForest0319Proof043
public import RootedSubsumedForest0319Proof044
public import RootedSubsumedForest0319Proof045
public import RootedSubsumedForest0319Proof046
public import RootedSubsumedForest0319Proof047
public import RootedSubsumedForest0319Proof048
public import RootedSubsumedForest0319Proof049
public import RootedSubsumedForest0319Proof050
public import RootedSubsumedForest0319Proof051
public import RootedSubsumedForest0319Proof052
public import RootedSubsumedForest0319Proof053
public import RootedSubsumedForest0319Proof054
public import RootedSubsumedForest0319Proof055
public import RootedSubsumedForest0319Proof056
public import RootedSubsumedForest0319Proof057
public import RootedSubsumedForest0319Proof058
public import RootedSubsumedForest0319Proof059
public import RootedSubsumedForest0319Proof060
public import RootedSubsumedForest0319Proof061
public import RootedSubsumedForest0319Proof062
public import RootedSubsumedForest0319Proof063
public import RootedSubsumedForest0319Proof064
public import RootedSubsumedForest0319Proof065
public import RootedSubsumedForest0319Proof066

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 21120 42707 (interval_append nodeTest 0 10240 21120 (interval_append nodeTest 0 5120 10240 (interval_append nodeTest 0 2560 5120 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5120 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480))) (interval_append nodeTest 5120 7680 10240 (interval_append nodeTest 5120 6400 7680 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760) (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)) (interval_append nodeTest 7680 8960 10240 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320) (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600)))) (interval_append nodeTest 10240 15360 21120 (interval_append nodeTest 10240 12800 15360 (interval_append nodeTest 10240 11520 12800 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880) (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160)) (interval_append nodeTest 12800 14080 15360 (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440) (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720))) (interval_append nodeTest 15360 17920 21120 (interval_append nodeTest 15360 16640 17920 (interval_append nodeTest 15360 16000 16640 nodeInterval15360 nodeInterval16000) (interval_append nodeTest 16640 17280 17920 nodeInterval16640 nodeInterval17280)) (interval_append nodeTest 17920 19200 21120 (interval_append nodeTest 17920 18560 19200 nodeInterval17920 nodeInterval18560) (interval_append nodeTest 19200 19840 21120 nodeInterval19200 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480)))))) (interval_append nodeTest 21120 32000 42707 (interval_append nodeTest 21120 26240 32000 (interval_append nodeTest 21120 23680 26240 (interval_append nodeTest 21120 22400 23680 (interval_append nodeTest 21120 21760 22400 nodeInterval21120 nodeInterval21760) (interval_append nodeTest 22400 23040 23680 nodeInterval22400 nodeInterval23040)) (interval_append nodeTest 23680 24960 26240 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320) (interval_append nodeTest 24960 25600 26240 nodeInterval24960 nodeInterval25600))) (interval_append nodeTest 26240 28800 32000 (interval_append nodeTest 26240 27520 28800 (interval_append nodeTest 26240 26880 27520 nodeInterval26240 nodeInterval26880) (interval_append nodeTest 27520 28160 28800 nodeInterval27520 nodeInterval28160)) (interval_append nodeTest 28800 30080 32000 (interval_append nodeTest 28800 29440 30080 nodeInterval28800 nodeInterval29440) (interval_append nodeTest 30080 30720 32000 nodeInterval30080 (interval_append nodeTest 30720 31360 32000 nodeInterval30720 nodeInterval31360))))) (interval_append nodeTest 32000 37120 42707 (interval_append nodeTest 32000 34560 37120 (interval_append nodeTest 32000 33280 34560 (interval_append nodeTest 32000 32640 33280 nodeInterval32000 nodeInterval32640) (interval_append nodeTest 33280 33920 34560 nodeInterval33280 nodeInterval33920)) (interval_append nodeTest 34560 35840 37120 (interval_append nodeTest 34560 35200 35840 nodeInterval34560 nodeInterval35200) (interval_append nodeTest 35840 36480 37120 nodeInterval35840 nodeInterval36480))) (interval_append nodeTest 37120 39680 42707 (interval_append nodeTest 37120 38400 39680 (interval_append nodeTest 37120 37760 38400 nodeInterval37120 nodeInterval37760) (interval_append nodeTest 38400 39040 39680 nodeInterval38400 nodeInterval39040)) (interval_append nodeTest 39680 40960 42707 (interval_append nodeTest 39680 40320 40960 nodeInterval39680 nodeInterval40320) (interval_append nodeTest 40960 41600 42707 nodeInterval40960 (interval_append nodeTest 41600 42240 42707 nodeInterval41600 nodeInterval42240)))))))
def root : Fin nodeCount := ⟨42706, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
