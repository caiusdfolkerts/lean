module
prelude
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0337Leaves
public import RootedSubsumedForest0337Proof000
public import RootedSubsumedForest0337Proof001
public import RootedSubsumedForest0337Proof002
public import RootedSubsumedForest0337Proof003
public import RootedSubsumedForest0337Proof004
public import RootedSubsumedForest0337Proof005
public import RootedSubsumedForest0337Proof006
public import RootedSubsumedForest0337Proof007
public import RootedSubsumedForest0337Proof008
public import RootedSubsumedForest0337Proof009
public import RootedSubsumedForest0337Proof010
public import RootedSubsumedForest0337Proof011
public import RootedSubsumedForest0337Proof012
public import RootedSubsumedForest0337Proof013
public import RootedSubsumedForest0337Proof014
public import RootedSubsumedForest0337Proof015
public import RootedSubsumedForest0337Proof016
public import RootedSubsumedForest0337Proof017
public import RootedSubsumedForest0337Proof018
public import RootedSubsumedForest0337Proof019
public import RootedSubsumedForest0337Proof020
public import RootedSubsumedForest0337Proof021
public import RootedSubsumedForest0337Proof022
public import RootedSubsumedForest0337Proof023
public import RootedSubsumedForest0337Proof024
public import RootedSubsumedForest0337Proof025
public import RootedSubsumedForest0337Proof026
public import RootedSubsumedForest0337Proof027
public import RootedSubsumedForest0337Proof028
public import RootedSubsumedForest0337Proof029
public import RootedSubsumedForest0337Proof030
public import RootedSubsumedForest0337Proof031
public import RootedSubsumedForest0337Proof032
public import RootedSubsumedForest0337Proof033
public import RootedSubsumedForest0337Proof034
public import RootedSubsumedForest0337Proof035
public import RootedSubsumedForest0337Proof036
public import RootedSubsumedForest0337Proof037
public import RootedSubsumedForest0337Proof038
public import RootedSubsumedForest0337Proof039
public import RootedSubsumedForest0337Proof040
public import RootedSubsumedForest0337Proof041
public import RootedSubsumedForest0337Proof042
public import RootedSubsumedForest0337Proof043
public import RootedSubsumedForest0337Proof044
public import RootedSubsumedForest0337Proof045
public import RootedSubsumedForest0337Proof046
public import RootedSubsumedForest0337Proof047
public import RootedSubsumedForest0337Proof048
public import RootedSubsumedForest0337Proof049
public import RootedSubsumedForest0337Proof050
public import RootedSubsumedForest0337Proof051
public import RootedSubsumedForest0337Proof052
public import RootedSubsumedForest0337Proof053
public import RootedSubsumedForest0337Proof054
public import RootedSubsumedForest0337Proof055
public import RootedSubsumedForest0337Proof056
public import RootedSubsumedForest0337Proof057
public import RootedSubsumedForest0337Proof058
public import RootedSubsumedForest0337Proof059
public import RootedSubsumedForest0337Proof060
public import RootedSubsumedForest0337Proof061
public import RootedSubsumedForest0337Proof062
public import RootedSubsumedForest0337Proof063
public import RootedSubsumedForest0337Proof064
public import RootedSubsumedForest0337Proof065

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 21120 41895 (interval_append nodeTest 0 10240 21120 (interval_append nodeTest 0 5120 10240 (interval_append nodeTest 0 2560 5120 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5120 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480))) (interval_append nodeTest 5120 7680 10240 (interval_append nodeTest 5120 6400 7680 (interval_append nodeTest 5120 5760 6400 nodeInterval5120 nodeInterval5760) (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)) (interval_append nodeTest 7680 8960 10240 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320) (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600)))) (interval_append nodeTest 10240 15360 21120 (interval_append nodeTest 10240 12800 15360 (interval_append nodeTest 10240 11520 12800 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880) (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160)) (interval_append nodeTest 12800 14080 15360 (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440) (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720))) (interval_append nodeTest 15360 17920 21120 (interval_append nodeTest 15360 16640 17920 (interval_append nodeTest 15360 16000 16640 nodeInterval15360 nodeInterval16000) (interval_append nodeTest 16640 17280 17920 nodeInterval16640 nodeInterval17280)) (interval_append nodeTest 17920 19200 21120 (interval_append nodeTest 17920 18560 19200 nodeInterval17920 nodeInterval18560) (interval_append nodeTest 19200 19840 21120 nodeInterval19200 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480)))))) (interval_append nodeTest 21120 31360 41895 (interval_append nodeTest 21120 26240 31360 (interval_append nodeTest 21120 23680 26240 (interval_append nodeTest 21120 22400 23680 (interval_append nodeTest 21120 21760 22400 nodeInterval21120 nodeInterval21760) (interval_append nodeTest 22400 23040 23680 nodeInterval22400 nodeInterval23040)) (interval_append nodeTest 23680 24960 26240 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320) (interval_append nodeTest 24960 25600 26240 nodeInterval24960 nodeInterval25600))) (interval_append nodeTest 26240 28800 31360 (interval_append nodeTest 26240 27520 28800 (interval_append nodeTest 26240 26880 27520 nodeInterval26240 nodeInterval26880) (interval_append nodeTest 27520 28160 28800 nodeInterval27520 nodeInterval28160)) (interval_append nodeTest 28800 30080 31360 (interval_append nodeTest 28800 29440 30080 nodeInterval28800 nodeInterval29440) (interval_append nodeTest 30080 30720 31360 nodeInterval30080 nodeInterval30720)))) (interval_append nodeTest 31360 36480 41895 (interval_append nodeTest 31360 33920 36480 (interval_append nodeTest 31360 32640 33920 (interval_append nodeTest 31360 32000 32640 nodeInterval31360 nodeInterval32000) (interval_append nodeTest 32640 33280 33920 nodeInterval32640 nodeInterval33280)) (interval_append nodeTest 33920 35200 36480 (interval_append nodeTest 33920 34560 35200 nodeInterval33920 nodeInterval34560) (interval_append nodeTest 35200 35840 36480 nodeInterval35200 nodeInterval35840))) (interval_append nodeTest 36480 39040 41895 (interval_append nodeTest 36480 37760 39040 (interval_append nodeTest 36480 37120 37760 nodeInterval36480 nodeInterval37120) (interval_append nodeTest 37760 38400 39040 nodeInterval37760 nodeInterval38400)) (interval_append nodeTest 39040 40320 41895 (interval_append nodeTest 39040 39680 40320 nodeInterval39040 nodeInterval39680) (interval_append nodeTest 40320 40960 41895 nodeInterval40320 (interval_append nodeTest 40960 41600 41895 nodeInterval40960 nodeInterval41600)))))))
def root : Fin nodeCount := ⟨41894, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
