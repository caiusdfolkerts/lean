module
prelude
public import RootedSixBase00GrowthCache
public import RootedSixBase00FastWords
public import SubsumedClassification
public import RootedSubsumedForest0338Leaves
public import RootedSubsumedForest0338Proof000
public import RootedSubsumedForest0338Proof001
public import RootedSubsumedForest0338Proof002
public import RootedSubsumedForest0338Proof003
public import RootedSubsumedForest0338Proof004
public import RootedSubsumedForest0338Proof005
public import RootedSubsumedForest0338Proof006
public import RootedSubsumedForest0338Proof007
public import RootedSubsumedForest0338Proof008
public import RootedSubsumedForest0338Proof009
public import RootedSubsumedForest0338Proof010
public import RootedSubsumedForest0338Proof011
public import RootedSubsumedForest0338Proof012
public import RootedSubsumedForest0338Proof013
public import RootedSubsumedForest0338Proof014
public import RootedSubsumedForest0338Proof015
public import RootedSubsumedForest0338Proof016
public import RootedSubsumedForest0338Proof017
public import RootedSubsumedForest0338Proof018
public import RootedSubsumedForest0338Proof019
public import RootedSubsumedForest0338Proof020
public import RootedSubsumedForest0338Proof021
public import RootedSubsumedForest0338Proof022
public import RootedSubsumedForest0338Proof023
public import RootedSubsumedForest0338Proof024
public import RootedSubsumedForest0338Proof025
public import RootedSubsumedForest0338Proof026
public import RootedSubsumedForest0338Proof027
public import RootedSubsumedForest0338Proof028
public import RootedSubsumedForest0338Proof029
public import RootedSubsumedForest0338Proof030
public import RootedSubsumedForest0338Proof031
public import RootedSubsumedForest0338Proof032
public import RootedSubsumedForest0338Proof033
public import RootedSubsumedForest0338Proof034
public import RootedSubsumedForest0338Proof035
public import RootedSubsumedForest0338Proof036
public import RootedSubsumedForest0338Proof037
public import RootedSubsumedForest0338Proof038
public import RootedSubsumedForest0338Proof039
public import RootedSubsumedForest0338Proof040
public import RootedSubsumedForest0338Proof041
public import RootedSubsumedForest0338Proof042
public import RootedSubsumedForest0338Proof043
public import RootedSubsumedForest0338Proof044
public import RootedSubsumedForest0338Proof045
public import RootedSubsumedForest0338Proof046
public import RootedSubsumedForest0338Proof047
public import RootedSubsumedForest0338Proof048
public import RootedSubsumedForest0338Proof049
public import RootedSubsumedForest0338Proof050
public import RootedSubsumedForest0338Proof051
public import RootedSubsumedForest0338Proof052
public import RootedSubsumedForest0338Proof053
public import RootedSubsumedForest0338Proof054
public import RootedSubsumedForest0338Proof055
public import RootedSubsumedForest0338Proof056
public import RootedSubsumedForest0338Proof057
public import RootedSubsumedForest0338Proof058
public import RootedSubsumedForest0338Proof059
public import RootedSubsumedForest0338Proof060
public import RootedSubsumedForest0338Proof061
public import RootedSubsumedForest0338Proof062
public import RootedSubsumedForest0338Proof063
public import RootedSubsumedForest0338Proof064
public import RootedSubsumedForest0338Proof065
public import RootedSubsumedForest0338Proof066
public import RootedSubsumedForest0338Proof067
public import RootedSubsumedForest0338Proof068
public import RootedSubsumedForest0338Proof069
public import RootedSubsumedForest0338Proof070
public import RootedSubsumedForest0338Proof071
public import RootedSubsumedForest0338Proof072
public import RootedSubsumedForest0338Proof073
public import RootedSubsumedForest0338Proof074
public import RootedSubsumedForest0338Proof075
public import RootedSubsumedForest0338Proof076
public import RootedSubsumedForest0338Proof077
public import RootedSubsumedForest0338Proof078
public import RootedSubsumedForest0338Proof079
public import RootedSubsumedForest0338Proof080
public import RootedSubsumedForest0338Proof081
public import RootedSubsumedForest0338Proof082
public import RootedSubsumedForest0338Proof083
public import RootedSubsumedForest0338Proof084
public import RootedSubsumedForest0338Proof085
public import RootedSubsumedForest0338Proof086
public import RootedSubsumedForest0338Proof087
public import RootedSubsumedForest0338Proof088
public import RootedSubsumedForest0338Proof089
public import RootedSubsumedForest0338Proof090

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 28800 58209 (interval_append nodeTest 0 14080 28800 (interval_append nodeTest 0 7040 14080 (interval_append nodeTest 0 3200 7040 (interval_append nodeTest 0 1280 3200 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 3200 nodeInterval1280 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560))) (interval_append nodeTest 3200 5120 7040 (interval_append nodeTest 3200 3840 5120 nodeInterval3200 (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480)) (interval_append nodeTest 5120 5760 7040 nodeInterval5120 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)))) (interval_append nodeTest 7040 10240 14080 (interval_append nodeTest 7040 8320 10240 (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680) (interval_append nodeTest 8320 8960 10240 nodeInterval8320 (interval_append nodeTest 8960 9600 10240 nodeInterval8960 nodeInterval9600))) (interval_append nodeTest 10240 12160 14080 (interval_append nodeTest 10240 10880 12160 nodeInterval10240 (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520)) (interval_append nodeTest 12160 12800 14080 nodeInterval12160 (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440))))) (interval_append nodeTest 14080 21120 28800 (interval_append nodeTest 14080 17280 21120 (interval_append nodeTest 14080 15360 17280 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720) (interval_append nodeTest 15360 16000 17280 nodeInterval15360 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640))) (interval_append nodeTest 17280 19200 21120 (interval_append nodeTest 17280 17920 19200 nodeInterval17280 (interval_append nodeTest 17920 18560 19200 nodeInterval17920 nodeInterval18560)) (interval_append nodeTest 19200 19840 21120 nodeInterval19200 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480)))) (interval_append nodeTest 21120 24960 28800 (interval_append nodeTest 21120 23040 24960 (interval_append nodeTest 21120 21760 23040 nodeInterval21120 (interval_append nodeTest 21760 22400 23040 nodeInterval21760 nodeInterval22400)) (interval_append nodeTest 23040 23680 24960 nodeInterval23040 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320))) (interval_append nodeTest 24960 26880 28800 (interval_append nodeTest 24960 25600 26880 nodeInterval24960 (interval_append nodeTest 25600 26240 26880 nodeInterval25600 nodeInterval26240)) (interval_append nodeTest 26880 27520 28800 nodeInterval26880 (interval_append nodeTest 27520 28160 28800 nodeInterval27520 nodeInterval28160)))))) (interval_append nodeTest 28800 43520 58209 (interval_append nodeTest 28800 35840 43520 (interval_append nodeTest 28800 32000 35840 (interval_append nodeTest 28800 30080 32000 (interval_append nodeTest 28800 29440 30080 nodeInterval28800 nodeInterval29440) (interval_append nodeTest 30080 30720 32000 nodeInterval30080 (interval_append nodeTest 30720 31360 32000 nodeInterval30720 nodeInterval31360))) (interval_append nodeTest 32000 33920 35840 (interval_append nodeTest 32000 32640 33920 nodeInterval32000 (interval_append nodeTest 32640 33280 33920 nodeInterval32640 nodeInterval33280)) (interval_append nodeTest 33920 34560 35840 nodeInterval33920 (interval_append nodeTest 34560 35200 35840 nodeInterval34560 nodeInterval35200)))) (interval_append nodeTest 35840 39680 43520 (interval_append nodeTest 35840 37760 39680 (interval_append nodeTest 35840 36480 37760 nodeInterval35840 (interval_append nodeTest 36480 37120 37760 nodeInterval36480 nodeInterval37120)) (interval_append nodeTest 37760 38400 39680 nodeInterval37760 (interval_append nodeTest 38400 39040 39680 nodeInterval38400 nodeInterval39040))) (interval_append nodeTest 39680 41600 43520 (interval_append nodeTest 39680 40320 41600 nodeInterval39680 (interval_append nodeTest 40320 40960 41600 nodeInterval40320 nodeInterval40960)) (interval_append nodeTest 41600 42240 43520 nodeInterval41600 (interval_append nodeTest 42240 42880 43520 nodeInterval42240 nodeInterval42880))))) (interval_append nodeTest 43520 50560 58209 (interval_append nodeTest 43520 46720 50560 (interval_append nodeTest 43520 44800 46720 (interval_append nodeTest 43520 44160 44800 nodeInterval43520 nodeInterval44160) (interval_append nodeTest 44800 45440 46720 nodeInterval44800 (interval_append nodeTest 45440 46080 46720 nodeInterval45440 nodeInterval46080))) (interval_append nodeTest 46720 48640 50560 (interval_append nodeTest 46720 47360 48640 nodeInterval46720 (interval_append nodeTest 47360 48000 48640 nodeInterval47360 nodeInterval48000)) (interval_append nodeTest 48640 49280 50560 nodeInterval48640 (interval_append nodeTest 49280 49920 50560 nodeInterval49280 nodeInterval49920)))) (interval_append nodeTest 50560 54400 58209 (interval_append nodeTest 50560 52480 54400 (interval_append nodeTest 50560 51200 52480 nodeInterval50560 (interval_append nodeTest 51200 51840 52480 nodeInterval51200 nodeInterval51840)) (interval_append nodeTest 52480 53120 54400 nodeInterval52480 (interval_append nodeTest 53120 53760 54400 nodeInterval53120 nodeInterval53760))) (interval_append nodeTest 54400 56320 58209 (interval_append nodeTest 54400 55040 56320 nodeInterval54400 (interval_append nodeTest 55040 55680 56320 nodeInterval55040 nodeInterval55680)) (interval_append nodeTest 56320 56960 58209 nodeInterval56320 (interval_append nodeTest 56960 57600 58209 nodeInterval56960 nodeInterval57600)))))))
def root : Fin nodeCount := ⟨58208, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
