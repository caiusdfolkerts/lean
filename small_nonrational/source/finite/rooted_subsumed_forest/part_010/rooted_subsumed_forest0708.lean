module
prelude
public import RootedSixBase02GrowthCache
public import RootedSixBase02FastWords
public import SubsumedClassification
public import RootedSubsumedForest0708Leaves
public import RootedSubsumedForest0708Proof000
public import RootedSubsumedForest0708Proof001
public import RootedSubsumedForest0708Proof002
public import RootedSubsumedForest0708Proof003
public import RootedSubsumedForest0708Proof004
public import RootedSubsumedForest0708Proof005
public import RootedSubsumedForest0708Proof006
public import RootedSubsumedForest0708Proof007
public import RootedSubsumedForest0708Proof008
public import RootedSubsumedForest0708Proof009
public import RootedSubsumedForest0708Proof010
public import RootedSubsumedForest0708Proof011
public import RootedSubsumedForest0708Proof012
public import RootedSubsumedForest0708Proof013
public import RootedSubsumedForest0708Proof014
public import RootedSubsumedForest0708Proof015
public import RootedSubsumedForest0708Proof016
public import RootedSubsumedForest0708Proof017
public import RootedSubsumedForest0708Proof018
public import RootedSubsumedForest0708Proof019
public import RootedSubsumedForest0708Proof020
public import RootedSubsumedForest0708Proof021
public import RootedSubsumedForest0708Proof022
public import RootedSubsumedForest0708Proof023
public import RootedSubsumedForest0708Proof024
public import RootedSubsumedForest0708Proof025
public import RootedSubsumedForest0708Proof026
public import RootedSubsumedForest0708Proof027
public import RootedSubsumedForest0708Proof028
public import RootedSubsumedForest0708Proof029
public import RootedSubsumedForest0708Proof030
public import RootedSubsumedForest0708Proof031
public import RootedSubsumedForest0708Proof032
public import RootedSubsumedForest0708Proof033
public import RootedSubsumedForest0708Proof034
public import RootedSubsumedForest0708Proof035
public import RootedSubsumedForest0708Proof036
public import RootedSubsumedForest0708Proof037
public import RootedSubsumedForest0708Proof038
public import RootedSubsumedForest0708Proof039
public import RootedSubsumedForest0708Proof040
public import RootedSubsumedForest0708Proof041
public import RootedSubsumedForest0708Proof042
public import RootedSubsumedForest0708Proof043
public import RootedSubsumedForest0708Proof044
public import RootedSubsumedForest0708Proof045
public import RootedSubsumedForest0708Proof046
public import RootedSubsumedForest0708Proof047
public import RootedSubsumedForest0708Proof048
public import RootedSubsumedForest0708Proof049
public import RootedSubsumedForest0708Proof050
public import RootedSubsumedForest0708Proof051
public import RootedSubsumedForest0708Proof052
public import RootedSubsumedForest0708Proof053
public import RootedSubsumedForest0708Proof054
public import RootedSubsumedForest0708Proof055
public import RootedSubsumedForest0708Proof056
public import RootedSubsumedForest0708Proof057
public import RootedSubsumedForest0708Proof058
public import RootedSubsumedForest0708Proof059
public import RootedSubsumedForest0708Proof060
public import RootedSubsumedForest0708Proof061
public import RootedSubsumedForest0708Proof062
public import RootedSubsumedForest0708Proof063
public import RootedSubsumedForest0708Proof064
public import RootedSubsumedForest0708Proof065
public import RootedSubsumedForest0708Proof066
public import RootedSubsumedForest0708Proof067
public import RootedSubsumedForest0708Proof068
public import RootedSubsumedForest0708Proof069
public import RootedSubsumedForest0708Proof070
public import RootedSubsumedForest0708Proof071
public import RootedSubsumedForest0708Proof072
public import RootedSubsumedForest0708Proof073
public import RootedSubsumedForest0708Proof074
public import RootedSubsumedForest0708Proof075
public import RootedSubsumedForest0708Proof076
public import RootedSubsumedForest0708Proof077
public import RootedSubsumedForest0708Proof078
public import RootedSubsumedForest0708Proof079
public import RootedSubsumedForest0708Proof080
public import RootedSubsumedForest0708Proof081
public import RootedSubsumedForest0708Proof082
public import RootedSubsumedForest0708Proof083
public import RootedSubsumedForest0708Proof084
public import RootedSubsumedForest0708Proof085
public import RootedSubsumedForest0708Proof086
public import RootedSubsumedForest0708Proof087
public import RootedSubsumedForest0708Proof088
public import RootedSubsumedForest0708Proof089
public import RootedSubsumedForest0708Proof090
public import RootedSubsumedForest0708Proof091
public import RootedSubsumedForest0708Proof092
public import RootedSubsumedForest0708Proof093
public import RootedSubsumedForest0708Proof094

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 30080 60366 (interval_append nodeTest 0 14720 30080 (interval_append nodeTest 0 7040 14720 (interval_append nodeTest 0 3200 7040 (interval_append nodeTest 0 1280 3200 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 3200 nodeInterval1280 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560))) (interval_append nodeTest 3200 5120 7040 (interval_append nodeTest 3200 3840 5120 nodeInterval3200 (interval_append nodeTest 3840 4480 5120 nodeInterval3840 nodeInterval4480)) (interval_append nodeTest 5120 5760 7040 nodeInterval5120 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)))) (interval_append nodeTest 7040 10880 14720 (interval_append nodeTest 7040 8960 10880 (interval_append nodeTest 7040 7680 8960 nodeInterval7040 (interval_append nodeTest 7680 8320 8960 nodeInterval7680 nodeInterval8320)) (interval_append nodeTest 8960 9600 10880 nodeInterval8960 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240))) (interval_append nodeTest 10880 12800 14720 (interval_append nodeTest 10880 11520 12800 nodeInterval10880 (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160)) (interval_append nodeTest 12800 13440 14720 nodeInterval12800 (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080))))) (interval_append nodeTest 14720 22400 30080 (interval_append nodeTest 14720 18560 22400 (interval_append nodeTest 14720 16640 18560 (interval_append nodeTest 14720 15360 16640 nodeInterval14720 (interval_append nodeTest 15360 16000 16640 nodeInterval15360 nodeInterval16000)) (interval_append nodeTest 16640 17280 18560 nodeInterval16640 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920))) (interval_append nodeTest 18560 20480 22400 (interval_append nodeTest 18560 19200 20480 nodeInterval18560 (interval_append nodeTest 19200 19840 20480 nodeInterval19200 nodeInterval19840)) (interval_append nodeTest 20480 21120 22400 nodeInterval20480 (interval_append nodeTest 21120 21760 22400 nodeInterval21120 nodeInterval21760)))) (interval_append nodeTest 22400 26240 30080 (interval_append nodeTest 22400 24320 26240 (interval_append nodeTest 22400 23040 24320 nodeInterval22400 (interval_append nodeTest 23040 23680 24320 nodeInterval23040 nodeInterval23680)) (interval_append nodeTest 24320 24960 26240 nodeInterval24320 (interval_append nodeTest 24960 25600 26240 nodeInterval24960 nodeInterval25600))) (interval_append nodeTest 26240 28160 30080 (interval_append nodeTest 26240 26880 28160 nodeInterval26240 (interval_append nodeTest 26880 27520 28160 nodeInterval26880 nodeInterval27520)) (interval_append nodeTest 28160 28800 30080 nodeInterval28160 (interval_append nodeTest 28800 29440 30080 nodeInterval28800 nodeInterval29440)))))) (interval_append nodeTest 30080 45440 60366 (interval_append nodeTest 30080 37760 45440 (interval_append nodeTest 30080 33920 37760 (interval_append nodeTest 30080 32000 33920 (interval_append nodeTest 30080 30720 32000 nodeInterval30080 (interval_append nodeTest 30720 31360 32000 nodeInterval30720 nodeInterval31360)) (interval_append nodeTest 32000 32640 33920 nodeInterval32000 (interval_append nodeTest 32640 33280 33920 nodeInterval32640 nodeInterval33280))) (interval_append nodeTest 33920 35840 37760 (interval_append nodeTest 33920 34560 35840 nodeInterval33920 (interval_append nodeTest 34560 35200 35840 nodeInterval34560 nodeInterval35200)) (interval_append nodeTest 35840 36480 37760 nodeInterval35840 (interval_append nodeTest 36480 37120 37760 nodeInterval36480 nodeInterval37120)))) (interval_append nodeTest 37760 41600 45440 (interval_append nodeTest 37760 39680 41600 (interval_append nodeTest 37760 38400 39680 nodeInterval37760 (interval_append nodeTest 38400 39040 39680 nodeInterval38400 nodeInterval39040)) (interval_append nodeTest 39680 40320 41600 nodeInterval39680 (interval_append nodeTest 40320 40960 41600 nodeInterval40320 nodeInterval40960))) (interval_append nodeTest 41600 43520 45440 (interval_append nodeTest 41600 42240 43520 nodeInterval41600 (interval_append nodeTest 42240 42880 43520 nodeInterval42240 nodeInterval42880)) (interval_append nodeTest 43520 44160 45440 nodeInterval43520 (interval_append nodeTest 44160 44800 45440 nodeInterval44160 nodeInterval44800))))) (interval_append nodeTest 45440 53120 60366 (interval_append nodeTest 45440 49280 53120 (interval_append nodeTest 45440 47360 49280 (interval_append nodeTest 45440 46080 47360 nodeInterval45440 (interval_append nodeTest 46080 46720 47360 nodeInterval46080 nodeInterval46720)) (interval_append nodeTest 47360 48000 49280 nodeInterval47360 (interval_append nodeTest 48000 48640 49280 nodeInterval48000 nodeInterval48640))) (interval_append nodeTest 49280 51200 53120 (interval_append nodeTest 49280 49920 51200 nodeInterval49280 (interval_append nodeTest 49920 50560 51200 nodeInterval49920 nodeInterval50560)) (interval_append nodeTest 51200 51840 53120 nodeInterval51200 (interval_append nodeTest 51840 52480 53120 nodeInterval51840 nodeInterval52480)))) (interval_append nodeTest 53120 56960 60366 (interval_append nodeTest 53120 55040 56960 (interval_append nodeTest 53120 53760 55040 nodeInterval53120 (interval_append nodeTest 53760 54400 55040 nodeInterval53760 nodeInterval54400)) (interval_append nodeTest 55040 55680 56960 nodeInterval55040 (interval_append nodeTest 55680 56320 56960 nodeInterval55680 nodeInterval56320))) (interval_append nodeTest 56960 58880 60366 (interval_append nodeTest 56960 57600 58880 nodeInterval56960 (interval_append nodeTest 57600 58240 58880 nodeInterval57600 nodeInterval58240)) (interval_append nodeTest 58880 59520 60366 nodeInterval58880 (interval_append nodeTest 59520 60160 60366 nodeInterval59520 nodeInterval60160)))))))
def root : Fin nodeCount := ⟨60365, by decide⟩
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
