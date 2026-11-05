module
prelude
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest15Leaves
public import SmallSubsumedForest15Proof000
public import SmallSubsumedForest15Proof001
public import SmallSubsumedForest15Proof002
public import SmallSubsumedForest15Proof003
public import SmallSubsumedForest15Proof004
public import SmallSubsumedForest15Proof005
public import SmallSubsumedForest15Proof006
public import SmallSubsumedForest15Proof007
public import SmallSubsumedForest15Proof008
public import SmallSubsumedForest15Proof009
public import SmallSubsumedForest15Proof010
public import SmallSubsumedForest15Proof011
public import SmallSubsumedForest15Proof012
public import SmallSubsumedForest15Proof013
public import SmallSubsumedForest15Proof014
public import SmallSubsumedForest15Proof015
public import SmallSubsumedForest15Proof016
public import SmallSubsumedForest15Proof017
public import SmallSubsumedForest15Proof018
public import SmallSubsumedForest15Proof019
public import SmallSubsumedForest15Proof020
public import SmallSubsumedForest15Proof021
public import SmallSubsumedForest15Proof022
public import SmallSubsumedForest15Proof023
public import SmallSubsumedForest15Proof024
public import SmallSubsumedForest15Proof025
public import SmallSubsumedForest15Proof026
public import SmallSubsumedForest15Proof027
public import SmallSubsumedForest15Proof028
public import SmallSubsumedForest15Proof029
public import SmallSubsumedForest15Proof030
public import SmallSubsumedForest15Proof031
public import SmallSubsumedForest15Proof032
public import SmallSubsumedForest15Proof033
public import SmallSubsumedForest15Proof034
public import SmallSubsumedForest15Proof035
public import SmallSubsumedForest15Proof036
public import SmallSubsumedForest15Proof037
public import SmallSubsumedForest15Proof038
public import SmallSubsumedForest15Proof039
public import SmallSubsumedForest15Proof040
public import SmallSubsumedForest15Proof041
public import SmallSubsumedForest15Proof042
public import SmallSubsumedForest15Proof043
public import SmallSubsumedForest15Proof044
public import SmallSubsumedForest15Proof045
public import SmallSubsumedForest15Proof046
public import SmallSubsumedForest15Proof047
public import SmallSubsumedForest15Proof048
public import SmallSubsumedForest15Proof049
public import SmallSubsumedForest15Proof050
public import SmallSubsumedForest15Proof051
public import SmallSubsumedForest15Proof052
public import SmallSubsumedForest15Proof053
public import SmallSubsumedForest15Proof054
public import SmallSubsumedForest15Proof055
public import SmallSubsumedForest15Proof056
public import SmallSubsumedForest15Proof057
public import SmallSubsumedForest15Proof058
public import SmallSubsumedForest15Proof059
public import SmallSubsumedForest15Proof060
public import SmallSubsumedForest15Proof061
public import SmallSubsumedForest15Proof062
public import SmallSubsumedForest15Proof063
public import SmallSubsumedForest15Proof064
public import SmallSubsumedForest15Proof065
public import SmallSubsumedForest15Proof066
public import SmallSubsumedForest15Proof067
public import SmallSubsumedForest15Proof068
public import SmallSubsumedForest15Proof069
public import SmallSubsumedForest15Proof070
public import SmallSubsumedForest15Proof071
public import SmallSubsumedForest15Proof072
public import SmallSubsumedForest15Proof073
public import SmallSubsumedForest15Proof074
public import SmallSubsumedForest15Proof075
public import SmallSubsumedForest15Proof076
public import SmallSubsumedForest15Proof077
public import SmallSubsumedForest15Proof078
public import SmallSubsumedForest15Proof079
public import SmallSubsumedForest15Proof080
public import SmallSubsumedForest15Proof081
public import SmallSubsumedForest15Proof082
public import SmallSubsumedForest15Proof083
public import SmallSubsumedForest15Proof084
public import SmallSubsumedForest15Proof085
public import SmallSubsumedForest15Proof086
public import SmallSubsumedForest15Proof087
public import SmallSubsumedForest15Proof088
public import SmallSubsumedForest15Proof089
public import SmallSubsumedForest15Proof090
public import SmallSubsumedForest15Proof091
public import SmallSubsumedForest15Proof092
public import SmallSubsumedForest15Proof093
public import SmallSubsumedForest15Proof094
public import SmallSubsumedForest15Proof095
public import SmallSubsumedForest15Proof096
public import SmallSubsumedForest15Proof097
public import SmallSubsumedForest15Proof098
public import SmallSubsumedForest15Proof099
public import SmallSubsumedForest15Proof100
public import SmallSubsumedForest15Proof101
public import SmallSubsumedForest15Proof102
public import SmallSubsumedForest15Proof103
public import SmallSubsumedForest15Proof104
public import SmallSubsumedForest15Proof105
public import SmallSubsumedForest15Proof106
public import SmallSubsumedForest15Proof107
public import SmallSubsumedForest15Proof108
public import SmallSubsumedForest15Proof109
public import SmallSubsumedForest15Proof110
public import SmallSubsumedForest15Proof111
public import SmallSubsumedForest15Proof112
public import SmallSubsumedForest15Proof113
public import SmallSubsumedForest15Proof114
public import SmallSubsumedForest15Proof115
public import SmallSubsumedForest15Proof116
public import SmallSubsumedForest15Proof117
public import SmallSubsumedForest15Proof118
public import SmallSubsumedForest15Proof119
public import SmallSubsumedForest15Proof120
public import SmallSubsumedForest15Proof121
public import SmallSubsumedForest15Proof122
public import SmallSubsumedForest15Proof123
public import SmallSubsumedForest15Proof124

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 39680 79417 (interval_append nodeTest 0 19840 39680 (interval_append nodeTest 0 9600 19840 (interval_append nodeTest 0 4480 9600 (interval_append nodeTest 0 1920 4480 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 3200 4480 (interval_append nodeTest 1920 2560 3200 nodeInterval1920 nodeInterval2560) (interval_append nodeTest 3200 3840 4480 nodeInterval3200 nodeInterval3840))) (interval_append nodeTest 4480 7040 9600 (interval_append nodeTest 4480 5760 7040 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120) (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400)) (interval_append nodeTest 7040 8320 9600 (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680) (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)))) (interval_append nodeTest 9600 14720 19840 (interval_append nodeTest 9600 12160 14720 (interval_append nodeTest 9600 10880 12160 (interval_append nodeTest 9600 10240 10880 nodeInterval9600 nodeInterval10240) (interval_append nodeTest 10880 11520 12160 nodeInterval10880 nodeInterval11520)) (interval_append nodeTest 12160 13440 14720 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800) (interval_append nodeTest 13440 14080 14720 nodeInterval13440 nodeInterval14080))) (interval_append nodeTest 14720 17280 19840 (interval_append nodeTest 14720 16000 17280 (interval_append nodeTest 14720 15360 16000 nodeInterval14720 nodeInterval15360) (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)) (interval_append nodeTest 17280 18560 19840 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920) (interval_append nodeTest 18560 19200 19840 nodeInterval18560 nodeInterval19200))))) (interval_append nodeTest 19840 29440 39680 (interval_append nodeTest 19840 24320 29440 (interval_append nodeTest 19840 21760 24320 (interval_append nodeTest 19840 20480 21760 nodeInterval19840 (interval_append nodeTest 20480 21120 21760 nodeInterval20480 nodeInterval21120)) (interval_append nodeTest 21760 23040 24320 (interval_append nodeTest 21760 22400 23040 nodeInterval21760 nodeInterval22400) (interval_append nodeTest 23040 23680 24320 nodeInterval23040 nodeInterval23680))) (interval_append nodeTest 24320 26880 29440 (interval_append nodeTest 24320 25600 26880 (interval_append nodeTest 24320 24960 25600 nodeInterval24320 nodeInterval24960) (interval_append nodeTest 25600 26240 26880 nodeInterval25600 nodeInterval26240)) (interval_append nodeTest 26880 28160 29440 (interval_append nodeTest 26880 27520 28160 nodeInterval26880 nodeInterval27520) (interval_append nodeTest 28160 28800 29440 nodeInterval28160 nodeInterval28800)))) (interval_append nodeTest 29440 34560 39680 (interval_append nodeTest 29440 32000 34560 (interval_append nodeTest 29440 30720 32000 (interval_append nodeTest 29440 30080 30720 nodeInterval29440 nodeInterval30080) (interval_append nodeTest 30720 31360 32000 nodeInterval30720 nodeInterval31360)) (interval_append nodeTest 32000 33280 34560 (interval_append nodeTest 32000 32640 33280 nodeInterval32000 nodeInterval32640) (interval_append nodeTest 33280 33920 34560 nodeInterval33280 nodeInterval33920))) (interval_append nodeTest 34560 37120 39680 (interval_append nodeTest 34560 35840 37120 (interval_append nodeTest 34560 35200 35840 nodeInterval34560 nodeInterval35200) (interval_append nodeTest 35840 36480 37120 nodeInterval35840 nodeInterval36480)) (interval_append nodeTest 37120 38400 39680 (interval_append nodeTest 37120 37760 38400 nodeInterval37120 nodeInterval37760) (interval_append nodeTest 38400 39040 39680 nodeInterval38400 nodeInterval39040)))))) (interval_append nodeTest 39680 59520 79417 (interval_append nodeTest 39680 49280 59520 (interval_append nodeTest 39680 44160 49280 (interval_append nodeTest 39680 41600 44160 (interval_append nodeTest 39680 40320 41600 nodeInterval39680 (interval_append nodeTest 40320 40960 41600 nodeInterval40320 nodeInterval40960)) (interval_append nodeTest 41600 42880 44160 (interval_append nodeTest 41600 42240 42880 nodeInterval41600 nodeInterval42240) (interval_append nodeTest 42880 43520 44160 nodeInterval42880 nodeInterval43520))) (interval_append nodeTest 44160 46720 49280 (interval_append nodeTest 44160 45440 46720 (interval_append nodeTest 44160 44800 45440 nodeInterval44160 nodeInterval44800) (interval_append nodeTest 45440 46080 46720 nodeInterval45440 nodeInterval46080)) (interval_append nodeTest 46720 48000 49280 (interval_append nodeTest 46720 47360 48000 nodeInterval46720 nodeInterval47360) (interval_append nodeTest 48000 48640 49280 nodeInterval48000 nodeInterval48640)))) (interval_append nodeTest 49280 54400 59520 (interval_append nodeTest 49280 51840 54400 (interval_append nodeTest 49280 50560 51840 (interval_append nodeTest 49280 49920 50560 nodeInterval49280 nodeInterval49920) (interval_append nodeTest 50560 51200 51840 nodeInterval50560 nodeInterval51200)) (interval_append nodeTest 51840 53120 54400 (interval_append nodeTest 51840 52480 53120 nodeInterval51840 nodeInterval52480) (interval_append nodeTest 53120 53760 54400 nodeInterval53120 nodeInterval53760))) (interval_append nodeTest 54400 56960 59520 (interval_append nodeTest 54400 55680 56960 (interval_append nodeTest 54400 55040 55680 nodeInterval54400 nodeInterval55040) (interval_append nodeTest 55680 56320 56960 nodeInterval55680 nodeInterval56320)) (interval_append nodeTest 56960 58240 59520 (interval_append nodeTest 56960 57600 58240 nodeInterval56960 nodeInterval57600) (interval_append nodeTest 58240 58880 59520 nodeInterval58240 nodeInterval58880))))) (interval_append nodeTest 59520 69760 79417 (interval_append nodeTest 59520 64640 69760 (interval_append nodeTest 59520 62080 64640 (interval_append nodeTest 59520 60800 62080 (interval_append nodeTest 59520 60160 60800 nodeInterval59520 nodeInterval60160) (interval_append nodeTest 60800 61440 62080 nodeInterval60800 nodeInterval61440)) (interval_append nodeTest 62080 63360 64640 (interval_append nodeTest 62080 62720 63360 nodeInterval62080 nodeInterval62720) (interval_append nodeTest 63360 64000 64640 nodeInterval63360 nodeInterval64000))) (interval_append nodeTest 64640 67200 69760 (interval_append nodeTest 64640 65920 67200 (interval_append nodeTest 64640 65280 65920 nodeInterval64640 nodeInterval65280) (interval_append nodeTest 65920 66560 67200 nodeInterval65920 nodeInterval66560)) (interval_append nodeTest 67200 68480 69760 (interval_append nodeTest 67200 67840 68480 nodeInterval67200 nodeInterval67840) (interval_append nodeTest 68480 69120 69760 nodeInterval68480 nodeInterval69120)))) (interval_append nodeTest 69760 74880 79417 (interval_append nodeTest 69760 72320 74880 (interval_append nodeTest 69760 71040 72320 (interval_append nodeTest 69760 70400 71040 nodeInterval69760 nodeInterval70400) (interval_append nodeTest 71040 71680 72320 nodeInterval71040 nodeInterval71680)) (interval_append nodeTest 72320 73600 74880 (interval_append nodeTest 72320 72960 73600 nodeInterval72320 nodeInterval72960) (interval_append nodeTest 73600 74240 74880 nodeInterval73600 nodeInterval74240))) (interval_append nodeTest 74880 77440 79417 (interval_append nodeTest 74880 76160 77440 (interval_append nodeTest 74880 75520 76160 nodeInterval74880 nodeInterval75520) (interval_append nodeTest 76160 76800 77440 nodeInterval76160 nodeInterval76800)) (interval_append nodeTest 77440 78720 79417 (interval_append nodeTest 77440 78080 78720 nodeInterval77440 nodeInterval78080) (interval_append nodeTest 78720 79360 79417 nodeInterval78720 nodeInterval79360)))))))
def root : Fin nodeCount := ⟨79416, by decide⟩
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
  refine SubsumedClassification.complete_of_raw_closed_checks
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

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
