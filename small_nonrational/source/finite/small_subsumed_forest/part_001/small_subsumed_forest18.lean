module
prelude
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest18Leaves
public import SmallSubsumedForest18Proof000
public import SmallSubsumedForest18Proof001
public import SmallSubsumedForest18Proof002
public import SmallSubsumedForest18Proof003
public import SmallSubsumedForest18Proof004
public import SmallSubsumedForest18Proof005
public import SmallSubsumedForest18Proof006
public import SmallSubsumedForest18Proof007
public import SmallSubsumedForest18Proof008
public import SmallSubsumedForest18Proof009
public import SmallSubsumedForest18Proof010
public import SmallSubsumedForest18Proof011
public import SmallSubsumedForest18Proof012
public import SmallSubsumedForest18Proof013
public import SmallSubsumedForest18Proof014
public import SmallSubsumedForest18Proof015
public import SmallSubsumedForest18Proof016
public import SmallSubsumedForest18Proof017
public import SmallSubsumedForest18Proof018
public import SmallSubsumedForest18Proof019
public import SmallSubsumedForest18Proof020
public import SmallSubsumedForest18Proof021
public import SmallSubsumedForest18Proof022
public import SmallSubsumedForest18Proof023
public import SmallSubsumedForest18Proof024
public import SmallSubsumedForest18Proof025
public import SmallSubsumedForest18Proof026
public import SmallSubsumedForest18Proof027
public import SmallSubsumedForest18Proof028
public import SmallSubsumedForest18Proof029
public import SmallSubsumedForest18Proof030
public import SmallSubsumedForest18Proof031
public import SmallSubsumedForest18Proof032
public import SmallSubsumedForest18Proof033
public import SmallSubsumedForest18Proof034
public import SmallSubsumedForest18Proof035
public import SmallSubsumedForest18Proof036
public import SmallSubsumedForest18Proof037
public import SmallSubsumedForest18Proof038
public import SmallSubsumedForest18Proof039
public import SmallSubsumedForest18Proof040
public import SmallSubsumedForest18Proof041
public import SmallSubsumedForest18Proof042
public import SmallSubsumedForest18Proof043
public import SmallSubsumedForest18Proof044
public import SmallSubsumedForest18Proof045
public import SmallSubsumedForest18Proof046
public import SmallSubsumedForest18Proof047
public import SmallSubsumedForest18Proof048
public import SmallSubsumedForest18Proof049
public import SmallSubsumedForest18Proof050
public import SmallSubsumedForest18Proof051
public import SmallSubsumedForest18Proof052
public import SmallSubsumedForest18Proof053
public import SmallSubsumedForest18Proof054
public import SmallSubsumedForest18Proof055
public import SmallSubsumedForest18Proof056
public import SmallSubsumedForest18Proof057
public import SmallSubsumedForest18Proof058
public import SmallSubsumedForest18Proof059
public import SmallSubsumedForest18Proof060
public import SmallSubsumedForest18Proof061
public import SmallSubsumedForest18Proof062
public import SmallSubsumedForest18Proof063
public import SmallSubsumedForest18Proof064
public import SmallSubsumedForest18Proof065
public import SmallSubsumedForest18Proof066
public import SmallSubsumedForest18Proof067
public import SmallSubsumedForest18Proof068
public import SmallSubsumedForest18Proof069
public import SmallSubsumedForest18Proof070
public import SmallSubsumedForest18Proof071
public import SmallSubsumedForest18Proof072
public import SmallSubsumedForest18Proof073
public import SmallSubsumedForest18Proof074
public import SmallSubsumedForest18Proof075
public import SmallSubsumedForest18Proof076
public import SmallSubsumedForest18Proof077
public import SmallSubsumedForest18Proof078
public import SmallSubsumedForest18Proof079
public import SmallSubsumedForest18Proof080
public import SmallSubsumedForest18Proof081
public import SmallSubsumedForest18Proof082
public import SmallSubsumedForest18Proof083
public import SmallSubsumedForest18Proof084
public import SmallSubsumedForest18Proof085
public import SmallSubsumedForest18Proof086
public import SmallSubsumedForest18Proof087
public import SmallSubsumedForest18Proof088
public import SmallSubsumedForest18Proof089
public import SmallSubsumedForest18Proof090
public import SmallSubsumedForest18Proof091
public import SmallSubsumedForest18Proof092
public import SmallSubsumedForest18Proof093
public import SmallSubsumedForest18Proof094
public import SmallSubsumedForest18Proof095
public import SmallSubsumedForest18Proof096
public import SmallSubsumedForest18Proof097
public import SmallSubsumedForest18Proof098

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 31360 62769 (interval_append nodeTest 0 15360 31360 (interval_append nodeTest 0 7680 15360 (interval_append nodeTest 0 3840 7680 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 7680 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 6400 7680 nodeInterval5760 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)))) (interval_append nodeTest 7680 11520 15360 (interval_append nodeTest 7680 9600 11520 (interval_append nodeTest 7680 8320 9600 nodeInterval7680 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))) (interval_append nodeTest 11520 13440 15360 (interval_append nodeTest 11520 12160 13440 nodeInterval11520 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800)) (interval_append nodeTest 13440 14080 15360 nodeInterval13440 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720))))) (interval_append nodeTest 15360 23040 31360 (interval_append nodeTest 15360 19200 23040 (interval_append nodeTest 15360 17280 19200 (interval_append nodeTest 15360 16000 17280 nodeInterval15360 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)) (interval_append nodeTest 17280 17920 19200 nodeInterval17280 (interval_append nodeTest 17920 18560 19200 nodeInterval17920 nodeInterval18560))) (interval_append nodeTest 19200 21120 23040 (interval_append nodeTest 19200 19840 21120 nodeInterval19200 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480)) (interval_append nodeTest 21120 21760 23040 nodeInterval21120 (interval_append nodeTest 21760 22400 23040 nodeInterval21760 nodeInterval22400)))) (interval_append nodeTest 23040 26880 31360 (interval_append nodeTest 23040 24960 26880 (interval_append nodeTest 23040 23680 24960 nodeInterval23040 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320)) (interval_append nodeTest 24960 25600 26880 nodeInterval24960 (interval_append nodeTest 25600 26240 26880 nodeInterval25600 nodeInterval26240))) (interval_append nodeTest 26880 28800 31360 (interval_append nodeTest 26880 27520 28800 nodeInterval26880 (interval_append nodeTest 27520 28160 28800 nodeInterval27520 nodeInterval28160)) (interval_append nodeTest 28800 30080 31360 (interval_append nodeTest 28800 29440 30080 nodeInterval28800 nodeInterval29440) (interval_append nodeTest 30080 30720 31360 nodeInterval30080 nodeInterval30720)))))) (interval_append nodeTest 31360 47360 62769 (interval_append nodeTest 31360 39040 47360 (interval_append nodeTest 31360 35200 39040 (interval_append nodeTest 31360 33280 35200 (interval_append nodeTest 31360 32000 33280 nodeInterval31360 (interval_append nodeTest 32000 32640 33280 nodeInterval32000 nodeInterval32640)) (interval_append nodeTest 33280 33920 35200 nodeInterval33280 (interval_append nodeTest 33920 34560 35200 nodeInterval33920 nodeInterval34560))) (interval_append nodeTest 35200 37120 39040 (interval_append nodeTest 35200 35840 37120 nodeInterval35200 (interval_append nodeTest 35840 36480 37120 nodeInterval35840 nodeInterval36480)) (interval_append nodeTest 37120 37760 39040 nodeInterval37120 (interval_append nodeTest 37760 38400 39040 nodeInterval37760 nodeInterval38400)))) (interval_append nodeTest 39040 42880 47360 (interval_append nodeTest 39040 40960 42880 (interval_append nodeTest 39040 39680 40960 nodeInterval39040 (interval_append nodeTest 39680 40320 40960 nodeInterval39680 nodeInterval40320)) (interval_append nodeTest 40960 41600 42880 nodeInterval40960 (interval_append nodeTest 41600 42240 42880 nodeInterval41600 nodeInterval42240))) (interval_append nodeTest 42880 44800 47360 (interval_append nodeTest 42880 43520 44800 nodeInterval42880 (interval_append nodeTest 43520 44160 44800 nodeInterval43520 nodeInterval44160)) (interval_append nodeTest 44800 46080 47360 (interval_append nodeTest 44800 45440 46080 nodeInterval44800 nodeInterval45440) (interval_append nodeTest 46080 46720 47360 nodeInterval46080 nodeInterval46720))))) (interval_append nodeTest 47360 55040 62769 (interval_append nodeTest 47360 51200 55040 (interval_append nodeTest 47360 49280 51200 (interval_append nodeTest 47360 48000 49280 nodeInterval47360 (interval_append nodeTest 48000 48640 49280 nodeInterval48000 nodeInterval48640)) (interval_append nodeTest 49280 49920 51200 nodeInterval49280 (interval_append nodeTest 49920 50560 51200 nodeInterval49920 nodeInterval50560))) (interval_append nodeTest 51200 53120 55040 (interval_append nodeTest 51200 51840 53120 nodeInterval51200 (interval_append nodeTest 51840 52480 53120 nodeInterval51840 nodeInterval52480)) (interval_append nodeTest 53120 53760 55040 nodeInterval53120 (interval_append nodeTest 53760 54400 55040 nodeInterval53760 nodeInterval54400)))) (interval_append nodeTest 55040 58880 62769 (interval_append nodeTest 55040 56960 58880 (interval_append nodeTest 55040 55680 56960 nodeInterval55040 (interval_append nodeTest 55680 56320 56960 nodeInterval55680 nodeInterval56320)) (interval_append nodeTest 56960 57600 58880 nodeInterval56960 (interval_append nodeTest 57600 58240 58880 nodeInterval57600 nodeInterval58240))) (interval_append nodeTest 58880 60800 62769 (interval_append nodeTest 58880 59520 60800 nodeInterval58880 (interval_append nodeTest 59520 60160 60800 nodeInterval59520 nodeInterval60160)) (interval_append nodeTest 60800 62080 62769 (interval_append nodeTest 60800 61440 62080 nodeInterval60800 nodeInterval61440) (interval_append nodeTest 62080 62720 62769 nodeInterval62080 nodeInterval62720)))))))
def root : Fin nodeCount := ⟨62768, by decide⟩
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

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
