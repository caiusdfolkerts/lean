module
prelude
public import RootedSmallCache
public import RootedSmallGeneratorWords
public import SubsumedClassification
public import SmallSubsumedForest08Leaves
public import SmallSubsumedForest08Proof000
public import SmallSubsumedForest08Proof001
public import SmallSubsumedForest08Proof002
public import SmallSubsumedForest08Proof003
public import SmallSubsumedForest08Proof004
public import SmallSubsumedForest08Proof005
public import SmallSubsumedForest08Proof006
public import SmallSubsumedForest08Proof007
public import SmallSubsumedForest08Proof008
public import SmallSubsumedForest08Proof009
public import SmallSubsumedForest08Proof010
public import SmallSubsumedForest08Proof011
public import SmallSubsumedForest08Proof012
public import SmallSubsumedForest08Proof013
public import SmallSubsumedForest08Proof014
public import SmallSubsumedForest08Proof015
public import SmallSubsumedForest08Proof016
public import SmallSubsumedForest08Proof017
public import SmallSubsumedForest08Proof018
public import SmallSubsumedForest08Proof019
public import SmallSubsumedForest08Proof020
public import SmallSubsumedForest08Proof021
public import SmallSubsumedForest08Proof022
public import SmallSubsumedForest08Proof023
public import SmallSubsumedForest08Proof024
public import SmallSubsumedForest08Proof025
public import SmallSubsumedForest08Proof026
public import SmallSubsumedForest08Proof027
public import SmallSubsumedForest08Proof028
public import SmallSubsumedForest08Proof029
public import SmallSubsumedForest08Proof030
public import SmallSubsumedForest08Proof031
public import SmallSubsumedForest08Proof032
public import SmallSubsumedForest08Proof033
public import SmallSubsumedForest08Proof034
public import SmallSubsumedForest08Proof035
public import SmallSubsumedForest08Proof036
public import SmallSubsumedForest08Proof037
public import SmallSubsumedForest08Proof038
public import SmallSubsumedForest08Proof039
public import SmallSubsumedForest08Proof040
public import SmallSubsumedForest08Proof041
public import SmallSubsumedForest08Proof042
public import SmallSubsumedForest08Proof043
public import SmallSubsumedForest08Proof044
public import SmallSubsumedForest08Proof045
public import SmallSubsumedForest08Proof046
public import SmallSubsumedForest08Proof047
public import SmallSubsumedForest08Proof048
public import SmallSubsumedForest08Proof049
public import SmallSubsumedForest08Proof050
public import SmallSubsumedForest08Proof051
public import SmallSubsumedForest08Proof052
public import SmallSubsumedForest08Proof053
public import SmallSubsumedForest08Proof054
public import SmallSubsumedForest08Proof055
public import SmallSubsumedForest08Proof056
public import SmallSubsumedForest08Proof057
public import SmallSubsumedForest08Proof058
public import SmallSubsumedForest08Proof059
public import SmallSubsumedForest08Proof060
public import SmallSubsumedForest08Proof061
public import SmallSubsumedForest08Proof062
public import SmallSubsumedForest08Proof063
public import SmallSubsumedForest08Proof064
public import SmallSubsumedForest08Proof065
public import SmallSubsumedForest08Proof066
public import SmallSubsumedForest08Proof067
public import SmallSubsumedForest08Proof068
public import SmallSubsumedForest08Proof069
public import SmallSubsumedForest08Proof070
public import SmallSubsumedForest08Proof071
public import SmallSubsumedForest08Proof072
public import SmallSubsumedForest08Proof073
public import SmallSubsumedForest08Proof074
public import SmallSubsumedForest08Proof075
public import SmallSubsumedForest08Proof076
public import SmallSubsumedForest08Proof077
public import SmallSubsumedForest08Proof078
public import SmallSubsumedForest08Proof079
public import SmallSubsumedForest08Proof080
public import SmallSubsumedForest08Proof081
public import SmallSubsumedForest08Proof082
public import SmallSubsumedForest08Proof083
public import SmallSubsumedForest08Proof084
public import SmallSubsumedForest08Proof085
public import SmallSubsumedForest08Proof086
public import SmallSubsumedForest08Proof087
public import SmallSubsumedForest08Proof088
public import SmallSubsumedForest08Proof089
public import SmallSubsumedForest08Proof090
public import SmallSubsumedForest08Proof091
public import SmallSubsumedForest08Proof092
public import SmallSubsumedForest08Proof093
public import SmallSubsumedForest08Proof094
public import SmallSubsumedForest08Proof095
public import SmallSubsumedForest08Proof096

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 30720 61753 (interval_append nodeTest 0 15360 30720 (interval_append nodeTest 0 7680 15360 (interval_append nodeTest 0 3840 7680 (interval_append nodeTest 0 1920 3840 (interval_append nodeTest 0 640 1920 nodeInterval0 (interval_append nodeTest 640 1280 1920 nodeInterval640 nodeInterval1280)) (interval_append nodeTest 1920 2560 3840 nodeInterval1920 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200))) (interval_append nodeTest 3840 5760 7680 (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)) (interval_append nodeTest 5760 6400 7680 nodeInterval5760 (interval_append nodeTest 6400 7040 7680 nodeInterval6400 nodeInterval7040)))) (interval_append nodeTest 7680 11520 15360 (interval_append nodeTest 7680 9600 11520 (interval_append nodeTest 7680 8320 9600 nodeInterval7680 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960)) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))) (interval_append nodeTest 11520 13440 15360 (interval_append nodeTest 11520 12160 13440 nodeInterval11520 (interval_append nodeTest 12160 12800 13440 nodeInterval12160 nodeInterval12800)) (interval_append nodeTest 13440 14080 15360 nodeInterval13440 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720))))) (interval_append nodeTest 15360 23040 30720 (interval_append nodeTest 15360 19200 23040 (interval_append nodeTest 15360 17280 19200 (interval_append nodeTest 15360 16000 17280 nodeInterval15360 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)) (interval_append nodeTest 17280 17920 19200 nodeInterval17280 (interval_append nodeTest 17920 18560 19200 nodeInterval17920 nodeInterval18560))) (interval_append nodeTest 19200 21120 23040 (interval_append nodeTest 19200 19840 21120 nodeInterval19200 (interval_append nodeTest 19840 20480 21120 nodeInterval19840 nodeInterval20480)) (interval_append nodeTest 21120 21760 23040 nodeInterval21120 (interval_append nodeTest 21760 22400 23040 nodeInterval21760 nodeInterval22400)))) (interval_append nodeTest 23040 26880 30720 (interval_append nodeTest 23040 24960 26880 (interval_append nodeTest 23040 23680 24960 nodeInterval23040 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320)) (interval_append nodeTest 24960 25600 26880 nodeInterval24960 (interval_append nodeTest 25600 26240 26880 nodeInterval25600 nodeInterval26240))) (interval_append nodeTest 26880 28800 30720 (interval_append nodeTest 26880 27520 28800 nodeInterval26880 (interval_append nodeTest 27520 28160 28800 nodeInterval27520 nodeInterval28160)) (interval_append nodeTest 28800 29440 30720 nodeInterval28800 (interval_append nodeTest 29440 30080 30720 nodeInterval29440 nodeInterval30080)))))) (interval_append nodeTest 30720 46080 61753 (interval_append nodeTest 30720 38400 46080 (interval_append nodeTest 30720 34560 38400 (interval_append nodeTest 30720 32640 34560 (interval_append nodeTest 30720 31360 32640 nodeInterval30720 (interval_append nodeTest 31360 32000 32640 nodeInterval31360 nodeInterval32000)) (interval_append nodeTest 32640 33280 34560 nodeInterval32640 (interval_append nodeTest 33280 33920 34560 nodeInterval33280 nodeInterval33920))) (interval_append nodeTest 34560 36480 38400 (interval_append nodeTest 34560 35200 36480 nodeInterval34560 (interval_append nodeTest 35200 35840 36480 nodeInterval35200 nodeInterval35840)) (interval_append nodeTest 36480 37120 38400 nodeInterval36480 (interval_append nodeTest 37120 37760 38400 nodeInterval37120 nodeInterval37760)))) (interval_append nodeTest 38400 42240 46080 (interval_append nodeTest 38400 40320 42240 (interval_append nodeTest 38400 39040 40320 nodeInterval38400 (interval_append nodeTest 39040 39680 40320 nodeInterval39040 nodeInterval39680)) (interval_append nodeTest 40320 40960 42240 nodeInterval40320 (interval_append nodeTest 40960 41600 42240 nodeInterval40960 nodeInterval41600))) (interval_append nodeTest 42240 44160 46080 (interval_append nodeTest 42240 42880 44160 nodeInterval42240 (interval_append nodeTest 42880 43520 44160 nodeInterval42880 nodeInterval43520)) (interval_append nodeTest 44160 44800 46080 nodeInterval44160 (interval_append nodeTest 44800 45440 46080 nodeInterval44800 nodeInterval45440))))) (interval_append nodeTest 46080 53760 61753 (interval_append nodeTest 46080 49920 53760 (interval_append nodeTest 46080 48000 49920 (interval_append nodeTest 46080 46720 48000 nodeInterval46080 (interval_append nodeTest 46720 47360 48000 nodeInterval46720 nodeInterval47360)) (interval_append nodeTest 48000 48640 49920 nodeInterval48000 (interval_append nodeTest 48640 49280 49920 nodeInterval48640 nodeInterval49280))) (interval_append nodeTest 49920 51840 53760 (interval_append nodeTest 49920 50560 51840 nodeInterval49920 (interval_append nodeTest 50560 51200 51840 nodeInterval50560 nodeInterval51200)) (interval_append nodeTest 51840 52480 53760 nodeInterval51840 (interval_append nodeTest 52480 53120 53760 nodeInterval52480 nodeInterval53120)))) (interval_append nodeTest 53760 57600 61753 (interval_append nodeTest 53760 55680 57600 (interval_append nodeTest 53760 54400 55680 nodeInterval53760 (interval_append nodeTest 54400 55040 55680 nodeInterval54400 nodeInterval55040)) (interval_append nodeTest 55680 56320 57600 nodeInterval55680 (interval_append nodeTest 56320 56960 57600 nodeInterval56320 nodeInterval56960))) (interval_append nodeTest 57600 59520 61753 (interval_append nodeTest 57600 58240 59520 nodeInterval57600 (interval_append nodeTest 58240 58880 59520 nodeInterval58240 nodeInterval58880)) (interval_append nodeTest 59520 60800 61753 (interval_append nodeTest 59520 60160 60800 nodeInterval59520 nodeInterval60160) (interval_append nodeTest 60800 61440 61753 nodeInterval60800 nodeInterval61440)))))))
def root : Fin nodeCount := ⟨61752, by decide⟩
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

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
