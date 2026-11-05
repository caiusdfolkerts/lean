module
prelude
public import RootedSixBase01GrowthCache
public import RootedSixBase01FastWords
public import SubsumedClassification
public import RootedSubsumedForest0320Leaves
public import RootedSubsumedForest0320Proof000
public import RootedSubsumedForest0320Proof001
public import RootedSubsumedForest0320Proof002
public import RootedSubsumedForest0320Proof003
public import RootedSubsumedForest0320Proof004
public import RootedSubsumedForest0320Proof005
public import RootedSubsumedForest0320Proof006
public import RootedSubsumedForest0320Proof007
public import RootedSubsumedForest0320Proof008
public import RootedSubsumedForest0320Proof009
public import RootedSubsumedForest0320Proof010
public import RootedSubsumedForest0320Proof011
public import RootedSubsumedForest0320Proof012
public import RootedSubsumedForest0320Proof013
public import RootedSubsumedForest0320Proof014
public import RootedSubsumedForest0320Proof015
public import RootedSubsumedForest0320Proof016
public import RootedSubsumedForest0320Proof017
public import RootedSubsumedForest0320Proof018
public import RootedSubsumedForest0320Proof019
public import RootedSubsumedForest0320Proof020
public import RootedSubsumedForest0320Proof021
public import RootedSubsumedForest0320Proof022
public import RootedSubsumedForest0320Proof023
public import RootedSubsumedForest0320Proof024
public import RootedSubsumedForest0320Proof025
public import RootedSubsumedForest0320Proof026
public import RootedSubsumedForest0320Proof027
public import RootedSubsumedForest0320Proof028
public import RootedSubsumedForest0320Proof029
public import RootedSubsumedForest0320Proof030
public import RootedSubsumedForest0320Proof031
public import RootedSubsumedForest0320Proof032
public import RootedSubsumedForest0320Proof033
public import RootedSubsumedForest0320Proof034
public import RootedSubsumedForest0320Proof035
public import RootedSubsumedForest0320Proof036
public import RootedSubsumedForest0320Proof037
public import RootedSubsumedForest0320Proof038
public import RootedSubsumedForest0320Proof039
public import RootedSubsumedForest0320Proof040
public import RootedSubsumedForest0320Proof041
public import RootedSubsumedForest0320Proof042
public import RootedSubsumedForest0320Proof043
public import RootedSubsumedForest0320Proof044
public import RootedSubsumedForest0320Proof045
public import RootedSubsumedForest0320Proof046
public import RootedSubsumedForest0320Proof047
public import RootedSubsumedForest0320Proof048
public import RootedSubsumedForest0320Proof049
public import RootedSubsumedForest0320Proof050
public import RootedSubsumedForest0320Proof051
public import RootedSubsumedForest0320Proof052
public import RootedSubsumedForest0320Proof053
public import RootedSubsumedForest0320Proof054
public import RootedSubsumedForest0320Proof055
public import RootedSubsumedForest0320Proof056
public import RootedSubsumedForest0320Proof057
public import RootedSubsumedForest0320Proof058
public import RootedSubsumedForest0320Proof059
public import RootedSubsumedForest0320Proof060
public import RootedSubsumedForest0320Proof061
public import RootedSubsumedForest0320Proof062
public import RootedSubsumedForest0320Proof063
public import RootedSubsumedForest0320Proof064
public import RootedSubsumedForest0320Proof065
public import RootedSubsumedForest0320Proof066
public import RootedSubsumedForest0320Proof067
public import RootedSubsumedForest0320Proof068
public import RootedSubsumedForest0320Proof069
public import RootedSubsumedForest0320Proof070
public import RootedSubsumedForest0320Proof071
public import RootedSubsumedForest0320Proof072
public import RootedSubsumedForest0320Proof073

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem nodeTest_complete : Interval nodeTest 0 nodeCount := (interval_append nodeTest 0 23680 47122 (interval_append nodeTest 0 11520 23680 (interval_append nodeTest 0 5760 11520 (interval_append nodeTest 0 2560 5760 (interval_append nodeTest 0 1280 2560 (interval_append nodeTest 0 640 1280 nodeInterval0 nodeInterval640) (interval_append nodeTest 1280 1920 2560 nodeInterval1280 nodeInterval1920)) (interval_append nodeTest 2560 3840 5760 (interval_append nodeTest 2560 3200 3840 nodeInterval2560 nodeInterval3200) (interval_append nodeTest 3840 4480 5760 nodeInterval3840 (interval_append nodeTest 4480 5120 5760 nodeInterval4480 nodeInterval5120)))) (interval_append nodeTest 5760 8320 11520 (interval_append nodeTest 5760 7040 8320 (interval_append nodeTest 5760 6400 7040 nodeInterval5760 nodeInterval6400) (interval_append nodeTest 7040 7680 8320 nodeInterval7040 nodeInterval7680)) (interval_append nodeTest 8320 9600 11520 (interval_append nodeTest 8320 8960 9600 nodeInterval8320 nodeInterval8960) (interval_append nodeTest 9600 10240 11520 nodeInterval9600 (interval_append nodeTest 10240 10880 11520 nodeInterval10240 nodeInterval10880))))) (interval_append nodeTest 11520 17280 23680 (interval_append nodeTest 11520 14080 17280 (interval_append nodeTest 11520 12800 14080 (interval_append nodeTest 11520 12160 12800 nodeInterval11520 nodeInterval12160) (interval_append nodeTest 12800 13440 14080 nodeInterval12800 nodeInterval13440)) (interval_append nodeTest 14080 15360 17280 (interval_append nodeTest 14080 14720 15360 nodeInterval14080 nodeInterval14720) (interval_append nodeTest 15360 16000 17280 nodeInterval15360 (interval_append nodeTest 16000 16640 17280 nodeInterval16000 nodeInterval16640)))) (interval_append nodeTest 17280 20480 23680 (interval_append nodeTest 17280 18560 20480 (interval_append nodeTest 17280 17920 18560 nodeInterval17280 nodeInterval17920) (interval_append nodeTest 18560 19200 20480 nodeInterval18560 (interval_append nodeTest 19200 19840 20480 nodeInterval19200 nodeInterval19840))) (interval_append nodeTest 20480 21760 23680 (interval_append nodeTest 20480 21120 21760 nodeInterval20480 nodeInterval21120) (interval_append nodeTest 21760 22400 23680 nodeInterval21760 (interval_append nodeTest 22400 23040 23680 nodeInterval22400 nodeInterval23040)))))) (interval_append nodeTest 23680 35200 47122 (interval_append nodeTest 23680 29440 35200 (interval_append nodeTest 23680 26240 29440 (interval_append nodeTest 23680 24960 26240 (interval_append nodeTest 23680 24320 24960 nodeInterval23680 nodeInterval24320) (interval_append nodeTest 24960 25600 26240 nodeInterval24960 nodeInterval25600)) (interval_append nodeTest 26240 27520 29440 (interval_append nodeTest 26240 26880 27520 nodeInterval26240 nodeInterval26880) (interval_append nodeTest 27520 28160 29440 nodeInterval27520 (interval_append nodeTest 28160 28800 29440 nodeInterval28160 nodeInterval28800)))) (interval_append nodeTest 29440 32000 35200 (interval_append nodeTest 29440 30720 32000 (interval_append nodeTest 29440 30080 30720 nodeInterval29440 nodeInterval30080) (interval_append nodeTest 30720 31360 32000 nodeInterval30720 nodeInterval31360)) (interval_append nodeTest 32000 33280 35200 (interval_append nodeTest 32000 32640 33280 nodeInterval32000 nodeInterval32640) (interval_append nodeTest 33280 33920 35200 nodeInterval33280 (interval_append nodeTest 33920 34560 35200 nodeInterval33920 nodeInterval34560))))) (interval_append nodeTest 35200 40960 47122 (interval_append nodeTest 35200 37760 40960 (interval_append nodeTest 35200 36480 37760 (interval_append nodeTest 35200 35840 36480 nodeInterval35200 nodeInterval35840) (interval_append nodeTest 36480 37120 37760 nodeInterval36480 nodeInterval37120)) (interval_append nodeTest 37760 39040 40960 (interval_append nodeTest 37760 38400 39040 nodeInterval37760 nodeInterval38400) (interval_append nodeTest 39040 39680 40960 nodeInterval39040 (interval_append nodeTest 39680 40320 40960 nodeInterval39680 nodeInterval40320)))) (interval_append nodeTest 40960 44160 47122 (interval_append nodeTest 40960 42240 44160 (interval_append nodeTest 40960 41600 42240 nodeInterval40960 nodeInterval41600) (interval_append nodeTest 42240 42880 44160 nodeInterval42240 (interval_append nodeTest 42880 43520 44160 nodeInterval42880 nodeInterval43520))) (interval_append nodeTest 44160 45440 47122 (interval_append nodeTest 44160 44800 45440 nodeInterval44160 nodeInterval44800) (interval_append nodeTest 45440 46080 47122 nodeInterval45440 (interval_append nodeTest 46080 46720 47122 nodeInterval46080 nodeInterval46720)))))))
def root : Fin nodeCount := ⟨47121, by decide⟩
def nodes : Fin nodeCount → BatchedOrbitGrowth.Node cellCount 1024 48 leafCount nodeCount :=
  decodedNodes rawNodes
theorem boundary_classification
    (renamings : Fin 48 → Renaming (fun c => has (FacetUniverses.RootedSixBase01.ridgeList c))
      FacetUniverses.RootedSixBase01.literalCompatible FacetUniverses.RootedSixBase01.kind)
    (hmaps : ∀ f c, Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawMaps f.val c.val =
      ((renamings f).cells.forward c).val)
    (B : List (Fin cellCount))
    (hB : Target (fun c => has (FacetUniverses.RootedSixBase01.ridgeList c))
      FacetUniverses.RootedSixBase01.literalCompatible FacetUniverses.RootedSixBase01.kind quota B)
    (hroot : (0 : Fin cellCount) ∈ B) :
    ∃ (j : Fin leafCount) (word : List (Fin 48)),
      (leaves j).Nodup ∧ Same (family (leaves j))
        (family (OrbitGrowthDAG.applyWord renamings word B)) := by
  have hrootCells : (nodes root).cells = [0] := by decide +kernel
  refine SubsumedClassification.complete_of_raw_closed_checks
    Papers.RationalityTen.RootedCaches.RootedSixBase01.candidateMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.badMasks Papers.RationalityTen.RootedCaches.RootedSixBase01.fastKind
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.rawMaps rawLeaves rawNodes Papers.RationalityTen.RootedCaches.RootedSixBase01.cache quota
    renamings (fun _ => rfl) (fun _ => rfl)
    (fun c => Papers.RationalityTen.RootedCaches.RootedSixBase01.facts.kindExact c) (fun f c => (Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.FastWords.raw_maps_eq f.val c.val c.isLt).trans (hmaps f c)) ?_ ?_ ?_ ?_ ?_ B hB root ?_ ?_
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
