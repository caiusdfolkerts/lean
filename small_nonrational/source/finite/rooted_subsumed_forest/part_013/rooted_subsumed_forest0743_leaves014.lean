module
prelude
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt448 (i : Nat) := leafTest (i+448)
theorem leafTestAt448_block_0 : Interval leafTestAt448 0 1 :=
  interval_of_check leafTestAt448 0 1 (by decide +kernel)

theorem leafTestAt448_block_1 : Interval leafTestAt448 1 2 :=
  interval_of_check leafTestAt448 1 1 (by decide +kernel)

theorem leafTestAt448_block_2 : Interval leafTestAt448 2 3 :=
  interval_of_check leafTestAt448 2 1 (by decide +kernel)

theorem leafTestAt448_complete : Interval leafTestAt448 0 3 :=
  (interval_append leafTestAt448 0 1 3
  leafTestAt448_block_0
  (interval_append leafTestAt448 1 2 3
  leafTestAt448_block_1
  leafTestAt448_block_2))
theorem leafInterval448 : Interval leafTest 448 451 := by
  intro i hlo hhi
  have h := leafTestAt448_complete (i-448) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt448, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
