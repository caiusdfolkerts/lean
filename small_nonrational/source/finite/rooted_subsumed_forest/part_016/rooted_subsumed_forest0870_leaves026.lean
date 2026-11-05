module
prelude
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt832 (i : Nat) := leafTest (i+832)
theorem leafTestAt832_block_0 : Interval leafTestAt832 0 1 :=
  interval_of_check leafTestAt832 0 1 (by decide +kernel)

theorem leafTestAt832_block_1 : Interval leafTestAt832 1 2 :=
  interval_of_check leafTestAt832 1 1 (by decide +kernel)

theorem leafTestAt832_block_2 : Interval leafTestAt832 2 3 :=
  interval_of_check leafTestAt832 2 1 (by decide +kernel)

theorem leafTestAt832_complete : Interval leafTestAt832 0 3 :=
  (interval_append leafTestAt832 0 1 3
  leafTestAt832_block_0
  (interval_append leafTestAt832 1 2 3
  leafTestAt832_block_1
  leafTestAt832_block_2))
theorem leafInterval832 : Interval leafTest 832 835 := by
  intro i hlo hhi
  have h := leafTestAt832_complete (i-832) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt832, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
