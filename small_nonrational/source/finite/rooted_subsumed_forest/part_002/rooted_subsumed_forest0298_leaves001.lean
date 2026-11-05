module
prelude
public import RootedSubsumedForest0298Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt32 (i : Nat) := leafTest (i+32)
theorem leafTestAt32_block_0 : Interval leafTestAt32 0 1 :=
  interval_of_check leafTestAt32 0 1 (by decide +kernel)

theorem leafTestAt32_block_1 : Interval leafTestAt32 1 2 :=
  interval_of_check leafTestAt32 1 1 (by decide +kernel)

theorem leafTestAt32_block_2 : Interval leafTestAt32 2 3 :=
  interval_of_check leafTestAt32 2 1 (by decide +kernel)

theorem leafTestAt32_block_3 : Interval leafTestAt32 3 4 :=
  interval_of_check leafTestAt32 3 1 (by decide +kernel)

theorem leafTestAt32_block_4 : Interval leafTestAt32 4 5 :=
  interval_of_check leafTestAt32 4 1 (by decide +kernel)

theorem leafTestAt32_block_5 : Interval leafTestAt32 5 6 :=
  interval_of_check leafTestAt32 5 1 (by decide +kernel)

theorem leafTestAt32_block_6 : Interval leafTestAt32 6 7 :=
  interval_of_check leafTestAt32 6 1 (by decide +kernel)

theorem leafTestAt32_block_7 : Interval leafTestAt32 7 8 :=
  interval_of_check leafTestAt32 7 1 (by decide +kernel)

theorem leafTestAt32_block_8 : Interval leafTestAt32 8 9 :=
  interval_of_check leafTestAt32 8 1 (by decide +kernel)

theorem leafTestAt32_block_9 : Interval leafTestAt32 9 10 :=
  interval_of_check leafTestAt32 9 1 (by decide +kernel)

theorem leafTestAt32_block_10 : Interval leafTestAt32 10 11 :=
  interval_of_check leafTestAt32 10 1 (by decide +kernel)

theorem leafTestAt32_complete : Interval leafTestAt32 0 11 :=
  (interval_append leafTestAt32 0 5 11
  (interval_append leafTestAt32 0 2 5
  (interval_append leafTestAt32 0 1 2
  leafTestAt32_block_0
  leafTestAt32_block_1)
  (interval_append leafTestAt32 2 3 5
  leafTestAt32_block_2
  (interval_append leafTestAt32 3 4 5
  leafTestAt32_block_3
  leafTestAt32_block_4)))
  (interval_append leafTestAt32 5 8 11
  (interval_append leafTestAt32 5 6 8
  leafTestAt32_block_5
  (interval_append leafTestAt32 6 7 8
  leafTestAt32_block_6
  leafTestAt32_block_7))
  (interval_append leafTestAt32 8 9 11
  leafTestAt32_block_8
  (interval_append leafTestAt32 9 10 11
  leafTestAt32_block_9
  leafTestAt32_block_10))))
theorem leafInterval32 : Interval leafTest 32 43 := by
  intro i hlo hhi
  have h := leafTestAt32_complete (i-32) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt32, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
