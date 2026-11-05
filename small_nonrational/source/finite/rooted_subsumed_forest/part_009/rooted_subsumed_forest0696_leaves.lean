module
prelude
public import RootedSubsumedForest0696Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
theorem leafTest_block_0 : Interval leafTest 0 1 :=
  interval_of_check leafTest 0 1 (by decide +kernel)

theorem leafTest_block_1 : Interval leafTest 1 2 :=
  interval_of_check leafTest 1 1 (by decide +kernel)

theorem leafTest_block_2 : Interval leafTest 2 3 :=
  interval_of_check leafTest 2 1 (by decide +kernel)

theorem leafTest_block_3 : Interval leafTest 3 4 :=
  interval_of_check leafTest 3 1 (by decide +kernel)

theorem leafTest_block_4 : Interval leafTest 4 5 :=
  interval_of_check leafTest 4 1 (by decide +kernel)

theorem leafTest_block_5 : Interval leafTest 5 6 :=
  interval_of_check leafTest 5 1 (by decide +kernel)

theorem leafTest_block_6 : Interval leafTest 6 7 :=
  interval_of_check leafTest 6 1 (by decide +kernel)

theorem leafTest_block_7 : Interval leafTest 7 8 :=
  interval_of_check leafTest 7 1 (by decide +kernel)

theorem leafTest_block_8 : Interval leafTest 8 9 :=
  interval_of_check leafTest 8 1 (by decide +kernel)

theorem leafTest_block_9 : Interval leafTest 9 10 :=
  interval_of_check leafTest 9 1 (by decide +kernel)

theorem leafTest_block_10 : Interval leafTest 10 11 :=
  interval_of_check leafTest 10 1 (by decide +kernel)

theorem leafTest_block_11 : Interval leafTest 11 12 :=
  interval_of_check leafTest 11 1 (by decide +kernel)

theorem leafTest_block_12 : Interval leafTest 12 13 :=
  interval_of_check leafTest 12 1 (by decide +kernel)

theorem leafTest_block_13 : Interval leafTest 13 14 :=
  interval_of_check leafTest 13 1 (by decide +kernel)

theorem leafTest_block_14 : Interval leafTest 14 15 :=
  interval_of_check leafTest 14 1 (by decide +kernel)

theorem leafTest_complete : Interval leafTest 0 15 :=
  (interval_append leafTest 0 7 15
  (interval_append leafTest 0 3 7
  (interval_append leafTest 0 1 3
  leafTest_block_0
  (interval_append leafTest 1 2 3
  leafTest_block_1
  leafTest_block_2))
  (interval_append leafTest 3 5 7
  (interval_append leafTest 3 4 5
  leafTest_block_3
  leafTest_block_4)
  (interval_append leafTest 5 6 7
  leafTest_block_5
  leafTest_block_6)))
  (interval_append leafTest 7 11 15
  (interval_append leafTest 7 9 11
  (interval_append leafTest 7 8 9
  leafTest_block_7
  leafTest_block_8)
  (interval_append leafTest 9 10 11
  leafTest_block_9
  leafTest_block_10))
  (interval_append leafTest 11 13 15
  (interval_append leafTest 11 12 13
  leafTest_block_11
  leafTest_block_12)
  (interval_append leafTest 13 14 15
  leafTest_block_13
  leafTest_block_14))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0696
