module
prelude
public import RootedSubsumedForest0279Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
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

theorem leafTest_block_15 : Interval leafTest 15 16 :=
  interval_of_check leafTest 15 1 (by decide +kernel)

theorem leafTest_complete : Interval leafTest 0 16 :=
  (interval_append leafTest 0 8 16
  (interval_append leafTest 0 4 8
  (interval_append leafTest 0 2 4
  (interval_append leafTest 0 1 2
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 2 3 4
  leafTest_block_2
  leafTest_block_3))
  (interval_append leafTest 4 6 8
  (interval_append leafTest 4 5 6
  leafTest_block_4
  leafTest_block_5)
  (interval_append leafTest 6 7 8
  leafTest_block_6
  leafTest_block_7)))
  (interval_append leafTest 8 12 16
  (interval_append leafTest 8 10 12
  (interval_append leafTest 8 9 10
  leafTest_block_8
  leafTest_block_9)
  (interval_append leafTest 10 11 12
  leafTest_block_10
  leafTest_block_11))
  (interval_append leafTest 12 14 16
  (interval_append leafTest 12 13 14
  leafTest_block_12
  leafTest_block_13)
  (interval_append leafTest 14 15 16
  leafTest_block_14
  leafTest_block_15))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
