module
prelude
public import RootedSubsumedForest0318Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0318
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

theorem leafTest_block_16 : Interval leafTest 16 17 :=
  interval_of_check leafTest 16 1 (by decide +kernel)

theorem leafTest_block_17 : Interval leafTest 17 18 :=
  interval_of_check leafTest 17 1 (by decide +kernel)

theorem leafTest_block_18 : Interval leafTest 18 19 :=
  interval_of_check leafTest 18 1 (by decide +kernel)

theorem leafTest_block_19 : Interval leafTest 19 20 :=
  interval_of_check leafTest 19 1 (by decide +kernel)

theorem leafTest_block_20 : Interval leafTest 20 21 :=
  interval_of_check leafTest 20 1 (by decide +kernel)

theorem leafTest_complete : Interval leafTest 0 21 :=
  (interval_append leafTest 0 10 21
  (interval_append leafTest 0 5 10
  (interval_append leafTest 0 2 5
  (interval_append leafTest 0 1 2
  leafTest_block_0
  leafTest_block_1)
  (interval_append leafTest 2 3 5
  leafTest_block_2
  (interval_append leafTest 3 4 5
  leafTest_block_3
  leafTest_block_4)))
  (interval_append leafTest 5 7 10
  (interval_append leafTest 5 6 7
  leafTest_block_5
  leafTest_block_6)
  (interval_append leafTest 7 8 10
  leafTest_block_7
  (interval_append leafTest 8 9 10
  leafTest_block_8
  leafTest_block_9))))
  (interval_append leafTest 10 15 21
  (interval_append leafTest 10 12 15
  (interval_append leafTest 10 11 12
  leafTest_block_10
  leafTest_block_11)
  (interval_append leafTest 12 13 15
  leafTest_block_12
  (interval_append leafTest 13 14 15
  leafTest_block_13
  leafTest_block_14)))
  (interval_append leafTest 15 18 21
  (interval_append leafTest 15 16 18
  leafTest_block_15
  (interval_append leafTest 16 17 18
  leafTest_block_16
  leafTest_block_17))
  (interval_append leafTest 18 19 21
  leafTest_block_18
  (interval_append leafTest 19 20 21
  leafTest_block_19
  leafTest_block_20)))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0318
