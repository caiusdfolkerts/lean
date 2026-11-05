module
prelude
public import RootedSubsumedForest0339Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
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

theorem leafTest_block_21 : Interval leafTest 21 22 :=
  interval_of_check leafTest 21 1 (by decide +kernel)

theorem leafTest_block_22 : Interval leafTest 22 23 :=
  interval_of_check leafTest 22 1 (by decide +kernel)

theorem leafTest_block_23 : Interval leafTest 23 24 :=
  interval_of_check leafTest 23 1 (by decide +kernel)

theorem leafTest_block_24 : Interval leafTest 24 25 :=
  interval_of_check leafTest 24 1 (by decide +kernel)

theorem leafTest_block_25 : Interval leafTest 25 26 :=
  interval_of_check leafTest 25 1 (by decide +kernel)

theorem leafTest_block_26 : Interval leafTest 26 27 :=
  interval_of_check leafTest 26 1 (by decide +kernel)

theorem leafTest_block_27 : Interval leafTest 27 28 :=
  interval_of_check leafTest 27 1 (by decide +kernel)

theorem leafTest_block_28 : Interval leafTest 28 29 :=
  interval_of_check leafTest 28 1 (by decide +kernel)

theorem leafTest_complete : Interval leafTest 0 29 :=
  (interval_append leafTest 0 14 29
  (interval_append leafTest 0 7 14
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
  (interval_append leafTest 7 10 14
  (interval_append leafTest 7 8 10
  leafTest_block_7
  (interval_append leafTest 8 9 10
  leafTest_block_8
  leafTest_block_9))
  (interval_append leafTest 10 12 14
  (interval_append leafTest 10 11 12
  leafTest_block_10
  leafTest_block_11)
  (interval_append leafTest 12 13 14
  leafTest_block_12
  leafTest_block_13))))
  (interval_append leafTest 14 21 29
  (interval_append leafTest 14 17 21
  (interval_append leafTest 14 15 17
  leafTest_block_14
  (interval_append leafTest 15 16 17
  leafTest_block_15
  leafTest_block_16))
  (interval_append leafTest 17 19 21
  (interval_append leafTest 17 18 19
  leafTest_block_17
  leafTest_block_18)
  (interval_append leafTest 19 20 21
  leafTest_block_19
  leafTest_block_20)))
  (interval_append leafTest 21 25 29
  (interval_append leafTest 21 23 25
  (interval_append leafTest 21 22 23
  leafTest_block_21
  leafTest_block_22)
  (interval_append leafTest 23 24 25
  leafTest_block_23
  leafTest_block_24))
  (interval_append leafTest 25 27 29
  (interval_append leafTest 25 26 27
  leafTest_block_25
  leafTest_block_26)
  (interval_append leafTest 27 28 29
  leafTest_block_27
  leafTest_block_28)))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
