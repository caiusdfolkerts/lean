module
prelude
public import RootedSubsumedForest0315Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0315
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

theorem leafTest_complete : Interval leafTest 0 10 :=
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0315
