module
prelude
public import RootedRawForest0102Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0102
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

theorem leafTest_complete : Interval leafTest 0 6 :=
  (interval_append leafTest 0 3 6
  (interval_append leafTest 0 1 3
  leafTest_block_0
  (interval_append leafTest 1 2 3
  leafTest_block_1
  leafTest_block_2))
  (interval_append leafTest 3 4 6
  leafTest_block_3
  (interval_append leafTest 4 5 6
  leafTest_block_4
  leafTest_block_5)))
end Papers.RationalityTen.RootedForests.RootedRawForest0102
