module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
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
cert_leafTest_block_3 0 1
cert_leafTest_block_3 1 2
cert_leafTest_block_3 2 3
cert_leafTest_block_3 3 4
cert_leafTest_block_3 4 5
cert_leafTest_block_3 5 6
cert_leafTest_block_3 6 7
cert_leafTest_block_3 7 8
cert_leafTest_block_3 8 9
cert_leafTest_block_3 9 10
cert_leafTest_block_3 10 11
cert_leafTest_block_3 11 12
cert_leafTest_block_3 12 13
cert_leafTest_block_3 13 14
cert_leafTest_block_3 14 15
cert_leafTest_block_3 15 16
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
