module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
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
