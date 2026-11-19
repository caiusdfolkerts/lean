module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest13Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_4 0 1
cert_leafTest_block_4 1 2
cert_leafTest_block_4 2 3
cert_leafTest_block_4 3 4
cert_leafTest_block_4 4 5
cert_leafTest_block_4 5 6
cert_leafTest_block_4 6 7
cert_leafTest_block_4 7 8
cert_leafTest_block_4 8 9
cert_leafTest_block_4 9 10
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
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest13
