module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0704Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
