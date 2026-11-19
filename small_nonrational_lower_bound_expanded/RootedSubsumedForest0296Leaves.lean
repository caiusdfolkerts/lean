module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0296Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0296
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
theorem leafTest_complete : Interval leafTest 0 7 :=
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0296
