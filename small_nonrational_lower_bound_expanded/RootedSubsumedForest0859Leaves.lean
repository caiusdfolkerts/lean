module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0859Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0859
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
theorem leafTest_complete : Interval leafTest 0 8 :=
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0859
