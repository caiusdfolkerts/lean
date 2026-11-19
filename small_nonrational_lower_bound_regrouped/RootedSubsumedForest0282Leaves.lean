module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0282Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
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
theorem leafTest_complete : Interval leafTest 0 12 :=
  (interval_append leafTest 0 6 12
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
  (interval_append leafTest 6 9 12
  (interval_append leafTest 6 7 9
  leafTest_block_6
  (interval_append leafTest 7 8 9
  leafTest_block_7
  leafTest_block_8))
  (interval_append leafTest 9 10 12
  leafTest_block_9
  (interval_append leafTest 10 11 12
  leafTest_block_10
  leafTest_block_11))))
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
