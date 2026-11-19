module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0095Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0095
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTest_block_2 0 1
cert_leafTest_block_2 1 2
cert_leafTest_block_2 2 3
cert_leafTest_block_2 3 4
cert_leafTest_block_2 4 5
cert_leafTest_block_2 5 6
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
end Papers.RationalityTen.RootedForests.RootedRawForest0095
