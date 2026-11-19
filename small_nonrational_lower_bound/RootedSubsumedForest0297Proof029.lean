module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0297Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 18560
cert_test_block_3 18560 0 0 16 16
cert_test_block_3 18560 1 16 32 16
cert_test_block_3 18560 2 32 48 16
cert_test_block_3 18560 3 48 56 8
theorem test18560_complete : Interval test18560 0 56 :=
  (interval_append test18560 0 32 56
  (interval_append test18560 0 16 32
  test18560_block_0
  test18560_block_1)
  (interval_append test18560 32 48 56
  test18560_block_2
  test18560_block_3))
cert_nodeInterval_3 18560 18616
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
