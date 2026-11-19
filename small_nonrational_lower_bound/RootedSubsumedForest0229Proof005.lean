module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0229Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0229
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3200
cert_test_block_3 3200 0 0 16 16
cert_test_block_3 3200 1 16 32 16
cert_test_block_3 3200 2 32 48 16
cert_test_block_3 3200 3 48 64 16
cert_test_block_3 3200 4 64 80 16
theorem test3200_complete : Interval test3200 0 80 :=
  (interval_append test3200 0 32 80
  (interval_append test3200 0 16 32
  test3200_block_0
  test3200_block_1)
  (interval_append test3200 32 48 80
  test3200_block_2
  (interval_append test3200 48 64 80
  test3200_block_3
  test3200_block_4)))
cert_nodeInterval_3 3200 3280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0229
