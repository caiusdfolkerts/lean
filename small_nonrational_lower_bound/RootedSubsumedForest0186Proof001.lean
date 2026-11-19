module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0186Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0186
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 640
cert_test_block_3 640 0 0 16 16
cert_test_block_3 640 1 16 32 16
cert_test_block_3 640 2 32 48 16
cert_test_block_3 640 3 48 64 16
cert_test_block_3 640 4 64 80 16
cert_test_block_3 640 5 80 96 16
cert_test_block_3 640 6 96 104 8
theorem test640_complete : Interval test640 0 104 :=
  (interval_append test640 0 48 104
  (interval_append test640 0 16 48
  test640_block_0
  (interval_append test640 16 32 48
  test640_block_1
  test640_block_2))
  (interval_append test640 48 80 104
  (interval_append test640 48 64 80
  test640_block_3
  test640_block_4)
  (interval_append test640 80 96 104
  test640_block_5
  test640_block_6)))
cert_nodeInterval_3 640 744
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0186
