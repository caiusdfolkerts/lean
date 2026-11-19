module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0742Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0742
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
cert_test_block_3 3200 5 80 96 16
cert_test_block_3 3200 6 96 112 16
cert_test_block_3 3200 7 112 128 16
cert_test_block_3 3200 8 128 144 16
cert_test_block_3 3200 9 144 160 16
cert_test_block_3 3200 10 160 176 16
cert_test_block_3 3200 11 176 188 12
theorem test3200_complete : Interval test3200 0 188 :=
  (interval_append test3200 0 96 188
  (interval_append test3200 0 48 96
  (interval_append test3200 0 16 48
  test3200_block_0
  (interval_append test3200 16 32 48
  test3200_block_1
  test3200_block_2))
  (interval_append test3200 48 64 96
  test3200_block_3
  (interval_append test3200 64 80 96
  test3200_block_4
  test3200_block_5)))
  (interval_append test3200 96 144 188
  (interval_append test3200 96 112 144
  test3200_block_6
  (interval_append test3200 112 128 144
  test3200_block_7
  test3200_block_8))
  (interval_append test3200 144 160 188
  test3200_block_9
  (interval_append test3200 160 176 188
  test3200_block_10
  test3200_block_11))))
cert_nodeInterval_3 3200 3388
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0742
