module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0300Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 7680
cert_test_block_3 7680 0 0 16 16
cert_test_block_3 7680 1 16 32 16
cert_test_block_3 7680 2 32 48 16
cert_test_block_3 7680 3 48 64 16
cert_test_block_3 7680 4 64 80 16
cert_test_block_3 7680 5 80 96 16
cert_test_block_3 7680 6 96 112 16
cert_test_block_3 7680 7 112 128 16
cert_test_block_3 7680 8 128 144 16
cert_test_block_3 7680 9 144 160 16
cert_test_block_3 7680 10 160 176 16
cert_test_block_3 7680 11 176 192 16
cert_test_block_3 7680 12 192 208 16
cert_test_block_3 7680 13 208 224 16
cert_test_block_3 7680 14 224 237 13
theorem test7680_complete : Interval test7680 0 237 :=
  (interval_append test7680 0 112 237
  (interval_append test7680 0 48 112
  (interval_append test7680 0 16 48
  test7680_block_0
  (interval_append test7680 16 32 48
  test7680_block_1
  test7680_block_2))
  (interval_append test7680 48 80 112
  (interval_append test7680 48 64 80
  test7680_block_3
  test7680_block_4)
  (interval_append test7680 80 96 112
  test7680_block_5
  test7680_block_6)))
  (interval_append test7680 112 176 237
  (interval_append test7680 112 144 176
  (interval_append test7680 112 128 144
  test7680_block_7
  test7680_block_8)
  (interval_append test7680 144 160 176
  test7680_block_9
  test7680_block_10))
  (interval_append test7680 176 208 237
  (interval_append test7680 176 192 208
  test7680_block_11
  test7680_block_12)
  (interval_append test7680 208 224 237
  test7680_block_13
  test7680_block_14))))
cert_nodeInterval_3 7680 7917
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
