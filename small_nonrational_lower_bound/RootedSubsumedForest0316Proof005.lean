module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0316Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0316
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
cert_test_block_3 3200 11 176 192 16
cert_test_block_3 3200 12 192 208 16
cert_test_block_3 3200 13 208 224 16
cert_test_block_3 3200 14 224 240 16
cert_test_block_3 3200 15 240 256 16
cert_test_block_3 3200 16 256 264 8
theorem test3200_complete : Interval test3200 0 264 :=
  (interval_append test3200 0 128 264
  (interval_append test3200 0 64 128
  (interval_append test3200 0 32 64
  (interval_append test3200 0 16 32
  test3200_block_0
  test3200_block_1)
  (interval_append test3200 32 48 64
  test3200_block_2
  test3200_block_3))
  (interval_append test3200 64 96 128
  (interval_append test3200 64 80 96
  test3200_block_4
  test3200_block_5)
  (interval_append test3200 96 112 128
  test3200_block_6
  test3200_block_7)))
  (interval_append test3200 128 192 264
  (interval_append test3200 128 160 192
  (interval_append test3200 128 144 160
  test3200_block_8
  test3200_block_9)
  (interval_append test3200 160 176 192
  test3200_block_10
  test3200_block_11))
  (interval_append test3200 192 224 264
  (interval_append test3200 192 208 224
  test3200_block_12
  test3200_block_13)
  (interval_append test3200 224 240 264
  test3200_block_14
  (interval_append test3200 240 256 264
  test3200_block_15
  test3200_block_16)))))
cert_nodeInterval_3 3200 3464
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0316
