module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0279Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5120
cert_test_block_3 5120 0 0 16 16
cert_test_block_3 5120 1 16 32 16
cert_test_block_3 5120 2 32 48 16
cert_test_block_3 5120 3 48 64 16
cert_test_block_3 5120 4 64 80 16
cert_test_block_3 5120 5 80 96 16
cert_test_block_3 5120 6 96 112 16
cert_test_block_3 5120 7 112 128 16
cert_test_block_3 5120 8 128 144 16
cert_test_block_3 5120 9 144 160 16
cert_test_block_3 5120 10 160 176 16
cert_test_block_3 5120 11 176 192 16
cert_test_block_3 5120 12 192 208 16
cert_test_block_3 5120 13 208 224 16
cert_test_block_3 5120 14 224 240 16
cert_test_block_3 5120 15 240 256 16
cert_test_block_3 5120 16 256 268 12
theorem test5120_complete : Interval test5120 0 268 :=
  (interval_append test5120 0 128 268
  (interval_append test5120 0 64 128
  (interval_append test5120 0 32 64
  (interval_append test5120 0 16 32
  test5120_block_0
  test5120_block_1)
  (interval_append test5120 32 48 64
  test5120_block_2
  test5120_block_3))
  (interval_append test5120 64 96 128
  (interval_append test5120 64 80 96
  test5120_block_4
  test5120_block_5)
  (interval_append test5120 96 112 128
  test5120_block_6
  test5120_block_7)))
  (interval_append test5120 128 192 268
  (interval_append test5120 128 160 192
  (interval_append test5120 128 144 160
  test5120_block_8
  test5120_block_9)
  (interval_append test5120 160 176 192
  test5120_block_10
  test5120_block_11))
  (interval_append test5120 192 224 268
  (interval_append test5120 192 208 224
  test5120_block_12
  test5120_block_13)
  (interval_append test5120 224 240 268
  test5120_block_14
  (interval_append test5120 240 256 268
  test5120_block_15
  test5120_block_16)))))
cert_nodeInterval_3 5120 5388
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0279
