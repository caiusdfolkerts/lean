module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0287Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0287
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
cert_test_block_3 640 6 96 112 16
cert_test_block_3 640 7 112 128 16
cert_test_block_3 640 8 128 144 16
cert_test_block_3 640 9 144 160 16
cert_test_block_3 640 10 160 176 16
cert_test_block_3 640 11 176 192 16
cert_test_block_3 640 12 192 208 16
cert_test_block_3 640 13 208 224 16
cert_test_block_3 640 14 224 240 16
cert_test_block_3 640 15 240 256 16
cert_test_block_3 640 16 256 272 16
cert_test_block_3 640 17 272 288 16
cert_test_block_3 640 18 288 293 5
theorem test640_complete : Interval test640 0 293 :=
  (interval_append test640 0 144 293
  (interval_append test640 0 64 144
  (interval_append test640 0 32 64
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 64
  test640_block_2
  test640_block_3))
  (interval_append test640 64 96 144
  (interval_append test640 64 80 96
  test640_block_4
  test640_block_5)
  (interval_append test640 96 112 144
  test640_block_6
  (interval_append test640 112 128 144
  test640_block_7
  test640_block_8))))
  (interval_append test640 144 224 293
  (interval_append test640 144 176 224
  (interval_append test640 144 160 176
  test640_block_9
  test640_block_10)
  (interval_append test640 176 192 224
  test640_block_11
  (interval_append test640 192 208 224
  test640_block_12
  test640_block_13)))
  (interval_append test640 224 256 293
  (interval_append test640 224 240 256
  test640_block_14
  test640_block_15)
  (interval_append test640 256 272 293
  test640_block_16
  (interval_append test640 272 288 293
  test640_block_17
  test640_block_18)))))
cert_nodeInterval_3 640 933
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0287
