module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0100Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0100
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_5 640
cert_test_block_2 640 0 0 32 32
cert_test_block_2 640 1 32 64 32
cert_test_block_2 640 2 64 96 32
cert_test_block_2 640 3 96 128 32
cert_test_block_2 640 4 128 160 32
cert_test_block_2 640 5 160 192 32
cert_test_block_2 640 6 192 224 32
cert_test_block_2 640 7 224 256 32
cert_test_block_2 640 8 256 288 32
cert_test_block_2 640 9 288 320 32
cert_test_block_2 640 10 320 352 32
cert_test_block_2 640 11 352 384 32
cert_test_block_2 640 12 384 416 32
cert_test_block_2 640 13 416 448 32
cert_test_block_2 640 14 448 480 32
cert_test_block_2 640 15 480 512 32
cert_test_block_2 640 16 512 544 32
cert_test_block_2 640 17 544 576 32
cert_test_block_2 640 18 576 588 12
theorem test640_complete : Interval test640 0 588 :=
  (interval_append test640 0 288 588
  (interval_append test640 0 128 288
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  test640_block_0
  test640_block_1)
  (interval_append test640 64 96 128
  test640_block_2
  test640_block_3))
  (interval_append test640 128 192 288
  (interval_append test640 128 160 192
  test640_block_4
  test640_block_5)
  (interval_append test640 192 224 288
  test640_block_6
  (interval_append test640 224 256 288
  test640_block_7
  test640_block_8))))
  (interval_append test640 288 448 588
  (interval_append test640 288 352 448
  (interval_append test640 288 320 352
  test640_block_9
  test640_block_10)
  (interval_append test640 352 384 448
  test640_block_11
  (interval_append test640 384 416 448
  test640_block_12
  test640_block_13)))
  (interval_append test640 448 512 588
  (interval_append test640 448 480 512
  test640_block_14
  test640_block_15)
  (interval_append test640 512 544 588
  test640_block_16
  (interval_append test640 544 576 588
  test640_block_17
  test640_block_18)))))
cert_nodeInterval_2 640 1228
end Papers.RationalityTen.RootedForests.RootedRawForest0100
