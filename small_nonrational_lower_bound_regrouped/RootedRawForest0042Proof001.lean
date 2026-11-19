module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0042Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0042
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
cert_test_block_2 640 16 512 528 16
theorem test640_complete : Interval test640 0 528 :=
  (interval_append test640 0 256 528
  (interval_append test640 0 128 256
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  test640_block_0
  test640_block_1)
  (interval_append test640 64 96 128
  test640_block_2
  test640_block_3))
  (interval_append test640 128 192 256
  (interval_append test640 128 160 192
  test640_block_4
  test640_block_5)
  (interval_append test640 192 224 256
  test640_block_6
  test640_block_7)))
  (interval_append test640 256 384 528
  (interval_append test640 256 320 384
  (interval_append test640 256 288 320
  test640_block_8
  test640_block_9)
  (interval_append test640 320 352 384
  test640_block_10
  test640_block_11))
  (interval_append test640 384 448 528
  (interval_append test640 384 416 448
  test640_block_12
  test640_block_13)
  (interval_append test640 448 480 528
  test640_block_14
  (interval_append test640 480 512 528
  test640_block_15
  test640_block_16)))))
cert_nodeInterval_2 640 1168
end Papers.RationalityTen.RootedForests.RootedRawForest0042
