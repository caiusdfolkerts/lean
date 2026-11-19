module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0064Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0064
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
cert_test_block_2 640 14 448 465 17
theorem test640_complete : Interval test640 0 465 :=
  (interval_append test640 0 224 465
  (interval_append test640 0 96 224
  (interval_append test640 0 32 96
  test640_block_0
  (interval_append test640 32 64 96
  test640_block_1
  test640_block_2))
  (interval_append test640 96 160 224
  (interval_append test640 96 128 160
  test640_block_3
  test640_block_4)
  (interval_append test640 160 192 224
  test640_block_5
  test640_block_6)))
  (interval_append test640 224 352 465
  (interval_append test640 224 288 352
  (interval_append test640 224 256 288
  test640_block_7
  test640_block_8)
  (interval_append test640 288 320 352
  test640_block_9
  test640_block_10))
  (interval_append test640 352 416 465
  (interval_append test640 352 384 416
  test640_block_11
  test640_block_12)
  (interval_append test640 416 448 465
  test640_block_13
  test640_block_14))))
cert_nodeInterval_2 640 1105
end Papers.RationalityTen.RootedForests.RootedRawForest0064
