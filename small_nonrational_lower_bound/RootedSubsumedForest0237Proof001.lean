module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0237Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0237
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
cert_test_block_3 640 18 288 304 16
cert_test_block_3 640 19 304 320 16
cert_test_block_3 640 20 320 336 16
cert_test_block_3 640 21 336 352 16
cert_test_block_3 640 22 352 355 3
theorem test640_complete : Interval test640 0 355 :=
  (interval_append test640 0 176 355
  (interval_append test640 0 80 176
  (interval_append test640 0 32 80
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 80
  test640_block_2
  (interval_append test640 48 64 80
  test640_block_3
  test640_block_4)))
  (interval_append test640 80 128 176
  (interval_append test640 80 96 128
  test640_block_5
  (interval_append test640 96 112 128
  test640_block_6
  test640_block_7))
  (interval_append test640 128 144 176
  test640_block_8
  (interval_append test640 144 160 176
  test640_block_9
  test640_block_10))))
  (interval_append test640 176 272 355
  (interval_append test640 176 224 272
  (interval_append test640 176 192 224
  test640_block_11
  (interval_append test640 192 208 224
  test640_block_12
  test640_block_13))
  (interval_append test640 224 240 272
  test640_block_14
  (interval_append test640 240 256 272
  test640_block_15
  test640_block_16)))
  (interval_append test640 272 320 355
  (interval_append test640 272 288 320
  test640_block_17
  (interval_append test640 288 304 320
  test640_block_18
  test640_block_19))
  (interval_append test640 320 336 355
  test640_block_20
  (interval_append test640 336 352 355
  test640_block_21
  test640_block_22)))))
cert_nodeInterval_3 640 995
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0237
