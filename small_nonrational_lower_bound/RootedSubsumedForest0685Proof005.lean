module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0685Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0685
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
cert_test_block_3 3200 16 256 272 16
cert_test_block_3 3200 17 272 288 16
cert_test_block_3 3200 18 288 304 16
cert_test_block_3 3200 19 304 320 16
cert_test_block_3 3200 20 320 336 16
cert_test_block_3 3200 21 336 352 16
cert_test_block_3 3200 22 352 368 16
cert_test_block_3 3200 23 368 384 16
cert_test_block_3 3200 24 384 400 16
cert_test_block_3 3200 25 400 416 16
cert_test_block_3 3200 26 416 428 12
theorem test3200_complete : Interval test3200 0 428 :=
  (interval_append test3200 0 208 428
  (interval_append test3200 0 96 208
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
  (interval_append test3200 96 144 208
  (interval_append test3200 96 112 144
  test3200_block_6
  (interval_append test3200 112 128 144
  test3200_block_7
  test3200_block_8))
  (interval_append test3200 144 176 208
  (interval_append test3200 144 160 176
  test3200_block_9
  test3200_block_10)
  (interval_append test3200 176 192 208
  test3200_block_11
  test3200_block_12))))
  (interval_append test3200 208 320 428
  (interval_append test3200 208 256 320
  (interval_append test3200 208 224 256
  test3200_block_13
  (interval_append test3200 224 240 256
  test3200_block_14
  test3200_block_15))
  (interval_append test3200 256 288 320
  (interval_append test3200 256 272 288
  test3200_block_16
  test3200_block_17)
  (interval_append test3200 288 304 320
  test3200_block_18
  test3200_block_19)))
  (interval_append test3200 320 368 428
  (interval_append test3200 320 336 368
  test3200_block_20
  (interval_append test3200 336 352 368
  test3200_block_21
  test3200_block_22))
  (interval_append test3200 368 400 428
  (interval_append test3200 368 384 400
  test3200_block_23
  test3200_block_24)
  (interval_append test3200 400 416 428
  test3200_block_25
  test3200_block_26)))))
cert_nodeInterval_3 3200 3628
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0685
