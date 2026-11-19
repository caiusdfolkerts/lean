module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest11Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 16640
cert_test_block_4 16640 0 0 16 16
cert_test_block_4 16640 1 16 32 16
cert_test_block_4 16640 2 32 48 16
cert_test_block_4 16640 3 48 64 16
cert_test_block_4 16640 4 64 80 16
cert_test_block_4 16640 5 80 96 16
cert_test_block_4 16640 6 96 112 16
cert_test_block_4 16640 7 112 128 16
cert_test_block_4 16640 8 128 144 16
cert_test_block_4 16640 9 144 160 16
cert_test_block_4 16640 10 160 176 16
cert_test_block_4 16640 11 176 192 16
cert_test_block_4 16640 12 192 208 16
cert_test_block_4 16640 13 208 224 16
cert_test_block_4 16640 14 224 240 16
cert_test_block_4 16640 15 240 256 16
cert_test_block_4 16640 16 256 272 16
cert_test_block_4 16640 17 272 288 16
cert_test_block_4 16640 18 288 304 16
cert_test_block_4 16640 19 304 320 16
cert_test_block_4 16640 20 320 336 16
cert_test_block_4 16640 21 336 352 16
cert_test_block_4 16640 22 352 368 16
cert_test_block_4 16640 23 368 384 16
cert_test_block_4 16640 24 384 400 16
cert_test_block_4 16640 25 400 416 16
cert_test_block_4 16640 26 416 432 16
cert_test_block_4 16640 27 432 448 16
cert_test_block_4 16640 28 448 464 16
cert_test_block_4 16640 29 464 480 16
cert_test_block_4 16640 30 480 496 16
cert_test_block_4 16640 31 496 512 16
cert_test_block_4 16640 32 512 528 16
cert_test_block_4 16640 33 528 544 16
cert_test_block_4 16640 34 544 560 16
theorem test16640_complete : Interval test16640 0 560 :=
  (interval_append test16640 0 272 560
  (interval_append test16640 0 128 272
  (interval_append test16640 0 64 128
  (interval_append test16640 0 32 64
  (interval_append test16640 0 16 32
  test16640_block_0
  test16640_block_1)
  (interval_append test16640 32 48 64
  test16640_block_2
  test16640_block_3))
  (interval_append test16640 64 96 128
  (interval_append test16640 64 80 96
  test16640_block_4
  test16640_block_5)
  (interval_append test16640 96 112 128
  test16640_block_6
  test16640_block_7)))
  (interval_append test16640 128 192 272
  (interval_append test16640 128 160 192
  (interval_append test16640 128 144 160
  test16640_block_8
  test16640_block_9)
  (interval_append test16640 160 176 192
  test16640_block_10
  test16640_block_11))
  (interval_append test16640 192 224 272
  (interval_append test16640 192 208 224
  test16640_block_12
  test16640_block_13)
  (interval_append test16640 224 240 272
  test16640_block_14
  (interval_append test16640 240 256 272
  test16640_block_15
  test16640_block_16)))))
  (interval_append test16640 272 416 560
  (interval_append test16640 272 336 416
  (interval_append test16640 272 304 336
  (interval_append test16640 272 288 304
  test16640_block_17
  test16640_block_18)
  (interval_append test16640 304 320 336
  test16640_block_19
  test16640_block_20))
  (interval_append test16640 336 368 416
  (interval_append test16640 336 352 368
  test16640_block_21
  test16640_block_22)
  (interval_append test16640 368 384 416
  test16640_block_23
  (interval_append test16640 384 400 416
  test16640_block_24
  test16640_block_25))))
  (interval_append test16640 416 480 560
  (interval_append test16640 416 448 480
  (interval_append test16640 416 432 448
  test16640_block_26
  test16640_block_27)
  (interval_append test16640 448 464 480
  test16640_block_28
  test16640_block_29))
  (interval_append test16640 480 512 560
  (interval_append test16640 480 496 512
  test16640_block_30
  test16640_block_31)
  (interval_append test16640 512 528 560
  test16640_block_32
  (interval_append test16640 528 544 560
  test16640_block_33
  test16640_block_34))))))
cert_nodeInterval_4 16640 17200
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
