module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 58880
cert_test_block_4 58880 0 0 16 16
cert_test_block_4 58880 1 16 32 16
cert_test_block_4 58880 2 32 48 16
cert_test_block_4 58880 3 48 64 16
cert_test_block_4 58880 4 64 80 16
cert_test_block_4 58880 5 80 96 16
cert_test_block_4 58880 6 96 112 16
cert_test_block_4 58880 7 112 128 16
cert_test_block_4 58880 8 128 144 16
cert_test_block_4 58880 9 144 160 16
cert_test_block_4 58880 10 160 176 16
cert_test_block_4 58880 11 176 192 16
cert_test_block_4 58880 12 192 208 16
cert_test_block_4 58880 13 208 224 16
cert_test_block_4 58880 14 224 240 16
cert_test_block_4 58880 15 240 256 16
cert_test_block_4 58880 16 256 272 16
cert_test_block_4 58880 17 272 288 16
cert_test_block_4 58880 18 288 304 16
cert_test_block_4 58880 19 304 320 16
cert_test_block_4 58880 20 320 336 16
cert_test_block_4 58880 21 336 352 16
cert_test_block_4 58880 22 352 368 16
cert_test_block_4 58880 23 368 384 16
cert_test_block_4 58880 24 384 400 16
cert_test_block_4 58880 25 400 416 16
cert_test_block_4 58880 26 416 432 16
cert_test_block_4 58880 27 432 448 16
cert_test_block_4 58880 28 448 464 16
cert_test_block_4 58880 29 464 480 16
cert_test_block_4 58880 30 480 496 16
cert_test_block_4 58880 31 496 512 16
cert_test_block_4 58880 32 512 528 16
cert_test_block_4 58880 33 528 544 16
cert_test_block_4 58880 34 544 560 16
cert_test_block_4 58880 35 560 576 16
cert_test_block_4 58880 36 576 592 16
cert_test_block_4 58880 37 592 608 16
cert_test_block_4 58880 38 608 624 16
cert_test_block_4 58880 39 624 640 16
theorem test58880_complete : Interval test58880 0 640 :=
  (interval_append test58880 0 320 640
  (interval_append test58880 0 160 320
  (interval_append test58880 0 80 160
  (interval_append test58880 0 32 80
  (interval_append test58880 0 16 32
  test58880_block_0
  test58880_block_1)
  (interval_append test58880 32 48 80
  test58880_block_2
  (interval_append test58880 48 64 80
  test58880_block_3
  test58880_block_4)))
  (interval_append test58880 80 112 160
  (interval_append test58880 80 96 112
  test58880_block_5
  test58880_block_6)
  (interval_append test58880 112 128 160
  test58880_block_7
  (interval_append test58880 128 144 160
  test58880_block_8
  test58880_block_9))))
  (interval_append test58880 160 240 320
  (interval_append test58880 160 192 240
  (interval_append test58880 160 176 192
  test58880_block_10
  test58880_block_11)
  (interval_append test58880 192 208 240
  test58880_block_12
  (interval_append test58880 208 224 240
  test58880_block_13
  test58880_block_14)))
  (interval_append test58880 240 272 320
  (interval_append test58880 240 256 272
  test58880_block_15
  test58880_block_16)
  (interval_append test58880 272 288 320
  test58880_block_17
  (interval_append test58880 288 304 320
  test58880_block_18
  test58880_block_19)))))
  (interval_append test58880 320 480 640
  (interval_append test58880 320 400 480
  (interval_append test58880 320 352 400
  (interval_append test58880 320 336 352
  test58880_block_20
  test58880_block_21)
  (interval_append test58880 352 368 400
  test58880_block_22
  (interval_append test58880 368 384 400
  test58880_block_23
  test58880_block_24)))
  (interval_append test58880 400 432 480
  (interval_append test58880 400 416 432
  test58880_block_25
  test58880_block_26)
  (interval_append test58880 432 448 480
  test58880_block_27
  (interval_append test58880 448 464 480
  test58880_block_28
  test58880_block_29))))
  (interval_append test58880 480 560 640
  (interval_append test58880 480 512 560
  (interval_append test58880 480 496 512
  test58880_block_30
  test58880_block_31)
  (interval_append test58880 512 528 560
  test58880_block_32
  (interval_append test58880 528 544 560
  test58880_block_33
  test58880_block_34)))
  (interval_append test58880 560 592 640
  (interval_append test58880 560 576 592
  test58880_block_35
  test58880_block_36)
  (interval_append test58880 592 608 640
  test58880_block_37
  (interval_append test58880 608 624 640
  test58880_block_38
  test58880_block_39))))))
cert_nodeInterval_4 58880 59520
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
