module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 72320
cert_test_block_4 72320 0 0 16 16
cert_test_block_4 72320 1 16 32 16
cert_test_block_4 72320 2 32 48 16
cert_test_block_4 72320 3 48 64 16
cert_test_block_4 72320 4 64 80 16
cert_test_block_4 72320 5 80 96 16
cert_test_block_4 72320 6 96 112 16
cert_test_block_4 72320 7 112 128 16
cert_test_block_4 72320 8 128 144 16
cert_test_block_4 72320 9 144 160 16
cert_test_block_4 72320 10 160 176 16
cert_test_block_4 72320 11 176 192 16
cert_test_block_4 72320 12 192 208 16
cert_test_block_4 72320 13 208 224 16
cert_test_block_4 72320 14 224 240 16
cert_test_block_4 72320 15 240 256 16
cert_test_block_4 72320 16 256 272 16
cert_test_block_4 72320 17 272 288 16
cert_test_block_4 72320 18 288 304 16
cert_test_block_4 72320 19 304 320 16
cert_test_block_4 72320 20 320 336 16
cert_test_block_4 72320 21 336 352 16
cert_test_block_4 72320 22 352 368 16
cert_test_block_4 72320 23 368 384 16
cert_test_block_4 72320 24 384 400 16
cert_test_block_4 72320 25 400 416 16
cert_test_block_4 72320 26 416 432 16
cert_test_block_4 72320 27 432 448 16
cert_test_block_4 72320 28 448 464 16
cert_test_block_4 72320 29 464 480 16
cert_test_block_4 72320 30 480 496 16
cert_test_block_4 72320 31 496 512 16
cert_test_block_4 72320 32 512 528 16
cert_test_block_4 72320 33 528 544 16
cert_test_block_4 72320 34 544 560 16
cert_test_block_4 72320 35 560 576 16
cert_test_block_4 72320 36 576 592 16
cert_test_block_4 72320 37 592 608 16
cert_test_block_4 72320 38 608 624 16
cert_test_block_4 72320 39 624 640 16
theorem test72320_complete : Interval test72320 0 640 :=
  (interval_append test72320 0 320 640
  (interval_append test72320 0 160 320
  (interval_append test72320 0 80 160
  (interval_append test72320 0 32 80
  (interval_append test72320 0 16 32
  test72320_block_0
  test72320_block_1)
  (interval_append test72320 32 48 80
  test72320_block_2
  (interval_append test72320 48 64 80
  test72320_block_3
  test72320_block_4)))
  (interval_append test72320 80 112 160
  (interval_append test72320 80 96 112
  test72320_block_5
  test72320_block_6)
  (interval_append test72320 112 128 160
  test72320_block_7
  (interval_append test72320 128 144 160
  test72320_block_8
  test72320_block_9))))
  (interval_append test72320 160 240 320
  (interval_append test72320 160 192 240
  (interval_append test72320 160 176 192
  test72320_block_10
  test72320_block_11)
  (interval_append test72320 192 208 240
  test72320_block_12
  (interval_append test72320 208 224 240
  test72320_block_13
  test72320_block_14)))
  (interval_append test72320 240 272 320
  (interval_append test72320 240 256 272
  test72320_block_15
  test72320_block_16)
  (interval_append test72320 272 288 320
  test72320_block_17
  (interval_append test72320 288 304 320
  test72320_block_18
  test72320_block_19)))))
  (interval_append test72320 320 480 640
  (interval_append test72320 320 400 480
  (interval_append test72320 320 352 400
  (interval_append test72320 320 336 352
  test72320_block_20
  test72320_block_21)
  (interval_append test72320 352 368 400
  test72320_block_22
  (interval_append test72320 368 384 400
  test72320_block_23
  test72320_block_24)))
  (interval_append test72320 400 432 480
  (interval_append test72320 400 416 432
  test72320_block_25
  test72320_block_26)
  (interval_append test72320 432 448 480
  test72320_block_27
  (interval_append test72320 448 464 480
  test72320_block_28
  test72320_block_29))))
  (interval_append test72320 480 560 640
  (interval_append test72320 480 512 560
  (interval_append test72320 480 496 512
  test72320_block_30
  test72320_block_31)
  (interval_append test72320 512 528 560
  test72320_block_32
  (interval_append test72320 528 544 560
  test72320_block_33
  test72320_block_34)))
  (interval_append test72320 560 592 640
  (interval_append test72320 560 576 592
  test72320_block_35
  test72320_block_36)
  (interval_append test72320 592 608 640
  test72320_block_37
  (interval_append test72320 608 624 640
  test72320_block_38
  test72320_block_39))))))
cert_nodeInterval_4 72320 72960
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
