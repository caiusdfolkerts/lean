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
cert_test_13 69120
cert_test_block_4 69120 0 0 16 16
cert_test_block_4 69120 1 16 32 16
cert_test_block_4 69120 2 32 48 16
cert_test_block_4 69120 3 48 64 16
cert_test_block_4 69120 4 64 80 16
cert_test_block_4 69120 5 80 96 16
cert_test_block_4 69120 6 96 112 16
cert_test_block_4 69120 7 112 128 16
cert_test_block_4 69120 8 128 144 16
cert_test_block_4 69120 9 144 160 16
cert_test_block_4 69120 10 160 176 16
cert_test_block_4 69120 11 176 192 16
cert_test_block_4 69120 12 192 208 16
cert_test_block_4 69120 13 208 224 16
cert_test_block_4 69120 14 224 240 16
cert_test_block_4 69120 15 240 256 16
cert_test_block_4 69120 16 256 272 16
cert_test_block_4 69120 17 272 288 16
cert_test_block_4 69120 18 288 304 16
cert_test_block_4 69120 19 304 320 16
cert_test_block_4 69120 20 320 336 16
cert_test_block_4 69120 21 336 352 16
cert_test_block_4 69120 22 352 368 16
cert_test_block_4 69120 23 368 384 16
cert_test_block_4 69120 24 384 400 16
cert_test_block_4 69120 25 400 416 16
cert_test_block_4 69120 26 416 432 16
cert_test_block_4 69120 27 432 448 16
cert_test_block_4 69120 28 448 464 16
cert_test_block_4 69120 29 464 480 16
cert_test_block_4 69120 30 480 496 16
cert_test_block_4 69120 31 496 512 16
cert_test_block_4 69120 32 512 528 16
cert_test_block_4 69120 33 528 544 16
cert_test_block_4 69120 34 544 560 16
cert_test_block_4 69120 35 560 576 16
cert_test_block_4 69120 36 576 592 16
cert_test_block_4 69120 37 592 608 16
cert_test_block_4 69120 38 608 624 16
cert_test_block_4 69120 39 624 640 16
theorem test69120_complete : Interval test69120 0 640 :=
  (interval_append test69120 0 320 640
  (interval_append test69120 0 160 320
  (interval_append test69120 0 80 160
  (interval_append test69120 0 32 80
  (interval_append test69120 0 16 32
  test69120_block_0
  test69120_block_1)
  (interval_append test69120 32 48 80
  test69120_block_2
  (interval_append test69120 48 64 80
  test69120_block_3
  test69120_block_4)))
  (interval_append test69120 80 112 160
  (interval_append test69120 80 96 112
  test69120_block_5
  test69120_block_6)
  (interval_append test69120 112 128 160
  test69120_block_7
  (interval_append test69120 128 144 160
  test69120_block_8
  test69120_block_9))))
  (interval_append test69120 160 240 320
  (interval_append test69120 160 192 240
  (interval_append test69120 160 176 192
  test69120_block_10
  test69120_block_11)
  (interval_append test69120 192 208 240
  test69120_block_12
  (interval_append test69120 208 224 240
  test69120_block_13
  test69120_block_14)))
  (interval_append test69120 240 272 320
  (interval_append test69120 240 256 272
  test69120_block_15
  test69120_block_16)
  (interval_append test69120 272 288 320
  test69120_block_17
  (interval_append test69120 288 304 320
  test69120_block_18
  test69120_block_19)))))
  (interval_append test69120 320 480 640
  (interval_append test69120 320 400 480
  (interval_append test69120 320 352 400
  (interval_append test69120 320 336 352
  test69120_block_20
  test69120_block_21)
  (interval_append test69120 352 368 400
  test69120_block_22
  (interval_append test69120 368 384 400
  test69120_block_23
  test69120_block_24)))
  (interval_append test69120 400 432 480
  (interval_append test69120 400 416 432
  test69120_block_25
  test69120_block_26)
  (interval_append test69120 432 448 480
  test69120_block_27
  (interval_append test69120 448 464 480
  test69120_block_28
  test69120_block_29))))
  (interval_append test69120 480 560 640
  (interval_append test69120 480 512 560
  (interval_append test69120 480 496 512
  test69120_block_30
  test69120_block_31)
  (interval_append test69120 512 528 560
  test69120_block_32
  (interval_append test69120 528 544 560
  test69120_block_33
  test69120_block_34)))
  (interval_append test69120 560 592 640
  (interval_append test69120 560 576 592
  test69120_block_35
  test69120_block_36)
  (interval_append test69120 592 608 640
  test69120_block_37
  (interval_append test69120 608 624 640
  test69120_block_38
  test69120_block_39))))))
cert_nodeInterval_4 69120 69760
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
