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
cert_test_13 31360
cert_test_block_4 31360 0 0 16 16
cert_test_block_4 31360 1 16 32 16
cert_test_block_4 31360 2 32 48 16
cert_test_block_4 31360 3 48 64 16
cert_test_block_4 31360 4 64 80 16
cert_test_block_4 31360 5 80 96 16
cert_test_block_4 31360 6 96 112 16
cert_test_block_4 31360 7 112 128 16
cert_test_block_4 31360 8 128 144 16
cert_test_block_4 31360 9 144 160 16
cert_test_block_4 31360 10 160 176 16
cert_test_block_4 31360 11 176 192 16
cert_test_block_4 31360 12 192 208 16
cert_test_block_4 31360 13 208 224 16
cert_test_block_4 31360 14 224 240 16
cert_test_block_4 31360 15 240 256 16
cert_test_block_4 31360 16 256 272 16
cert_test_block_4 31360 17 272 288 16
cert_test_block_4 31360 18 288 304 16
cert_test_block_4 31360 19 304 320 16
cert_test_block_4 31360 20 320 336 16
cert_test_block_4 31360 21 336 352 16
cert_test_block_4 31360 22 352 368 16
cert_test_block_4 31360 23 368 384 16
cert_test_block_4 31360 24 384 400 16
cert_test_block_4 31360 25 400 416 16
cert_test_block_4 31360 26 416 432 16
cert_test_block_4 31360 27 432 448 16
cert_test_block_4 31360 28 448 464 16
cert_test_block_4 31360 29 464 480 16
cert_test_block_4 31360 30 480 496 16
cert_test_block_4 31360 31 496 512 16
cert_test_block_4 31360 32 512 528 16
cert_test_block_4 31360 33 528 544 16
cert_test_block_4 31360 34 544 560 16
cert_test_block_4 31360 35 560 576 16
cert_test_block_4 31360 36 576 592 16
cert_test_block_4 31360 37 592 608 16
cert_test_block_4 31360 38 608 624 16
cert_test_block_4 31360 39 624 640 16
theorem test31360_complete : Interval test31360 0 640 :=
  (interval_append test31360 0 320 640
  (interval_append test31360 0 160 320
  (interval_append test31360 0 80 160
  (interval_append test31360 0 32 80
  (interval_append test31360 0 16 32
  test31360_block_0
  test31360_block_1)
  (interval_append test31360 32 48 80
  test31360_block_2
  (interval_append test31360 48 64 80
  test31360_block_3
  test31360_block_4)))
  (interval_append test31360 80 112 160
  (interval_append test31360 80 96 112
  test31360_block_5
  test31360_block_6)
  (interval_append test31360 112 128 160
  test31360_block_7
  (interval_append test31360 128 144 160
  test31360_block_8
  test31360_block_9))))
  (interval_append test31360 160 240 320
  (interval_append test31360 160 192 240
  (interval_append test31360 160 176 192
  test31360_block_10
  test31360_block_11)
  (interval_append test31360 192 208 240
  test31360_block_12
  (interval_append test31360 208 224 240
  test31360_block_13
  test31360_block_14)))
  (interval_append test31360 240 272 320
  (interval_append test31360 240 256 272
  test31360_block_15
  test31360_block_16)
  (interval_append test31360 272 288 320
  test31360_block_17
  (interval_append test31360 288 304 320
  test31360_block_18
  test31360_block_19)))))
  (interval_append test31360 320 480 640
  (interval_append test31360 320 400 480
  (interval_append test31360 320 352 400
  (interval_append test31360 320 336 352
  test31360_block_20
  test31360_block_21)
  (interval_append test31360 352 368 400
  test31360_block_22
  (interval_append test31360 368 384 400
  test31360_block_23
  test31360_block_24)))
  (interval_append test31360 400 432 480
  (interval_append test31360 400 416 432
  test31360_block_25
  test31360_block_26)
  (interval_append test31360 432 448 480
  test31360_block_27
  (interval_append test31360 448 464 480
  test31360_block_28
  test31360_block_29))))
  (interval_append test31360 480 560 640
  (interval_append test31360 480 512 560
  (interval_append test31360 480 496 512
  test31360_block_30
  test31360_block_31)
  (interval_append test31360 512 528 560
  test31360_block_32
  (interval_append test31360 528 544 560
  test31360_block_33
  test31360_block_34)))
  (interval_append test31360 560 592 640
  (interval_append test31360 560 576 592
  test31360_block_35
  test31360_block_36)
  (interval_append test31360 592 608 640
  test31360_block_37
  (interval_append test31360 608 624 640
  test31360_block_38
  test31360_block_39))))))
cert_nodeInterval_4 31360 32000
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
