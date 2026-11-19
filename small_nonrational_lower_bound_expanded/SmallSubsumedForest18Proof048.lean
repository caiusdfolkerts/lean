module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 30720
cert_test_block_4 30720 0 0 16 16
cert_test_block_4 30720 1 16 32 16
cert_test_block_4 30720 2 32 48 16
cert_test_block_4 30720 3 48 64 16
cert_test_block_4 30720 4 64 80 16
cert_test_block_4 30720 5 80 96 16
cert_test_block_4 30720 6 96 112 16
cert_test_block_4 30720 7 112 128 16
cert_test_block_4 30720 8 128 144 16
cert_test_block_4 30720 9 144 160 16
cert_test_block_4 30720 10 160 176 16
cert_test_block_4 30720 11 176 192 16
cert_test_block_4 30720 12 192 208 16
cert_test_block_4 30720 13 208 224 16
cert_test_block_4 30720 14 224 240 16
cert_test_block_4 30720 15 240 256 16
cert_test_block_4 30720 16 256 272 16
cert_test_block_4 30720 17 272 288 16
cert_test_block_4 30720 18 288 304 16
cert_test_block_4 30720 19 304 320 16
cert_test_block_4 30720 20 320 336 16
cert_test_block_4 30720 21 336 352 16
cert_test_block_4 30720 22 352 368 16
cert_test_block_4 30720 23 368 384 16
cert_test_block_4 30720 24 384 400 16
cert_test_block_4 30720 25 400 416 16
cert_test_block_4 30720 26 416 432 16
cert_test_block_4 30720 27 432 448 16
cert_test_block_4 30720 28 448 464 16
cert_test_block_4 30720 29 464 480 16
cert_test_block_4 30720 30 480 496 16
cert_test_block_4 30720 31 496 512 16
cert_test_block_4 30720 32 512 528 16
cert_test_block_4 30720 33 528 544 16
cert_test_block_4 30720 34 544 560 16
cert_test_block_4 30720 35 560 576 16
cert_test_block_4 30720 36 576 592 16
cert_test_block_4 30720 37 592 608 16
cert_test_block_4 30720 38 608 624 16
cert_test_block_4 30720 39 624 640 16
theorem test30720_complete : Interval test30720 0 640 :=
  (interval_append test30720 0 320 640
  (interval_append test30720 0 160 320
  (interval_append test30720 0 80 160
  (interval_append test30720 0 32 80
  (interval_append test30720 0 16 32
  test30720_block_0
  test30720_block_1)
  (interval_append test30720 32 48 80
  test30720_block_2
  (interval_append test30720 48 64 80
  test30720_block_3
  test30720_block_4)))
  (interval_append test30720 80 112 160
  (interval_append test30720 80 96 112
  test30720_block_5
  test30720_block_6)
  (interval_append test30720 112 128 160
  test30720_block_7
  (interval_append test30720 128 144 160
  test30720_block_8
  test30720_block_9))))
  (interval_append test30720 160 240 320
  (interval_append test30720 160 192 240
  (interval_append test30720 160 176 192
  test30720_block_10
  test30720_block_11)
  (interval_append test30720 192 208 240
  test30720_block_12
  (interval_append test30720 208 224 240
  test30720_block_13
  test30720_block_14)))
  (interval_append test30720 240 272 320
  (interval_append test30720 240 256 272
  test30720_block_15
  test30720_block_16)
  (interval_append test30720 272 288 320
  test30720_block_17
  (interval_append test30720 288 304 320
  test30720_block_18
  test30720_block_19)))))
  (interval_append test30720 320 480 640
  (interval_append test30720 320 400 480
  (interval_append test30720 320 352 400
  (interval_append test30720 320 336 352
  test30720_block_20
  test30720_block_21)
  (interval_append test30720 352 368 400
  test30720_block_22
  (interval_append test30720 368 384 400
  test30720_block_23
  test30720_block_24)))
  (interval_append test30720 400 432 480
  (interval_append test30720 400 416 432
  test30720_block_25
  test30720_block_26)
  (interval_append test30720 432 448 480
  test30720_block_27
  (interval_append test30720 448 464 480
  test30720_block_28
  test30720_block_29))))
  (interval_append test30720 480 560 640
  (interval_append test30720 480 512 560
  (interval_append test30720 480 496 512
  test30720_block_30
  test30720_block_31)
  (interval_append test30720 512 528 560
  test30720_block_32
  (interval_append test30720 528 544 560
  test30720_block_33
  test30720_block_34)))
  (interval_append test30720 560 592 640
  (interval_append test30720 560 576 592
  test30720_block_35
  test30720_block_36)
  (interval_append test30720 592 608 640
  test30720_block_37
  (interval_append test30720 608 624 640
  test30720_block_38
  test30720_block_39))))))
cert_nodeInterval_4 30720 31360
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
