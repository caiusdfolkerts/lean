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
cert_test_13 46080
cert_test_block_4 46080 0 0 16 16
cert_test_block_4 46080 1 16 32 16
cert_test_block_4 46080 2 32 48 16
cert_test_block_4 46080 3 48 64 16
cert_test_block_4 46080 4 64 80 16
cert_test_block_4 46080 5 80 96 16
cert_test_block_4 46080 6 96 112 16
cert_test_block_4 46080 7 112 128 16
cert_test_block_4 46080 8 128 144 16
cert_test_block_4 46080 9 144 160 16
cert_test_block_4 46080 10 160 176 16
cert_test_block_4 46080 11 176 192 16
cert_test_block_4 46080 12 192 208 16
cert_test_block_4 46080 13 208 224 16
cert_test_block_4 46080 14 224 240 16
cert_test_block_4 46080 15 240 256 16
cert_test_block_4 46080 16 256 272 16
cert_test_block_4 46080 17 272 288 16
cert_test_block_4 46080 18 288 304 16
cert_test_block_4 46080 19 304 320 16
cert_test_block_4 46080 20 320 336 16
cert_test_block_4 46080 21 336 352 16
cert_test_block_4 46080 22 352 368 16
cert_test_block_4 46080 23 368 384 16
cert_test_block_4 46080 24 384 400 16
cert_test_block_4 46080 25 400 416 16
cert_test_block_4 46080 26 416 432 16
cert_test_block_4 46080 27 432 448 16
cert_test_block_4 46080 28 448 464 16
cert_test_block_4 46080 29 464 480 16
cert_test_block_4 46080 30 480 496 16
cert_test_block_4 46080 31 496 512 16
cert_test_block_4 46080 32 512 528 16
cert_test_block_4 46080 33 528 544 16
cert_test_block_4 46080 34 544 560 16
cert_test_block_4 46080 35 560 576 16
cert_test_block_4 46080 36 576 592 16
cert_test_block_4 46080 37 592 608 16
cert_test_block_4 46080 38 608 624 16
cert_test_block_4 46080 39 624 640 16
theorem test46080_complete : Interval test46080 0 640 :=
  (interval_append test46080 0 320 640
  (interval_append test46080 0 160 320
  (interval_append test46080 0 80 160
  (interval_append test46080 0 32 80
  (interval_append test46080 0 16 32
  test46080_block_0
  test46080_block_1)
  (interval_append test46080 32 48 80
  test46080_block_2
  (interval_append test46080 48 64 80
  test46080_block_3
  test46080_block_4)))
  (interval_append test46080 80 112 160
  (interval_append test46080 80 96 112
  test46080_block_5
  test46080_block_6)
  (interval_append test46080 112 128 160
  test46080_block_7
  (interval_append test46080 128 144 160
  test46080_block_8
  test46080_block_9))))
  (interval_append test46080 160 240 320
  (interval_append test46080 160 192 240
  (interval_append test46080 160 176 192
  test46080_block_10
  test46080_block_11)
  (interval_append test46080 192 208 240
  test46080_block_12
  (interval_append test46080 208 224 240
  test46080_block_13
  test46080_block_14)))
  (interval_append test46080 240 272 320
  (interval_append test46080 240 256 272
  test46080_block_15
  test46080_block_16)
  (interval_append test46080 272 288 320
  test46080_block_17
  (interval_append test46080 288 304 320
  test46080_block_18
  test46080_block_19)))))
  (interval_append test46080 320 480 640
  (interval_append test46080 320 400 480
  (interval_append test46080 320 352 400
  (interval_append test46080 320 336 352
  test46080_block_20
  test46080_block_21)
  (interval_append test46080 352 368 400
  test46080_block_22
  (interval_append test46080 368 384 400
  test46080_block_23
  test46080_block_24)))
  (interval_append test46080 400 432 480
  (interval_append test46080 400 416 432
  test46080_block_25
  test46080_block_26)
  (interval_append test46080 432 448 480
  test46080_block_27
  (interval_append test46080 448 464 480
  test46080_block_28
  test46080_block_29))))
  (interval_append test46080 480 560 640
  (interval_append test46080 480 512 560
  (interval_append test46080 480 496 512
  test46080_block_30
  test46080_block_31)
  (interval_append test46080 512 528 560
  test46080_block_32
  (interval_append test46080 528 544 560
  test46080_block_33
  test46080_block_34)))
  (interval_append test46080 560 592 640
  (interval_append test46080 560 576 592
  test46080_block_35
  test46080_block_36)
  (interval_append test46080 592 608 640
  test46080_block_37
  (interval_append test46080 608 624 640
  test46080_block_38
  test46080_block_39))))))
cert_nodeInterval_4 46080 46720
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
