module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 85120
cert_test_block_3 85120 0 0 16 16
cert_test_block_3 85120 1 16 32 16
cert_test_block_3 85120 2 32 48 16
cert_test_block_3 85120 3 48 64 16
cert_test_block_3 85120 4 64 80 16
cert_test_block_3 85120 5 80 96 16
cert_test_block_3 85120 6 96 112 16
cert_test_block_3 85120 7 112 128 16
cert_test_block_3 85120 8 128 144 16
cert_test_block_3 85120 9 144 160 16
cert_test_block_3 85120 10 160 176 16
cert_test_block_3 85120 11 176 192 16
cert_test_block_3 85120 12 192 208 16
cert_test_block_3 85120 13 208 224 16
cert_test_block_3 85120 14 224 240 16
cert_test_block_3 85120 15 240 256 16
cert_test_block_3 85120 16 256 272 16
cert_test_block_3 85120 17 272 288 16
cert_test_block_3 85120 18 288 304 16
cert_test_block_3 85120 19 304 320 16
cert_test_block_3 85120 20 320 336 16
cert_test_block_3 85120 21 336 352 16
cert_test_block_3 85120 22 352 368 16
cert_test_block_3 85120 23 368 384 16
cert_test_block_3 85120 24 384 400 16
cert_test_block_3 85120 25 400 416 16
cert_test_block_3 85120 26 416 432 16
cert_test_block_3 85120 27 432 448 16
cert_test_block_3 85120 28 448 464 16
cert_test_block_3 85120 29 464 480 16
cert_test_block_3 85120 30 480 496 16
cert_test_block_3 85120 31 496 512 16
cert_test_block_3 85120 32 512 528 16
cert_test_block_3 85120 33 528 544 16
cert_test_block_3 85120 34 544 560 16
cert_test_block_3 85120 35 560 576 16
cert_test_block_3 85120 36 576 592 16
cert_test_block_3 85120 37 592 608 16
cert_test_block_3 85120 38 608 624 16
cert_test_block_3 85120 39 624 640 16
theorem test85120_complete : Interval test85120 0 640 :=
  (interval_append test85120 0 320 640
  (interval_append test85120 0 160 320
  (interval_append test85120 0 80 160
  (interval_append test85120 0 32 80
  (interval_append test85120 0 16 32
  test85120_block_0
  test85120_block_1)
  (interval_append test85120 32 48 80
  test85120_block_2
  (interval_append test85120 48 64 80
  test85120_block_3
  test85120_block_4)))
  (interval_append test85120 80 112 160
  (interval_append test85120 80 96 112
  test85120_block_5
  test85120_block_6)
  (interval_append test85120 112 128 160
  test85120_block_7
  (interval_append test85120 128 144 160
  test85120_block_8
  test85120_block_9))))
  (interval_append test85120 160 240 320
  (interval_append test85120 160 192 240
  (interval_append test85120 160 176 192
  test85120_block_10
  test85120_block_11)
  (interval_append test85120 192 208 240
  test85120_block_12
  (interval_append test85120 208 224 240
  test85120_block_13
  test85120_block_14)))
  (interval_append test85120 240 272 320
  (interval_append test85120 240 256 272
  test85120_block_15
  test85120_block_16)
  (interval_append test85120 272 288 320
  test85120_block_17
  (interval_append test85120 288 304 320
  test85120_block_18
  test85120_block_19)))))
  (interval_append test85120 320 480 640
  (interval_append test85120 320 400 480
  (interval_append test85120 320 352 400
  (interval_append test85120 320 336 352
  test85120_block_20
  test85120_block_21)
  (interval_append test85120 352 368 400
  test85120_block_22
  (interval_append test85120 368 384 400
  test85120_block_23
  test85120_block_24)))
  (interval_append test85120 400 432 480
  (interval_append test85120 400 416 432
  test85120_block_25
  test85120_block_26)
  (interval_append test85120 432 448 480
  test85120_block_27
  (interval_append test85120 448 464 480
  test85120_block_28
  test85120_block_29))))
  (interval_append test85120 480 560 640
  (interval_append test85120 480 512 560
  (interval_append test85120 480 496 512
  test85120_block_30
  test85120_block_31)
  (interval_append test85120 512 528 560
  test85120_block_32
  (interval_append test85120 528 544 560
  test85120_block_33
  test85120_block_34)))
  (interval_append test85120 560 592 640
  (interval_append test85120 560 576 592
  test85120_block_35
  test85120_block_36)
  (interval_append test85120 592 608 640
  test85120_block_37
  (interval_append test85120 608 624 640
  test85120_block_38
  test85120_block_39))))))
cert_nodeInterval_3 85120 85760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
