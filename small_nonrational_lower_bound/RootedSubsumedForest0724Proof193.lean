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
cert_test_11 123520
cert_test_block_3 123520 0 0 16 16
cert_test_block_3 123520 1 16 32 16
cert_test_block_3 123520 2 32 48 16
cert_test_block_3 123520 3 48 64 16
cert_test_block_3 123520 4 64 80 16
cert_test_block_3 123520 5 80 96 16
cert_test_block_3 123520 6 96 112 16
cert_test_block_3 123520 7 112 128 16
cert_test_block_3 123520 8 128 144 16
cert_test_block_3 123520 9 144 160 16
cert_test_block_3 123520 10 160 176 16
cert_test_block_3 123520 11 176 192 16
cert_test_block_3 123520 12 192 208 16
cert_test_block_3 123520 13 208 224 16
cert_test_block_3 123520 14 224 240 16
cert_test_block_3 123520 15 240 256 16
cert_test_block_3 123520 16 256 272 16
cert_test_block_3 123520 17 272 288 16
cert_test_block_3 123520 18 288 304 16
cert_test_block_3 123520 19 304 320 16
cert_test_block_3 123520 20 320 336 16
cert_test_block_3 123520 21 336 352 16
cert_test_block_3 123520 22 352 368 16
cert_test_block_3 123520 23 368 384 16
cert_test_block_3 123520 24 384 400 16
cert_test_block_3 123520 25 400 416 16
cert_test_block_3 123520 26 416 432 16
cert_test_block_3 123520 27 432 448 16
cert_test_block_3 123520 28 448 464 16
cert_test_block_3 123520 29 464 480 16
cert_test_block_3 123520 30 480 496 16
cert_test_block_3 123520 31 496 512 16
cert_test_block_3 123520 32 512 528 16
cert_test_block_3 123520 33 528 544 16
cert_test_block_3 123520 34 544 560 16
cert_test_block_3 123520 35 560 576 16
cert_test_block_3 123520 36 576 592 16
cert_test_block_3 123520 37 592 608 16
cert_test_block_3 123520 38 608 624 16
cert_test_block_3 123520 39 624 640 16
theorem test123520_complete : Interval test123520 0 640 :=
  (interval_append test123520 0 320 640
  (interval_append test123520 0 160 320
  (interval_append test123520 0 80 160
  (interval_append test123520 0 32 80
  (interval_append test123520 0 16 32
  test123520_block_0
  test123520_block_1)
  (interval_append test123520 32 48 80
  test123520_block_2
  (interval_append test123520 48 64 80
  test123520_block_3
  test123520_block_4)))
  (interval_append test123520 80 112 160
  (interval_append test123520 80 96 112
  test123520_block_5
  test123520_block_6)
  (interval_append test123520 112 128 160
  test123520_block_7
  (interval_append test123520 128 144 160
  test123520_block_8
  test123520_block_9))))
  (interval_append test123520 160 240 320
  (interval_append test123520 160 192 240
  (interval_append test123520 160 176 192
  test123520_block_10
  test123520_block_11)
  (interval_append test123520 192 208 240
  test123520_block_12
  (interval_append test123520 208 224 240
  test123520_block_13
  test123520_block_14)))
  (interval_append test123520 240 272 320
  (interval_append test123520 240 256 272
  test123520_block_15
  test123520_block_16)
  (interval_append test123520 272 288 320
  test123520_block_17
  (interval_append test123520 288 304 320
  test123520_block_18
  test123520_block_19)))))
  (interval_append test123520 320 480 640
  (interval_append test123520 320 400 480
  (interval_append test123520 320 352 400
  (interval_append test123520 320 336 352
  test123520_block_20
  test123520_block_21)
  (interval_append test123520 352 368 400
  test123520_block_22
  (interval_append test123520 368 384 400
  test123520_block_23
  test123520_block_24)))
  (interval_append test123520 400 432 480
  (interval_append test123520 400 416 432
  test123520_block_25
  test123520_block_26)
  (interval_append test123520 432 448 480
  test123520_block_27
  (interval_append test123520 448 464 480
  test123520_block_28
  test123520_block_29))))
  (interval_append test123520 480 560 640
  (interval_append test123520 480 512 560
  (interval_append test123520 480 496 512
  test123520_block_30
  test123520_block_31)
  (interval_append test123520 512 528 560
  test123520_block_32
  (interval_append test123520 528 544 560
  test123520_block_33
  test123520_block_34)))
  (interval_append test123520 560 592 640
  (interval_append test123520 560 576 592
  test123520_block_35
  test123520_block_36)
  (interval_append test123520 592 608 640
  test123520_block_37
  (interval_append test123520 608 624 640
  test123520_block_38
  test123520_block_39))))))
cert_nodeInterval_3 123520 124160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
