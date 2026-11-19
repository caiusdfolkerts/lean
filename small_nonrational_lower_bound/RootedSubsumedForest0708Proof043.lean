module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 27520
cert_test_block_3 27520 0 0 16 16
cert_test_block_3 27520 1 16 32 16
cert_test_block_3 27520 2 32 48 16
cert_test_block_3 27520 3 48 64 16
cert_test_block_3 27520 4 64 80 16
cert_test_block_3 27520 5 80 96 16
cert_test_block_3 27520 6 96 112 16
cert_test_block_3 27520 7 112 128 16
cert_test_block_3 27520 8 128 144 16
cert_test_block_3 27520 9 144 160 16
cert_test_block_3 27520 10 160 176 16
cert_test_block_3 27520 11 176 192 16
cert_test_block_3 27520 12 192 208 16
cert_test_block_3 27520 13 208 224 16
cert_test_block_3 27520 14 224 240 16
cert_test_block_3 27520 15 240 256 16
cert_test_block_3 27520 16 256 272 16
cert_test_block_3 27520 17 272 288 16
cert_test_block_3 27520 18 288 304 16
cert_test_block_3 27520 19 304 320 16
cert_test_block_3 27520 20 320 336 16
cert_test_block_3 27520 21 336 352 16
cert_test_block_3 27520 22 352 368 16
cert_test_block_3 27520 23 368 384 16
cert_test_block_3 27520 24 384 400 16
cert_test_block_3 27520 25 400 416 16
cert_test_block_3 27520 26 416 432 16
cert_test_block_3 27520 27 432 448 16
cert_test_block_3 27520 28 448 464 16
cert_test_block_3 27520 29 464 480 16
cert_test_block_3 27520 30 480 496 16
cert_test_block_3 27520 31 496 512 16
cert_test_block_3 27520 32 512 528 16
cert_test_block_3 27520 33 528 544 16
cert_test_block_3 27520 34 544 560 16
cert_test_block_3 27520 35 560 576 16
cert_test_block_3 27520 36 576 592 16
cert_test_block_3 27520 37 592 608 16
cert_test_block_3 27520 38 608 624 16
cert_test_block_3 27520 39 624 640 16
theorem test27520_complete : Interval test27520 0 640 :=
  (interval_append test27520 0 320 640
  (interval_append test27520 0 160 320
  (interval_append test27520 0 80 160
  (interval_append test27520 0 32 80
  (interval_append test27520 0 16 32
  test27520_block_0
  test27520_block_1)
  (interval_append test27520 32 48 80
  test27520_block_2
  (interval_append test27520 48 64 80
  test27520_block_3
  test27520_block_4)))
  (interval_append test27520 80 112 160
  (interval_append test27520 80 96 112
  test27520_block_5
  test27520_block_6)
  (interval_append test27520 112 128 160
  test27520_block_7
  (interval_append test27520 128 144 160
  test27520_block_8
  test27520_block_9))))
  (interval_append test27520 160 240 320
  (interval_append test27520 160 192 240
  (interval_append test27520 160 176 192
  test27520_block_10
  test27520_block_11)
  (interval_append test27520 192 208 240
  test27520_block_12
  (interval_append test27520 208 224 240
  test27520_block_13
  test27520_block_14)))
  (interval_append test27520 240 272 320
  (interval_append test27520 240 256 272
  test27520_block_15
  test27520_block_16)
  (interval_append test27520 272 288 320
  test27520_block_17
  (interval_append test27520 288 304 320
  test27520_block_18
  test27520_block_19)))))
  (interval_append test27520 320 480 640
  (interval_append test27520 320 400 480
  (interval_append test27520 320 352 400
  (interval_append test27520 320 336 352
  test27520_block_20
  test27520_block_21)
  (interval_append test27520 352 368 400
  test27520_block_22
  (interval_append test27520 368 384 400
  test27520_block_23
  test27520_block_24)))
  (interval_append test27520 400 432 480
  (interval_append test27520 400 416 432
  test27520_block_25
  test27520_block_26)
  (interval_append test27520 432 448 480
  test27520_block_27
  (interval_append test27520 448 464 480
  test27520_block_28
  test27520_block_29))))
  (interval_append test27520 480 560 640
  (interval_append test27520 480 512 560
  (interval_append test27520 480 496 512
  test27520_block_30
  test27520_block_31)
  (interval_append test27520 512 528 560
  test27520_block_32
  (interval_append test27520 528 544 560
  test27520_block_33
  test27520_block_34)))
  (interval_append test27520 560 592 640
  (interval_append test27520 560 576 592
  test27520_block_35
  test27520_block_36)
  (interval_append test27520 592 608 640
  test27520_block_37
  (interval_append test27520 608 624 640
  test27520_block_38
  test27520_block_39))))))
cert_nodeInterval_3 27520 28160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
