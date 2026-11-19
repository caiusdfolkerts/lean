module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0283Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 0
cert_test_block_3 0 0 0 16 16
cert_test_block_3 0 1 16 32 16
cert_test_block_3 0 2 32 48 16
cert_test_block_3 0 3 48 64 16
cert_test_block_3 0 4 64 80 16
cert_test_block_3 0 5 80 96 16
cert_test_block_3 0 6 96 112 16
cert_test_block_3 0 7 112 128 16
cert_test_block_3 0 8 128 144 16
cert_test_block_3 0 9 144 160 16
cert_test_block_3 0 10 160 176 16
cert_test_block_3 0 11 176 192 16
cert_test_block_3 0 12 192 208 16
cert_test_block_3 0 13 208 224 16
cert_test_block_3 0 14 224 240 16
cert_test_block_3 0 15 240 256 16
cert_test_block_3 0 16 256 272 16
cert_test_block_3 0 17 272 288 16
cert_test_block_3 0 18 288 304 16
cert_test_block_3 0 19 304 320 16
cert_test_block_3 0 20 320 336 16
cert_test_block_3 0 21 336 352 16
cert_test_block_3 0 22 352 368 16
cert_test_block_3 0 23 368 384 16
cert_test_block_3 0 24 384 400 16
cert_test_block_3 0 25 400 416 16
cert_test_block_3 0 26 416 432 16
cert_test_block_3 0 27 432 448 16
cert_test_block_3 0 28 448 464 16
cert_test_block_3 0 29 464 480 16
cert_test_block_3 0 30 480 496 16
cert_test_block_3 0 31 496 512 16
cert_test_block_3 0 32 512 528 16
cert_test_block_3 0 33 528 544 16
cert_test_block_3 0 34 544 560 16
cert_test_block_3 0 35 560 576 16
cert_test_block_3 0 36 576 592 16
cert_test_block_3 0 37 592 608 16
cert_test_block_3 0 38 608 624 16
cert_test_block_3 0 39 624 640 16
theorem test0_complete : Interval test0 0 640 :=
  (interval_append test0 0 320 640
  (interval_append test0 0 160 320
  (interval_append test0 0 80 160
  (interval_append test0 0 32 80
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 80
  test0_block_2
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)))
  (interval_append test0 80 112 160
  (interval_append test0 80 96 112
  test0_block_5
  test0_block_6)
  (interval_append test0 112 128 160
  test0_block_7
  (interval_append test0 128 144 160
  test0_block_8
  test0_block_9))))
  (interval_append test0 160 240 320
  (interval_append test0 160 192 240
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11)
  (interval_append test0 192 208 240
  test0_block_12
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14)))
  (interval_append test0 240 272 320
  (interval_append test0 240 256 272
  test0_block_15
  test0_block_16)
  (interval_append test0 272 288 320
  test0_block_17
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19)))))
  (interval_append test0 320 480 640
  (interval_append test0 320 400 480
  (interval_append test0 320 352 400
  (interval_append test0 320 336 352
  test0_block_20
  test0_block_21)
  (interval_append test0 352 368 400
  test0_block_22
  (interval_append test0 368 384 400
  test0_block_23
  test0_block_24)))
  (interval_append test0 400 432 480
  (interval_append test0 400 416 432
  test0_block_25
  test0_block_26)
  (interval_append test0 432 448 480
  test0_block_27
  (interval_append test0 448 464 480
  test0_block_28
  test0_block_29))))
  (interval_append test0 480 560 640
  (interval_append test0 480 512 560
  (interval_append test0 480 496 512
  test0_block_30
  test0_block_31)
  (interval_append test0 512 528 560
  test0_block_32
  (interval_append test0 528 544 560
  test0_block_33
  test0_block_34)))
  (interval_append test0 560 592 640
  (interval_append test0 560 576 592
  test0_block_35
  test0_block_36)
  (interval_append test0 592 608 640
  test0_block_37
  (interval_append test0 608 624 640
  test0_block_38
  test0_block_39))))))
cert_nodeInterval_3 0 640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
