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
cert_test_11 145920
cert_test_block_3 145920 0 0 16 16
cert_test_block_3 145920 1 16 32 16
cert_test_block_3 145920 2 32 48 16
cert_test_block_3 145920 3 48 64 16
cert_test_block_3 145920 4 64 80 16
cert_test_block_3 145920 5 80 96 16
cert_test_block_3 145920 6 96 112 16
cert_test_block_3 145920 7 112 128 16
cert_test_block_3 145920 8 128 144 16
cert_test_block_3 145920 9 144 160 16
cert_test_block_3 145920 10 160 176 16
cert_test_block_3 145920 11 176 192 16
cert_test_block_3 145920 12 192 208 16
cert_test_block_3 145920 13 208 224 16
cert_test_block_3 145920 14 224 240 16
cert_test_block_3 145920 15 240 256 16
cert_test_block_3 145920 16 256 272 16
cert_test_block_3 145920 17 272 288 16
cert_test_block_3 145920 18 288 304 16
cert_test_block_3 145920 19 304 320 16
cert_test_block_3 145920 20 320 336 16
cert_test_block_3 145920 21 336 352 16
cert_test_block_3 145920 22 352 368 16
cert_test_block_3 145920 23 368 384 16
cert_test_block_3 145920 24 384 400 16
cert_test_block_3 145920 25 400 416 16
cert_test_block_3 145920 26 416 432 16
cert_test_block_3 145920 27 432 448 16
cert_test_block_3 145920 28 448 464 16
cert_test_block_3 145920 29 464 480 16
cert_test_block_3 145920 30 480 496 16
cert_test_block_3 145920 31 496 512 16
cert_test_block_3 145920 32 512 528 16
cert_test_block_3 145920 33 528 544 16
cert_test_block_3 145920 34 544 560 16
cert_test_block_3 145920 35 560 576 16
cert_test_block_3 145920 36 576 592 16
cert_test_block_3 145920 37 592 608 16
cert_test_block_3 145920 38 608 624 16
cert_test_block_3 145920 39 624 640 16
theorem test145920_complete : Interval test145920 0 640 :=
  (interval_append test145920 0 320 640
  (interval_append test145920 0 160 320
  (interval_append test145920 0 80 160
  (interval_append test145920 0 32 80
  (interval_append test145920 0 16 32
  test145920_block_0
  test145920_block_1)
  (interval_append test145920 32 48 80
  test145920_block_2
  (interval_append test145920 48 64 80
  test145920_block_3
  test145920_block_4)))
  (interval_append test145920 80 112 160
  (interval_append test145920 80 96 112
  test145920_block_5
  test145920_block_6)
  (interval_append test145920 112 128 160
  test145920_block_7
  (interval_append test145920 128 144 160
  test145920_block_8
  test145920_block_9))))
  (interval_append test145920 160 240 320
  (interval_append test145920 160 192 240
  (interval_append test145920 160 176 192
  test145920_block_10
  test145920_block_11)
  (interval_append test145920 192 208 240
  test145920_block_12
  (interval_append test145920 208 224 240
  test145920_block_13
  test145920_block_14)))
  (interval_append test145920 240 272 320
  (interval_append test145920 240 256 272
  test145920_block_15
  test145920_block_16)
  (interval_append test145920 272 288 320
  test145920_block_17
  (interval_append test145920 288 304 320
  test145920_block_18
  test145920_block_19)))))
  (interval_append test145920 320 480 640
  (interval_append test145920 320 400 480
  (interval_append test145920 320 352 400
  (interval_append test145920 320 336 352
  test145920_block_20
  test145920_block_21)
  (interval_append test145920 352 368 400
  test145920_block_22
  (interval_append test145920 368 384 400
  test145920_block_23
  test145920_block_24)))
  (interval_append test145920 400 432 480
  (interval_append test145920 400 416 432
  test145920_block_25
  test145920_block_26)
  (interval_append test145920 432 448 480
  test145920_block_27
  (interval_append test145920 448 464 480
  test145920_block_28
  test145920_block_29))))
  (interval_append test145920 480 560 640
  (interval_append test145920 480 512 560
  (interval_append test145920 480 496 512
  test145920_block_30
  test145920_block_31)
  (interval_append test145920 512 528 560
  test145920_block_32
  (interval_append test145920 528 544 560
  test145920_block_33
  test145920_block_34)))
  (interval_append test145920 560 592 640
  (interval_append test145920 560 576 592
  test145920_block_35
  test145920_block_36)
  (interval_append test145920 592 608 640
  test145920_block_37
  (interval_append test145920 608 624 640
  test145920_block_38
  test145920_block_39))))))
cert_nodeInterval_3 145920 146560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
