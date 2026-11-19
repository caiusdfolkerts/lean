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
cert_test_11 100480
cert_test_block_3 100480 0 0 16 16
cert_test_block_3 100480 1 16 32 16
cert_test_block_3 100480 2 32 48 16
cert_test_block_3 100480 3 48 64 16
cert_test_block_3 100480 4 64 80 16
cert_test_block_3 100480 5 80 96 16
cert_test_block_3 100480 6 96 112 16
cert_test_block_3 100480 7 112 128 16
cert_test_block_3 100480 8 128 144 16
cert_test_block_3 100480 9 144 160 16
cert_test_block_3 100480 10 160 176 16
cert_test_block_3 100480 11 176 192 16
cert_test_block_3 100480 12 192 208 16
cert_test_block_3 100480 13 208 224 16
cert_test_block_3 100480 14 224 240 16
cert_test_block_3 100480 15 240 256 16
cert_test_block_3 100480 16 256 272 16
cert_test_block_3 100480 17 272 288 16
cert_test_block_3 100480 18 288 304 16
cert_test_block_3 100480 19 304 320 16
cert_test_block_3 100480 20 320 336 16
cert_test_block_3 100480 21 336 352 16
cert_test_block_3 100480 22 352 368 16
cert_test_block_3 100480 23 368 384 16
cert_test_block_3 100480 24 384 400 16
cert_test_block_3 100480 25 400 416 16
cert_test_block_3 100480 26 416 432 16
cert_test_block_3 100480 27 432 448 16
cert_test_block_3 100480 28 448 464 16
cert_test_block_3 100480 29 464 480 16
cert_test_block_3 100480 30 480 496 16
cert_test_block_3 100480 31 496 512 16
cert_test_block_3 100480 32 512 528 16
cert_test_block_3 100480 33 528 544 16
cert_test_block_3 100480 34 544 560 16
cert_test_block_3 100480 35 560 576 16
cert_test_block_3 100480 36 576 592 16
cert_test_block_3 100480 37 592 608 16
cert_test_block_3 100480 38 608 624 16
cert_test_block_3 100480 39 624 640 16
theorem test100480_complete : Interval test100480 0 640 :=
  (interval_append test100480 0 320 640
  (interval_append test100480 0 160 320
  (interval_append test100480 0 80 160
  (interval_append test100480 0 32 80
  (interval_append test100480 0 16 32
  test100480_block_0
  test100480_block_1)
  (interval_append test100480 32 48 80
  test100480_block_2
  (interval_append test100480 48 64 80
  test100480_block_3
  test100480_block_4)))
  (interval_append test100480 80 112 160
  (interval_append test100480 80 96 112
  test100480_block_5
  test100480_block_6)
  (interval_append test100480 112 128 160
  test100480_block_7
  (interval_append test100480 128 144 160
  test100480_block_8
  test100480_block_9))))
  (interval_append test100480 160 240 320
  (interval_append test100480 160 192 240
  (interval_append test100480 160 176 192
  test100480_block_10
  test100480_block_11)
  (interval_append test100480 192 208 240
  test100480_block_12
  (interval_append test100480 208 224 240
  test100480_block_13
  test100480_block_14)))
  (interval_append test100480 240 272 320
  (interval_append test100480 240 256 272
  test100480_block_15
  test100480_block_16)
  (interval_append test100480 272 288 320
  test100480_block_17
  (interval_append test100480 288 304 320
  test100480_block_18
  test100480_block_19)))))
  (interval_append test100480 320 480 640
  (interval_append test100480 320 400 480
  (interval_append test100480 320 352 400
  (interval_append test100480 320 336 352
  test100480_block_20
  test100480_block_21)
  (interval_append test100480 352 368 400
  test100480_block_22
  (interval_append test100480 368 384 400
  test100480_block_23
  test100480_block_24)))
  (interval_append test100480 400 432 480
  (interval_append test100480 400 416 432
  test100480_block_25
  test100480_block_26)
  (interval_append test100480 432 448 480
  test100480_block_27
  (interval_append test100480 448 464 480
  test100480_block_28
  test100480_block_29))))
  (interval_append test100480 480 560 640
  (interval_append test100480 480 512 560
  (interval_append test100480 480 496 512
  test100480_block_30
  test100480_block_31)
  (interval_append test100480 512 528 560
  test100480_block_32
  (interval_append test100480 528 544 560
  test100480_block_33
  test100480_block_34)))
  (interval_append test100480 560 592 640
  (interval_append test100480 560 576 592
  test100480_block_35
  test100480_block_36)
  (interval_append test100480 592 608 640
  test100480_block_37
  (interval_append test100480 608 624 640
  test100480_block_38
  test100480_block_39))))))
cert_nodeInterval_3 100480 101120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
