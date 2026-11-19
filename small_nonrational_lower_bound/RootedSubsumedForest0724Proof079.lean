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
cert_test_11 50560
cert_test_block_3 50560 0 0 16 16
cert_test_block_3 50560 1 16 32 16
cert_test_block_3 50560 2 32 48 16
cert_test_block_3 50560 3 48 64 16
cert_test_block_3 50560 4 64 80 16
cert_test_block_3 50560 5 80 96 16
cert_test_block_3 50560 6 96 112 16
cert_test_block_3 50560 7 112 128 16
cert_test_block_3 50560 8 128 144 16
cert_test_block_3 50560 9 144 160 16
cert_test_block_3 50560 10 160 176 16
cert_test_block_3 50560 11 176 192 16
cert_test_block_3 50560 12 192 208 16
cert_test_block_3 50560 13 208 224 16
cert_test_block_3 50560 14 224 240 16
cert_test_block_3 50560 15 240 256 16
cert_test_block_3 50560 16 256 272 16
cert_test_block_3 50560 17 272 288 16
cert_test_block_3 50560 18 288 304 16
cert_test_block_3 50560 19 304 320 16
cert_test_block_3 50560 20 320 336 16
cert_test_block_3 50560 21 336 352 16
cert_test_block_3 50560 22 352 368 16
cert_test_block_3 50560 23 368 384 16
cert_test_block_3 50560 24 384 400 16
cert_test_block_3 50560 25 400 416 16
cert_test_block_3 50560 26 416 432 16
cert_test_block_3 50560 27 432 448 16
cert_test_block_3 50560 28 448 464 16
cert_test_block_3 50560 29 464 480 16
cert_test_block_3 50560 30 480 496 16
cert_test_block_3 50560 31 496 512 16
cert_test_block_3 50560 32 512 528 16
cert_test_block_3 50560 33 528 544 16
cert_test_block_3 50560 34 544 560 16
cert_test_block_3 50560 35 560 576 16
cert_test_block_3 50560 36 576 592 16
cert_test_block_3 50560 37 592 608 16
cert_test_block_3 50560 38 608 624 16
cert_test_block_3 50560 39 624 640 16
theorem test50560_complete : Interval test50560 0 640 :=
  (interval_append test50560 0 320 640
  (interval_append test50560 0 160 320
  (interval_append test50560 0 80 160
  (interval_append test50560 0 32 80
  (interval_append test50560 0 16 32
  test50560_block_0
  test50560_block_1)
  (interval_append test50560 32 48 80
  test50560_block_2
  (interval_append test50560 48 64 80
  test50560_block_3
  test50560_block_4)))
  (interval_append test50560 80 112 160
  (interval_append test50560 80 96 112
  test50560_block_5
  test50560_block_6)
  (interval_append test50560 112 128 160
  test50560_block_7
  (interval_append test50560 128 144 160
  test50560_block_8
  test50560_block_9))))
  (interval_append test50560 160 240 320
  (interval_append test50560 160 192 240
  (interval_append test50560 160 176 192
  test50560_block_10
  test50560_block_11)
  (interval_append test50560 192 208 240
  test50560_block_12
  (interval_append test50560 208 224 240
  test50560_block_13
  test50560_block_14)))
  (interval_append test50560 240 272 320
  (interval_append test50560 240 256 272
  test50560_block_15
  test50560_block_16)
  (interval_append test50560 272 288 320
  test50560_block_17
  (interval_append test50560 288 304 320
  test50560_block_18
  test50560_block_19)))))
  (interval_append test50560 320 480 640
  (interval_append test50560 320 400 480
  (interval_append test50560 320 352 400
  (interval_append test50560 320 336 352
  test50560_block_20
  test50560_block_21)
  (interval_append test50560 352 368 400
  test50560_block_22
  (interval_append test50560 368 384 400
  test50560_block_23
  test50560_block_24)))
  (interval_append test50560 400 432 480
  (interval_append test50560 400 416 432
  test50560_block_25
  test50560_block_26)
  (interval_append test50560 432 448 480
  test50560_block_27
  (interval_append test50560 448 464 480
  test50560_block_28
  test50560_block_29))))
  (interval_append test50560 480 560 640
  (interval_append test50560 480 512 560
  (interval_append test50560 480 496 512
  test50560_block_30
  test50560_block_31)
  (interval_append test50560 512 528 560
  test50560_block_32
  (interval_append test50560 528 544 560
  test50560_block_33
  test50560_block_34)))
  (interval_append test50560 560 592 640
  (interval_append test50560 560 576 592
  test50560_block_35
  test50560_block_36)
  (interval_append test50560 592 608 640
  test50560_block_37
  (interval_append test50560 608 624 640
  test50560_block_38
  test50560_block_39))))))
cert_nodeInterval_3 50560 51200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
