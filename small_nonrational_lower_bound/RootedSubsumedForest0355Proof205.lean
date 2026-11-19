module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 131200
cert_test_block_3 131200 0 0 16 16
cert_test_block_3 131200 1 16 32 16
cert_test_block_3 131200 2 32 48 16
cert_test_block_3 131200 3 48 64 16
cert_test_block_3 131200 4 64 80 16
cert_test_block_3 131200 5 80 96 16
cert_test_block_3 131200 6 96 112 16
cert_test_block_3 131200 7 112 128 16
cert_test_block_3 131200 8 128 144 16
cert_test_block_3 131200 9 144 160 16
cert_test_block_3 131200 10 160 176 16
cert_test_block_3 131200 11 176 192 16
cert_test_block_3 131200 12 192 208 16
cert_test_block_3 131200 13 208 224 16
cert_test_block_3 131200 14 224 240 16
cert_test_block_3 131200 15 240 256 16
cert_test_block_3 131200 16 256 272 16
cert_test_block_3 131200 17 272 288 16
cert_test_block_3 131200 18 288 304 16
cert_test_block_3 131200 19 304 320 16
cert_test_block_3 131200 20 320 336 16
cert_test_block_3 131200 21 336 352 16
cert_test_block_3 131200 22 352 368 16
cert_test_block_3 131200 23 368 384 16
cert_test_block_3 131200 24 384 400 16
cert_test_block_3 131200 25 400 416 16
cert_test_block_3 131200 26 416 432 16
cert_test_block_3 131200 27 432 448 16
cert_test_block_3 131200 28 448 464 16
cert_test_block_3 131200 29 464 480 16
cert_test_block_3 131200 30 480 496 16
cert_test_block_3 131200 31 496 512 16
cert_test_block_3 131200 32 512 528 16
cert_test_block_3 131200 33 528 544 16
cert_test_block_3 131200 34 544 560 16
cert_test_block_3 131200 35 560 576 16
cert_test_block_3 131200 36 576 592 16
cert_test_block_3 131200 37 592 608 16
cert_test_block_3 131200 38 608 624 16
cert_test_block_3 131200 39 624 640 16
theorem test131200_complete : Interval test131200 0 640 :=
  (interval_append test131200 0 320 640
  (interval_append test131200 0 160 320
  (interval_append test131200 0 80 160
  (interval_append test131200 0 32 80
  (interval_append test131200 0 16 32
  test131200_block_0
  test131200_block_1)
  (interval_append test131200 32 48 80
  test131200_block_2
  (interval_append test131200 48 64 80
  test131200_block_3
  test131200_block_4)))
  (interval_append test131200 80 112 160
  (interval_append test131200 80 96 112
  test131200_block_5
  test131200_block_6)
  (interval_append test131200 112 128 160
  test131200_block_7
  (interval_append test131200 128 144 160
  test131200_block_8
  test131200_block_9))))
  (interval_append test131200 160 240 320
  (interval_append test131200 160 192 240
  (interval_append test131200 160 176 192
  test131200_block_10
  test131200_block_11)
  (interval_append test131200 192 208 240
  test131200_block_12
  (interval_append test131200 208 224 240
  test131200_block_13
  test131200_block_14)))
  (interval_append test131200 240 272 320
  (interval_append test131200 240 256 272
  test131200_block_15
  test131200_block_16)
  (interval_append test131200 272 288 320
  test131200_block_17
  (interval_append test131200 288 304 320
  test131200_block_18
  test131200_block_19)))))
  (interval_append test131200 320 480 640
  (interval_append test131200 320 400 480
  (interval_append test131200 320 352 400
  (interval_append test131200 320 336 352
  test131200_block_20
  test131200_block_21)
  (interval_append test131200 352 368 400
  test131200_block_22
  (interval_append test131200 368 384 400
  test131200_block_23
  test131200_block_24)))
  (interval_append test131200 400 432 480
  (interval_append test131200 400 416 432
  test131200_block_25
  test131200_block_26)
  (interval_append test131200 432 448 480
  test131200_block_27
  (interval_append test131200 448 464 480
  test131200_block_28
  test131200_block_29))))
  (interval_append test131200 480 560 640
  (interval_append test131200 480 512 560
  (interval_append test131200 480 496 512
  test131200_block_30
  test131200_block_31)
  (interval_append test131200 512 528 560
  test131200_block_32
  (interval_append test131200 528 544 560
  test131200_block_33
  test131200_block_34)))
  (interval_append test131200 560 592 640
  (interval_append test131200 560 576 592
  test131200_block_35
  test131200_block_36)
  (interval_append test131200 592 608 640
  test131200_block_37
  (interval_append test131200 608 624 640
  test131200_block_38
  test131200_block_39))))))
cert_nodeInterval_3 131200 131840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
