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
cert_test_11 83200
cert_test_block_3 83200 0 0 16 16
cert_test_block_3 83200 1 16 32 16
cert_test_block_3 83200 2 32 48 16
cert_test_block_3 83200 3 48 64 16
cert_test_block_3 83200 4 64 80 16
cert_test_block_3 83200 5 80 96 16
cert_test_block_3 83200 6 96 112 16
cert_test_block_3 83200 7 112 128 16
cert_test_block_3 83200 8 128 144 16
cert_test_block_3 83200 9 144 160 16
cert_test_block_3 83200 10 160 176 16
cert_test_block_3 83200 11 176 192 16
cert_test_block_3 83200 12 192 208 16
cert_test_block_3 83200 13 208 224 16
cert_test_block_3 83200 14 224 240 16
cert_test_block_3 83200 15 240 256 16
cert_test_block_3 83200 16 256 272 16
cert_test_block_3 83200 17 272 288 16
cert_test_block_3 83200 18 288 304 16
cert_test_block_3 83200 19 304 320 16
cert_test_block_3 83200 20 320 336 16
cert_test_block_3 83200 21 336 352 16
cert_test_block_3 83200 22 352 368 16
cert_test_block_3 83200 23 368 384 16
cert_test_block_3 83200 24 384 400 16
cert_test_block_3 83200 25 400 416 16
cert_test_block_3 83200 26 416 432 16
cert_test_block_3 83200 27 432 448 16
cert_test_block_3 83200 28 448 464 16
cert_test_block_3 83200 29 464 480 16
cert_test_block_3 83200 30 480 496 16
cert_test_block_3 83200 31 496 512 16
cert_test_block_3 83200 32 512 528 16
cert_test_block_3 83200 33 528 544 16
cert_test_block_3 83200 34 544 560 16
cert_test_block_3 83200 35 560 576 16
cert_test_block_3 83200 36 576 592 16
cert_test_block_3 83200 37 592 608 16
cert_test_block_3 83200 38 608 624 16
cert_test_block_3 83200 39 624 640 16
theorem test83200_complete : Interval test83200 0 640 :=
  (interval_append test83200 0 320 640
  (interval_append test83200 0 160 320
  (interval_append test83200 0 80 160
  (interval_append test83200 0 32 80
  (interval_append test83200 0 16 32
  test83200_block_0
  test83200_block_1)
  (interval_append test83200 32 48 80
  test83200_block_2
  (interval_append test83200 48 64 80
  test83200_block_3
  test83200_block_4)))
  (interval_append test83200 80 112 160
  (interval_append test83200 80 96 112
  test83200_block_5
  test83200_block_6)
  (interval_append test83200 112 128 160
  test83200_block_7
  (interval_append test83200 128 144 160
  test83200_block_8
  test83200_block_9))))
  (interval_append test83200 160 240 320
  (interval_append test83200 160 192 240
  (interval_append test83200 160 176 192
  test83200_block_10
  test83200_block_11)
  (interval_append test83200 192 208 240
  test83200_block_12
  (interval_append test83200 208 224 240
  test83200_block_13
  test83200_block_14)))
  (interval_append test83200 240 272 320
  (interval_append test83200 240 256 272
  test83200_block_15
  test83200_block_16)
  (interval_append test83200 272 288 320
  test83200_block_17
  (interval_append test83200 288 304 320
  test83200_block_18
  test83200_block_19)))))
  (interval_append test83200 320 480 640
  (interval_append test83200 320 400 480
  (interval_append test83200 320 352 400
  (interval_append test83200 320 336 352
  test83200_block_20
  test83200_block_21)
  (interval_append test83200 352 368 400
  test83200_block_22
  (interval_append test83200 368 384 400
  test83200_block_23
  test83200_block_24)))
  (interval_append test83200 400 432 480
  (interval_append test83200 400 416 432
  test83200_block_25
  test83200_block_26)
  (interval_append test83200 432 448 480
  test83200_block_27
  (interval_append test83200 448 464 480
  test83200_block_28
  test83200_block_29))))
  (interval_append test83200 480 560 640
  (interval_append test83200 480 512 560
  (interval_append test83200 480 496 512
  test83200_block_30
  test83200_block_31)
  (interval_append test83200 512 528 560
  test83200_block_32
  (interval_append test83200 528 544 560
  test83200_block_33
  test83200_block_34)))
  (interval_append test83200 560 592 640
  (interval_append test83200 560 576 592
  test83200_block_35
  test83200_block_36)
  (interval_append test83200 592 608 640
  test83200_block_37
  (interval_append test83200 608 624 640
  test83200_block_38
  test83200_block_39))))))
cert_nodeInterval_3 83200 83840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
