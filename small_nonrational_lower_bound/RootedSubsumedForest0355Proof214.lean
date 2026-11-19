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
cert_test_11 136960
cert_test_block_3 136960 0 0 16 16
cert_test_block_3 136960 1 16 32 16
cert_test_block_3 136960 2 32 48 16
cert_test_block_3 136960 3 48 64 16
cert_test_block_3 136960 4 64 80 16
cert_test_block_3 136960 5 80 96 16
cert_test_block_3 136960 6 96 112 16
cert_test_block_3 136960 7 112 128 16
cert_test_block_3 136960 8 128 144 16
cert_test_block_3 136960 9 144 160 16
cert_test_block_3 136960 10 160 176 16
cert_test_block_3 136960 11 176 192 16
cert_test_block_3 136960 12 192 208 16
cert_test_block_3 136960 13 208 224 16
cert_test_block_3 136960 14 224 240 16
cert_test_block_3 136960 15 240 256 16
cert_test_block_3 136960 16 256 272 16
cert_test_block_3 136960 17 272 288 16
cert_test_block_3 136960 18 288 304 16
cert_test_block_3 136960 19 304 320 16
cert_test_block_3 136960 20 320 336 16
cert_test_block_3 136960 21 336 352 16
cert_test_block_3 136960 22 352 368 16
cert_test_block_3 136960 23 368 384 16
cert_test_block_3 136960 24 384 400 16
cert_test_block_3 136960 25 400 416 16
cert_test_block_3 136960 26 416 432 16
cert_test_block_3 136960 27 432 448 16
cert_test_block_3 136960 28 448 464 16
cert_test_block_3 136960 29 464 480 16
cert_test_block_3 136960 30 480 496 16
cert_test_block_3 136960 31 496 512 16
cert_test_block_3 136960 32 512 528 16
cert_test_block_3 136960 33 528 544 16
cert_test_block_3 136960 34 544 560 16
cert_test_block_3 136960 35 560 576 16
cert_test_block_3 136960 36 576 592 16
cert_test_block_3 136960 37 592 608 16
cert_test_block_3 136960 38 608 624 16
cert_test_block_3 136960 39 624 640 16
theorem test136960_complete : Interval test136960 0 640 :=
  (interval_append test136960 0 320 640
  (interval_append test136960 0 160 320
  (interval_append test136960 0 80 160
  (interval_append test136960 0 32 80
  (interval_append test136960 0 16 32
  test136960_block_0
  test136960_block_1)
  (interval_append test136960 32 48 80
  test136960_block_2
  (interval_append test136960 48 64 80
  test136960_block_3
  test136960_block_4)))
  (interval_append test136960 80 112 160
  (interval_append test136960 80 96 112
  test136960_block_5
  test136960_block_6)
  (interval_append test136960 112 128 160
  test136960_block_7
  (interval_append test136960 128 144 160
  test136960_block_8
  test136960_block_9))))
  (interval_append test136960 160 240 320
  (interval_append test136960 160 192 240
  (interval_append test136960 160 176 192
  test136960_block_10
  test136960_block_11)
  (interval_append test136960 192 208 240
  test136960_block_12
  (interval_append test136960 208 224 240
  test136960_block_13
  test136960_block_14)))
  (interval_append test136960 240 272 320
  (interval_append test136960 240 256 272
  test136960_block_15
  test136960_block_16)
  (interval_append test136960 272 288 320
  test136960_block_17
  (interval_append test136960 288 304 320
  test136960_block_18
  test136960_block_19)))))
  (interval_append test136960 320 480 640
  (interval_append test136960 320 400 480
  (interval_append test136960 320 352 400
  (interval_append test136960 320 336 352
  test136960_block_20
  test136960_block_21)
  (interval_append test136960 352 368 400
  test136960_block_22
  (interval_append test136960 368 384 400
  test136960_block_23
  test136960_block_24)))
  (interval_append test136960 400 432 480
  (interval_append test136960 400 416 432
  test136960_block_25
  test136960_block_26)
  (interval_append test136960 432 448 480
  test136960_block_27
  (interval_append test136960 448 464 480
  test136960_block_28
  test136960_block_29))))
  (interval_append test136960 480 560 640
  (interval_append test136960 480 512 560
  (interval_append test136960 480 496 512
  test136960_block_30
  test136960_block_31)
  (interval_append test136960 512 528 560
  test136960_block_32
  (interval_append test136960 528 544 560
  test136960_block_33
  test136960_block_34)))
  (interval_append test136960 560 592 640
  (interval_append test136960 560 576 592
  test136960_block_35
  test136960_block_36)
  (interval_append test136960 592 608 640
  test136960_block_37
  (interval_append test136960 608 624 640
  test136960_block_38
  test136960_block_39))))))
cert_nodeInterval_3 136960 137600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
