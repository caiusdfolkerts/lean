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
cert_test_11 119040
cert_test_block_3 119040 0 0 16 16
cert_test_block_3 119040 1 16 32 16
cert_test_block_3 119040 2 32 48 16
cert_test_block_3 119040 3 48 64 16
cert_test_block_3 119040 4 64 80 16
cert_test_block_3 119040 5 80 96 16
cert_test_block_3 119040 6 96 112 16
cert_test_block_3 119040 7 112 128 16
cert_test_block_3 119040 8 128 144 16
cert_test_block_3 119040 9 144 160 16
cert_test_block_3 119040 10 160 176 16
cert_test_block_3 119040 11 176 192 16
cert_test_block_3 119040 12 192 208 16
cert_test_block_3 119040 13 208 224 16
cert_test_block_3 119040 14 224 240 16
cert_test_block_3 119040 15 240 256 16
cert_test_block_3 119040 16 256 272 16
cert_test_block_3 119040 17 272 288 16
cert_test_block_3 119040 18 288 304 16
cert_test_block_3 119040 19 304 320 16
cert_test_block_3 119040 20 320 336 16
cert_test_block_3 119040 21 336 352 16
cert_test_block_3 119040 22 352 368 16
cert_test_block_3 119040 23 368 384 16
cert_test_block_3 119040 24 384 400 16
cert_test_block_3 119040 25 400 416 16
cert_test_block_3 119040 26 416 432 16
cert_test_block_3 119040 27 432 448 16
cert_test_block_3 119040 28 448 464 16
cert_test_block_3 119040 29 464 480 16
cert_test_block_3 119040 30 480 496 16
cert_test_block_3 119040 31 496 512 16
cert_test_block_3 119040 32 512 528 16
cert_test_block_3 119040 33 528 544 16
cert_test_block_3 119040 34 544 560 16
cert_test_block_3 119040 35 560 576 16
cert_test_block_3 119040 36 576 592 16
cert_test_block_3 119040 37 592 608 16
cert_test_block_3 119040 38 608 624 16
cert_test_block_3 119040 39 624 640 16
theorem test119040_complete : Interval test119040 0 640 :=
  (interval_append test119040 0 320 640
  (interval_append test119040 0 160 320
  (interval_append test119040 0 80 160
  (interval_append test119040 0 32 80
  (interval_append test119040 0 16 32
  test119040_block_0
  test119040_block_1)
  (interval_append test119040 32 48 80
  test119040_block_2
  (interval_append test119040 48 64 80
  test119040_block_3
  test119040_block_4)))
  (interval_append test119040 80 112 160
  (interval_append test119040 80 96 112
  test119040_block_5
  test119040_block_6)
  (interval_append test119040 112 128 160
  test119040_block_7
  (interval_append test119040 128 144 160
  test119040_block_8
  test119040_block_9))))
  (interval_append test119040 160 240 320
  (interval_append test119040 160 192 240
  (interval_append test119040 160 176 192
  test119040_block_10
  test119040_block_11)
  (interval_append test119040 192 208 240
  test119040_block_12
  (interval_append test119040 208 224 240
  test119040_block_13
  test119040_block_14)))
  (interval_append test119040 240 272 320
  (interval_append test119040 240 256 272
  test119040_block_15
  test119040_block_16)
  (interval_append test119040 272 288 320
  test119040_block_17
  (interval_append test119040 288 304 320
  test119040_block_18
  test119040_block_19)))))
  (interval_append test119040 320 480 640
  (interval_append test119040 320 400 480
  (interval_append test119040 320 352 400
  (interval_append test119040 320 336 352
  test119040_block_20
  test119040_block_21)
  (interval_append test119040 352 368 400
  test119040_block_22
  (interval_append test119040 368 384 400
  test119040_block_23
  test119040_block_24)))
  (interval_append test119040 400 432 480
  (interval_append test119040 400 416 432
  test119040_block_25
  test119040_block_26)
  (interval_append test119040 432 448 480
  test119040_block_27
  (interval_append test119040 448 464 480
  test119040_block_28
  test119040_block_29))))
  (interval_append test119040 480 560 640
  (interval_append test119040 480 512 560
  (interval_append test119040 480 496 512
  test119040_block_30
  test119040_block_31)
  (interval_append test119040 512 528 560
  test119040_block_32
  (interval_append test119040 528 544 560
  test119040_block_33
  test119040_block_34)))
  (interval_append test119040 560 592 640
  (interval_append test119040 560 576 592
  test119040_block_35
  test119040_block_36)
  (interval_append test119040 592 608 640
  test119040_block_37
  (interval_append test119040 608 624 640
  test119040_block_38
  test119040_block_39))))))
cert_nodeInterval_3 119040 119680
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
