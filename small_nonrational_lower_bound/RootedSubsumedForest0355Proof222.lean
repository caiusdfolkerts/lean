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
cert_test_11 142080
cert_test_block_3 142080 0 0 16 16
cert_test_block_3 142080 1 16 32 16
cert_test_block_3 142080 2 32 48 16
cert_test_block_3 142080 3 48 64 16
cert_test_block_3 142080 4 64 80 16
cert_test_block_3 142080 5 80 96 16
cert_test_block_3 142080 6 96 112 16
cert_test_block_3 142080 7 112 128 16
cert_test_block_3 142080 8 128 144 16
cert_test_block_3 142080 9 144 160 16
cert_test_block_3 142080 10 160 176 16
cert_test_block_3 142080 11 176 192 16
cert_test_block_3 142080 12 192 208 16
cert_test_block_3 142080 13 208 224 16
cert_test_block_3 142080 14 224 240 16
cert_test_block_3 142080 15 240 256 16
cert_test_block_3 142080 16 256 272 16
cert_test_block_3 142080 17 272 288 16
cert_test_block_3 142080 18 288 304 16
cert_test_block_3 142080 19 304 320 16
cert_test_block_3 142080 20 320 336 16
cert_test_block_3 142080 21 336 352 16
cert_test_block_3 142080 22 352 368 16
cert_test_block_3 142080 23 368 384 16
cert_test_block_3 142080 24 384 400 16
cert_test_block_3 142080 25 400 416 16
cert_test_block_3 142080 26 416 432 16
cert_test_block_3 142080 27 432 448 16
cert_test_block_3 142080 28 448 464 16
cert_test_block_3 142080 29 464 480 16
cert_test_block_3 142080 30 480 496 16
cert_test_block_3 142080 31 496 512 16
cert_test_block_3 142080 32 512 528 16
cert_test_block_3 142080 33 528 544 16
cert_test_block_3 142080 34 544 560 16
cert_test_block_3 142080 35 560 576 16
cert_test_block_3 142080 36 576 592 16
cert_test_block_3 142080 37 592 608 16
cert_test_block_3 142080 38 608 624 16
cert_test_block_3 142080 39 624 640 16
theorem test142080_complete : Interval test142080 0 640 :=
  (interval_append test142080 0 320 640
  (interval_append test142080 0 160 320
  (interval_append test142080 0 80 160
  (interval_append test142080 0 32 80
  (interval_append test142080 0 16 32
  test142080_block_0
  test142080_block_1)
  (interval_append test142080 32 48 80
  test142080_block_2
  (interval_append test142080 48 64 80
  test142080_block_3
  test142080_block_4)))
  (interval_append test142080 80 112 160
  (interval_append test142080 80 96 112
  test142080_block_5
  test142080_block_6)
  (interval_append test142080 112 128 160
  test142080_block_7
  (interval_append test142080 128 144 160
  test142080_block_8
  test142080_block_9))))
  (interval_append test142080 160 240 320
  (interval_append test142080 160 192 240
  (interval_append test142080 160 176 192
  test142080_block_10
  test142080_block_11)
  (interval_append test142080 192 208 240
  test142080_block_12
  (interval_append test142080 208 224 240
  test142080_block_13
  test142080_block_14)))
  (interval_append test142080 240 272 320
  (interval_append test142080 240 256 272
  test142080_block_15
  test142080_block_16)
  (interval_append test142080 272 288 320
  test142080_block_17
  (interval_append test142080 288 304 320
  test142080_block_18
  test142080_block_19)))))
  (interval_append test142080 320 480 640
  (interval_append test142080 320 400 480
  (interval_append test142080 320 352 400
  (interval_append test142080 320 336 352
  test142080_block_20
  test142080_block_21)
  (interval_append test142080 352 368 400
  test142080_block_22
  (interval_append test142080 368 384 400
  test142080_block_23
  test142080_block_24)))
  (interval_append test142080 400 432 480
  (interval_append test142080 400 416 432
  test142080_block_25
  test142080_block_26)
  (interval_append test142080 432 448 480
  test142080_block_27
  (interval_append test142080 448 464 480
  test142080_block_28
  test142080_block_29))))
  (interval_append test142080 480 560 640
  (interval_append test142080 480 512 560
  (interval_append test142080 480 496 512
  test142080_block_30
  test142080_block_31)
  (interval_append test142080 512 528 560
  test142080_block_32
  (interval_append test142080 528 544 560
  test142080_block_33
  test142080_block_34)))
  (interval_append test142080 560 592 640
  (interval_append test142080 560 576 592
  test142080_block_35
  test142080_block_36)
  (interval_append test142080 592 608 640
  test142080_block_37
  (interval_append test142080 608 624 640
  test142080_block_38
  test142080_block_39))))))
cert_nodeInterval_3 142080 142720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
