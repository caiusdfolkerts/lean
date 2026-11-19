module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0317Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5120
cert_test_block_3 5120 0 0 16 16
cert_test_block_3 5120 1 16 32 16
cert_test_block_3 5120 2 32 48 16
cert_test_block_3 5120 3 48 64 16
cert_test_block_3 5120 4 64 80 16
cert_test_block_3 5120 5 80 96 16
cert_test_block_3 5120 6 96 112 16
cert_test_block_3 5120 7 112 128 16
cert_test_block_3 5120 8 128 144 16
cert_test_block_3 5120 9 144 160 16
cert_test_block_3 5120 10 160 176 16
cert_test_block_3 5120 11 176 192 16
cert_test_block_3 5120 12 192 208 16
cert_test_block_3 5120 13 208 224 16
cert_test_block_3 5120 14 224 240 16
cert_test_block_3 5120 15 240 256 16
cert_test_block_3 5120 16 256 272 16
cert_test_block_3 5120 17 272 288 16
cert_test_block_3 5120 18 288 304 16
cert_test_block_3 5120 19 304 320 16
cert_test_block_3 5120 20 320 336 16
cert_test_block_3 5120 21 336 352 16
cert_test_block_3 5120 22 352 368 16
cert_test_block_3 5120 23 368 384 16
cert_test_block_3 5120 24 384 400 16
cert_test_block_3 5120 25 400 416 16
cert_test_block_3 5120 26 416 432 16
cert_test_block_3 5120 27 432 448 16
cert_test_block_3 5120 28 448 464 16
cert_test_block_3 5120 29 464 480 16
cert_test_block_3 5120 30 480 496 16
cert_test_block_3 5120 31 496 512 16
cert_test_block_3 5120 32 512 528 16
cert_test_block_3 5120 33 528 544 16
cert_test_block_3 5120 34 544 560 16
cert_test_block_3 5120 35 560 576 16
cert_test_block_3 5120 36 576 592 16
cert_test_block_3 5120 37 592 608 16
cert_test_block_3 5120 38 608 624 16
cert_test_block_3 5120 39 624 640 16
theorem test5120_complete : Interval test5120 0 640 :=
  (interval_append test5120 0 320 640
  (interval_append test5120 0 160 320
  (interval_append test5120 0 80 160
  (interval_append test5120 0 32 80
  (interval_append test5120 0 16 32
  test5120_block_0
  test5120_block_1)
  (interval_append test5120 32 48 80
  test5120_block_2
  (interval_append test5120 48 64 80
  test5120_block_3
  test5120_block_4)))
  (interval_append test5120 80 112 160
  (interval_append test5120 80 96 112
  test5120_block_5
  test5120_block_6)
  (interval_append test5120 112 128 160
  test5120_block_7
  (interval_append test5120 128 144 160
  test5120_block_8
  test5120_block_9))))
  (interval_append test5120 160 240 320
  (interval_append test5120 160 192 240
  (interval_append test5120 160 176 192
  test5120_block_10
  test5120_block_11)
  (interval_append test5120 192 208 240
  test5120_block_12
  (interval_append test5120 208 224 240
  test5120_block_13
  test5120_block_14)))
  (interval_append test5120 240 272 320
  (interval_append test5120 240 256 272
  test5120_block_15
  test5120_block_16)
  (interval_append test5120 272 288 320
  test5120_block_17
  (interval_append test5120 288 304 320
  test5120_block_18
  test5120_block_19)))))
  (interval_append test5120 320 480 640
  (interval_append test5120 320 400 480
  (interval_append test5120 320 352 400
  (interval_append test5120 320 336 352
  test5120_block_20
  test5120_block_21)
  (interval_append test5120 352 368 400
  test5120_block_22
  (interval_append test5120 368 384 400
  test5120_block_23
  test5120_block_24)))
  (interval_append test5120 400 432 480
  (interval_append test5120 400 416 432
  test5120_block_25
  test5120_block_26)
  (interval_append test5120 432 448 480
  test5120_block_27
  (interval_append test5120 448 464 480
  test5120_block_28
  test5120_block_29))))
  (interval_append test5120 480 560 640
  (interval_append test5120 480 512 560
  (interval_append test5120 480 496 512
  test5120_block_30
  test5120_block_31)
  (interval_append test5120 512 528 560
  test5120_block_32
  (interval_append test5120 528 544 560
  test5120_block_33
  test5120_block_34)))
  (interval_append test5120 560 592 640
  (interval_append test5120 560 576 592
  test5120_block_35
  test5120_block_36)
  (interval_append test5120 592 608 640
  test5120_block_37
  (interval_append test5120 608 624 640
  test5120_block_38
  test5120_block_39))))))
cert_nodeInterval_3 5120 5760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
