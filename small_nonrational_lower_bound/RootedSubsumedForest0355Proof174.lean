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
cert_test_11 111360
cert_test_block_3 111360 0 0 16 16
cert_test_block_3 111360 1 16 32 16
cert_test_block_3 111360 2 32 48 16
cert_test_block_3 111360 3 48 64 16
cert_test_block_3 111360 4 64 80 16
cert_test_block_3 111360 5 80 96 16
cert_test_block_3 111360 6 96 112 16
cert_test_block_3 111360 7 112 128 16
cert_test_block_3 111360 8 128 144 16
cert_test_block_3 111360 9 144 160 16
cert_test_block_3 111360 10 160 176 16
cert_test_block_3 111360 11 176 192 16
cert_test_block_3 111360 12 192 208 16
cert_test_block_3 111360 13 208 224 16
cert_test_block_3 111360 14 224 240 16
cert_test_block_3 111360 15 240 256 16
cert_test_block_3 111360 16 256 272 16
cert_test_block_3 111360 17 272 288 16
cert_test_block_3 111360 18 288 304 16
cert_test_block_3 111360 19 304 320 16
cert_test_block_3 111360 20 320 336 16
cert_test_block_3 111360 21 336 352 16
cert_test_block_3 111360 22 352 368 16
cert_test_block_3 111360 23 368 384 16
cert_test_block_3 111360 24 384 400 16
cert_test_block_3 111360 25 400 416 16
cert_test_block_3 111360 26 416 432 16
cert_test_block_3 111360 27 432 448 16
cert_test_block_3 111360 28 448 464 16
cert_test_block_3 111360 29 464 480 16
cert_test_block_3 111360 30 480 496 16
cert_test_block_3 111360 31 496 512 16
cert_test_block_3 111360 32 512 528 16
cert_test_block_3 111360 33 528 544 16
cert_test_block_3 111360 34 544 560 16
cert_test_block_3 111360 35 560 576 16
cert_test_block_3 111360 36 576 592 16
cert_test_block_3 111360 37 592 608 16
cert_test_block_3 111360 38 608 624 16
cert_test_block_3 111360 39 624 640 16
theorem test111360_complete : Interval test111360 0 640 :=
  (interval_append test111360 0 320 640
  (interval_append test111360 0 160 320
  (interval_append test111360 0 80 160
  (interval_append test111360 0 32 80
  (interval_append test111360 0 16 32
  test111360_block_0
  test111360_block_1)
  (interval_append test111360 32 48 80
  test111360_block_2
  (interval_append test111360 48 64 80
  test111360_block_3
  test111360_block_4)))
  (interval_append test111360 80 112 160
  (interval_append test111360 80 96 112
  test111360_block_5
  test111360_block_6)
  (interval_append test111360 112 128 160
  test111360_block_7
  (interval_append test111360 128 144 160
  test111360_block_8
  test111360_block_9))))
  (interval_append test111360 160 240 320
  (interval_append test111360 160 192 240
  (interval_append test111360 160 176 192
  test111360_block_10
  test111360_block_11)
  (interval_append test111360 192 208 240
  test111360_block_12
  (interval_append test111360 208 224 240
  test111360_block_13
  test111360_block_14)))
  (interval_append test111360 240 272 320
  (interval_append test111360 240 256 272
  test111360_block_15
  test111360_block_16)
  (interval_append test111360 272 288 320
  test111360_block_17
  (interval_append test111360 288 304 320
  test111360_block_18
  test111360_block_19)))))
  (interval_append test111360 320 480 640
  (interval_append test111360 320 400 480
  (interval_append test111360 320 352 400
  (interval_append test111360 320 336 352
  test111360_block_20
  test111360_block_21)
  (interval_append test111360 352 368 400
  test111360_block_22
  (interval_append test111360 368 384 400
  test111360_block_23
  test111360_block_24)))
  (interval_append test111360 400 432 480
  (interval_append test111360 400 416 432
  test111360_block_25
  test111360_block_26)
  (interval_append test111360 432 448 480
  test111360_block_27
  (interval_append test111360 448 464 480
  test111360_block_28
  test111360_block_29))))
  (interval_append test111360 480 560 640
  (interval_append test111360 480 512 560
  (interval_append test111360 480 496 512
  test111360_block_30
  test111360_block_31)
  (interval_append test111360 512 528 560
  test111360_block_32
  (interval_append test111360 528 544 560
  test111360_block_33
  test111360_block_34)))
  (interval_append test111360 560 592 640
  (interval_append test111360 560 576 592
  test111360_block_35
  test111360_block_36)
  (interval_append test111360 592 608 640
  test111360_block_37
  (interval_append test111360 608 624 640
  test111360_block_38
  test111360_block_39))))))
cert_nodeInterval_3 111360 112000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
