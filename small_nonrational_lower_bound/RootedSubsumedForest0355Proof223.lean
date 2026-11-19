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
cert_test_11 142720
cert_test_block_3 142720 0 0 16 16
cert_test_block_3 142720 1 16 32 16
cert_test_block_3 142720 2 32 48 16
cert_test_block_3 142720 3 48 64 16
cert_test_block_3 142720 4 64 80 16
cert_test_block_3 142720 5 80 96 16
cert_test_block_3 142720 6 96 112 16
cert_test_block_3 142720 7 112 128 16
cert_test_block_3 142720 8 128 144 16
cert_test_block_3 142720 9 144 160 16
cert_test_block_3 142720 10 160 176 16
cert_test_block_3 142720 11 176 192 16
cert_test_block_3 142720 12 192 208 16
cert_test_block_3 142720 13 208 224 16
cert_test_block_3 142720 14 224 240 16
cert_test_block_3 142720 15 240 256 16
cert_test_block_3 142720 16 256 272 16
cert_test_block_3 142720 17 272 288 16
cert_test_block_3 142720 18 288 304 16
cert_test_block_3 142720 19 304 320 16
cert_test_block_3 142720 20 320 336 16
cert_test_block_3 142720 21 336 352 16
cert_test_block_3 142720 22 352 368 16
cert_test_block_3 142720 23 368 384 16
cert_test_block_3 142720 24 384 400 16
cert_test_block_3 142720 25 400 416 16
cert_test_block_3 142720 26 416 432 16
cert_test_block_3 142720 27 432 448 16
cert_test_block_3 142720 28 448 464 16
cert_test_block_3 142720 29 464 480 16
cert_test_block_3 142720 30 480 496 16
cert_test_block_3 142720 31 496 512 16
cert_test_block_3 142720 32 512 528 16
cert_test_block_3 142720 33 528 544 16
cert_test_block_3 142720 34 544 560 16
cert_test_block_3 142720 35 560 576 16
cert_test_block_3 142720 36 576 592 16
cert_test_block_3 142720 37 592 608 16
cert_test_block_3 142720 38 608 624 16
cert_test_block_3 142720 39 624 640 16
theorem test142720_complete : Interval test142720 0 640 :=
  (interval_append test142720 0 320 640
  (interval_append test142720 0 160 320
  (interval_append test142720 0 80 160
  (interval_append test142720 0 32 80
  (interval_append test142720 0 16 32
  test142720_block_0
  test142720_block_1)
  (interval_append test142720 32 48 80
  test142720_block_2
  (interval_append test142720 48 64 80
  test142720_block_3
  test142720_block_4)))
  (interval_append test142720 80 112 160
  (interval_append test142720 80 96 112
  test142720_block_5
  test142720_block_6)
  (interval_append test142720 112 128 160
  test142720_block_7
  (interval_append test142720 128 144 160
  test142720_block_8
  test142720_block_9))))
  (interval_append test142720 160 240 320
  (interval_append test142720 160 192 240
  (interval_append test142720 160 176 192
  test142720_block_10
  test142720_block_11)
  (interval_append test142720 192 208 240
  test142720_block_12
  (interval_append test142720 208 224 240
  test142720_block_13
  test142720_block_14)))
  (interval_append test142720 240 272 320
  (interval_append test142720 240 256 272
  test142720_block_15
  test142720_block_16)
  (interval_append test142720 272 288 320
  test142720_block_17
  (interval_append test142720 288 304 320
  test142720_block_18
  test142720_block_19)))))
  (interval_append test142720 320 480 640
  (interval_append test142720 320 400 480
  (interval_append test142720 320 352 400
  (interval_append test142720 320 336 352
  test142720_block_20
  test142720_block_21)
  (interval_append test142720 352 368 400
  test142720_block_22
  (interval_append test142720 368 384 400
  test142720_block_23
  test142720_block_24)))
  (interval_append test142720 400 432 480
  (interval_append test142720 400 416 432
  test142720_block_25
  test142720_block_26)
  (interval_append test142720 432 448 480
  test142720_block_27
  (interval_append test142720 448 464 480
  test142720_block_28
  test142720_block_29))))
  (interval_append test142720 480 560 640
  (interval_append test142720 480 512 560
  (interval_append test142720 480 496 512
  test142720_block_30
  test142720_block_31)
  (interval_append test142720 512 528 560
  test142720_block_32
  (interval_append test142720 528 544 560
  test142720_block_33
  test142720_block_34)))
  (interval_append test142720 560 592 640
  (interval_append test142720 560 576 592
  test142720_block_35
  test142720_block_36)
  (interval_append test142720 592 608 640
  test142720_block_37
  (interval_append test142720 608 624 640
  test142720_block_38
  test142720_block_39))))))
cert_nodeInterval_3 142720 143360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
