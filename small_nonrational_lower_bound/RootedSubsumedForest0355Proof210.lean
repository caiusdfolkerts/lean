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
cert_test_11 134400
cert_test_block_3 134400 0 0 16 16
cert_test_block_3 134400 1 16 32 16
cert_test_block_3 134400 2 32 48 16
cert_test_block_3 134400 3 48 64 16
cert_test_block_3 134400 4 64 80 16
cert_test_block_3 134400 5 80 96 16
cert_test_block_3 134400 6 96 112 16
cert_test_block_3 134400 7 112 128 16
cert_test_block_3 134400 8 128 144 16
cert_test_block_3 134400 9 144 160 16
cert_test_block_3 134400 10 160 176 16
cert_test_block_3 134400 11 176 192 16
cert_test_block_3 134400 12 192 208 16
cert_test_block_3 134400 13 208 224 16
cert_test_block_3 134400 14 224 240 16
cert_test_block_3 134400 15 240 256 16
cert_test_block_3 134400 16 256 272 16
cert_test_block_3 134400 17 272 288 16
cert_test_block_3 134400 18 288 304 16
cert_test_block_3 134400 19 304 320 16
cert_test_block_3 134400 20 320 336 16
cert_test_block_3 134400 21 336 352 16
cert_test_block_3 134400 22 352 368 16
cert_test_block_3 134400 23 368 384 16
cert_test_block_3 134400 24 384 400 16
cert_test_block_3 134400 25 400 416 16
cert_test_block_3 134400 26 416 432 16
cert_test_block_3 134400 27 432 448 16
cert_test_block_3 134400 28 448 464 16
cert_test_block_3 134400 29 464 480 16
cert_test_block_3 134400 30 480 496 16
cert_test_block_3 134400 31 496 512 16
cert_test_block_3 134400 32 512 528 16
cert_test_block_3 134400 33 528 544 16
cert_test_block_3 134400 34 544 560 16
cert_test_block_3 134400 35 560 576 16
cert_test_block_3 134400 36 576 592 16
cert_test_block_3 134400 37 592 608 16
cert_test_block_3 134400 38 608 624 16
cert_test_block_3 134400 39 624 640 16
theorem test134400_complete : Interval test134400 0 640 :=
  (interval_append test134400 0 320 640
  (interval_append test134400 0 160 320
  (interval_append test134400 0 80 160
  (interval_append test134400 0 32 80
  (interval_append test134400 0 16 32
  test134400_block_0
  test134400_block_1)
  (interval_append test134400 32 48 80
  test134400_block_2
  (interval_append test134400 48 64 80
  test134400_block_3
  test134400_block_4)))
  (interval_append test134400 80 112 160
  (interval_append test134400 80 96 112
  test134400_block_5
  test134400_block_6)
  (interval_append test134400 112 128 160
  test134400_block_7
  (interval_append test134400 128 144 160
  test134400_block_8
  test134400_block_9))))
  (interval_append test134400 160 240 320
  (interval_append test134400 160 192 240
  (interval_append test134400 160 176 192
  test134400_block_10
  test134400_block_11)
  (interval_append test134400 192 208 240
  test134400_block_12
  (interval_append test134400 208 224 240
  test134400_block_13
  test134400_block_14)))
  (interval_append test134400 240 272 320
  (interval_append test134400 240 256 272
  test134400_block_15
  test134400_block_16)
  (interval_append test134400 272 288 320
  test134400_block_17
  (interval_append test134400 288 304 320
  test134400_block_18
  test134400_block_19)))))
  (interval_append test134400 320 480 640
  (interval_append test134400 320 400 480
  (interval_append test134400 320 352 400
  (interval_append test134400 320 336 352
  test134400_block_20
  test134400_block_21)
  (interval_append test134400 352 368 400
  test134400_block_22
  (interval_append test134400 368 384 400
  test134400_block_23
  test134400_block_24)))
  (interval_append test134400 400 432 480
  (interval_append test134400 400 416 432
  test134400_block_25
  test134400_block_26)
  (interval_append test134400 432 448 480
  test134400_block_27
  (interval_append test134400 448 464 480
  test134400_block_28
  test134400_block_29))))
  (interval_append test134400 480 560 640
  (interval_append test134400 480 512 560
  (interval_append test134400 480 496 512
  test134400_block_30
  test134400_block_31)
  (interval_append test134400 512 528 560
  test134400_block_32
  (interval_append test134400 528 544 560
  test134400_block_33
  test134400_block_34)))
  (interval_append test134400 560 592 640
  (interval_append test134400 560 576 592
  test134400_block_35
  test134400_block_36)
  (interval_append test134400 592 608 640
  test134400_block_37
  (interval_append test134400 608 624 640
  test134400_block_38
  test134400_block_39))))))
cert_nodeInterval_3 134400 135040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
