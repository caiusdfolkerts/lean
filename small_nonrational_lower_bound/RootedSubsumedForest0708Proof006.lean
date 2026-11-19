module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3840
cert_test_block_3 3840 0 0 16 16
cert_test_block_3 3840 1 16 32 16
cert_test_block_3 3840 2 32 48 16
cert_test_block_3 3840 3 48 64 16
cert_test_block_3 3840 4 64 80 16
cert_test_block_3 3840 5 80 96 16
cert_test_block_3 3840 6 96 112 16
cert_test_block_3 3840 7 112 128 16
cert_test_block_3 3840 8 128 144 16
cert_test_block_3 3840 9 144 160 16
cert_test_block_3 3840 10 160 176 16
cert_test_block_3 3840 11 176 192 16
cert_test_block_3 3840 12 192 208 16
cert_test_block_3 3840 13 208 224 16
cert_test_block_3 3840 14 224 240 16
cert_test_block_3 3840 15 240 256 16
cert_test_block_3 3840 16 256 272 16
cert_test_block_3 3840 17 272 288 16
cert_test_block_3 3840 18 288 304 16
cert_test_block_3 3840 19 304 320 16
cert_test_block_3 3840 20 320 336 16
cert_test_block_3 3840 21 336 352 16
cert_test_block_3 3840 22 352 368 16
cert_test_block_3 3840 23 368 384 16
cert_test_block_3 3840 24 384 400 16
cert_test_block_3 3840 25 400 416 16
cert_test_block_3 3840 26 416 432 16
cert_test_block_3 3840 27 432 448 16
cert_test_block_3 3840 28 448 464 16
cert_test_block_3 3840 29 464 480 16
cert_test_block_3 3840 30 480 496 16
cert_test_block_3 3840 31 496 512 16
cert_test_block_3 3840 32 512 528 16
cert_test_block_3 3840 33 528 544 16
cert_test_block_3 3840 34 544 560 16
cert_test_block_3 3840 35 560 576 16
cert_test_block_3 3840 36 576 592 16
cert_test_block_3 3840 37 592 608 16
cert_test_block_3 3840 38 608 624 16
cert_test_block_3 3840 39 624 640 16
theorem test3840_complete : Interval test3840 0 640 :=
  (interval_append test3840 0 320 640
  (interval_append test3840 0 160 320
  (interval_append test3840 0 80 160
  (interval_append test3840 0 32 80
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 80
  test3840_block_2
  (interval_append test3840 48 64 80
  test3840_block_3
  test3840_block_4)))
  (interval_append test3840 80 112 160
  (interval_append test3840 80 96 112
  test3840_block_5
  test3840_block_6)
  (interval_append test3840 112 128 160
  test3840_block_7
  (interval_append test3840 128 144 160
  test3840_block_8
  test3840_block_9))))
  (interval_append test3840 160 240 320
  (interval_append test3840 160 192 240
  (interval_append test3840 160 176 192
  test3840_block_10
  test3840_block_11)
  (interval_append test3840 192 208 240
  test3840_block_12
  (interval_append test3840 208 224 240
  test3840_block_13
  test3840_block_14)))
  (interval_append test3840 240 272 320
  (interval_append test3840 240 256 272
  test3840_block_15
  test3840_block_16)
  (interval_append test3840 272 288 320
  test3840_block_17
  (interval_append test3840 288 304 320
  test3840_block_18
  test3840_block_19)))))
  (interval_append test3840 320 480 640
  (interval_append test3840 320 400 480
  (interval_append test3840 320 352 400
  (interval_append test3840 320 336 352
  test3840_block_20
  test3840_block_21)
  (interval_append test3840 352 368 400
  test3840_block_22
  (interval_append test3840 368 384 400
  test3840_block_23
  test3840_block_24)))
  (interval_append test3840 400 432 480
  (interval_append test3840 400 416 432
  test3840_block_25
  test3840_block_26)
  (interval_append test3840 432 448 480
  test3840_block_27
  (interval_append test3840 448 464 480
  test3840_block_28
  test3840_block_29))))
  (interval_append test3840 480 560 640
  (interval_append test3840 480 512 560
  (interval_append test3840 480 496 512
  test3840_block_30
  test3840_block_31)
  (interval_append test3840 512 528 560
  test3840_block_32
  (interval_append test3840 528 544 560
  test3840_block_33
  test3840_block_34)))
  (interval_append test3840 560 592 640
  (interval_append test3840 560 576 592
  test3840_block_35
  test3840_block_36)
  (interval_append test3840 592 608 640
  test3840_block_37
  (interval_append test3840 608 624 640
  test3840_block_38
  test3840_block_39))))))
cert_nodeInterval_3 3840 4480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
