module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0320Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 29440
cert_test_block_3 29440 0 0 16 16
cert_test_block_3 29440 1 16 32 16
cert_test_block_3 29440 2 32 48 16
cert_test_block_3 29440 3 48 64 16
cert_test_block_3 29440 4 64 80 16
cert_test_block_3 29440 5 80 96 16
cert_test_block_3 29440 6 96 112 16
cert_test_block_3 29440 7 112 128 16
cert_test_block_3 29440 8 128 144 16
cert_test_block_3 29440 9 144 160 16
cert_test_block_3 29440 10 160 176 16
cert_test_block_3 29440 11 176 192 16
cert_test_block_3 29440 12 192 208 16
cert_test_block_3 29440 13 208 224 16
cert_test_block_3 29440 14 224 240 16
cert_test_block_3 29440 15 240 256 16
cert_test_block_3 29440 16 256 272 16
cert_test_block_3 29440 17 272 288 16
cert_test_block_3 29440 18 288 304 16
cert_test_block_3 29440 19 304 320 16
cert_test_block_3 29440 20 320 336 16
cert_test_block_3 29440 21 336 352 16
cert_test_block_3 29440 22 352 368 16
cert_test_block_3 29440 23 368 384 16
cert_test_block_3 29440 24 384 400 16
cert_test_block_3 29440 25 400 416 16
cert_test_block_3 29440 26 416 432 16
cert_test_block_3 29440 27 432 448 16
cert_test_block_3 29440 28 448 464 16
cert_test_block_3 29440 29 464 480 16
cert_test_block_3 29440 30 480 496 16
cert_test_block_3 29440 31 496 512 16
cert_test_block_3 29440 32 512 528 16
cert_test_block_3 29440 33 528 544 16
cert_test_block_3 29440 34 544 560 16
cert_test_block_3 29440 35 560 576 16
cert_test_block_3 29440 36 576 592 16
cert_test_block_3 29440 37 592 608 16
cert_test_block_3 29440 38 608 624 16
cert_test_block_3 29440 39 624 640 16
theorem test29440_complete : Interval test29440 0 640 :=
  (interval_append test29440 0 320 640
  (interval_append test29440 0 160 320
  (interval_append test29440 0 80 160
  (interval_append test29440 0 32 80
  (interval_append test29440 0 16 32
  test29440_block_0
  test29440_block_1)
  (interval_append test29440 32 48 80
  test29440_block_2
  (interval_append test29440 48 64 80
  test29440_block_3
  test29440_block_4)))
  (interval_append test29440 80 112 160
  (interval_append test29440 80 96 112
  test29440_block_5
  test29440_block_6)
  (interval_append test29440 112 128 160
  test29440_block_7
  (interval_append test29440 128 144 160
  test29440_block_8
  test29440_block_9))))
  (interval_append test29440 160 240 320
  (interval_append test29440 160 192 240
  (interval_append test29440 160 176 192
  test29440_block_10
  test29440_block_11)
  (interval_append test29440 192 208 240
  test29440_block_12
  (interval_append test29440 208 224 240
  test29440_block_13
  test29440_block_14)))
  (interval_append test29440 240 272 320
  (interval_append test29440 240 256 272
  test29440_block_15
  test29440_block_16)
  (interval_append test29440 272 288 320
  test29440_block_17
  (interval_append test29440 288 304 320
  test29440_block_18
  test29440_block_19)))))
  (interval_append test29440 320 480 640
  (interval_append test29440 320 400 480
  (interval_append test29440 320 352 400
  (interval_append test29440 320 336 352
  test29440_block_20
  test29440_block_21)
  (interval_append test29440 352 368 400
  test29440_block_22
  (interval_append test29440 368 384 400
  test29440_block_23
  test29440_block_24)))
  (interval_append test29440 400 432 480
  (interval_append test29440 400 416 432
  test29440_block_25
  test29440_block_26)
  (interval_append test29440 432 448 480
  test29440_block_27
  (interval_append test29440 448 464 480
  test29440_block_28
  test29440_block_29))))
  (interval_append test29440 480 560 640
  (interval_append test29440 480 512 560
  (interval_append test29440 480 496 512
  test29440_block_30
  test29440_block_31)
  (interval_append test29440 512 528 560
  test29440_block_32
  (interval_append test29440 528 544 560
  test29440_block_33
  test29440_block_34)))
  (interval_append test29440 560 592 640
  (interval_append test29440 560 576 592
  test29440_block_35
  test29440_block_36)
  (interval_append test29440 592 608 640
  test29440_block_37
  (interval_append test29440 608 624 640
  test29440_block_38
  test29440_block_39))))))
cert_nodeInterval_3 29440 30080
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
