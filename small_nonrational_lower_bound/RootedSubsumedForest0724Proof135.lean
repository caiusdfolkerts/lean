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
cert_test_11 86400
cert_test_block_3 86400 0 0 16 16
cert_test_block_3 86400 1 16 32 16
cert_test_block_3 86400 2 32 48 16
cert_test_block_3 86400 3 48 64 16
cert_test_block_3 86400 4 64 80 16
cert_test_block_3 86400 5 80 96 16
cert_test_block_3 86400 6 96 112 16
cert_test_block_3 86400 7 112 128 16
cert_test_block_3 86400 8 128 144 16
cert_test_block_3 86400 9 144 160 16
cert_test_block_3 86400 10 160 176 16
cert_test_block_3 86400 11 176 192 16
cert_test_block_3 86400 12 192 208 16
cert_test_block_3 86400 13 208 224 16
cert_test_block_3 86400 14 224 240 16
cert_test_block_3 86400 15 240 256 16
cert_test_block_3 86400 16 256 272 16
cert_test_block_3 86400 17 272 288 16
cert_test_block_3 86400 18 288 304 16
cert_test_block_3 86400 19 304 320 16
cert_test_block_3 86400 20 320 336 16
cert_test_block_3 86400 21 336 352 16
cert_test_block_3 86400 22 352 368 16
cert_test_block_3 86400 23 368 384 16
cert_test_block_3 86400 24 384 400 16
cert_test_block_3 86400 25 400 416 16
cert_test_block_3 86400 26 416 432 16
cert_test_block_3 86400 27 432 448 16
cert_test_block_3 86400 28 448 464 16
cert_test_block_3 86400 29 464 480 16
cert_test_block_3 86400 30 480 496 16
cert_test_block_3 86400 31 496 512 16
cert_test_block_3 86400 32 512 528 16
cert_test_block_3 86400 33 528 544 16
cert_test_block_3 86400 34 544 560 16
cert_test_block_3 86400 35 560 576 16
cert_test_block_3 86400 36 576 592 16
cert_test_block_3 86400 37 592 608 16
cert_test_block_3 86400 38 608 624 16
cert_test_block_3 86400 39 624 640 16
theorem test86400_complete : Interval test86400 0 640 :=
  (interval_append test86400 0 320 640
  (interval_append test86400 0 160 320
  (interval_append test86400 0 80 160
  (interval_append test86400 0 32 80
  (interval_append test86400 0 16 32
  test86400_block_0
  test86400_block_1)
  (interval_append test86400 32 48 80
  test86400_block_2
  (interval_append test86400 48 64 80
  test86400_block_3
  test86400_block_4)))
  (interval_append test86400 80 112 160
  (interval_append test86400 80 96 112
  test86400_block_5
  test86400_block_6)
  (interval_append test86400 112 128 160
  test86400_block_7
  (interval_append test86400 128 144 160
  test86400_block_8
  test86400_block_9))))
  (interval_append test86400 160 240 320
  (interval_append test86400 160 192 240
  (interval_append test86400 160 176 192
  test86400_block_10
  test86400_block_11)
  (interval_append test86400 192 208 240
  test86400_block_12
  (interval_append test86400 208 224 240
  test86400_block_13
  test86400_block_14)))
  (interval_append test86400 240 272 320
  (interval_append test86400 240 256 272
  test86400_block_15
  test86400_block_16)
  (interval_append test86400 272 288 320
  test86400_block_17
  (interval_append test86400 288 304 320
  test86400_block_18
  test86400_block_19)))))
  (interval_append test86400 320 480 640
  (interval_append test86400 320 400 480
  (interval_append test86400 320 352 400
  (interval_append test86400 320 336 352
  test86400_block_20
  test86400_block_21)
  (interval_append test86400 352 368 400
  test86400_block_22
  (interval_append test86400 368 384 400
  test86400_block_23
  test86400_block_24)))
  (interval_append test86400 400 432 480
  (interval_append test86400 400 416 432
  test86400_block_25
  test86400_block_26)
  (interval_append test86400 432 448 480
  test86400_block_27
  (interval_append test86400 448 464 480
  test86400_block_28
  test86400_block_29))))
  (interval_append test86400 480 560 640
  (interval_append test86400 480 512 560
  (interval_append test86400 480 496 512
  test86400_block_30
  test86400_block_31)
  (interval_append test86400 512 528 560
  test86400_block_32
  (interval_append test86400 528 544 560
  test86400_block_33
  test86400_block_34)))
  (interval_append test86400 560 592 640
  (interval_append test86400 560 576 592
  test86400_block_35
  test86400_block_36)
  (interval_append test86400 592 608 640
  test86400_block_37
  (interval_append test86400 608 624 640
  test86400_block_38
  test86400_block_39))))))
cert_nodeInterval_3 86400 87040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
