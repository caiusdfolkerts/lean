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
cert_test_11 153600
cert_test_block_3 153600 0 0 16 16
cert_test_block_3 153600 1 16 32 16
cert_test_block_3 153600 2 32 48 16
cert_test_block_3 153600 3 48 64 16
cert_test_block_3 153600 4 64 80 16
cert_test_block_3 153600 5 80 96 16
cert_test_block_3 153600 6 96 112 16
cert_test_block_3 153600 7 112 128 16
cert_test_block_3 153600 8 128 144 16
cert_test_block_3 153600 9 144 160 16
cert_test_block_3 153600 10 160 176 16
cert_test_block_3 153600 11 176 192 16
cert_test_block_3 153600 12 192 208 16
cert_test_block_3 153600 13 208 224 16
cert_test_block_3 153600 14 224 240 16
cert_test_block_3 153600 15 240 256 16
cert_test_block_3 153600 16 256 272 16
cert_test_block_3 153600 17 272 288 16
cert_test_block_3 153600 18 288 304 16
cert_test_block_3 153600 19 304 320 16
cert_test_block_3 153600 20 320 336 16
cert_test_block_3 153600 21 336 352 16
cert_test_block_3 153600 22 352 368 16
cert_test_block_3 153600 23 368 384 16
cert_test_block_3 153600 24 384 400 16
cert_test_block_3 153600 25 400 416 16
cert_test_block_3 153600 26 416 432 16
cert_test_block_3 153600 27 432 448 16
cert_test_block_3 153600 28 448 464 16
cert_test_block_3 153600 29 464 480 16
cert_test_block_3 153600 30 480 496 16
cert_test_block_3 153600 31 496 512 16
cert_test_block_3 153600 32 512 528 16
cert_test_block_3 153600 33 528 544 16
cert_test_block_3 153600 34 544 560 16
cert_test_block_3 153600 35 560 576 16
cert_test_block_3 153600 36 576 592 16
cert_test_block_3 153600 37 592 608 16
cert_test_block_3 153600 38 608 624 16
cert_test_block_3 153600 39 624 640 16
theorem test153600_complete : Interval test153600 0 640 :=
  (interval_append test153600 0 320 640
  (interval_append test153600 0 160 320
  (interval_append test153600 0 80 160
  (interval_append test153600 0 32 80
  (interval_append test153600 0 16 32
  test153600_block_0
  test153600_block_1)
  (interval_append test153600 32 48 80
  test153600_block_2
  (interval_append test153600 48 64 80
  test153600_block_3
  test153600_block_4)))
  (interval_append test153600 80 112 160
  (interval_append test153600 80 96 112
  test153600_block_5
  test153600_block_6)
  (interval_append test153600 112 128 160
  test153600_block_7
  (interval_append test153600 128 144 160
  test153600_block_8
  test153600_block_9))))
  (interval_append test153600 160 240 320
  (interval_append test153600 160 192 240
  (interval_append test153600 160 176 192
  test153600_block_10
  test153600_block_11)
  (interval_append test153600 192 208 240
  test153600_block_12
  (interval_append test153600 208 224 240
  test153600_block_13
  test153600_block_14)))
  (interval_append test153600 240 272 320
  (interval_append test153600 240 256 272
  test153600_block_15
  test153600_block_16)
  (interval_append test153600 272 288 320
  test153600_block_17
  (interval_append test153600 288 304 320
  test153600_block_18
  test153600_block_19)))))
  (interval_append test153600 320 480 640
  (interval_append test153600 320 400 480
  (interval_append test153600 320 352 400
  (interval_append test153600 320 336 352
  test153600_block_20
  test153600_block_21)
  (interval_append test153600 352 368 400
  test153600_block_22
  (interval_append test153600 368 384 400
  test153600_block_23
  test153600_block_24)))
  (interval_append test153600 400 432 480
  (interval_append test153600 400 416 432
  test153600_block_25
  test153600_block_26)
  (interval_append test153600 432 448 480
  test153600_block_27
  (interval_append test153600 448 464 480
  test153600_block_28
  test153600_block_29))))
  (interval_append test153600 480 560 640
  (interval_append test153600 480 512 560
  (interval_append test153600 480 496 512
  test153600_block_30
  test153600_block_31)
  (interval_append test153600 512 528 560
  test153600_block_32
  (interval_append test153600 528 544 560
  test153600_block_33
  test153600_block_34)))
  (interval_append test153600 560 592 640
  (interval_append test153600 560 576 592
  test153600_block_35
  test153600_block_36)
  (interval_append test153600 592 608 640
  test153600_block_37
  (interval_append test153600 608 624 640
  test153600_block_38
  test153600_block_39))))))
cert_nodeInterval_3 153600 154240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
