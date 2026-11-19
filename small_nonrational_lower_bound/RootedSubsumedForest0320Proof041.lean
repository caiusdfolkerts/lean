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
cert_test_11 26240
cert_test_block_3 26240 0 0 16 16
cert_test_block_3 26240 1 16 32 16
cert_test_block_3 26240 2 32 48 16
cert_test_block_3 26240 3 48 64 16
cert_test_block_3 26240 4 64 80 16
cert_test_block_3 26240 5 80 96 16
cert_test_block_3 26240 6 96 112 16
cert_test_block_3 26240 7 112 128 16
cert_test_block_3 26240 8 128 144 16
cert_test_block_3 26240 9 144 160 16
cert_test_block_3 26240 10 160 176 16
cert_test_block_3 26240 11 176 192 16
cert_test_block_3 26240 12 192 208 16
cert_test_block_3 26240 13 208 224 16
cert_test_block_3 26240 14 224 240 16
cert_test_block_3 26240 15 240 256 16
cert_test_block_3 26240 16 256 272 16
cert_test_block_3 26240 17 272 288 16
cert_test_block_3 26240 18 288 304 16
cert_test_block_3 26240 19 304 320 16
cert_test_block_3 26240 20 320 336 16
cert_test_block_3 26240 21 336 352 16
cert_test_block_3 26240 22 352 368 16
cert_test_block_3 26240 23 368 384 16
cert_test_block_3 26240 24 384 400 16
cert_test_block_3 26240 25 400 416 16
cert_test_block_3 26240 26 416 432 16
cert_test_block_3 26240 27 432 448 16
cert_test_block_3 26240 28 448 464 16
cert_test_block_3 26240 29 464 480 16
cert_test_block_3 26240 30 480 496 16
cert_test_block_3 26240 31 496 512 16
cert_test_block_3 26240 32 512 528 16
cert_test_block_3 26240 33 528 544 16
cert_test_block_3 26240 34 544 560 16
cert_test_block_3 26240 35 560 576 16
cert_test_block_3 26240 36 576 592 16
cert_test_block_3 26240 37 592 608 16
cert_test_block_3 26240 38 608 624 16
cert_test_block_3 26240 39 624 640 16
theorem test26240_complete : Interval test26240 0 640 :=
  (interval_append test26240 0 320 640
  (interval_append test26240 0 160 320
  (interval_append test26240 0 80 160
  (interval_append test26240 0 32 80
  (interval_append test26240 0 16 32
  test26240_block_0
  test26240_block_1)
  (interval_append test26240 32 48 80
  test26240_block_2
  (interval_append test26240 48 64 80
  test26240_block_3
  test26240_block_4)))
  (interval_append test26240 80 112 160
  (interval_append test26240 80 96 112
  test26240_block_5
  test26240_block_6)
  (interval_append test26240 112 128 160
  test26240_block_7
  (interval_append test26240 128 144 160
  test26240_block_8
  test26240_block_9))))
  (interval_append test26240 160 240 320
  (interval_append test26240 160 192 240
  (interval_append test26240 160 176 192
  test26240_block_10
  test26240_block_11)
  (interval_append test26240 192 208 240
  test26240_block_12
  (interval_append test26240 208 224 240
  test26240_block_13
  test26240_block_14)))
  (interval_append test26240 240 272 320
  (interval_append test26240 240 256 272
  test26240_block_15
  test26240_block_16)
  (interval_append test26240 272 288 320
  test26240_block_17
  (interval_append test26240 288 304 320
  test26240_block_18
  test26240_block_19)))))
  (interval_append test26240 320 480 640
  (interval_append test26240 320 400 480
  (interval_append test26240 320 352 400
  (interval_append test26240 320 336 352
  test26240_block_20
  test26240_block_21)
  (interval_append test26240 352 368 400
  test26240_block_22
  (interval_append test26240 368 384 400
  test26240_block_23
  test26240_block_24)))
  (interval_append test26240 400 432 480
  (interval_append test26240 400 416 432
  test26240_block_25
  test26240_block_26)
  (interval_append test26240 432 448 480
  test26240_block_27
  (interval_append test26240 448 464 480
  test26240_block_28
  test26240_block_29))))
  (interval_append test26240 480 560 640
  (interval_append test26240 480 512 560
  (interval_append test26240 480 496 512
  test26240_block_30
  test26240_block_31)
  (interval_append test26240 512 528 560
  test26240_block_32
  (interval_append test26240 528 544 560
  test26240_block_33
  test26240_block_34)))
  (interval_append test26240 560 592 640
  (interval_append test26240 560 576 592
  test26240_block_35
  test26240_block_36)
  (interval_append test26240 592 608 640
  test26240_block_37
  (interval_append test26240 608 624 640
  test26240_block_38
  test26240_block_39))))))
cert_nodeInterval_3 26240 26880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
