module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0365Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 640
cert_test_block_3 640 0 0 16 16
cert_test_block_3 640 1 16 32 16
cert_test_block_3 640 2 32 48 16
cert_test_block_3 640 3 48 64 16
cert_test_block_3 640 4 64 80 16
cert_test_block_3 640 5 80 96 16
cert_test_block_3 640 6 96 112 16
cert_test_block_3 640 7 112 128 16
cert_test_block_3 640 8 128 144 16
cert_test_block_3 640 9 144 160 16
cert_test_block_3 640 10 160 176 16
cert_test_block_3 640 11 176 192 16
cert_test_block_3 640 12 192 208 16
cert_test_block_3 640 13 208 224 16
cert_test_block_3 640 14 224 240 16
cert_test_block_3 640 15 240 256 16
cert_test_block_3 640 16 256 272 16
cert_test_block_3 640 17 272 288 16
cert_test_block_3 640 18 288 304 16
cert_test_block_3 640 19 304 320 16
cert_test_block_3 640 20 320 336 16
cert_test_block_3 640 21 336 352 16
cert_test_block_3 640 22 352 368 16
cert_test_block_3 640 23 368 384 16
cert_test_block_3 640 24 384 400 16
cert_test_block_3 640 25 400 416 16
cert_test_block_3 640 26 416 432 16
cert_test_block_3 640 27 432 448 16
cert_test_block_3 640 28 448 464 16
cert_test_block_3 640 29 464 480 16
cert_test_block_3 640 30 480 496 16
cert_test_block_3 640 31 496 512 16
cert_test_block_3 640 32 512 528 16
cert_test_block_3 640 33 528 544 16
cert_test_block_3 640 34 544 560 16
cert_test_block_3 640 35 560 576 16
cert_test_block_3 640 36 576 592 16
cert_test_block_3 640 37 592 608 16
cert_test_block_3 640 38 608 624 16
cert_test_block_3 640 39 624 640 16
theorem test640_complete : Interval test640 0 640 :=
  (interval_append test640 0 320 640
  (interval_append test640 0 160 320
  (interval_append test640 0 80 160
  (interval_append test640 0 32 80
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 80
  test640_block_2
  (interval_append test640 48 64 80
  test640_block_3
  test640_block_4)))
  (interval_append test640 80 112 160
  (interval_append test640 80 96 112
  test640_block_5
  test640_block_6)
  (interval_append test640 112 128 160
  test640_block_7
  (interval_append test640 128 144 160
  test640_block_8
  test640_block_9))))
  (interval_append test640 160 240 320
  (interval_append test640 160 192 240
  (interval_append test640 160 176 192
  test640_block_10
  test640_block_11)
  (interval_append test640 192 208 240
  test640_block_12
  (interval_append test640 208 224 240
  test640_block_13
  test640_block_14)))
  (interval_append test640 240 272 320
  (interval_append test640 240 256 272
  test640_block_15
  test640_block_16)
  (interval_append test640 272 288 320
  test640_block_17
  (interval_append test640 288 304 320
  test640_block_18
  test640_block_19)))))
  (interval_append test640 320 480 640
  (interval_append test640 320 400 480
  (interval_append test640 320 352 400
  (interval_append test640 320 336 352
  test640_block_20
  test640_block_21)
  (interval_append test640 352 368 400
  test640_block_22
  (interval_append test640 368 384 400
  test640_block_23
  test640_block_24)))
  (interval_append test640 400 432 480
  (interval_append test640 400 416 432
  test640_block_25
  test640_block_26)
  (interval_append test640 432 448 480
  test640_block_27
  (interval_append test640 448 464 480
  test640_block_28
  test640_block_29))))
  (interval_append test640 480 560 640
  (interval_append test640 480 512 560
  (interval_append test640 480 496 512
  test640_block_30
  test640_block_31)
  (interval_append test640 512 528 560
  test640_block_32
  (interval_append test640 528 544 560
  test640_block_33
  test640_block_34)))
  (interval_append test640 560 592 640
  (interval_append test640 560 576 592
  test640_block_35
  test640_block_36)
  (interval_append test640 592 608 640
  test640_block_37
  (interval_append test640 608 624 640
  test640_block_38
  test640_block_39))))))
cert_nodeInterval_3 640 1280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
