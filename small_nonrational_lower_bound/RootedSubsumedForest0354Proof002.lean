module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0354Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1280
cert_test_block_3 1280 0 0 16 16
cert_test_block_3 1280 1 16 32 16
cert_test_block_3 1280 2 32 48 16
cert_test_block_3 1280 3 48 64 16
cert_test_block_3 1280 4 64 80 16
cert_test_block_3 1280 5 80 96 16
cert_test_block_3 1280 6 96 112 16
cert_test_block_3 1280 7 112 128 16
cert_test_block_3 1280 8 128 144 16
cert_test_block_3 1280 9 144 160 16
cert_test_block_3 1280 10 160 176 16
cert_test_block_3 1280 11 176 192 16
cert_test_block_3 1280 12 192 208 16
cert_test_block_3 1280 13 208 224 16
cert_test_block_3 1280 14 224 240 16
cert_test_block_3 1280 15 240 256 16
cert_test_block_3 1280 16 256 272 16
cert_test_block_3 1280 17 272 288 16
cert_test_block_3 1280 18 288 304 16
cert_test_block_3 1280 19 304 320 16
cert_test_block_3 1280 20 320 336 16
cert_test_block_3 1280 21 336 352 16
cert_test_block_3 1280 22 352 368 16
cert_test_block_3 1280 23 368 384 16
cert_test_block_3 1280 24 384 400 16
cert_test_block_3 1280 25 400 416 16
cert_test_block_3 1280 26 416 432 16
cert_test_block_3 1280 27 432 448 16
cert_test_block_3 1280 28 448 464 16
cert_test_block_3 1280 29 464 480 16
cert_test_block_3 1280 30 480 496 16
cert_test_block_3 1280 31 496 512 16
cert_test_block_3 1280 32 512 528 16
cert_test_block_3 1280 33 528 544 16
cert_test_block_3 1280 34 544 560 16
cert_test_block_3 1280 35 560 576 16
cert_test_block_3 1280 36 576 592 16
cert_test_block_3 1280 37 592 608 16
cert_test_block_3 1280 38 608 624 16
cert_test_block_3 1280 39 624 640 16
theorem test1280_complete : Interval test1280 0 640 :=
  (interval_append test1280 0 320 640
  (interval_append test1280 0 160 320
  (interval_append test1280 0 80 160
  (interval_append test1280 0 32 80
  (interval_append test1280 0 16 32
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 32 48 80
  test1280_block_2
  (interval_append test1280 48 64 80
  test1280_block_3
  test1280_block_4)))
  (interval_append test1280 80 112 160
  (interval_append test1280 80 96 112
  test1280_block_5
  test1280_block_6)
  (interval_append test1280 112 128 160
  test1280_block_7
  (interval_append test1280 128 144 160
  test1280_block_8
  test1280_block_9))))
  (interval_append test1280 160 240 320
  (interval_append test1280 160 192 240
  (interval_append test1280 160 176 192
  test1280_block_10
  test1280_block_11)
  (interval_append test1280 192 208 240
  test1280_block_12
  (interval_append test1280 208 224 240
  test1280_block_13
  test1280_block_14)))
  (interval_append test1280 240 272 320
  (interval_append test1280 240 256 272
  test1280_block_15
  test1280_block_16)
  (interval_append test1280 272 288 320
  test1280_block_17
  (interval_append test1280 288 304 320
  test1280_block_18
  test1280_block_19)))))
  (interval_append test1280 320 480 640
  (interval_append test1280 320 400 480
  (interval_append test1280 320 352 400
  (interval_append test1280 320 336 352
  test1280_block_20
  test1280_block_21)
  (interval_append test1280 352 368 400
  test1280_block_22
  (interval_append test1280 368 384 400
  test1280_block_23
  test1280_block_24)))
  (interval_append test1280 400 432 480
  (interval_append test1280 400 416 432
  test1280_block_25
  test1280_block_26)
  (interval_append test1280 432 448 480
  test1280_block_27
  (interval_append test1280 448 464 480
  test1280_block_28
  test1280_block_29))))
  (interval_append test1280 480 560 640
  (interval_append test1280 480 512 560
  (interval_append test1280 480 496 512
  test1280_block_30
  test1280_block_31)
  (interval_append test1280 512 528 560
  test1280_block_32
  (interval_append test1280 528 544 560
  test1280_block_33
  test1280_block_34)))
  (interval_append test1280 560 592 640
  (interval_append test1280 560 576 592
  test1280_block_35
  test1280_block_36)
  (interval_append test1280 592 608 640
  test1280_block_37
  (interval_append test1280 608 624 640
  test1280_block_38
  test1280_block_39))))))
cert_nodeInterval_3 1280 1920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
