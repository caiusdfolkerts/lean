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
cert_test_11 145280
cert_test_block_3 145280 0 0 16 16
cert_test_block_3 145280 1 16 32 16
cert_test_block_3 145280 2 32 48 16
cert_test_block_3 145280 3 48 64 16
cert_test_block_3 145280 4 64 80 16
cert_test_block_3 145280 5 80 96 16
cert_test_block_3 145280 6 96 112 16
cert_test_block_3 145280 7 112 128 16
cert_test_block_3 145280 8 128 144 16
cert_test_block_3 145280 9 144 160 16
cert_test_block_3 145280 10 160 176 16
cert_test_block_3 145280 11 176 192 16
cert_test_block_3 145280 12 192 208 16
cert_test_block_3 145280 13 208 224 16
cert_test_block_3 145280 14 224 240 16
cert_test_block_3 145280 15 240 256 16
cert_test_block_3 145280 16 256 272 16
cert_test_block_3 145280 17 272 288 16
cert_test_block_3 145280 18 288 304 16
cert_test_block_3 145280 19 304 320 16
cert_test_block_3 145280 20 320 336 16
cert_test_block_3 145280 21 336 352 16
cert_test_block_3 145280 22 352 368 16
cert_test_block_3 145280 23 368 384 16
cert_test_block_3 145280 24 384 400 16
cert_test_block_3 145280 25 400 416 16
cert_test_block_3 145280 26 416 432 16
cert_test_block_3 145280 27 432 448 16
cert_test_block_3 145280 28 448 464 16
cert_test_block_3 145280 29 464 480 16
cert_test_block_3 145280 30 480 496 16
cert_test_block_3 145280 31 496 512 16
cert_test_block_3 145280 32 512 528 16
cert_test_block_3 145280 33 528 544 16
cert_test_block_3 145280 34 544 560 16
cert_test_block_3 145280 35 560 576 16
cert_test_block_3 145280 36 576 592 16
cert_test_block_3 145280 37 592 608 16
cert_test_block_3 145280 38 608 624 16
cert_test_block_3 145280 39 624 640 16
theorem test145280_complete : Interval test145280 0 640 :=
  (interval_append test145280 0 320 640
  (interval_append test145280 0 160 320
  (interval_append test145280 0 80 160
  (interval_append test145280 0 32 80
  (interval_append test145280 0 16 32
  test145280_block_0
  test145280_block_1)
  (interval_append test145280 32 48 80
  test145280_block_2
  (interval_append test145280 48 64 80
  test145280_block_3
  test145280_block_4)))
  (interval_append test145280 80 112 160
  (interval_append test145280 80 96 112
  test145280_block_5
  test145280_block_6)
  (interval_append test145280 112 128 160
  test145280_block_7
  (interval_append test145280 128 144 160
  test145280_block_8
  test145280_block_9))))
  (interval_append test145280 160 240 320
  (interval_append test145280 160 192 240
  (interval_append test145280 160 176 192
  test145280_block_10
  test145280_block_11)
  (interval_append test145280 192 208 240
  test145280_block_12
  (interval_append test145280 208 224 240
  test145280_block_13
  test145280_block_14)))
  (interval_append test145280 240 272 320
  (interval_append test145280 240 256 272
  test145280_block_15
  test145280_block_16)
  (interval_append test145280 272 288 320
  test145280_block_17
  (interval_append test145280 288 304 320
  test145280_block_18
  test145280_block_19)))))
  (interval_append test145280 320 480 640
  (interval_append test145280 320 400 480
  (interval_append test145280 320 352 400
  (interval_append test145280 320 336 352
  test145280_block_20
  test145280_block_21)
  (interval_append test145280 352 368 400
  test145280_block_22
  (interval_append test145280 368 384 400
  test145280_block_23
  test145280_block_24)))
  (interval_append test145280 400 432 480
  (interval_append test145280 400 416 432
  test145280_block_25
  test145280_block_26)
  (interval_append test145280 432 448 480
  test145280_block_27
  (interval_append test145280 448 464 480
  test145280_block_28
  test145280_block_29))))
  (interval_append test145280 480 560 640
  (interval_append test145280 480 512 560
  (interval_append test145280 480 496 512
  test145280_block_30
  test145280_block_31)
  (interval_append test145280 512 528 560
  test145280_block_32
  (interval_append test145280 528 544 560
  test145280_block_33
  test145280_block_34)))
  (interval_append test145280 560 592 640
  (interval_append test145280 560 576 592
  test145280_block_35
  test145280_block_36)
  (interval_append test145280 592 608 640
  test145280_block_37
  (interval_append test145280 608 624 640
  test145280_block_38
  test145280_block_39))))))
cert_nodeInterval_3 145280 145920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
