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
cert_test_11 120320
cert_test_block_3 120320 0 0 16 16
cert_test_block_3 120320 1 16 32 16
cert_test_block_3 120320 2 32 48 16
cert_test_block_3 120320 3 48 64 16
cert_test_block_3 120320 4 64 80 16
cert_test_block_3 120320 5 80 96 16
cert_test_block_3 120320 6 96 112 16
cert_test_block_3 120320 7 112 128 16
cert_test_block_3 120320 8 128 144 16
cert_test_block_3 120320 9 144 160 16
cert_test_block_3 120320 10 160 176 16
cert_test_block_3 120320 11 176 192 16
cert_test_block_3 120320 12 192 208 16
cert_test_block_3 120320 13 208 224 16
cert_test_block_3 120320 14 224 240 16
cert_test_block_3 120320 15 240 256 16
cert_test_block_3 120320 16 256 272 16
cert_test_block_3 120320 17 272 288 16
cert_test_block_3 120320 18 288 304 16
cert_test_block_3 120320 19 304 320 16
cert_test_block_3 120320 20 320 336 16
cert_test_block_3 120320 21 336 352 16
cert_test_block_3 120320 22 352 368 16
cert_test_block_3 120320 23 368 384 16
cert_test_block_3 120320 24 384 400 16
cert_test_block_3 120320 25 400 416 16
cert_test_block_3 120320 26 416 432 16
cert_test_block_3 120320 27 432 448 16
cert_test_block_3 120320 28 448 464 16
cert_test_block_3 120320 29 464 480 16
cert_test_block_3 120320 30 480 496 16
cert_test_block_3 120320 31 496 512 16
cert_test_block_3 120320 32 512 528 16
cert_test_block_3 120320 33 528 544 16
cert_test_block_3 120320 34 544 560 16
cert_test_block_3 120320 35 560 576 16
cert_test_block_3 120320 36 576 592 16
cert_test_block_3 120320 37 592 608 16
cert_test_block_3 120320 38 608 624 16
cert_test_block_3 120320 39 624 640 16
theorem test120320_complete : Interval test120320 0 640 :=
  (interval_append test120320 0 320 640
  (interval_append test120320 0 160 320
  (interval_append test120320 0 80 160
  (interval_append test120320 0 32 80
  (interval_append test120320 0 16 32
  test120320_block_0
  test120320_block_1)
  (interval_append test120320 32 48 80
  test120320_block_2
  (interval_append test120320 48 64 80
  test120320_block_3
  test120320_block_4)))
  (interval_append test120320 80 112 160
  (interval_append test120320 80 96 112
  test120320_block_5
  test120320_block_6)
  (interval_append test120320 112 128 160
  test120320_block_7
  (interval_append test120320 128 144 160
  test120320_block_8
  test120320_block_9))))
  (interval_append test120320 160 240 320
  (interval_append test120320 160 192 240
  (interval_append test120320 160 176 192
  test120320_block_10
  test120320_block_11)
  (interval_append test120320 192 208 240
  test120320_block_12
  (interval_append test120320 208 224 240
  test120320_block_13
  test120320_block_14)))
  (interval_append test120320 240 272 320
  (interval_append test120320 240 256 272
  test120320_block_15
  test120320_block_16)
  (interval_append test120320 272 288 320
  test120320_block_17
  (interval_append test120320 288 304 320
  test120320_block_18
  test120320_block_19)))))
  (interval_append test120320 320 480 640
  (interval_append test120320 320 400 480
  (interval_append test120320 320 352 400
  (interval_append test120320 320 336 352
  test120320_block_20
  test120320_block_21)
  (interval_append test120320 352 368 400
  test120320_block_22
  (interval_append test120320 368 384 400
  test120320_block_23
  test120320_block_24)))
  (interval_append test120320 400 432 480
  (interval_append test120320 400 416 432
  test120320_block_25
  test120320_block_26)
  (interval_append test120320 432 448 480
  test120320_block_27
  (interval_append test120320 448 464 480
  test120320_block_28
  test120320_block_29))))
  (interval_append test120320 480 560 640
  (interval_append test120320 480 512 560
  (interval_append test120320 480 496 512
  test120320_block_30
  test120320_block_31)
  (interval_append test120320 512 528 560
  test120320_block_32
  (interval_append test120320 528 544 560
  test120320_block_33
  test120320_block_34)))
  (interval_append test120320 560 592 640
  (interval_append test120320 560 576 592
  test120320_block_35
  test120320_block_36)
  (interval_append test120320 592 608 640
  test120320_block_37
  (interval_append test120320 608 624 640
  test120320_block_38
  test120320_block_39))))))
cert_nodeInterval_3 120320 120960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
