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
cert_test_11 136320
cert_test_block_3 136320 0 0 16 16
cert_test_block_3 136320 1 16 32 16
cert_test_block_3 136320 2 32 48 16
cert_test_block_3 136320 3 48 64 16
cert_test_block_3 136320 4 64 80 16
cert_test_block_3 136320 5 80 96 16
cert_test_block_3 136320 6 96 112 16
cert_test_block_3 136320 7 112 128 16
cert_test_block_3 136320 8 128 144 16
cert_test_block_3 136320 9 144 160 16
cert_test_block_3 136320 10 160 176 16
cert_test_block_3 136320 11 176 192 16
cert_test_block_3 136320 12 192 208 16
cert_test_block_3 136320 13 208 224 16
cert_test_block_3 136320 14 224 240 16
cert_test_block_3 136320 15 240 256 16
cert_test_block_3 136320 16 256 272 16
cert_test_block_3 136320 17 272 288 16
cert_test_block_3 136320 18 288 304 16
cert_test_block_3 136320 19 304 320 16
cert_test_block_3 136320 20 320 336 16
cert_test_block_3 136320 21 336 352 16
cert_test_block_3 136320 22 352 368 16
cert_test_block_3 136320 23 368 384 16
cert_test_block_3 136320 24 384 400 16
cert_test_block_3 136320 25 400 416 16
cert_test_block_3 136320 26 416 432 16
cert_test_block_3 136320 27 432 448 16
cert_test_block_3 136320 28 448 464 16
cert_test_block_3 136320 29 464 480 16
cert_test_block_3 136320 30 480 496 16
cert_test_block_3 136320 31 496 512 16
cert_test_block_3 136320 32 512 528 16
cert_test_block_3 136320 33 528 544 16
cert_test_block_3 136320 34 544 560 16
cert_test_block_3 136320 35 560 576 16
cert_test_block_3 136320 36 576 592 16
cert_test_block_3 136320 37 592 608 16
cert_test_block_3 136320 38 608 624 16
cert_test_block_3 136320 39 624 640 16
theorem test136320_complete : Interval test136320 0 640 :=
  (interval_append test136320 0 320 640
  (interval_append test136320 0 160 320
  (interval_append test136320 0 80 160
  (interval_append test136320 0 32 80
  (interval_append test136320 0 16 32
  test136320_block_0
  test136320_block_1)
  (interval_append test136320 32 48 80
  test136320_block_2
  (interval_append test136320 48 64 80
  test136320_block_3
  test136320_block_4)))
  (interval_append test136320 80 112 160
  (interval_append test136320 80 96 112
  test136320_block_5
  test136320_block_6)
  (interval_append test136320 112 128 160
  test136320_block_7
  (interval_append test136320 128 144 160
  test136320_block_8
  test136320_block_9))))
  (interval_append test136320 160 240 320
  (interval_append test136320 160 192 240
  (interval_append test136320 160 176 192
  test136320_block_10
  test136320_block_11)
  (interval_append test136320 192 208 240
  test136320_block_12
  (interval_append test136320 208 224 240
  test136320_block_13
  test136320_block_14)))
  (interval_append test136320 240 272 320
  (interval_append test136320 240 256 272
  test136320_block_15
  test136320_block_16)
  (interval_append test136320 272 288 320
  test136320_block_17
  (interval_append test136320 288 304 320
  test136320_block_18
  test136320_block_19)))))
  (interval_append test136320 320 480 640
  (interval_append test136320 320 400 480
  (interval_append test136320 320 352 400
  (interval_append test136320 320 336 352
  test136320_block_20
  test136320_block_21)
  (interval_append test136320 352 368 400
  test136320_block_22
  (interval_append test136320 368 384 400
  test136320_block_23
  test136320_block_24)))
  (interval_append test136320 400 432 480
  (interval_append test136320 400 416 432
  test136320_block_25
  test136320_block_26)
  (interval_append test136320 432 448 480
  test136320_block_27
  (interval_append test136320 448 464 480
  test136320_block_28
  test136320_block_29))))
  (interval_append test136320 480 560 640
  (interval_append test136320 480 512 560
  (interval_append test136320 480 496 512
  test136320_block_30
  test136320_block_31)
  (interval_append test136320 512 528 560
  test136320_block_32
  (interval_append test136320 528 544 560
  test136320_block_33
  test136320_block_34)))
  (interval_append test136320 560 592 640
  (interval_append test136320 560 576 592
  test136320_block_35
  test136320_block_36)
  (interval_append test136320 592 608 640
  test136320_block_37
  (interval_append test136320 608 624 640
  test136320_block_38
  test136320_block_39))))))
cert_nodeInterval_3 136320 136960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
