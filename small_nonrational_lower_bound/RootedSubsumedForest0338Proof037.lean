module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 23680
cert_test_block_3 23680 0 0 16 16
cert_test_block_3 23680 1 16 32 16
cert_test_block_3 23680 2 32 48 16
cert_test_block_3 23680 3 48 64 16
cert_test_block_3 23680 4 64 80 16
cert_test_block_3 23680 5 80 96 16
cert_test_block_3 23680 6 96 112 16
cert_test_block_3 23680 7 112 128 16
cert_test_block_3 23680 8 128 144 16
cert_test_block_3 23680 9 144 160 16
cert_test_block_3 23680 10 160 176 16
cert_test_block_3 23680 11 176 192 16
cert_test_block_3 23680 12 192 208 16
cert_test_block_3 23680 13 208 224 16
cert_test_block_3 23680 14 224 240 16
cert_test_block_3 23680 15 240 256 16
cert_test_block_3 23680 16 256 272 16
cert_test_block_3 23680 17 272 288 16
cert_test_block_3 23680 18 288 304 16
cert_test_block_3 23680 19 304 320 16
cert_test_block_3 23680 20 320 336 16
cert_test_block_3 23680 21 336 352 16
cert_test_block_3 23680 22 352 368 16
cert_test_block_3 23680 23 368 384 16
cert_test_block_3 23680 24 384 400 16
cert_test_block_3 23680 25 400 416 16
cert_test_block_3 23680 26 416 432 16
cert_test_block_3 23680 27 432 448 16
cert_test_block_3 23680 28 448 464 16
cert_test_block_3 23680 29 464 480 16
cert_test_block_3 23680 30 480 496 16
cert_test_block_3 23680 31 496 512 16
cert_test_block_3 23680 32 512 528 16
cert_test_block_3 23680 33 528 544 16
cert_test_block_3 23680 34 544 560 16
cert_test_block_3 23680 35 560 576 16
cert_test_block_3 23680 36 576 592 16
cert_test_block_3 23680 37 592 608 16
cert_test_block_3 23680 38 608 624 16
cert_test_block_3 23680 39 624 640 16
theorem test23680_complete : Interval test23680 0 640 :=
  (interval_append test23680 0 320 640
  (interval_append test23680 0 160 320
  (interval_append test23680 0 80 160
  (interval_append test23680 0 32 80
  (interval_append test23680 0 16 32
  test23680_block_0
  test23680_block_1)
  (interval_append test23680 32 48 80
  test23680_block_2
  (interval_append test23680 48 64 80
  test23680_block_3
  test23680_block_4)))
  (interval_append test23680 80 112 160
  (interval_append test23680 80 96 112
  test23680_block_5
  test23680_block_6)
  (interval_append test23680 112 128 160
  test23680_block_7
  (interval_append test23680 128 144 160
  test23680_block_8
  test23680_block_9))))
  (interval_append test23680 160 240 320
  (interval_append test23680 160 192 240
  (interval_append test23680 160 176 192
  test23680_block_10
  test23680_block_11)
  (interval_append test23680 192 208 240
  test23680_block_12
  (interval_append test23680 208 224 240
  test23680_block_13
  test23680_block_14)))
  (interval_append test23680 240 272 320
  (interval_append test23680 240 256 272
  test23680_block_15
  test23680_block_16)
  (interval_append test23680 272 288 320
  test23680_block_17
  (interval_append test23680 288 304 320
  test23680_block_18
  test23680_block_19)))))
  (interval_append test23680 320 480 640
  (interval_append test23680 320 400 480
  (interval_append test23680 320 352 400
  (interval_append test23680 320 336 352
  test23680_block_20
  test23680_block_21)
  (interval_append test23680 352 368 400
  test23680_block_22
  (interval_append test23680 368 384 400
  test23680_block_23
  test23680_block_24)))
  (interval_append test23680 400 432 480
  (interval_append test23680 400 416 432
  test23680_block_25
  test23680_block_26)
  (interval_append test23680 432 448 480
  test23680_block_27
  (interval_append test23680 448 464 480
  test23680_block_28
  test23680_block_29))))
  (interval_append test23680 480 560 640
  (interval_append test23680 480 512 560
  (interval_append test23680 480 496 512
  test23680_block_30
  test23680_block_31)
  (interval_append test23680 512 528 560
  test23680_block_32
  (interval_append test23680 528 544 560
  test23680_block_33
  test23680_block_34)))
  (interval_append test23680 560 592 640
  (interval_append test23680 560 576 592
  test23680_block_35
  test23680_block_36)
  (interval_append test23680 592 608 640
  test23680_block_37
  (interval_append test23680 608 624 640
  test23680_block_38
  test23680_block_39))))))
cert_nodeInterval_3 23680 24320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
