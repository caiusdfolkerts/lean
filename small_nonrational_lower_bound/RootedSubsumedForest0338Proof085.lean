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
cert_test_11 54400
cert_test_block_3 54400 0 0 16 16
cert_test_block_3 54400 1 16 32 16
cert_test_block_3 54400 2 32 48 16
cert_test_block_3 54400 3 48 64 16
cert_test_block_3 54400 4 64 80 16
cert_test_block_3 54400 5 80 96 16
cert_test_block_3 54400 6 96 112 16
cert_test_block_3 54400 7 112 128 16
cert_test_block_3 54400 8 128 144 16
cert_test_block_3 54400 9 144 160 16
cert_test_block_3 54400 10 160 176 16
cert_test_block_3 54400 11 176 192 16
cert_test_block_3 54400 12 192 208 16
cert_test_block_3 54400 13 208 224 16
cert_test_block_3 54400 14 224 240 16
cert_test_block_3 54400 15 240 256 16
cert_test_block_3 54400 16 256 272 16
cert_test_block_3 54400 17 272 288 16
cert_test_block_3 54400 18 288 304 16
cert_test_block_3 54400 19 304 320 16
cert_test_block_3 54400 20 320 336 16
cert_test_block_3 54400 21 336 352 16
cert_test_block_3 54400 22 352 368 16
cert_test_block_3 54400 23 368 384 16
cert_test_block_3 54400 24 384 400 16
cert_test_block_3 54400 25 400 416 16
cert_test_block_3 54400 26 416 432 16
cert_test_block_3 54400 27 432 448 16
cert_test_block_3 54400 28 448 464 16
cert_test_block_3 54400 29 464 480 16
cert_test_block_3 54400 30 480 496 16
cert_test_block_3 54400 31 496 512 16
cert_test_block_3 54400 32 512 528 16
cert_test_block_3 54400 33 528 544 16
cert_test_block_3 54400 34 544 560 16
cert_test_block_3 54400 35 560 576 16
cert_test_block_3 54400 36 576 592 16
cert_test_block_3 54400 37 592 608 16
cert_test_block_3 54400 38 608 624 16
cert_test_block_3 54400 39 624 640 16
theorem test54400_complete : Interval test54400 0 640 :=
  (interval_append test54400 0 320 640
  (interval_append test54400 0 160 320
  (interval_append test54400 0 80 160
  (interval_append test54400 0 32 80
  (interval_append test54400 0 16 32
  test54400_block_0
  test54400_block_1)
  (interval_append test54400 32 48 80
  test54400_block_2
  (interval_append test54400 48 64 80
  test54400_block_3
  test54400_block_4)))
  (interval_append test54400 80 112 160
  (interval_append test54400 80 96 112
  test54400_block_5
  test54400_block_6)
  (interval_append test54400 112 128 160
  test54400_block_7
  (interval_append test54400 128 144 160
  test54400_block_8
  test54400_block_9))))
  (interval_append test54400 160 240 320
  (interval_append test54400 160 192 240
  (interval_append test54400 160 176 192
  test54400_block_10
  test54400_block_11)
  (interval_append test54400 192 208 240
  test54400_block_12
  (interval_append test54400 208 224 240
  test54400_block_13
  test54400_block_14)))
  (interval_append test54400 240 272 320
  (interval_append test54400 240 256 272
  test54400_block_15
  test54400_block_16)
  (interval_append test54400 272 288 320
  test54400_block_17
  (interval_append test54400 288 304 320
  test54400_block_18
  test54400_block_19)))))
  (interval_append test54400 320 480 640
  (interval_append test54400 320 400 480
  (interval_append test54400 320 352 400
  (interval_append test54400 320 336 352
  test54400_block_20
  test54400_block_21)
  (interval_append test54400 352 368 400
  test54400_block_22
  (interval_append test54400 368 384 400
  test54400_block_23
  test54400_block_24)))
  (interval_append test54400 400 432 480
  (interval_append test54400 400 416 432
  test54400_block_25
  test54400_block_26)
  (interval_append test54400 432 448 480
  test54400_block_27
  (interval_append test54400 448 464 480
  test54400_block_28
  test54400_block_29))))
  (interval_append test54400 480 560 640
  (interval_append test54400 480 512 560
  (interval_append test54400 480 496 512
  test54400_block_30
  test54400_block_31)
  (interval_append test54400 512 528 560
  test54400_block_32
  (interval_append test54400 528 544 560
  test54400_block_33
  test54400_block_34)))
  (interval_append test54400 560 592 640
  (interval_append test54400 560 576 592
  test54400_block_35
  test54400_block_36)
  (interval_append test54400 592 608 640
  test54400_block_37
  (interval_append test54400 608 624 640
  test54400_block_38
  test54400_block_39))))))
cert_nodeInterval_3 54400 55040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
