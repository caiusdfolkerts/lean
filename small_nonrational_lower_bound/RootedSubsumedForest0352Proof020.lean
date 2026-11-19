module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0352Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 12800
cert_test_block_3 12800 0 0 16 16
cert_test_block_3 12800 1 16 32 16
cert_test_block_3 12800 2 32 48 16
cert_test_block_3 12800 3 48 64 16
cert_test_block_3 12800 4 64 80 16
cert_test_block_3 12800 5 80 96 16
cert_test_block_3 12800 6 96 112 16
cert_test_block_3 12800 7 112 128 16
cert_test_block_3 12800 8 128 144 16
cert_test_block_3 12800 9 144 160 16
cert_test_block_3 12800 10 160 176 16
cert_test_block_3 12800 11 176 192 16
cert_test_block_3 12800 12 192 208 16
cert_test_block_3 12800 13 208 224 16
cert_test_block_3 12800 14 224 240 16
cert_test_block_3 12800 15 240 256 16
cert_test_block_3 12800 16 256 272 16
cert_test_block_3 12800 17 272 288 16
cert_test_block_3 12800 18 288 304 16
cert_test_block_3 12800 19 304 320 16
cert_test_block_3 12800 20 320 336 16
cert_test_block_3 12800 21 336 352 16
cert_test_block_3 12800 22 352 368 16
cert_test_block_3 12800 23 368 384 16
cert_test_block_3 12800 24 384 400 16
cert_test_block_3 12800 25 400 416 16
cert_test_block_3 12800 26 416 432 16
cert_test_block_3 12800 27 432 448 16
cert_test_block_3 12800 28 448 464 16
cert_test_block_3 12800 29 464 480 16
cert_test_block_3 12800 30 480 496 16
cert_test_block_3 12800 31 496 512 16
cert_test_block_3 12800 32 512 528 16
cert_test_block_3 12800 33 528 544 16
cert_test_block_3 12800 34 544 560 16
cert_test_block_3 12800 35 560 576 16
cert_test_block_3 12800 36 576 592 16
cert_test_block_3 12800 37 592 608 16
cert_test_block_3 12800 38 608 624 16
cert_test_block_3 12800 39 624 640 16
theorem test12800_complete : Interval test12800 0 640 :=
  (interval_append test12800 0 320 640
  (interval_append test12800 0 160 320
  (interval_append test12800 0 80 160
  (interval_append test12800 0 32 80
  (interval_append test12800 0 16 32
  test12800_block_0
  test12800_block_1)
  (interval_append test12800 32 48 80
  test12800_block_2
  (interval_append test12800 48 64 80
  test12800_block_3
  test12800_block_4)))
  (interval_append test12800 80 112 160
  (interval_append test12800 80 96 112
  test12800_block_5
  test12800_block_6)
  (interval_append test12800 112 128 160
  test12800_block_7
  (interval_append test12800 128 144 160
  test12800_block_8
  test12800_block_9))))
  (interval_append test12800 160 240 320
  (interval_append test12800 160 192 240
  (interval_append test12800 160 176 192
  test12800_block_10
  test12800_block_11)
  (interval_append test12800 192 208 240
  test12800_block_12
  (interval_append test12800 208 224 240
  test12800_block_13
  test12800_block_14)))
  (interval_append test12800 240 272 320
  (interval_append test12800 240 256 272
  test12800_block_15
  test12800_block_16)
  (interval_append test12800 272 288 320
  test12800_block_17
  (interval_append test12800 288 304 320
  test12800_block_18
  test12800_block_19)))))
  (interval_append test12800 320 480 640
  (interval_append test12800 320 400 480
  (interval_append test12800 320 352 400
  (interval_append test12800 320 336 352
  test12800_block_20
  test12800_block_21)
  (interval_append test12800 352 368 400
  test12800_block_22
  (interval_append test12800 368 384 400
  test12800_block_23
  test12800_block_24)))
  (interval_append test12800 400 432 480
  (interval_append test12800 400 416 432
  test12800_block_25
  test12800_block_26)
  (interval_append test12800 432 448 480
  test12800_block_27
  (interval_append test12800 448 464 480
  test12800_block_28
  test12800_block_29))))
  (interval_append test12800 480 560 640
  (interval_append test12800 480 512 560
  (interval_append test12800 480 496 512
  test12800_block_30
  test12800_block_31)
  (interval_append test12800 512 528 560
  test12800_block_32
  (interval_append test12800 528 544 560
  test12800_block_33
  test12800_block_34)))
  (interval_append test12800 560 592 640
  (interval_append test12800 560 576 592
  test12800_block_35
  test12800_block_36)
  (interval_append test12800 592 608 640
  test12800_block_37
  (interval_append test12800 608 624 640
  test12800_block_38
  test12800_block_39))))))
cert_nodeInterval_3 12800 13440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
