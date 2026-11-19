module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 110080
cert_test_block_3 110080 0 0 16 16
cert_test_block_3 110080 1 16 32 16
cert_test_block_3 110080 2 32 48 16
cert_test_block_3 110080 3 48 64 16
cert_test_block_3 110080 4 64 80 16
cert_test_block_3 110080 5 80 96 16
cert_test_block_3 110080 6 96 112 16
cert_test_block_3 110080 7 112 128 16
cert_test_block_3 110080 8 128 144 16
cert_test_block_3 110080 9 144 160 16
cert_test_block_3 110080 10 160 176 16
cert_test_block_3 110080 11 176 192 16
cert_test_block_3 110080 12 192 208 16
cert_test_block_3 110080 13 208 224 16
cert_test_block_3 110080 14 224 240 16
cert_test_block_3 110080 15 240 256 16
cert_test_block_3 110080 16 256 272 16
cert_test_block_3 110080 17 272 288 16
cert_test_block_3 110080 18 288 304 16
cert_test_block_3 110080 19 304 320 16
cert_test_block_3 110080 20 320 336 16
cert_test_block_3 110080 21 336 352 16
cert_test_block_3 110080 22 352 368 16
cert_test_block_3 110080 23 368 384 16
cert_test_block_3 110080 24 384 400 16
cert_test_block_3 110080 25 400 416 16
cert_test_block_3 110080 26 416 432 16
cert_test_block_3 110080 27 432 448 16
cert_test_block_3 110080 28 448 464 16
cert_test_block_3 110080 29 464 480 16
cert_test_block_3 110080 30 480 496 16
cert_test_block_3 110080 31 496 512 16
cert_test_block_3 110080 32 512 528 16
cert_test_block_3 110080 33 528 544 16
cert_test_block_3 110080 34 544 560 16
cert_test_block_3 110080 35 560 576 16
cert_test_block_3 110080 36 576 592 16
cert_test_block_3 110080 37 592 608 16
cert_test_block_3 110080 38 608 624 16
cert_test_block_3 110080 39 624 640 16
theorem test110080_complete : Interval test110080 0 640 :=
  (interval_append test110080 0 320 640
  (interval_append test110080 0 160 320
  (interval_append test110080 0 80 160
  (interval_append test110080 0 32 80
  (interval_append test110080 0 16 32
  test110080_block_0
  test110080_block_1)
  (interval_append test110080 32 48 80
  test110080_block_2
  (interval_append test110080 48 64 80
  test110080_block_3
  test110080_block_4)))
  (interval_append test110080 80 112 160
  (interval_append test110080 80 96 112
  test110080_block_5
  test110080_block_6)
  (interval_append test110080 112 128 160
  test110080_block_7
  (interval_append test110080 128 144 160
  test110080_block_8
  test110080_block_9))))
  (interval_append test110080 160 240 320
  (interval_append test110080 160 192 240
  (interval_append test110080 160 176 192
  test110080_block_10
  test110080_block_11)
  (interval_append test110080 192 208 240
  test110080_block_12
  (interval_append test110080 208 224 240
  test110080_block_13
  test110080_block_14)))
  (interval_append test110080 240 272 320
  (interval_append test110080 240 256 272
  test110080_block_15
  test110080_block_16)
  (interval_append test110080 272 288 320
  test110080_block_17
  (interval_append test110080 288 304 320
  test110080_block_18
  test110080_block_19)))))
  (interval_append test110080 320 480 640
  (interval_append test110080 320 400 480
  (interval_append test110080 320 352 400
  (interval_append test110080 320 336 352
  test110080_block_20
  test110080_block_21)
  (interval_append test110080 352 368 400
  test110080_block_22
  (interval_append test110080 368 384 400
  test110080_block_23
  test110080_block_24)))
  (interval_append test110080 400 432 480
  (interval_append test110080 400 416 432
  test110080_block_25
  test110080_block_26)
  (interval_append test110080 432 448 480
  test110080_block_27
  (interval_append test110080 448 464 480
  test110080_block_28
  test110080_block_29))))
  (interval_append test110080 480 560 640
  (interval_append test110080 480 512 560
  (interval_append test110080 480 496 512
  test110080_block_30
  test110080_block_31)
  (interval_append test110080 512 528 560
  test110080_block_32
  (interval_append test110080 528 544 560
  test110080_block_33
  test110080_block_34)))
  (interval_append test110080 560 592 640
  (interval_append test110080 560 576 592
  test110080_block_35
  test110080_block_36)
  (interval_append test110080 592 608 640
  test110080_block_37
  (interval_append test110080 608 624 640
  test110080_block_38
  test110080_block_39))))))
cert_nodeInterval_3 110080 110720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
