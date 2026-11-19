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
cert_test_11 65920
cert_test_block_3 65920 0 0 16 16
cert_test_block_3 65920 1 16 32 16
cert_test_block_3 65920 2 32 48 16
cert_test_block_3 65920 3 48 64 16
cert_test_block_3 65920 4 64 80 16
cert_test_block_3 65920 5 80 96 16
cert_test_block_3 65920 6 96 112 16
cert_test_block_3 65920 7 112 128 16
cert_test_block_3 65920 8 128 144 16
cert_test_block_3 65920 9 144 160 16
cert_test_block_3 65920 10 160 176 16
cert_test_block_3 65920 11 176 192 16
cert_test_block_3 65920 12 192 208 16
cert_test_block_3 65920 13 208 224 16
cert_test_block_3 65920 14 224 240 16
cert_test_block_3 65920 15 240 256 16
cert_test_block_3 65920 16 256 272 16
cert_test_block_3 65920 17 272 288 16
cert_test_block_3 65920 18 288 304 16
cert_test_block_3 65920 19 304 320 16
cert_test_block_3 65920 20 320 336 16
cert_test_block_3 65920 21 336 352 16
cert_test_block_3 65920 22 352 368 16
cert_test_block_3 65920 23 368 384 16
cert_test_block_3 65920 24 384 400 16
cert_test_block_3 65920 25 400 416 16
cert_test_block_3 65920 26 416 432 16
cert_test_block_3 65920 27 432 448 16
cert_test_block_3 65920 28 448 464 16
cert_test_block_3 65920 29 464 480 16
cert_test_block_3 65920 30 480 496 16
cert_test_block_3 65920 31 496 512 16
cert_test_block_3 65920 32 512 528 16
cert_test_block_3 65920 33 528 544 16
cert_test_block_3 65920 34 544 560 16
cert_test_block_3 65920 35 560 576 16
cert_test_block_3 65920 36 576 592 16
cert_test_block_3 65920 37 592 608 16
cert_test_block_3 65920 38 608 624 16
cert_test_block_3 65920 39 624 640 16
theorem test65920_complete : Interval test65920 0 640 :=
  (interval_append test65920 0 320 640
  (interval_append test65920 0 160 320
  (interval_append test65920 0 80 160
  (interval_append test65920 0 32 80
  (interval_append test65920 0 16 32
  test65920_block_0
  test65920_block_1)
  (interval_append test65920 32 48 80
  test65920_block_2
  (interval_append test65920 48 64 80
  test65920_block_3
  test65920_block_4)))
  (interval_append test65920 80 112 160
  (interval_append test65920 80 96 112
  test65920_block_5
  test65920_block_6)
  (interval_append test65920 112 128 160
  test65920_block_7
  (interval_append test65920 128 144 160
  test65920_block_8
  test65920_block_9))))
  (interval_append test65920 160 240 320
  (interval_append test65920 160 192 240
  (interval_append test65920 160 176 192
  test65920_block_10
  test65920_block_11)
  (interval_append test65920 192 208 240
  test65920_block_12
  (interval_append test65920 208 224 240
  test65920_block_13
  test65920_block_14)))
  (interval_append test65920 240 272 320
  (interval_append test65920 240 256 272
  test65920_block_15
  test65920_block_16)
  (interval_append test65920 272 288 320
  test65920_block_17
  (interval_append test65920 288 304 320
  test65920_block_18
  test65920_block_19)))))
  (interval_append test65920 320 480 640
  (interval_append test65920 320 400 480
  (interval_append test65920 320 352 400
  (interval_append test65920 320 336 352
  test65920_block_20
  test65920_block_21)
  (interval_append test65920 352 368 400
  test65920_block_22
  (interval_append test65920 368 384 400
  test65920_block_23
  test65920_block_24)))
  (interval_append test65920 400 432 480
  (interval_append test65920 400 416 432
  test65920_block_25
  test65920_block_26)
  (interval_append test65920 432 448 480
  test65920_block_27
  (interval_append test65920 448 464 480
  test65920_block_28
  test65920_block_29))))
  (interval_append test65920 480 560 640
  (interval_append test65920 480 512 560
  (interval_append test65920 480 496 512
  test65920_block_30
  test65920_block_31)
  (interval_append test65920 512 528 560
  test65920_block_32
  (interval_append test65920 528 544 560
  test65920_block_33
  test65920_block_34)))
  (interval_append test65920 560 592 640
  (interval_append test65920 560 576 592
  test65920_block_35
  test65920_block_36)
  (interval_append test65920 592 608 640
  test65920_block_37
  (interval_append test65920 608 624 640
  test65920_block_38
  test65920_block_39))))))
cert_nodeInterval_3 65920 66560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
