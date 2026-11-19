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
cert_test_11 81920
cert_test_block_3 81920 0 0 16 16
cert_test_block_3 81920 1 16 32 16
cert_test_block_3 81920 2 32 48 16
cert_test_block_3 81920 3 48 64 16
cert_test_block_3 81920 4 64 80 16
cert_test_block_3 81920 5 80 96 16
cert_test_block_3 81920 6 96 112 16
cert_test_block_3 81920 7 112 128 16
cert_test_block_3 81920 8 128 144 16
cert_test_block_3 81920 9 144 160 16
cert_test_block_3 81920 10 160 176 16
cert_test_block_3 81920 11 176 192 16
cert_test_block_3 81920 12 192 208 16
cert_test_block_3 81920 13 208 224 16
cert_test_block_3 81920 14 224 240 16
cert_test_block_3 81920 15 240 256 16
cert_test_block_3 81920 16 256 272 16
cert_test_block_3 81920 17 272 288 16
cert_test_block_3 81920 18 288 304 16
cert_test_block_3 81920 19 304 320 16
cert_test_block_3 81920 20 320 336 16
cert_test_block_3 81920 21 336 352 16
cert_test_block_3 81920 22 352 368 16
cert_test_block_3 81920 23 368 384 16
cert_test_block_3 81920 24 384 400 16
cert_test_block_3 81920 25 400 416 16
cert_test_block_3 81920 26 416 432 16
cert_test_block_3 81920 27 432 448 16
cert_test_block_3 81920 28 448 464 16
cert_test_block_3 81920 29 464 480 16
cert_test_block_3 81920 30 480 496 16
cert_test_block_3 81920 31 496 512 16
cert_test_block_3 81920 32 512 528 16
cert_test_block_3 81920 33 528 544 16
cert_test_block_3 81920 34 544 560 16
cert_test_block_3 81920 35 560 576 16
cert_test_block_3 81920 36 576 592 16
cert_test_block_3 81920 37 592 608 16
cert_test_block_3 81920 38 608 624 16
cert_test_block_3 81920 39 624 640 16
theorem test81920_complete : Interval test81920 0 640 :=
  (interval_append test81920 0 320 640
  (interval_append test81920 0 160 320
  (interval_append test81920 0 80 160
  (interval_append test81920 0 32 80
  (interval_append test81920 0 16 32
  test81920_block_0
  test81920_block_1)
  (interval_append test81920 32 48 80
  test81920_block_2
  (interval_append test81920 48 64 80
  test81920_block_3
  test81920_block_4)))
  (interval_append test81920 80 112 160
  (interval_append test81920 80 96 112
  test81920_block_5
  test81920_block_6)
  (interval_append test81920 112 128 160
  test81920_block_7
  (interval_append test81920 128 144 160
  test81920_block_8
  test81920_block_9))))
  (interval_append test81920 160 240 320
  (interval_append test81920 160 192 240
  (interval_append test81920 160 176 192
  test81920_block_10
  test81920_block_11)
  (interval_append test81920 192 208 240
  test81920_block_12
  (interval_append test81920 208 224 240
  test81920_block_13
  test81920_block_14)))
  (interval_append test81920 240 272 320
  (interval_append test81920 240 256 272
  test81920_block_15
  test81920_block_16)
  (interval_append test81920 272 288 320
  test81920_block_17
  (interval_append test81920 288 304 320
  test81920_block_18
  test81920_block_19)))))
  (interval_append test81920 320 480 640
  (interval_append test81920 320 400 480
  (interval_append test81920 320 352 400
  (interval_append test81920 320 336 352
  test81920_block_20
  test81920_block_21)
  (interval_append test81920 352 368 400
  test81920_block_22
  (interval_append test81920 368 384 400
  test81920_block_23
  test81920_block_24)))
  (interval_append test81920 400 432 480
  (interval_append test81920 400 416 432
  test81920_block_25
  test81920_block_26)
  (interval_append test81920 432 448 480
  test81920_block_27
  (interval_append test81920 448 464 480
  test81920_block_28
  test81920_block_29))))
  (interval_append test81920 480 560 640
  (interval_append test81920 480 512 560
  (interval_append test81920 480 496 512
  test81920_block_30
  test81920_block_31)
  (interval_append test81920 512 528 560
  test81920_block_32
  (interval_append test81920 528 544 560
  test81920_block_33
  test81920_block_34)))
  (interval_append test81920 560 592 640
  (interval_append test81920 560 576 592
  test81920_block_35
  test81920_block_36)
  (interval_append test81920 592 608 640
  test81920_block_37
  (interval_append test81920 608 624 640
  test81920_block_38
  test81920_block_39))))))
cert_nodeInterval_3 81920 82560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
