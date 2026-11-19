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
cert_test_11 85760
cert_test_block_3 85760 0 0 16 16
cert_test_block_3 85760 1 16 32 16
cert_test_block_3 85760 2 32 48 16
cert_test_block_3 85760 3 48 64 16
cert_test_block_3 85760 4 64 80 16
cert_test_block_3 85760 5 80 96 16
cert_test_block_3 85760 6 96 112 16
cert_test_block_3 85760 7 112 128 16
cert_test_block_3 85760 8 128 144 16
cert_test_block_3 85760 9 144 160 16
cert_test_block_3 85760 10 160 176 16
cert_test_block_3 85760 11 176 192 16
cert_test_block_3 85760 12 192 208 16
cert_test_block_3 85760 13 208 224 16
cert_test_block_3 85760 14 224 240 16
cert_test_block_3 85760 15 240 256 16
cert_test_block_3 85760 16 256 272 16
cert_test_block_3 85760 17 272 288 16
cert_test_block_3 85760 18 288 304 16
cert_test_block_3 85760 19 304 320 16
cert_test_block_3 85760 20 320 336 16
cert_test_block_3 85760 21 336 352 16
cert_test_block_3 85760 22 352 368 16
cert_test_block_3 85760 23 368 384 16
cert_test_block_3 85760 24 384 400 16
cert_test_block_3 85760 25 400 416 16
cert_test_block_3 85760 26 416 432 16
cert_test_block_3 85760 27 432 448 16
cert_test_block_3 85760 28 448 464 16
cert_test_block_3 85760 29 464 480 16
cert_test_block_3 85760 30 480 496 16
cert_test_block_3 85760 31 496 512 16
cert_test_block_3 85760 32 512 528 16
cert_test_block_3 85760 33 528 544 16
cert_test_block_3 85760 34 544 560 16
cert_test_block_3 85760 35 560 576 16
cert_test_block_3 85760 36 576 592 16
cert_test_block_3 85760 37 592 608 16
cert_test_block_3 85760 38 608 624 16
cert_test_block_3 85760 39 624 640 16
theorem test85760_complete : Interval test85760 0 640 :=
  (interval_append test85760 0 320 640
  (interval_append test85760 0 160 320
  (interval_append test85760 0 80 160
  (interval_append test85760 0 32 80
  (interval_append test85760 0 16 32
  test85760_block_0
  test85760_block_1)
  (interval_append test85760 32 48 80
  test85760_block_2
  (interval_append test85760 48 64 80
  test85760_block_3
  test85760_block_4)))
  (interval_append test85760 80 112 160
  (interval_append test85760 80 96 112
  test85760_block_5
  test85760_block_6)
  (interval_append test85760 112 128 160
  test85760_block_7
  (interval_append test85760 128 144 160
  test85760_block_8
  test85760_block_9))))
  (interval_append test85760 160 240 320
  (interval_append test85760 160 192 240
  (interval_append test85760 160 176 192
  test85760_block_10
  test85760_block_11)
  (interval_append test85760 192 208 240
  test85760_block_12
  (interval_append test85760 208 224 240
  test85760_block_13
  test85760_block_14)))
  (interval_append test85760 240 272 320
  (interval_append test85760 240 256 272
  test85760_block_15
  test85760_block_16)
  (interval_append test85760 272 288 320
  test85760_block_17
  (interval_append test85760 288 304 320
  test85760_block_18
  test85760_block_19)))))
  (interval_append test85760 320 480 640
  (interval_append test85760 320 400 480
  (interval_append test85760 320 352 400
  (interval_append test85760 320 336 352
  test85760_block_20
  test85760_block_21)
  (interval_append test85760 352 368 400
  test85760_block_22
  (interval_append test85760 368 384 400
  test85760_block_23
  test85760_block_24)))
  (interval_append test85760 400 432 480
  (interval_append test85760 400 416 432
  test85760_block_25
  test85760_block_26)
  (interval_append test85760 432 448 480
  test85760_block_27
  (interval_append test85760 448 464 480
  test85760_block_28
  test85760_block_29))))
  (interval_append test85760 480 560 640
  (interval_append test85760 480 512 560
  (interval_append test85760 480 496 512
  test85760_block_30
  test85760_block_31)
  (interval_append test85760 512 528 560
  test85760_block_32
  (interval_append test85760 528 544 560
  test85760_block_33
  test85760_block_34)))
  (interval_append test85760 560 592 640
  (interval_append test85760 560 576 592
  test85760_block_35
  test85760_block_36)
  (interval_append test85760 592 608 640
  test85760_block_37
  (interval_append test85760 608 624 640
  test85760_block_38
  test85760_block_39))))))
cert_nodeInterval_3 85760 86400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
