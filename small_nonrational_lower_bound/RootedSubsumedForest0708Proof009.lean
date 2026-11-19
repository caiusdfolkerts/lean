module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5760
cert_test_block_3 5760 0 0 16 16
cert_test_block_3 5760 1 16 32 16
cert_test_block_3 5760 2 32 48 16
cert_test_block_3 5760 3 48 64 16
cert_test_block_3 5760 4 64 80 16
cert_test_block_3 5760 5 80 96 16
cert_test_block_3 5760 6 96 112 16
cert_test_block_3 5760 7 112 128 16
cert_test_block_3 5760 8 128 144 16
cert_test_block_3 5760 9 144 160 16
cert_test_block_3 5760 10 160 176 16
cert_test_block_3 5760 11 176 192 16
cert_test_block_3 5760 12 192 208 16
cert_test_block_3 5760 13 208 224 16
cert_test_block_3 5760 14 224 240 16
cert_test_block_3 5760 15 240 256 16
cert_test_block_3 5760 16 256 272 16
cert_test_block_3 5760 17 272 288 16
cert_test_block_3 5760 18 288 304 16
cert_test_block_3 5760 19 304 320 16
cert_test_block_3 5760 20 320 336 16
cert_test_block_3 5760 21 336 352 16
cert_test_block_3 5760 22 352 368 16
cert_test_block_3 5760 23 368 384 16
cert_test_block_3 5760 24 384 400 16
cert_test_block_3 5760 25 400 416 16
cert_test_block_3 5760 26 416 432 16
cert_test_block_3 5760 27 432 448 16
cert_test_block_3 5760 28 448 464 16
cert_test_block_3 5760 29 464 480 16
cert_test_block_3 5760 30 480 496 16
cert_test_block_3 5760 31 496 512 16
cert_test_block_3 5760 32 512 528 16
cert_test_block_3 5760 33 528 544 16
cert_test_block_3 5760 34 544 560 16
cert_test_block_3 5760 35 560 576 16
cert_test_block_3 5760 36 576 592 16
cert_test_block_3 5760 37 592 608 16
cert_test_block_3 5760 38 608 624 16
cert_test_block_3 5760 39 624 640 16
theorem test5760_complete : Interval test5760 0 640 :=
  (interval_append test5760 0 320 640
  (interval_append test5760 0 160 320
  (interval_append test5760 0 80 160
  (interval_append test5760 0 32 80
  (interval_append test5760 0 16 32
  test5760_block_0
  test5760_block_1)
  (interval_append test5760 32 48 80
  test5760_block_2
  (interval_append test5760 48 64 80
  test5760_block_3
  test5760_block_4)))
  (interval_append test5760 80 112 160
  (interval_append test5760 80 96 112
  test5760_block_5
  test5760_block_6)
  (interval_append test5760 112 128 160
  test5760_block_7
  (interval_append test5760 128 144 160
  test5760_block_8
  test5760_block_9))))
  (interval_append test5760 160 240 320
  (interval_append test5760 160 192 240
  (interval_append test5760 160 176 192
  test5760_block_10
  test5760_block_11)
  (interval_append test5760 192 208 240
  test5760_block_12
  (interval_append test5760 208 224 240
  test5760_block_13
  test5760_block_14)))
  (interval_append test5760 240 272 320
  (interval_append test5760 240 256 272
  test5760_block_15
  test5760_block_16)
  (interval_append test5760 272 288 320
  test5760_block_17
  (interval_append test5760 288 304 320
  test5760_block_18
  test5760_block_19)))))
  (interval_append test5760 320 480 640
  (interval_append test5760 320 400 480
  (interval_append test5760 320 352 400
  (interval_append test5760 320 336 352
  test5760_block_20
  test5760_block_21)
  (interval_append test5760 352 368 400
  test5760_block_22
  (interval_append test5760 368 384 400
  test5760_block_23
  test5760_block_24)))
  (interval_append test5760 400 432 480
  (interval_append test5760 400 416 432
  test5760_block_25
  test5760_block_26)
  (interval_append test5760 432 448 480
  test5760_block_27
  (interval_append test5760 448 464 480
  test5760_block_28
  test5760_block_29))))
  (interval_append test5760 480 560 640
  (interval_append test5760 480 512 560
  (interval_append test5760 480 496 512
  test5760_block_30
  test5760_block_31)
  (interval_append test5760 512 528 560
  test5760_block_32
  (interval_append test5760 528 544 560
  test5760_block_33
  test5760_block_34)))
  (interval_append test5760 560 592 640
  (interval_append test5760 560 576 592
  test5760_block_35
  test5760_block_36)
  (interval_append test5760 592 608 640
  test5760_block_37
  (interval_append test5760 608 624 640
  test5760_block_38
  test5760_block_39))))))
cert_nodeInterval_3 5760 6400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
