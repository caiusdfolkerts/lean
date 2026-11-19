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
cert_test_11 112000
cert_test_block_3 112000 0 0 16 16
cert_test_block_3 112000 1 16 32 16
cert_test_block_3 112000 2 32 48 16
cert_test_block_3 112000 3 48 64 16
cert_test_block_3 112000 4 64 80 16
cert_test_block_3 112000 5 80 96 16
cert_test_block_3 112000 6 96 112 16
cert_test_block_3 112000 7 112 128 16
cert_test_block_3 112000 8 128 144 16
cert_test_block_3 112000 9 144 160 16
cert_test_block_3 112000 10 160 176 16
cert_test_block_3 112000 11 176 192 16
cert_test_block_3 112000 12 192 208 16
cert_test_block_3 112000 13 208 224 16
cert_test_block_3 112000 14 224 240 16
cert_test_block_3 112000 15 240 256 16
cert_test_block_3 112000 16 256 272 16
cert_test_block_3 112000 17 272 288 16
cert_test_block_3 112000 18 288 304 16
cert_test_block_3 112000 19 304 320 16
cert_test_block_3 112000 20 320 336 16
cert_test_block_3 112000 21 336 352 16
cert_test_block_3 112000 22 352 368 16
cert_test_block_3 112000 23 368 384 16
cert_test_block_3 112000 24 384 400 16
cert_test_block_3 112000 25 400 416 16
cert_test_block_3 112000 26 416 432 16
cert_test_block_3 112000 27 432 448 16
cert_test_block_3 112000 28 448 464 16
cert_test_block_3 112000 29 464 480 16
cert_test_block_3 112000 30 480 496 16
cert_test_block_3 112000 31 496 512 16
cert_test_block_3 112000 32 512 528 16
cert_test_block_3 112000 33 528 544 16
cert_test_block_3 112000 34 544 560 16
cert_test_block_3 112000 35 560 576 16
cert_test_block_3 112000 36 576 592 16
cert_test_block_3 112000 37 592 608 16
cert_test_block_3 112000 38 608 624 16
cert_test_block_3 112000 39 624 640 16
theorem test112000_complete : Interval test112000 0 640 :=
  (interval_append test112000 0 320 640
  (interval_append test112000 0 160 320
  (interval_append test112000 0 80 160
  (interval_append test112000 0 32 80
  (interval_append test112000 0 16 32
  test112000_block_0
  test112000_block_1)
  (interval_append test112000 32 48 80
  test112000_block_2
  (interval_append test112000 48 64 80
  test112000_block_3
  test112000_block_4)))
  (interval_append test112000 80 112 160
  (interval_append test112000 80 96 112
  test112000_block_5
  test112000_block_6)
  (interval_append test112000 112 128 160
  test112000_block_7
  (interval_append test112000 128 144 160
  test112000_block_8
  test112000_block_9))))
  (interval_append test112000 160 240 320
  (interval_append test112000 160 192 240
  (interval_append test112000 160 176 192
  test112000_block_10
  test112000_block_11)
  (interval_append test112000 192 208 240
  test112000_block_12
  (interval_append test112000 208 224 240
  test112000_block_13
  test112000_block_14)))
  (interval_append test112000 240 272 320
  (interval_append test112000 240 256 272
  test112000_block_15
  test112000_block_16)
  (interval_append test112000 272 288 320
  test112000_block_17
  (interval_append test112000 288 304 320
  test112000_block_18
  test112000_block_19)))))
  (interval_append test112000 320 480 640
  (interval_append test112000 320 400 480
  (interval_append test112000 320 352 400
  (interval_append test112000 320 336 352
  test112000_block_20
  test112000_block_21)
  (interval_append test112000 352 368 400
  test112000_block_22
  (interval_append test112000 368 384 400
  test112000_block_23
  test112000_block_24)))
  (interval_append test112000 400 432 480
  (interval_append test112000 400 416 432
  test112000_block_25
  test112000_block_26)
  (interval_append test112000 432 448 480
  test112000_block_27
  (interval_append test112000 448 464 480
  test112000_block_28
  test112000_block_29))))
  (interval_append test112000 480 560 640
  (interval_append test112000 480 512 560
  (interval_append test112000 480 496 512
  test112000_block_30
  test112000_block_31)
  (interval_append test112000 512 528 560
  test112000_block_32
  (interval_append test112000 528 544 560
  test112000_block_33
  test112000_block_34)))
  (interval_append test112000 560 592 640
  (interval_append test112000 560 576 592
  test112000_block_35
  test112000_block_36)
  (interval_append test112000 592 608 640
  test112000_block_37
  (interval_append test112000 608 624 640
  test112000_block_38
  test112000_block_39))))))
cert_nodeInterval_3 112000 112640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
