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
cert_test_11 137600
cert_test_block_3 137600 0 0 16 16
cert_test_block_3 137600 1 16 32 16
cert_test_block_3 137600 2 32 48 16
cert_test_block_3 137600 3 48 64 16
cert_test_block_3 137600 4 64 80 16
cert_test_block_3 137600 5 80 96 16
cert_test_block_3 137600 6 96 112 16
cert_test_block_3 137600 7 112 128 16
cert_test_block_3 137600 8 128 144 16
cert_test_block_3 137600 9 144 160 16
cert_test_block_3 137600 10 160 176 16
cert_test_block_3 137600 11 176 192 16
cert_test_block_3 137600 12 192 208 16
cert_test_block_3 137600 13 208 224 16
cert_test_block_3 137600 14 224 240 16
cert_test_block_3 137600 15 240 256 16
cert_test_block_3 137600 16 256 272 16
cert_test_block_3 137600 17 272 288 16
cert_test_block_3 137600 18 288 304 16
cert_test_block_3 137600 19 304 320 16
cert_test_block_3 137600 20 320 336 16
cert_test_block_3 137600 21 336 352 16
cert_test_block_3 137600 22 352 368 16
cert_test_block_3 137600 23 368 384 16
cert_test_block_3 137600 24 384 400 16
cert_test_block_3 137600 25 400 416 16
cert_test_block_3 137600 26 416 432 16
cert_test_block_3 137600 27 432 448 16
cert_test_block_3 137600 28 448 464 16
cert_test_block_3 137600 29 464 480 16
cert_test_block_3 137600 30 480 496 16
cert_test_block_3 137600 31 496 512 16
cert_test_block_3 137600 32 512 528 16
cert_test_block_3 137600 33 528 544 16
cert_test_block_3 137600 34 544 560 16
cert_test_block_3 137600 35 560 576 16
cert_test_block_3 137600 36 576 592 16
cert_test_block_3 137600 37 592 608 16
cert_test_block_3 137600 38 608 624 16
cert_test_block_3 137600 39 624 640 16
theorem test137600_complete : Interval test137600 0 640 :=
  (interval_append test137600 0 320 640
  (interval_append test137600 0 160 320
  (interval_append test137600 0 80 160
  (interval_append test137600 0 32 80
  (interval_append test137600 0 16 32
  test137600_block_0
  test137600_block_1)
  (interval_append test137600 32 48 80
  test137600_block_2
  (interval_append test137600 48 64 80
  test137600_block_3
  test137600_block_4)))
  (interval_append test137600 80 112 160
  (interval_append test137600 80 96 112
  test137600_block_5
  test137600_block_6)
  (interval_append test137600 112 128 160
  test137600_block_7
  (interval_append test137600 128 144 160
  test137600_block_8
  test137600_block_9))))
  (interval_append test137600 160 240 320
  (interval_append test137600 160 192 240
  (interval_append test137600 160 176 192
  test137600_block_10
  test137600_block_11)
  (interval_append test137600 192 208 240
  test137600_block_12
  (interval_append test137600 208 224 240
  test137600_block_13
  test137600_block_14)))
  (interval_append test137600 240 272 320
  (interval_append test137600 240 256 272
  test137600_block_15
  test137600_block_16)
  (interval_append test137600 272 288 320
  test137600_block_17
  (interval_append test137600 288 304 320
  test137600_block_18
  test137600_block_19)))))
  (interval_append test137600 320 480 640
  (interval_append test137600 320 400 480
  (interval_append test137600 320 352 400
  (interval_append test137600 320 336 352
  test137600_block_20
  test137600_block_21)
  (interval_append test137600 352 368 400
  test137600_block_22
  (interval_append test137600 368 384 400
  test137600_block_23
  test137600_block_24)))
  (interval_append test137600 400 432 480
  (interval_append test137600 400 416 432
  test137600_block_25
  test137600_block_26)
  (interval_append test137600 432 448 480
  test137600_block_27
  (interval_append test137600 448 464 480
  test137600_block_28
  test137600_block_29))))
  (interval_append test137600 480 560 640
  (interval_append test137600 480 512 560
  (interval_append test137600 480 496 512
  test137600_block_30
  test137600_block_31)
  (interval_append test137600 512 528 560
  test137600_block_32
  (interval_append test137600 528 544 560
  test137600_block_33
  test137600_block_34)))
  (interval_append test137600 560 592 640
  (interval_append test137600 560 576 592
  test137600_block_35
  test137600_block_36)
  (interval_append test137600 592 608 640
  test137600_block_37
  (interval_append test137600 608 624 640
  test137600_block_38
  test137600_block_39))))))
cert_nodeInterval_3 137600 138240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
