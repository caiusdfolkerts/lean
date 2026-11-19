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
cert_test_11 139520
cert_test_block_3 139520 0 0 16 16
cert_test_block_3 139520 1 16 32 16
cert_test_block_3 139520 2 32 48 16
cert_test_block_3 139520 3 48 64 16
cert_test_block_3 139520 4 64 80 16
cert_test_block_3 139520 5 80 96 16
cert_test_block_3 139520 6 96 112 16
cert_test_block_3 139520 7 112 128 16
cert_test_block_3 139520 8 128 144 16
cert_test_block_3 139520 9 144 160 16
cert_test_block_3 139520 10 160 176 16
cert_test_block_3 139520 11 176 192 16
cert_test_block_3 139520 12 192 208 16
cert_test_block_3 139520 13 208 224 16
cert_test_block_3 139520 14 224 240 16
cert_test_block_3 139520 15 240 256 16
cert_test_block_3 139520 16 256 272 16
cert_test_block_3 139520 17 272 288 16
cert_test_block_3 139520 18 288 304 16
cert_test_block_3 139520 19 304 320 16
cert_test_block_3 139520 20 320 336 16
cert_test_block_3 139520 21 336 352 16
cert_test_block_3 139520 22 352 368 16
cert_test_block_3 139520 23 368 384 16
cert_test_block_3 139520 24 384 400 16
cert_test_block_3 139520 25 400 416 16
cert_test_block_3 139520 26 416 432 16
cert_test_block_3 139520 27 432 448 16
cert_test_block_3 139520 28 448 464 16
cert_test_block_3 139520 29 464 480 16
cert_test_block_3 139520 30 480 496 16
cert_test_block_3 139520 31 496 512 16
cert_test_block_3 139520 32 512 528 16
cert_test_block_3 139520 33 528 544 16
cert_test_block_3 139520 34 544 560 16
cert_test_block_3 139520 35 560 576 16
cert_test_block_3 139520 36 576 592 16
cert_test_block_3 139520 37 592 608 16
cert_test_block_3 139520 38 608 624 16
cert_test_block_3 139520 39 624 640 16
theorem test139520_complete : Interval test139520 0 640 :=
  (interval_append test139520 0 320 640
  (interval_append test139520 0 160 320
  (interval_append test139520 0 80 160
  (interval_append test139520 0 32 80
  (interval_append test139520 0 16 32
  test139520_block_0
  test139520_block_1)
  (interval_append test139520 32 48 80
  test139520_block_2
  (interval_append test139520 48 64 80
  test139520_block_3
  test139520_block_4)))
  (interval_append test139520 80 112 160
  (interval_append test139520 80 96 112
  test139520_block_5
  test139520_block_6)
  (interval_append test139520 112 128 160
  test139520_block_7
  (interval_append test139520 128 144 160
  test139520_block_8
  test139520_block_9))))
  (interval_append test139520 160 240 320
  (interval_append test139520 160 192 240
  (interval_append test139520 160 176 192
  test139520_block_10
  test139520_block_11)
  (interval_append test139520 192 208 240
  test139520_block_12
  (interval_append test139520 208 224 240
  test139520_block_13
  test139520_block_14)))
  (interval_append test139520 240 272 320
  (interval_append test139520 240 256 272
  test139520_block_15
  test139520_block_16)
  (interval_append test139520 272 288 320
  test139520_block_17
  (interval_append test139520 288 304 320
  test139520_block_18
  test139520_block_19)))))
  (interval_append test139520 320 480 640
  (interval_append test139520 320 400 480
  (interval_append test139520 320 352 400
  (interval_append test139520 320 336 352
  test139520_block_20
  test139520_block_21)
  (interval_append test139520 352 368 400
  test139520_block_22
  (interval_append test139520 368 384 400
  test139520_block_23
  test139520_block_24)))
  (interval_append test139520 400 432 480
  (interval_append test139520 400 416 432
  test139520_block_25
  test139520_block_26)
  (interval_append test139520 432 448 480
  test139520_block_27
  (interval_append test139520 448 464 480
  test139520_block_28
  test139520_block_29))))
  (interval_append test139520 480 560 640
  (interval_append test139520 480 512 560
  (interval_append test139520 480 496 512
  test139520_block_30
  test139520_block_31)
  (interval_append test139520 512 528 560
  test139520_block_32
  (interval_append test139520 528 544 560
  test139520_block_33
  test139520_block_34)))
  (interval_append test139520 560 592 640
  (interval_append test139520 560 576 592
  test139520_block_35
  test139520_block_36)
  (interval_append test139520 592 608 640
  test139520_block_37
  (interval_append test139520 608 624 640
  test139520_block_38
  test139520_block_39))))))
cert_nodeInterval_3 139520 140160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
