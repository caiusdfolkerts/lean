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
cert_test_11 71040
cert_test_block_3 71040 0 0 16 16
cert_test_block_3 71040 1 16 32 16
cert_test_block_3 71040 2 32 48 16
cert_test_block_3 71040 3 48 64 16
cert_test_block_3 71040 4 64 80 16
cert_test_block_3 71040 5 80 96 16
cert_test_block_3 71040 6 96 112 16
cert_test_block_3 71040 7 112 128 16
cert_test_block_3 71040 8 128 144 16
cert_test_block_3 71040 9 144 160 16
cert_test_block_3 71040 10 160 176 16
cert_test_block_3 71040 11 176 192 16
cert_test_block_3 71040 12 192 208 16
cert_test_block_3 71040 13 208 224 16
cert_test_block_3 71040 14 224 240 16
cert_test_block_3 71040 15 240 256 16
cert_test_block_3 71040 16 256 272 16
cert_test_block_3 71040 17 272 288 16
cert_test_block_3 71040 18 288 304 16
cert_test_block_3 71040 19 304 320 16
cert_test_block_3 71040 20 320 336 16
cert_test_block_3 71040 21 336 352 16
cert_test_block_3 71040 22 352 368 16
cert_test_block_3 71040 23 368 384 16
cert_test_block_3 71040 24 384 400 16
cert_test_block_3 71040 25 400 416 16
cert_test_block_3 71040 26 416 432 16
cert_test_block_3 71040 27 432 448 16
cert_test_block_3 71040 28 448 464 16
cert_test_block_3 71040 29 464 480 16
cert_test_block_3 71040 30 480 496 16
cert_test_block_3 71040 31 496 512 16
cert_test_block_3 71040 32 512 528 16
cert_test_block_3 71040 33 528 544 16
cert_test_block_3 71040 34 544 560 16
cert_test_block_3 71040 35 560 576 16
cert_test_block_3 71040 36 576 592 16
cert_test_block_3 71040 37 592 608 16
cert_test_block_3 71040 38 608 624 16
cert_test_block_3 71040 39 624 640 16
theorem test71040_complete : Interval test71040 0 640 :=
  (interval_append test71040 0 320 640
  (interval_append test71040 0 160 320
  (interval_append test71040 0 80 160
  (interval_append test71040 0 32 80
  (interval_append test71040 0 16 32
  test71040_block_0
  test71040_block_1)
  (interval_append test71040 32 48 80
  test71040_block_2
  (interval_append test71040 48 64 80
  test71040_block_3
  test71040_block_4)))
  (interval_append test71040 80 112 160
  (interval_append test71040 80 96 112
  test71040_block_5
  test71040_block_6)
  (interval_append test71040 112 128 160
  test71040_block_7
  (interval_append test71040 128 144 160
  test71040_block_8
  test71040_block_9))))
  (interval_append test71040 160 240 320
  (interval_append test71040 160 192 240
  (interval_append test71040 160 176 192
  test71040_block_10
  test71040_block_11)
  (interval_append test71040 192 208 240
  test71040_block_12
  (interval_append test71040 208 224 240
  test71040_block_13
  test71040_block_14)))
  (interval_append test71040 240 272 320
  (interval_append test71040 240 256 272
  test71040_block_15
  test71040_block_16)
  (interval_append test71040 272 288 320
  test71040_block_17
  (interval_append test71040 288 304 320
  test71040_block_18
  test71040_block_19)))))
  (interval_append test71040 320 480 640
  (interval_append test71040 320 400 480
  (interval_append test71040 320 352 400
  (interval_append test71040 320 336 352
  test71040_block_20
  test71040_block_21)
  (interval_append test71040 352 368 400
  test71040_block_22
  (interval_append test71040 368 384 400
  test71040_block_23
  test71040_block_24)))
  (interval_append test71040 400 432 480
  (interval_append test71040 400 416 432
  test71040_block_25
  test71040_block_26)
  (interval_append test71040 432 448 480
  test71040_block_27
  (interval_append test71040 448 464 480
  test71040_block_28
  test71040_block_29))))
  (interval_append test71040 480 560 640
  (interval_append test71040 480 512 560
  (interval_append test71040 480 496 512
  test71040_block_30
  test71040_block_31)
  (interval_append test71040 512 528 560
  test71040_block_32
  (interval_append test71040 528 544 560
  test71040_block_33
  test71040_block_34)))
  (interval_append test71040 560 592 640
  (interval_append test71040 560 576 592
  test71040_block_35
  test71040_block_36)
  (interval_append test71040 592 608 640
  test71040_block_37
  (interval_append test71040 608 624 640
  test71040_block_38
  test71040_block_39))))))
cert_nodeInterval_3 71040 71680
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
