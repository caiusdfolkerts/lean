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
cert_test_11 76800
cert_test_block_3 76800 0 0 16 16
cert_test_block_3 76800 1 16 32 16
cert_test_block_3 76800 2 32 48 16
cert_test_block_3 76800 3 48 64 16
cert_test_block_3 76800 4 64 80 16
cert_test_block_3 76800 5 80 96 16
cert_test_block_3 76800 6 96 112 16
cert_test_block_3 76800 7 112 128 16
cert_test_block_3 76800 8 128 144 16
cert_test_block_3 76800 9 144 160 16
cert_test_block_3 76800 10 160 176 16
cert_test_block_3 76800 11 176 192 16
cert_test_block_3 76800 12 192 208 16
cert_test_block_3 76800 13 208 224 16
cert_test_block_3 76800 14 224 240 16
cert_test_block_3 76800 15 240 256 16
cert_test_block_3 76800 16 256 272 16
cert_test_block_3 76800 17 272 288 16
cert_test_block_3 76800 18 288 304 16
cert_test_block_3 76800 19 304 320 16
cert_test_block_3 76800 20 320 336 16
cert_test_block_3 76800 21 336 352 16
cert_test_block_3 76800 22 352 368 16
cert_test_block_3 76800 23 368 384 16
cert_test_block_3 76800 24 384 400 16
cert_test_block_3 76800 25 400 416 16
cert_test_block_3 76800 26 416 432 16
cert_test_block_3 76800 27 432 448 16
cert_test_block_3 76800 28 448 464 16
cert_test_block_3 76800 29 464 480 16
cert_test_block_3 76800 30 480 496 16
cert_test_block_3 76800 31 496 512 16
cert_test_block_3 76800 32 512 528 16
cert_test_block_3 76800 33 528 544 16
cert_test_block_3 76800 34 544 560 16
cert_test_block_3 76800 35 560 576 16
cert_test_block_3 76800 36 576 592 16
cert_test_block_3 76800 37 592 608 16
cert_test_block_3 76800 38 608 624 16
cert_test_block_3 76800 39 624 640 16
theorem test76800_complete : Interval test76800 0 640 :=
  (interval_append test76800 0 320 640
  (interval_append test76800 0 160 320
  (interval_append test76800 0 80 160
  (interval_append test76800 0 32 80
  (interval_append test76800 0 16 32
  test76800_block_0
  test76800_block_1)
  (interval_append test76800 32 48 80
  test76800_block_2
  (interval_append test76800 48 64 80
  test76800_block_3
  test76800_block_4)))
  (interval_append test76800 80 112 160
  (interval_append test76800 80 96 112
  test76800_block_5
  test76800_block_6)
  (interval_append test76800 112 128 160
  test76800_block_7
  (interval_append test76800 128 144 160
  test76800_block_8
  test76800_block_9))))
  (interval_append test76800 160 240 320
  (interval_append test76800 160 192 240
  (interval_append test76800 160 176 192
  test76800_block_10
  test76800_block_11)
  (interval_append test76800 192 208 240
  test76800_block_12
  (interval_append test76800 208 224 240
  test76800_block_13
  test76800_block_14)))
  (interval_append test76800 240 272 320
  (interval_append test76800 240 256 272
  test76800_block_15
  test76800_block_16)
  (interval_append test76800 272 288 320
  test76800_block_17
  (interval_append test76800 288 304 320
  test76800_block_18
  test76800_block_19)))))
  (interval_append test76800 320 480 640
  (interval_append test76800 320 400 480
  (interval_append test76800 320 352 400
  (interval_append test76800 320 336 352
  test76800_block_20
  test76800_block_21)
  (interval_append test76800 352 368 400
  test76800_block_22
  (interval_append test76800 368 384 400
  test76800_block_23
  test76800_block_24)))
  (interval_append test76800 400 432 480
  (interval_append test76800 400 416 432
  test76800_block_25
  test76800_block_26)
  (interval_append test76800 432 448 480
  test76800_block_27
  (interval_append test76800 448 464 480
  test76800_block_28
  test76800_block_29))))
  (interval_append test76800 480 560 640
  (interval_append test76800 480 512 560
  (interval_append test76800 480 496 512
  test76800_block_30
  test76800_block_31)
  (interval_append test76800 512 528 560
  test76800_block_32
  (interval_append test76800 528 544 560
  test76800_block_33
  test76800_block_34)))
  (interval_append test76800 560 592 640
  (interval_append test76800 560 576 592
  test76800_block_35
  test76800_block_36)
  (interval_append test76800 592 608 640
  test76800_block_37
  (interval_append test76800 608 624 640
  test76800_block_38
  test76800_block_39))))))
cert_nodeInterval_3 76800 77440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
