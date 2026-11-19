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
cert_test_11 132480
cert_test_block_3 132480 0 0 16 16
cert_test_block_3 132480 1 16 32 16
cert_test_block_3 132480 2 32 48 16
cert_test_block_3 132480 3 48 64 16
cert_test_block_3 132480 4 64 80 16
cert_test_block_3 132480 5 80 96 16
cert_test_block_3 132480 6 96 112 16
cert_test_block_3 132480 7 112 128 16
cert_test_block_3 132480 8 128 144 16
cert_test_block_3 132480 9 144 160 16
cert_test_block_3 132480 10 160 176 16
cert_test_block_3 132480 11 176 192 16
cert_test_block_3 132480 12 192 208 16
cert_test_block_3 132480 13 208 224 16
cert_test_block_3 132480 14 224 240 16
cert_test_block_3 132480 15 240 256 16
cert_test_block_3 132480 16 256 272 16
cert_test_block_3 132480 17 272 288 16
cert_test_block_3 132480 18 288 304 16
cert_test_block_3 132480 19 304 320 16
cert_test_block_3 132480 20 320 336 16
cert_test_block_3 132480 21 336 352 16
cert_test_block_3 132480 22 352 368 16
cert_test_block_3 132480 23 368 384 16
cert_test_block_3 132480 24 384 400 16
cert_test_block_3 132480 25 400 416 16
cert_test_block_3 132480 26 416 432 16
cert_test_block_3 132480 27 432 448 16
cert_test_block_3 132480 28 448 464 16
cert_test_block_3 132480 29 464 480 16
cert_test_block_3 132480 30 480 496 16
cert_test_block_3 132480 31 496 512 16
cert_test_block_3 132480 32 512 528 16
cert_test_block_3 132480 33 528 544 16
cert_test_block_3 132480 34 544 560 16
cert_test_block_3 132480 35 560 576 16
cert_test_block_3 132480 36 576 592 16
cert_test_block_3 132480 37 592 608 16
cert_test_block_3 132480 38 608 624 16
cert_test_block_3 132480 39 624 640 16
theorem test132480_complete : Interval test132480 0 640 :=
  (interval_append test132480 0 320 640
  (interval_append test132480 0 160 320
  (interval_append test132480 0 80 160
  (interval_append test132480 0 32 80
  (interval_append test132480 0 16 32
  test132480_block_0
  test132480_block_1)
  (interval_append test132480 32 48 80
  test132480_block_2
  (interval_append test132480 48 64 80
  test132480_block_3
  test132480_block_4)))
  (interval_append test132480 80 112 160
  (interval_append test132480 80 96 112
  test132480_block_5
  test132480_block_6)
  (interval_append test132480 112 128 160
  test132480_block_7
  (interval_append test132480 128 144 160
  test132480_block_8
  test132480_block_9))))
  (interval_append test132480 160 240 320
  (interval_append test132480 160 192 240
  (interval_append test132480 160 176 192
  test132480_block_10
  test132480_block_11)
  (interval_append test132480 192 208 240
  test132480_block_12
  (interval_append test132480 208 224 240
  test132480_block_13
  test132480_block_14)))
  (interval_append test132480 240 272 320
  (interval_append test132480 240 256 272
  test132480_block_15
  test132480_block_16)
  (interval_append test132480 272 288 320
  test132480_block_17
  (interval_append test132480 288 304 320
  test132480_block_18
  test132480_block_19)))))
  (interval_append test132480 320 480 640
  (interval_append test132480 320 400 480
  (interval_append test132480 320 352 400
  (interval_append test132480 320 336 352
  test132480_block_20
  test132480_block_21)
  (interval_append test132480 352 368 400
  test132480_block_22
  (interval_append test132480 368 384 400
  test132480_block_23
  test132480_block_24)))
  (interval_append test132480 400 432 480
  (interval_append test132480 400 416 432
  test132480_block_25
  test132480_block_26)
  (interval_append test132480 432 448 480
  test132480_block_27
  (interval_append test132480 448 464 480
  test132480_block_28
  test132480_block_29))))
  (interval_append test132480 480 560 640
  (interval_append test132480 480 512 560
  (interval_append test132480 480 496 512
  test132480_block_30
  test132480_block_31)
  (interval_append test132480 512 528 560
  test132480_block_32
  (interval_append test132480 528 544 560
  test132480_block_33
  test132480_block_34)))
  (interval_append test132480 560 592 640
  (interval_append test132480 560 576 592
  test132480_block_35
  test132480_block_36)
  (interval_append test132480 592 608 640
  test132480_block_37
  (interval_append test132480 608 624 640
  test132480_block_38
  test132480_block_39))))))
cert_nodeInterval_3 132480 133120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
