module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 18560
cert_test_block_3 18560 0 0 16 16
cert_test_block_3 18560 1 16 32 16
cert_test_block_3 18560 2 32 48 16
cert_test_block_3 18560 3 48 64 16
cert_test_block_3 18560 4 64 80 16
cert_test_block_3 18560 5 80 96 16
cert_test_block_3 18560 6 96 112 16
cert_test_block_3 18560 7 112 128 16
cert_test_block_3 18560 8 128 144 16
cert_test_block_3 18560 9 144 160 16
cert_test_block_3 18560 10 160 176 16
cert_test_block_3 18560 11 176 192 16
cert_test_block_3 18560 12 192 208 16
cert_test_block_3 18560 13 208 224 16
cert_test_block_3 18560 14 224 240 16
cert_test_block_3 18560 15 240 256 16
cert_test_block_3 18560 16 256 272 16
cert_test_block_3 18560 17 272 288 16
cert_test_block_3 18560 18 288 304 16
cert_test_block_3 18560 19 304 320 16
cert_test_block_3 18560 20 320 336 16
cert_test_block_3 18560 21 336 352 16
cert_test_block_3 18560 22 352 368 16
cert_test_block_3 18560 23 368 384 16
cert_test_block_3 18560 24 384 400 16
cert_test_block_3 18560 25 400 416 16
cert_test_block_3 18560 26 416 432 16
cert_test_block_3 18560 27 432 448 16
cert_test_block_3 18560 28 448 464 16
cert_test_block_3 18560 29 464 480 16
cert_test_block_3 18560 30 480 496 16
cert_test_block_3 18560 31 496 512 16
cert_test_block_3 18560 32 512 528 16
cert_test_block_3 18560 33 528 544 16
cert_test_block_3 18560 34 544 560 16
cert_test_block_3 18560 35 560 576 16
cert_test_block_3 18560 36 576 592 16
cert_test_block_3 18560 37 592 608 16
cert_test_block_3 18560 38 608 624 16
cert_test_block_3 18560 39 624 640 16
theorem test18560_complete : Interval test18560 0 640 :=
  (interval_append test18560 0 320 640
  (interval_append test18560 0 160 320
  (interval_append test18560 0 80 160
  (interval_append test18560 0 32 80
  (interval_append test18560 0 16 32
  test18560_block_0
  test18560_block_1)
  (interval_append test18560 32 48 80
  test18560_block_2
  (interval_append test18560 48 64 80
  test18560_block_3
  test18560_block_4)))
  (interval_append test18560 80 112 160
  (interval_append test18560 80 96 112
  test18560_block_5
  test18560_block_6)
  (interval_append test18560 112 128 160
  test18560_block_7
  (interval_append test18560 128 144 160
  test18560_block_8
  test18560_block_9))))
  (interval_append test18560 160 240 320
  (interval_append test18560 160 192 240
  (interval_append test18560 160 176 192
  test18560_block_10
  test18560_block_11)
  (interval_append test18560 192 208 240
  test18560_block_12
  (interval_append test18560 208 224 240
  test18560_block_13
  test18560_block_14)))
  (interval_append test18560 240 272 320
  (interval_append test18560 240 256 272
  test18560_block_15
  test18560_block_16)
  (interval_append test18560 272 288 320
  test18560_block_17
  (interval_append test18560 288 304 320
  test18560_block_18
  test18560_block_19)))))
  (interval_append test18560 320 480 640
  (interval_append test18560 320 400 480
  (interval_append test18560 320 352 400
  (interval_append test18560 320 336 352
  test18560_block_20
  test18560_block_21)
  (interval_append test18560 352 368 400
  test18560_block_22
  (interval_append test18560 368 384 400
  test18560_block_23
  test18560_block_24)))
  (interval_append test18560 400 432 480
  (interval_append test18560 400 416 432
  test18560_block_25
  test18560_block_26)
  (interval_append test18560 432 448 480
  test18560_block_27
  (interval_append test18560 448 464 480
  test18560_block_28
  test18560_block_29))))
  (interval_append test18560 480 560 640
  (interval_append test18560 480 512 560
  (interval_append test18560 480 496 512
  test18560_block_30
  test18560_block_31)
  (interval_append test18560 512 528 560
  test18560_block_32
  (interval_append test18560 528 544 560
  test18560_block_33
  test18560_block_34)))
  (interval_append test18560 560 592 640
  (interval_append test18560 560 576 592
  test18560_block_35
  test18560_block_36)
  (interval_append test18560 592 608 640
  test18560_block_37
  (interval_append test18560 608 624 640
  test18560_block_38
  test18560_block_39))))))
cert_nodeInterval_3 18560 19200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
