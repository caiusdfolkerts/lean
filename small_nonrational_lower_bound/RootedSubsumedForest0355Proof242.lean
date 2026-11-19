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
cert_test_11 154880
cert_test_block_3 154880 0 0 16 16
cert_test_block_3 154880 1 16 32 16
cert_test_block_3 154880 2 32 48 16
cert_test_block_3 154880 3 48 64 16
cert_test_block_3 154880 4 64 80 16
cert_test_block_3 154880 5 80 96 16
cert_test_block_3 154880 6 96 112 16
cert_test_block_3 154880 7 112 128 16
cert_test_block_3 154880 8 128 144 16
cert_test_block_3 154880 9 144 160 16
cert_test_block_3 154880 10 160 176 16
cert_test_block_3 154880 11 176 192 16
cert_test_block_3 154880 12 192 208 16
cert_test_block_3 154880 13 208 224 16
cert_test_block_3 154880 14 224 240 16
cert_test_block_3 154880 15 240 256 16
cert_test_block_3 154880 16 256 272 16
cert_test_block_3 154880 17 272 288 16
cert_test_block_3 154880 18 288 304 16
cert_test_block_3 154880 19 304 320 16
cert_test_block_3 154880 20 320 336 16
cert_test_block_3 154880 21 336 352 16
cert_test_block_3 154880 22 352 368 16
cert_test_block_3 154880 23 368 384 16
cert_test_block_3 154880 24 384 400 16
cert_test_block_3 154880 25 400 416 16
cert_test_block_3 154880 26 416 432 16
cert_test_block_3 154880 27 432 448 16
cert_test_block_3 154880 28 448 464 16
cert_test_block_3 154880 29 464 480 16
cert_test_block_3 154880 30 480 496 16
cert_test_block_3 154880 31 496 512 16
cert_test_block_3 154880 32 512 528 16
cert_test_block_3 154880 33 528 544 16
cert_test_block_3 154880 34 544 560 16
cert_test_block_3 154880 35 560 576 16
cert_test_block_3 154880 36 576 592 16
cert_test_block_3 154880 37 592 608 16
cert_test_block_3 154880 38 608 624 16
cert_test_block_3 154880 39 624 640 16
theorem test154880_complete : Interval test154880 0 640 :=
  (interval_append test154880 0 320 640
  (interval_append test154880 0 160 320
  (interval_append test154880 0 80 160
  (interval_append test154880 0 32 80
  (interval_append test154880 0 16 32
  test154880_block_0
  test154880_block_1)
  (interval_append test154880 32 48 80
  test154880_block_2
  (interval_append test154880 48 64 80
  test154880_block_3
  test154880_block_4)))
  (interval_append test154880 80 112 160
  (interval_append test154880 80 96 112
  test154880_block_5
  test154880_block_6)
  (interval_append test154880 112 128 160
  test154880_block_7
  (interval_append test154880 128 144 160
  test154880_block_8
  test154880_block_9))))
  (interval_append test154880 160 240 320
  (interval_append test154880 160 192 240
  (interval_append test154880 160 176 192
  test154880_block_10
  test154880_block_11)
  (interval_append test154880 192 208 240
  test154880_block_12
  (interval_append test154880 208 224 240
  test154880_block_13
  test154880_block_14)))
  (interval_append test154880 240 272 320
  (interval_append test154880 240 256 272
  test154880_block_15
  test154880_block_16)
  (interval_append test154880 272 288 320
  test154880_block_17
  (interval_append test154880 288 304 320
  test154880_block_18
  test154880_block_19)))))
  (interval_append test154880 320 480 640
  (interval_append test154880 320 400 480
  (interval_append test154880 320 352 400
  (interval_append test154880 320 336 352
  test154880_block_20
  test154880_block_21)
  (interval_append test154880 352 368 400
  test154880_block_22
  (interval_append test154880 368 384 400
  test154880_block_23
  test154880_block_24)))
  (interval_append test154880 400 432 480
  (interval_append test154880 400 416 432
  test154880_block_25
  test154880_block_26)
  (interval_append test154880 432 448 480
  test154880_block_27
  (interval_append test154880 448 464 480
  test154880_block_28
  test154880_block_29))))
  (interval_append test154880 480 560 640
  (interval_append test154880 480 512 560
  (interval_append test154880 480 496 512
  test154880_block_30
  test154880_block_31)
  (interval_append test154880 512 528 560
  test154880_block_32
  (interval_append test154880 528 544 560
  test154880_block_33
  test154880_block_34)))
  (interval_append test154880 560 592 640
  (interval_append test154880 560 576 592
  test154880_block_35
  test154880_block_36)
  (interval_append test154880 592 608 640
  test154880_block_37
  (interval_append test154880 608 624 640
  test154880_block_38
  test154880_block_39))))))
cert_nodeInterval_3 154880 155520
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
