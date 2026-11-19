module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 28160
cert_test_block_4 28160 0 0 16 16
cert_test_block_4 28160 1 16 32 16
cert_test_block_4 28160 2 32 48 16
cert_test_block_4 28160 3 48 64 16
cert_test_block_4 28160 4 64 80 16
cert_test_block_4 28160 5 80 96 16
cert_test_block_4 28160 6 96 112 16
cert_test_block_4 28160 7 112 128 16
cert_test_block_4 28160 8 128 144 16
cert_test_block_4 28160 9 144 160 16
cert_test_block_4 28160 10 160 176 16
cert_test_block_4 28160 11 176 192 16
cert_test_block_4 28160 12 192 208 16
cert_test_block_4 28160 13 208 224 16
cert_test_block_4 28160 14 224 240 16
cert_test_block_4 28160 15 240 256 16
cert_test_block_4 28160 16 256 272 16
cert_test_block_4 28160 17 272 288 16
cert_test_block_4 28160 18 288 304 16
cert_test_block_4 28160 19 304 320 16
cert_test_block_4 28160 20 320 336 16
cert_test_block_4 28160 21 336 352 16
cert_test_block_4 28160 22 352 368 16
cert_test_block_4 28160 23 368 384 16
cert_test_block_4 28160 24 384 400 16
cert_test_block_4 28160 25 400 416 16
cert_test_block_4 28160 26 416 432 16
cert_test_block_4 28160 27 432 448 16
cert_test_block_4 28160 28 448 464 16
cert_test_block_4 28160 29 464 480 16
cert_test_block_4 28160 30 480 496 16
cert_test_block_4 28160 31 496 512 16
cert_test_block_4 28160 32 512 528 16
cert_test_block_4 28160 33 528 544 16
cert_test_block_4 28160 34 544 560 16
cert_test_block_4 28160 35 560 576 16
cert_test_block_4 28160 36 576 592 16
cert_test_block_4 28160 37 592 608 16
cert_test_block_4 28160 38 608 624 16
cert_test_block_4 28160 39 624 640 16
theorem test28160_complete : Interval test28160 0 640 :=
  (interval_append test28160 0 320 640
  (interval_append test28160 0 160 320
  (interval_append test28160 0 80 160
  (interval_append test28160 0 32 80
  (interval_append test28160 0 16 32
  test28160_block_0
  test28160_block_1)
  (interval_append test28160 32 48 80
  test28160_block_2
  (interval_append test28160 48 64 80
  test28160_block_3
  test28160_block_4)))
  (interval_append test28160 80 112 160
  (interval_append test28160 80 96 112
  test28160_block_5
  test28160_block_6)
  (interval_append test28160 112 128 160
  test28160_block_7
  (interval_append test28160 128 144 160
  test28160_block_8
  test28160_block_9))))
  (interval_append test28160 160 240 320
  (interval_append test28160 160 192 240
  (interval_append test28160 160 176 192
  test28160_block_10
  test28160_block_11)
  (interval_append test28160 192 208 240
  test28160_block_12
  (interval_append test28160 208 224 240
  test28160_block_13
  test28160_block_14)))
  (interval_append test28160 240 272 320
  (interval_append test28160 240 256 272
  test28160_block_15
  test28160_block_16)
  (interval_append test28160 272 288 320
  test28160_block_17
  (interval_append test28160 288 304 320
  test28160_block_18
  test28160_block_19)))))
  (interval_append test28160 320 480 640
  (interval_append test28160 320 400 480
  (interval_append test28160 320 352 400
  (interval_append test28160 320 336 352
  test28160_block_20
  test28160_block_21)
  (interval_append test28160 352 368 400
  test28160_block_22
  (interval_append test28160 368 384 400
  test28160_block_23
  test28160_block_24)))
  (interval_append test28160 400 432 480
  (interval_append test28160 400 416 432
  test28160_block_25
  test28160_block_26)
  (interval_append test28160 432 448 480
  test28160_block_27
  (interval_append test28160 448 464 480
  test28160_block_28
  test28160_block_29))))
  (interval_append test28160 480 560 640
  (interval_append test28160 480 512 560
  (interval_append test28160 480 496 512
  test28160_block_30
  test28160_block_31)
  (interval_append test28160 512 528 560
  test28160_block_32
  (interval_append test28160 528 544 560
  test28160_block_33
  test28160_block_34)))
  (interval_append test28160 560 592 640
  (interval_append test28160 560 576 592
  test28160_block_35
  test28160_block_36)
  (interval_append test28160 592 608 640
  test28160_block_37
  (interval_append test28160 608 624 640
  test28160_block_38
  test28160_block_39))))))
cert_nodeInterval_4 28160 28800
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
