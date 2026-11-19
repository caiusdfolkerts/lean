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
cert_test_13 51840
cert_test_block_4 51840 0 0 16 16
cert_test_block_4 51840 1 16 32 16
cert_test_block_4 51840 2 32 48 16
cert_test_block_4 51840 3 48 64 16
cert_test_block_4 51840 4 64 80 16
cert_test_block_4 51840 5 80 96 16
cert_test_block_4 51840 6 96 112 16
cert_test_block_4 51840 7 112 128 16
cert_test_block_4 51840 8 128 144 16
cert_test_block_4 51840 9 144 160 16
cert_test_block_4 51840 10 160 176 16
cert_test_block_4 51840 11 176 192 16
cert_test_block_4 51840 12 192 208 16
cert_test_block_4 51840 13 208 224 16
cert_test_block_4 51840 14 224 240 16
cert_test_block_4 51840 15 240 256 16
cert_test_block_4 51840 16 256 272 16
cert_test_block_4 51840 17 272 288 16
cert_test_block_4 51840 18 288 304 16
cert_test_block_4 51840 19 304 320 16
cert_test_block_4 51840 20 320 336 16
cert_test_block_4 51840 21 336 352 16
cert_test_block_4 51840 22 352 368 16
cert_test_block_4 51840 23 368 384 16
cert_test_block_4 51840 24 384 400 16
cert_test_block_4 51840 25 400 416 16
cert_test_block_4 51840 26 416 432 16
cert_test_block_4 51840 27 432 448 16
cert_test_block_4 51840 28 448 464 16
cert_test_block_4 51840 29 464 480 16
cert_test_block_4 51840 30 480 496 16
cert_test_block_4 51840 31 496 512 16
cert_test_block_4 51840 32 512 528 16
cert_test_block_4 51840 33 528 544 16
cert_test_block_4 51840 34 544 560 16
cert_test_block_4 51840 35 560 576 16
cert_test_block_4 51840 36 576 592 16
cert_test_block_4 51840 37 592 608 16
cert_test_block_4 51840 38 608 624 16
cert_test_block_4 51840 39 624 640 16
theorem test51840_complete : Interval test51840 0 640 :=
  (interval_append test51840 0 320 640
  (interval_append test51840 0 160 320
  (interval_append test51840 0 80 160
  (interval_append test51840 0 32 80
  (interval_append test51840 0 16 32
  test51840_block_0
  test51840_block_1)
  (interval_append test51840 32 48 80
  test51840_block_2
  (interval_append test51840 48 64 80
  test51840_block_3
  test51840_block_4)))
  (interval_append test51840 80 112 160
  (interval_append test51840 80 96 112
  test51840_block_5
  test51840_block_6)
  (interval_append test51840 112 128 160
  test51840_block_7
  (interval_append test51840 128 144 160
  test51840_block_8
  test51840_block_9))))
  (interval_append test51840 160 240 320
  (interval_append test51840 160 192 240
  (interval_append test51840 160 176 192
  test51840_block_10
  test51840_block_11)
  (interval_append test51840 192 208 240
  test51840_block_12
  (interval_append test51840 208 224 240
  test51840_block_13
  test51840_block_14)))
  (interval_append test51840 240 272 320
  (interval_append test51840 240 256 272
  test51840_block_15
  test51840_block_16)
  (interval_append test51840 272 288 320
  test51840_block_17
  (interval_append test51840 288 304 320
  test51840_block_18
  test51840_block_19)))))
  (interval_append test51840 320 480 640
  (interval_append test51840 320 400 480
  (interval_append test51840 320 352 400
  (interval_append test51840 320 336 352
  test51840_block_20
  test51840_block_21)
  (interval_append test51840 352 368 400
  test51840_block_22
  (interval_append test51840 368 384 400
  test51840_block_23
  test51840_block_24)))
  (interval_append test51840 400 432 480
  (interval_append test51840 400 416 432
  test51840_block_25
  test51840_block_26)
  (interval_append test51840 432 448 480
  test51840_block_27
  (interval_append test51840 448 464 480
  test51840_block_28
  test51840_block_29))))
  (interval_append test51840 480 560 640
  (interval_append test51840 480 512 560
  (interval_append test51840 480 496 512
  test51840_block_30
  test51840_block_31)
  (interval_append test51840 512 528 560
  test51840_block_32
  (interval_append test51840 528 544 560
  test51840_block_33
  test51840_block_34)))
  (interval_append test51840 560 592 640
  (interval_append test51840 560 576 592
  test51840_block_35
  test51840_block_36)
  (interval_append test51840 592 608 640
  test51840_block_37
  (interval_append test51840 608 624 640
  test51840_block_38
  test51840_block_39))))))
cert_nodeInterval_4 51840 52480
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
