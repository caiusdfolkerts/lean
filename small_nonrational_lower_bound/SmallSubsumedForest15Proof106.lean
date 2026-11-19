module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 67840
cert_test_block_4 67840 0 0 16 16
cert_test_block_4 67840 1 16 32 16
cert_test_block_4 67840 2 32 48 16
cert_test_block_4 67840 3 48 64 16
cert_test_block_4 67840 4 64 80 16
cert_test_block_4 67840 5 80 96 16
cert_test_block_4 67840 6 96 112 16
cert_test_block_4 67840 7 112 128 16
cert_test_block_4 67840 8 128 144 16
cert_test_block_4 67840 9 144 160 16
cert_test_block_4 67840 10 160 176 16
cert_test_block_4 67840 11 176 192 16
cert_test_block_4 67840 12 192 208 16
cert_test_block_4 67840 13 208 224 16
cert_test_block_4 67840 14 224 240 16
cert_test_block_4 67840 15 240 256 16
cert_test_block_4 67840 16 256 272 16
cert_test_block_4 67840 17 272 288 16
cert_test_block_4 67840 18 288 304 16
cert_test_block_4 67840 19 304 320 16
cert_test_block_4 67840 20 320 336 16
cert_test_block_4 67840 21 336 352 16
cert_test_block_4 67840 22 352 368 16
cert_test_block_4 67840 23 368 384 16
cert_test_block_4 67840 24 384 400 16
cert_test_block_4 67840 25 400 416 16
cert_test_block_4 67840 26 416 432 16
cert_test_block_4 67840 27 432 448 16
cert_test_block_4 67840 28 448 464 16
cert_test_block_4 67840 29 464 480 16
cert_test_block_4 67840 30 480 496 16
cert_test_block_4 67840 31 496 512 16
cert_test_block_4 67840 32 512 528 16
cert_test_block_4 67840 33 528 544 16
cert_test_block_4 67840 34 544 560 16
cert_test_block_4 67840 35 560 576 16
cert_test_block_4 67840 36 576 592 16
cert_test_block_4 67840 37 592 608 16
cert_test_block_4 67840 38 608 624 16
cert_test_block_4 67840 39 624 640 16
theorem test67840_complete : Interval test67840 0 640 :=
  (interval_append test67840 0 320 640
  (interval_append test67840 0 160 320
  (interval_append test67840 0 80 160
  (interval_append test67840 0 32 80
  (interval_append test67840 0 16 32
  test67840_block_0
  test67840_block_1)
  (interval_append test67840 32 48 80
  test67840_block_2
  (interval_append test67840 48 64 80
  test67840_block_3
  test67840_block_4)))
  (interval_append test67840 80 112 160
  (interval_append test67840 80 96 112
  test67840_block_5
  test67840_block_6)
  (interval_append test67840 112 128 160
  test67840_block_7
  (interval_append test67840 128 144 160
  test67840_block_8
  test67840_block_9))))
  (interval_append test67840 160 240 320
  (interval_append test67840 160 192 240
  (interval_append test67840 160 176 192
  test67840_block_10
  test67840_block_11)
  (interval_append test67840 192 208 240
  test67840_block_12
  (interval_append test67840 208 224 240
  test67840_block_13
  test67840_block_14)))
  (interval_append test67840 240 272 320
  (interval_append test67840 240 256 272
  test67840_block_15
  test67840_block_16)
  (interval_append test67840 272 288 320
  test67840_block_17
  (interval_append test67840 288 304 320
  test67840_block_18
  test67840_block_19)))))
  (interval_append test67840 320 480 640
  (interval_append test67840 320 400 480
  (interval_append test67840 320 352 400
  (interval_append test67840 320 336 352
  test67840_block_20
  test67840_block_21)
  (interval_append test67840 352 368 400
  test67840_block_22
  (interval_append test67840 368 384 400
  test67840_block_23
  test67840_block_24)))
  (interval_append test67840 400 432 480
  (interval_append test67840 400 416 432
  test67840_block_25
  test67840_block_26)
  (interval_append test67840 432 448 480
  test67840_block_27
  (interval_append test67840 448 464 480
  test67840_block_28
  test67840_block_29))))
  (interval_append test67840 480 560 640
  (interval_append test67840 480 512 560
  (interval_append test67840 480 496 512
  test67840_block_30
  test67840_block_31)
  (interval_append test67840 512 528 560
  test67840_block_32
  (interval_append test67840 528 544 560
  test67840_block_33
  test67840_block_34)))
  (interval_append test67840 560 592 640
  (interval_append test67840 560 576 592
  test67840_block_35
  test67840_block_36)
  (interval_append test67840 592 608 640
  test67840_block_37
  (interval_append test67840 608 624 640
  test67840_block_38
  test67840_block_39))))))
cert_nodeInterval_4 67840 68480
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
