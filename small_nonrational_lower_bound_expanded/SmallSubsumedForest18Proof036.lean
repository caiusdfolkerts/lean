module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 23040
cert_test_block_4 23040 0 0 16 16
cert_test_block_4 23040 1 16 32 16
cert_test_block_4 23040 2 32 48 16
cert_test_block_4 23040 3 48 64 16
cert_test_block_4 23040 4 64 80 16
cert_test_block_4 23040 5 80 96 16
cert_test_block_4 23040 6 96 112 16
cert_test_block_4 23040 7 112 128 16
cert_test_block_4 23040 8 128 144 16
cert_test_block_4 23040 9 144 160 16
cert_test_block_4 23040 10 160 176 16
cert_test_block_4 23040 11 176 192 16
cert_test_block_4 23040 12 192 208 16
cert_test_block_4 23040 13 208 224 16
cert_test_block_4 23040 14 224 240 16
cert_test_block_4 23040 15 240 256 16
cert_test_block_4 23040 16 256 272 16
cert_test_block_4 23040 17 272 288 16
cert_test_block_4 23040 18 288 304 16
cert_test_block_4 23040 19 304 320 16
cert_test_block_4 23040 20 320 336 16
cert_test_block_4 23040 21 336 352 16
cert_test_block_4 23040 22 352 368 16
cert_test_block_4 23040 23 368 384 16
cert_test_block_4 23040 24 384 400 16
cert_test_block_4 23040 25 400 416 16
cert_test_block_4 23040 26 416 432 16
cert_test_block_4 23040 27 432 448 16
cert_test_block_4 23040 28 448 464 16
cert_test_block_4 23040 29 464 480 16
cert_test_block_4 23040 30 480 496 16
cert_test_block_4 23040 31 496 512 16
cert_test_block_4 23040 32 512 528 16
cert_test_block_4 23040 33 528 544 16
cert_test_block_4 23040 34 544 560 16
cert_test_block_4 23040 35 560 576 16
cert_test_block_4 23040 36 576 592 16
cert_test_block_4 23040 37 592 608 16
cert_test_block_4 23040 38 608 624 16
cert_test_block_4 23040 39 624 640 16
theorem test23040_complete : Interval test23040 0 640 :=
  (interval_append test23040 0 320 640
  (interval_append test23040 0 160 320
  (interval_append test23040 0 80 160
  (interval_append test23040 0 32 80
  (interval_append test23040 0 16 32
  test23040_block_0
  test23040_block_1)
  (interval_append test23040 32 48 80
  test23040_block_2
  (interval_append test23040 48 64 80
  test23040_block_3
  test23040_block_4)))
  (interval_append test23040 80 112 160
  (interval_append test23040 80 96 112
  test23040_block_5
  test23040_block_6)
  (interval_append test23040 112 128 160
  test23040_block_7
  (interval_append test23040 128 144 160
  test23040_block_8
  test23040_block_9))))
  (interval_append test23040 160 240 320
  (interval_append test23040 160 192 240
  (interval_append test23040 160 176 192
  test23040_block_10
  test23040_block_11)
  (interval_append test23040 192 208 240
  test23040_block_12
  (interval_append test23040 208 224 240
  test23040_block_13
  test23040_block_14)))
  (interval_append test23040 240 272 320
  (interval_append test23040 240 256 272
  test23040_block_15
  test23040_block_16)
  (interval_append test23040 272 288 320
  test23040_block_17
  (interval_append test23040 288 304 320
  test23040_block_18
  test23040_block_19)))))
  (interval_append test23040 320 480 640
  (interval_append test23040 320 400 480
  (interval_append test23040 320 352 400
  (interval_append test23040 320 336 352
  test23040_block_20
  test23040_block_21)
  (interval_append test23040 352 368 400
  test23040_block_22
  (interval_append test23040 368 384 400
  test23040_block_23
  test23040_block_24)))
  (interval_append test23040 400 432 480
  (interval_append test23040 400 416 432
  test23040_block_25
  test23040_block_26)
  (interval_append test23040 432 448 480
  test23040_block_27
  (interval_append test23040 448 464 480
  test23040_block_28
  test23040_block_29))))
  (interval_append test23040 480 560 640
  (interval_append test23040 480 512 560
  (interval_append test23040 480 496 512
  test23040_block_30
  test23040_block_31)
  (interval_append test23040 512 528 560
  test23040_block_32
  (interval_append test23040 528 544 560
  test23040_block_33
  test23040_block_34)))
  (interval_append test23040 560 592 640
  (interval_append test23040 560 576 592
  test23040_block_35
  test23040_block_36)
  (interval_append test23040 592 608 640
  test23040_block_37
  (interval_append test23040 608 624 640
  test23040_block_38
  test23040_block_39))))))
cert_nodeInterval_4 23040 23680
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
