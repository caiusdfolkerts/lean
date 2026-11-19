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
cert_test_13 55040
cert_test_block_4 55040 0 0 16 16
cert_test_block_4 55040 1 16 32 16
cert_test_block_4 55040 2 32 48 16
cert_test_block_4 55040 3 48 64 16
cert_test_block_4 55040 4 64 80 16
cert_test_block_4 55040 5 80 96 16
cert_test_block_4 55040 6 96 112 16
cert_test_block_4 55040 7 112 128 16
cert_test_block_4 55040 8 128 144 16
cert_test_block_4 55040 9 144 160 16
cert_test_block_4 55040 10 160 176 16
cert_test_block_4 55040 11 176 192 16
cert_test_block_4 55040 12 192 208 16
cert_test_block_4 55040 13 208 224 16
cert_test_block_4 55040 14 224 240 16
cert_test_block_4 55040 15 240 256 16
cert_test_block_4 55040 16 256 272 16
cert_test_block_4 55040 17 272 288 16
cert_test_block_4 55040 18 288 304 16
cert_test_block_4 55040 19 304 320 16
cert_test_block_4 55040 20 320 336 16
cert_test_block_4 55040 21 336 352 16
cert_test_block_4 55040 22 352 368 16
cert_test_block_4 55040 23 368 384 16
cert_test_block_4 55040 24 384 400 16
cert_test_block_4 55040 25 400 416 16
cert_test_block_4 55040 26 416 432 16
cert_test_block_4 55040 27 432 448 16
cert_test_block_4 55040 28 448 464 16
cert_test_block_4 55040 29 464 480 16
cert_test_block_4 55040 30 480 496 16
cert_test_block_4 55040 31 496 512 16
cert_test_block_4 55040 32 512 528 16
cert_test_block_4 55040 33 528 544 16
cert_test_block_4 55040 34 544 560 16
cert_test_block_4 55040 35 560 576 16
cert_test_block_4 55040 36 576 592 16
cert_test_block_4 55040 37 592 608 16
cert_test_block_4 55040 38 608 624 16
cert_test_block_4 55040 39 624 640 16
theorem test55040_complete : Interval test55040 0 640 :=
  (interval_append test55040 0 320 640
  (interval_append test55040 0 160 320
  (interval_append test55040 0 80 160
  (interval_append test55040 0 32 80
  (interval_append test55040 0 16 32
  test55040_block_0
  test55040_block_1)
  (interval_append test55040 32 48 80
  test55040_block_2
  (interval_append test55040 48 64 80
  test55040_block_3
  test55040_block_4)))
  (interval_append test55040 80 112 160
  (interval_append test55040 80 96 112
  test55040_block_5
  test55040_block_6)
  (interval_append test55040 112 128 160
  test55040_block_7
  (interval_append test55040 128 144 160
  test55040_block_8
  test55040_block_9))))
  (interval_append test55040 160 240 320
  (interval_append test55040 160 192 240
  (interval_append test55040 160 176 192
  test55040_block_10
  test55040_block_11)
  (interval_append test55040 192 208 240
  test55040_block_12
  (interval_append test55040 208 224 240
  test55040_block_13
  test55040_block_14)))
  (interval_append test55040 240 272 320
  (interval_append test55040 240 256 272
  test55040_block_15
  test55040_block_16)
  (interval_append test55040 272 288 320
  test55040_block_17
  (interval_append test55040 288 304 320
  test55040_block_18
  test55040_block_19)))))
  (interval_append test55040 320 480 640
  (interval_append test55040 320 400 480
  (interval_append test55040 320 352 400
  (interval_append test55040 320 336 352
  test55040_block_20
  test55040_block_21)
  (interval_append test55040 352 368 400
  test55040_block_22
  (interval_append test55040 368 384 400
  test55040_block_23
  test55040_block_24)))
  (interval_append test55040 400 432 480
  (interval_append test55040 400 416 432
  test55040_block_25
  test55040_block_26)
  (interval_append test55040 432 448 480
  test55040_block_27
  (interval_append test55040 448 464 480
  test55040_block_28
  test55040_block_29))))
  (interval_append test55040 480 560 640
  (interval_append test55040 480 512 560
  (interval_append test55040 480 496 512
  test55040_block_30
  test55040_block_31)
  (interval_append test55040 512 528 560
  test55040_block_32
  (interval_append test55040 528 544 560
  test55040_block_33
  test55040_block_34)))
  (interval_append test55040 560 592 640
  (interval_append test55040 560 576 592
  test55040_block_35
  test55040_block_36)
  (interval_append test55040 592 608 640
  test55040_block_37
  (interval_append test55040 608 624 640
  test55040_block_38
  test55040_block_39))))))
cert_nodeInterval_4 55040 55680
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
