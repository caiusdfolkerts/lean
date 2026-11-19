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
cert_test_13 69760
cert_test_block_4 69760 0 0 16 16
cert_test_block_4 69760 1 16 32 16
cert_test_block_4 69760 2 32 48 16
cert_test_block_4 69760 3 48 64 16
cert_test_block_4 69760 4 64 80 16
cert_test_block_4 69760 5 80 96 16
cert_test_block_4 69760 6 96 112 16
cert_test_block_4 69760 7 112 128 16
cert_test_block_4 69760 8 128 144 16
cert_test_block_4 69760 9 144 160 16
cert_test_block_4 69760 10 160 176 16
cert_test_block_4 69760 11 176 192 16
cert_test_block_4 69760 12 192 208 16
cert_test_block_4 69760 13 208 224 16
cert_test_block_4 69760 14 224 240 16
cert_test_block_4 69760 15 240 256 16
cert_test_block_4 69760 16 256 272 16
cert_test_block_4 69760 17 272 288 16
cert_test_block_4 69760 18 288 304 16
cert_test_block_4 69760 19 304 320 16
cert_test_block_4 69760 20 320 336 16
cert_test_block_4 69760 21 336 352 16
cert_test_block_4 69760 22 352 368 16
cert_test_block_4 69760 23 368 384 16
cert_test_block_4 69760 24 384 400 16
cert_test_block_4 69760 25 400 416 16
cert_test_block_4 69760 26 416 432 16
cert_test_block_4 69760 27 432 448 16
cert_test_block_4 69760 28 448 464 16
cert_test_block_4 69760 29 464 480 16
cert_test_block_4 69760 30 480 496 16
cert_test_block_4 69760 31 496 512 16
cert_test_block_4 69760 32 512 528 16
cert_test_block_4 69760 33 528 544 16
cert_test_block_4 69760 34 544 560 16
cert_test_block_4 69760 35 560 576 16
cert_test_block_4 69760 36 576 592 16
cert_test_block_4 69760 37 592 608 16
cert_test_block_4 69760 38 608 624 16
cert_test_block_4 69760 39 624 640 16
theorem test69760_complete : Interval test69760 0 640 :=
  (interval_append test69760 0 320 640
  (interval_append test69760 0 160 320
  (interval_append test69760 0 80 160
  (interval_append test69760 0 32 80
  (interval_append test69760 0 16 32
  test69760_block_0
  test69760_block_1)
  (interval_append test69760 32 48 80
  test69760_block_2
  (interval_append test69760 48 64 80
  test69760_block_3
  test69760_block_4)))
  (interval_append test69760 80 112 160
  (interval_append test69760 80 96 112
  test69760_block_5
  test69760_block_6)
  (interval_append test69760 112 128 160
  test69760_block_7
  (interval_append test69760 128 144 160
  test69760_block_8
  test69760_block_9))))
  (interval_append test69760 160 240 320
  (interval_append test69760 160 192 240
  (interval_append test69760 160 176 192
  test69760_block_10
  test69760_block_11)
  (interval_append test69760 192 208 240
  test69760_block_12
  (interval_append test69760 208 224 240
  test69760_block_13
  test69760_block_14)))
  (interval_append test69760 240 272 320
  (interval_append test69760 240 256 272
  test69760_block_15
  test69760_block_16)
  (interval_append test69760 272 288 320
  test69760_block_17
  (interval_append test69760 288 304 320
  test69760_block_18
  test69760_block_19)))))
  (interval_append test69760 320 480 640
  (interval_append test69760 320 400 480
  (interval_append test69760 320 352 400
  (interval_append test69760 320 336 352
  test69760_block_20
  test69760_block_21)
  (interval_append test69760 352 368 400
  test69760_block_22
  (interval_append test69760 368 384 400
  test69760_block_23
  test69760_block_24)))
  (interval_append test69760 400 432 480
  (interval_append test69760 400 416 432
  test69760_block_25
  test69760_block_26)
  (interval_append test69760 432 448 480
  test69760_block_27
  (interval_append test69760 448 464 480
  test69760_block_28
  test69760_block_29))))
  (interval_append test69760 480 560 640
  (interval_append test69760 480 512 560
  (interval_append test69760 480 496 512
  test69760_block_30
  test69760_block_31)
  (interval_append test69760 512 528 560
  test69760_block_32
  (interval_append test69760 528 544 560
  test69760_block_33
  test69760_block_34)))
  (interval_append test69760 560 592 640
  (interval_append test69760 560 576 592
  test69760_block_35
  test69760_block_36)
  (interval_append test69760 592 608 640
  test69760_block_37
  (interval_append test69760 608 624 640
  test69760_block_38
  test69760_block_39))))))
cert_nodeInterval_4 69760 70400
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
