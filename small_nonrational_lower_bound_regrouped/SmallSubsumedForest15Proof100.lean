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
cert_test_13 64000
cert_test_block_4 64000 0 0 16 16
cert_test_block_4 64000 1 16 32 16
cert_test_block_4 64000 2 32 48 16
cert_test_block_4 64000 3 48 64 16
cert_test_block_4 64000 4 64 80 16
cert_test_block_4 64000 5 80 96 16
cert_test_block_4 64000 6 96 112 16
cert_test_block_4 64000 7 112 128 16
cert_test_block_4 64000 8 128 144 16
cert_test_block_4 64000 9 144 160 16
cert_test_block_4 64000 10 160 176 16
cert_test_block_4 64000 11 176 192 16
cert_test_block_4 64000 12 192 208 16
cert_test_block_4 64000 13 208 224 16
cert_test_block_4 64000 14 224 240 16
cert_test_block_4 64000 15 240 256 16
cert_test_block_4 64000 16 256 272 16
cert_test_block_4 64000 17 272 288 16
cert_test_block_4 64000 18 288 304 16
cert_test_block_4 64000 19 304 320 16
cert_test_block_4 64000 20 320 336 16
cert_test_block_4 64000 21 336 352 16
cert_test_block_4 64000 22 352 368 16
cert_test_block_4 64000 23 368 384 16
cert_test_block_4 64000 24 384 400 16
cert_test_block_4 64000 25 400 416 16
cert_test_block_4 64000 26 416 432 16
cert_test_block_4 64000 27 432 448 16
cert_test_block_4 64000 28 448 464 16
cert_test_block_4 64000 29 464 480 16
cert_test_block_4 64000 30 480 496 16
cert_test_block_4 64000 31 496 512 16
cert_test_block_4 64000 32 512 528 16
cert_test_block_4 64000 33 528 544 16
cert_test_block_4 64000 34 544 560 16
cert_test_block_4 64000 35 560 576 16
cert_test_block_4 64000 36 576 592 16
cert_test_block_4 64000 37 592 608 16
cert_test_block_4 64000 38 608 624 16
cert_test_block_4 64000 39 624 640 16
theorem test64000_complete : Interval test64000 0 640 :=
  (interval_append test64000 0 320 640
  (interval_append test64000 0 160 320
  (interval_append test64000 0 80 160
  (interval_append test64000 0 32 80
  (interval_append test64000 0 16 32
  test64000_block_0
  test64000_block_1)
  (interval_append test64000 32 48 80
  test64000_block_2
  (interval_append test64000 48 64 80
  test64000_block_3
  test64000_block_4)))
  (interval_append test64000 80 112 160
  (interval_append test64000 80 96 112
  test64000_block_5
  test64000_block_6)
  (interval_append test64000 112 128 160
  test64000_block_7
  (interval_append test64000 128 144 160
  test64000_block_8
  test64000_block_9))))
  (interval_append test64000 160 240 320
  (interval_append test64000 160 192 240
  (interval_append test64000 160 176 192
  test64000_block_10
  test64000_block_11)
  (interval_append test64000 192 208 240
  test64000_block_12
  (interval_append test64000 208 224 240
  test64000_block_13
  test64000_block_14)))
  (interval_append test64000 240 272 320
  (interval_append test64000 240 256 272
  test64000_block_15
  test64000_block_16)
  (interval_append test64000 272 288 320
  test64000_block_17
  (interval_append test64000 288 304 320
  test64000_block_18
  test64000_block_19)))))
  (interval_append test64000 320 480 640
  (interval_append test64000 320 400 480
  (interval_append test64000 320 352 400
  (interval_append test64000 320 336 352
  test64000_block_20
  test64000_block_21)
  (interval_append test64000 352 368 400
  test64000_block_22
  (interval_append test64000 368 384 400
  test64000_block_23
  test64000_block_24)))
  (interval_append test64000 400 432 480
  (interval_append test64000 400 416 432
  test64000_block_25
  test64000_block_26)
  (interval_append test64000 432 448 480
  test64000_block_27
  (interval_append test64000 448 464 480
  test64000_block_28
  test64000_block_29))))
  (interval_append test64000 480 560 640
  (interval_append test64000 480 512 560
  (interval_append test64000 480 496 512
  test64000_block_30
  test64000_block_31)
  (interval_append test64000 512 528 560
  test64000_block_32
  (interval_append test64000 528 544 560
  test64000_block_33
  test64000_block_34)))
  (interval_append test64000 560 592 640
  (interval_append test64000 560 576 592
  test64000_block_35
  test64000_block_36)
  (interval_append test64000 592 608 640
  test64000_block_37
  (interval_append test64000 608 624 640
  test64000_block_38
  test64000_block_39))))))
cert_nodeInterval_4 64000 64640
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
