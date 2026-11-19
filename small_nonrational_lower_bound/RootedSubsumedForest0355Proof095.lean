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
cert_test_11 60800
cert_test_block_3 60800 0 0 16 16
cert_test_block_3 60800 1 16 32 16
cert_test_block_3 60800 2 32 48 16
cert_test_block_3 60800 3 48 64 16
cert_test_block_3 60800 4 64 80 16
cert_test_block_3 60800 5 80 96 16
cert_test_block_3 60800 6 96 112 16
cert_test_block_3 60800 7 112 128 16
cert_test_block_3 60800 8 128 144 16
cert_test_block_3 60800 9 144 160 16
cert_test_block_3 60800 10 160 176 16
cert_test_block_3 60800 11 176 192 16
cert_test_block_3 60800 12 192 208 16
cert_test_block_3 60800 13 208 224 16
cert_test_block_3 60800 14 224 240 16
cert_test_block_3 60800 15 240 256 16
cert_test_block_3 60800 16 256 272 16
cert_test_block_3 60800 17 272 288 16
cert_test_block_3 60800 18 288 304 16
cert_test_block_3 60800 19 304 320 16
cert_test_block_3 60800 20 320 336 16
cert_test_block_3 60800 21 336 352 16
cert_test_block_3 60800 22 352 368 16
cert_test_block_3 60800 23 368 384 16
cert_test_block_3 60800 24 384 400 16
cert_test_block_3 60800 25 400 416 16
cert_test_block_3 60800 26 416 432 16
cert_test_block_3 60800 27 432 448 16
cert_test_block_3 60800 28 448 464 16
cert_test_block_3 60800 29 464 480 16
cert_test_block_3 60800 30 480 496 16
cert_test_block_3 60800 31 496 512 16
cert_test_block_3 60800 32 512 528 16
cert_test_block_3 60800 33 528 544 16
cert_test_block_3 60800 34 544 560 16
cert_test_block_3 60800 35 560 576 16
cert_test_block_3 60800 36 576 592 16
cert_test_block_3 60800 37 592 608 16
cert_test_block_3 60800 38 608 624 16
cert_test_block_3 60800 39 624 640 16
theorem test60800_complete : Interval test60800 0 640 :=
  (interval_append test60800 0 320 640
  (interval_append test60800 0 160 320
  (interval_append test60800 0 80 160
  (interval_append test60800 0 32 80
  (interval_append test60800 0 16 32
  test60800_block_0
  test60800_block_1)
  (interval_append test60800 32 48 80
  test60800_block_2
  (interval_append test60800 48 64 80
  test60800_block_3
  test60800_block_4)))
  (interval_append test60800 80 112 160
  (interval_append test60800 80 96 112
  test60800_block_5
  test60800_block_6)
  (interval_append test60800 112 128 160
  test60800_block_7
  (interval_append test60800 128 144 160
  test60800_block_8
  test60800_block_9))))
  (interval_append test60800 160 240 320
  (interval_append test60800 160 192 240
  (interval_append test60800 160 176 192
  test60800_block_10
  test60800_block_11)
  (interval_append test60800 192 208 240
  test60800_block_12
  (interval_append test60800 208 224 240
  test60800_block_13
  test60800_block_14)))
  (interval_append test60800 240 272 320
  (interval_append test60800 240 256 272
  test60800_block_15
  test60800_block_16)
  (interval_append test60800 272 288 320
  test60800_block_17
  (interval_append test60800 288 304 320
  test60800_block_18
  test60800_block_19)))))
  (interval_append test60800 320 480 640
  (interval_append test60800 320 400 480
  (interval_append test60800 320 352 400
  (interval_append test60800 320 336 352
  test60800_block_20
  test60800_block_21)
  (interval_append test60800 352 368 400
  test60800_block_22
  (interval_append test60800 368 384 400
  test60800_block_23
  test60800_block_24)))
  (interval_append test60800 400 432 480
  (interval_append test60800 400 416 432
  test60800_block_25
  test60800_block_26)
  (interval_append test60800 432 448 480
  test60800_block_27
  (interval_append test60800 448 464 480
  test60800_block_28
  test60800_block_29))))
  (interval_append test60800 480 560 640
  (interval_append test60800 480 512 560
  (interval_append test60800 480 496 512
  test60800_block_30
  test60800_block_31)
  (interval_append test60800 512 528 560
  test60800_block_32
  (interval_append test60800 528 544 560
  test60800_block_33
  test60800_block_34)))
  (interval_append test60800 560 592 640
  (interval_append test60800 560 576 592
  test60800_block_35
  test60800_block_36)
  (interval_append test60800 592 608 640
  test60800_block_37
  (interval_append test60800 608 624 640
  test60800_block_38
  test60800_block_39))))))
cert_nodeInterval_3 60800 61440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
