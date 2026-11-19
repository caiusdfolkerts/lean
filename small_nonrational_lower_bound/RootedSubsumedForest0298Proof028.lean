module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0298Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 17920
cert_test_block_3 17920 0 0 16 16
cert_test_block_3 17920 1 16 32 16
cert_test_block_3 17920 2 32 48 16
cert_test_block_3 17920 3 48 64 16
cert_test_block_3 17920 4 64 80 16
cert_test_block_3 17920 5 80 96 16
cert_test_block_3 17920 6 96 112 16
cert_test_block_3 17920 7 112 128 16
cert_test_block_3 17920 8 128 144 16
cert_test_block_3 17920 9 144 160 16
cert_test_block_3 17920 10 160 176 16
cert_test_block_3 17920 11 176 192 16
cert_test_block_3 17920 12 192 208 16
cert_test_block_3 17920 13 208 224 16
cert_test_block_3 17920 14 224 240 16
cert_test_block_3 17920 15 240 256 16
cert_test_block_3 17920 16 256 272 16
cert_test_block_3 17920 17 272 288 16
cert_test_block_3 17920 18 288 304 16
cert_test_block_3 17920 19 304 320 16
cert_test_block_3 17920 20 320 336 16
cert_test_block_3 17920 21 336 352 16
cert_test_block_3 17920 22 352 368 16
cert_test_block_3 17920 23 368 384 16
cert_test_block_3 17920 24 384 400 16
cert_test_block_3 17920 25 400 416 16
cert_test_block_3 17920 26 416 432 16
cert_test_block_3 17920 27 432 448 16
cert_test_block_3 17920 28 448 464 16
cert_test_block_3 17920 29 464 480 16
cert_test_block_3 17920 30 480 496 16
cert_test_block_3 17920 31 496 512 16
cert_test_block_3 17920 32 512 528 16
cert_test_block_3 17920 33 528 544 16
cert_test_block_3 17920 34 544 560 16
cert_test_block_3 17920 35 560 576 16
cert_test_block_3 17920 36 576 592 16
cert_test_block_3 17920 37 592 608 16
cert_test_block_3 17920 38 608 624 16
cert_test_block_3 17920 39 624 640 16
theorem test17920_complete : Interval test17920 0 640 :=
  (interval_append test17920 0 320 640
  (interval_append test17920 0 160 320
  (interval_append test17920 0 80 160
  (interval_append test17920 0 32 80
  (interval_append test17920 0 16 32
  test17920_block_0
  test17920_block_1)
  (interval_append test17920 32 48 80
  test17920_block_2
  (interval_append test17920 48 64 80
  test17920_block_3
  test17920_block_4)))
  (interval_append test17920 80 112 160
  (interval_append test17920 80 96 112
  test17920_block_5
  test17920_block_6)
  (interval_append test17920 112 128 160
  test17920_block_7
  (interval_append test17920 128 144 160
  test17920_block_8
  test17920_block_9))))
  (interval_append test17920 160 240 320
  (interval_append test17920 160 192 240
  (interval_append test17920 160 176 192
  test17920_block_10
  test17920_block_11)
  (interval_append test17920 192 208 240
  test17920_block_12
  (interval_append test17920 208 224 240
  test17920_block_13
  test17920_block_14)))
  (interval_append test17920 240 272 320
  (interval_append test17920 240 256 272
  test17920_block_15
  test17920_block_16)
  (interval_append test17920 272 288 320
  test17920_block_17
  (interval_append test17920 288 304 320
  test17920_block_18
  test17920_block_19)))))
  (interval_append test17920 320 480 640
  (interval_append test17920 320 400 480
  (interval_append test17920 320 352 400
  (interval_append test17920 320 336 352
  test17920_block_20
  test17920_block_21)
  (interval_append test17920 352 368 400
  test17920_block_22
  (interval_append test17920 368 384 400
  test17920_block_23
  test17920_block_24)))
  (interval_append test17920 400 432 480
  (interval_append test17920 400 416 432
  test17920_block_25
  test17920_block_26)
  (interval_append test17920 432 448 480
  test17920_block_27
  (interval_append test17920 448 464 480
  test17920_block_28
  test17920_block_29))))
  (interval_append test17920 480 560 640
  (interval_append test17920 480 512 560
  (interval_append test17920 480 496 512
  test17920_block_30
  test17920_block_31)
  (interval_append test17920 512 528 560
  test17920_block_32
  (interval_append test17920 528 544 560
  test17920_block_33
  test17920_block_34)))
  (interval_append test17920 560 592 640
  (interval_append test17920 560 576 592
  test17920_block_35
  test17920_block_36)
  (interval_append test17920 592 608 640
  test17920_block_37
  (interval_append test17920 608 624 640
  test17920_block_38
  test17920_block_39))))))
cert_nodeInterval_3 17920 18560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
