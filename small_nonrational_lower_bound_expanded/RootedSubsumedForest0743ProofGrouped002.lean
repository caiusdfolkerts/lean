module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 16000
cert_test_block_3 16000 0 0 16 16
cert_test_block_3 16000 1 16 32 16
cert_test_block_3 16000 2 32 48 16
cert_test_block_3 16000 3 48 64 16
cert_test_block_3 16000 4 64 80 16
cert_test_block_3 16000 5 80 96 16
cert_test_block_3 16000 6 96 112 16
cert_test_block_3 16000 7 112 128 16
cert_test_block_3 16000 8 128 144 16
cert_test_block_3 16000 9 144 160 16
cert_test_block_3 16000 10 160 176 16
cert_test_block_3 16000 11 176 192 16
cert_test_block_3 16000 12 192 208 16
cert_test_block_3 16000 13 208 224 16
cert_test_block_3 16000 14 224 240 16
cert_test_block_3 16000 15 240 256 16
cert_test_block_3 16000 16 256 272 16
cert_test_block_3 16000 17 272 288 16
cert_test_block_3 16000 18 288 304 16
cert_test_block_3 16000 19 304 320 16
cert_test_block_3 16000 20 320 336 16
cert_test_block_3 16000 21 336 352 16
cert_test_block_3 16000 22 352 368 16
cert_test_block_3 16000 23 368 384 16
cert_test_block_3 16000 24 384 400 16
cert_test_block_3 16000 25 400 416 16
cert_test_block_3 16000 26 416 432 16
cert_test_block_3 16000 27 432 448 16
cert_test_block_3 16000 28 448 464 16
cert_test_block_3 16000 29 464 480 16
cert_test_block_3 16000 30 480 496 16
cert_test_block_3 16000 31 496 512 16
cert_test_block_3 16000 32 512 528 16
cert_test_block_3 16000 33 528 544 16
cert_test_block_3 16000 34 544 560 16
cert_test_block_3 16000 35 560 576 16
cert_test_block_3 16000 36 576 592 16
cert_test_block_3 16000 37 592 608 16
cert_test_block_3 16000 38 608 624 16
cert_test_block_3 16000 39 624 640 16
theorem test16000_complete : Interval test16000 0 640 :=
  (interval_append test16000 0 320 640
  (interval_append test16000 0 160 320
  (interval_append test16000 0 80 160
  (interval_append test16000 0 32 80
  (interval_append test16000 0 16 32
  test16000_block_0
  test16000_block_1)
  (interval_append test16000 32 48 80
  test16000_block_2
  (interval_append test16000 48 64 80
  test16000_block_3
  test16000_block_4)))
  (interval_append test16000 80 112 160
  (interval_append test16000 80 96 112
  test16000_block_5
  test16000_block_6)
  (interval_append test16000 112 128 160
  test16000_block_7
  (interval_append test16000 128 144 160
  test16000_block_8
  test16000_block_9))))
  (interval_append test16000 160 240 320
  (interval_append test16000 160 192 240
  (interval_append test16000 160 176 192
  test16000_block_10
  test16000_block_11)
  (interval_append test16000 192 208 240
  test16000_block_12
  (interval_append test16000 208 224 240
  test16000_block_13
  test16000_block_14)))
  (interval_append test16000 240 272 320
  (interval_append test16000 240 256 272
  test16000_block_15
  test16000_block_16)
  (interval_append test16000 272 288 320
  test16000_block_17
  (interval_append test16000 288 304 320
  test16000_block_18
  test16000_block_19)))))
  (interval_append test16000 320 480 640
  (interval_append test16000 320 400 480
  (interval_append test16000 320 352 400
  (interval_append test16000 320 336 352
  test16000_block_20
  test16000_block_21)
  (interval_append test16000 352 368 400
  test16000_block_22
  (interval_append test16000 368 384 400
  test16000_block_23
  test16000_block_24)))
  (interval_append test16000 400 432 480
  (interval_append test16000 400 416 432
  test16000_block_25
  test16000_block_26)
  (interval_append test16000 432 448 480
  test16000_block_27
  (interval_append test16000 448 464 480
  test16000_block_28
  test16000_block_29))))
  (interval_append test16000 480 560 640
  (interval_append test16000 480 512 560
  (interval_append test16000 480 496 512
  test16000_block_30
  test16000_block_31)
  (interval_append test16000 512 528 560
  test16000_block_32
  (interval_append test16000 528 544 560
  test16000_block_33
  test16000_block_34)))
  (interval_append test16000 560 592 640
  (interval_append test16000 560 576 592
  test16000_block_35
  test16000_block_36)
  (interval_append test16000 592 608 640
  test16000_block_37
  (interval_append test16000 608 624 640
  test16000_block_38
  test16000_block_39))))))
cert_nodeInterval_3 16000 16640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 16640
cert_test_block_3 16640 0 0 16 16
cert_test_block_3 16640 1 16 32 16
cert_test_block_3 16640 2 32 48 16
cert_test_block_3 16640 3 48 64 16
cert_test_block_3 16640 4 64 80 16
cert_test_block_3 16640 5 80 96 16
cert_test_block_3 16640 6 96 112 16
cert_test_block_3 16640 7 112 128 16
cert_test_block_3 16640 8 128 144 16
cert_test_block_3 16640 9 144 160 16
cert_test_block_3 16640 10 160 176 16
cert_test_block_3 16640 11 176 192 16
cert_test_block_3 16640 12 192 208 16
cert_test_block_3 16640 13 208 224 16
cert_test_block_3 16640 14 224 240 16
cert_test_block_3 16640 15 240 256 16
cert_test_block_3 16640 16 256 272 16
cert_test_block_3 16640 17 272 288 16
cert_test_block_3 16640 18 288 304 16
cert_test_block_3 16640 19 304 320 16
cert_test_block_3 16640 20 320 336 16
cert_test_block_3 16640 21 336 352 16
cert_test_block_3 16640 22 352 368 16
cert_test_block_3 16640 23 368 384 16
cert_test_block_3 16640 24 384 400 16
cert_test_block_3 16640 25 400 416 16
cert_test_block_3 16640 26 416 432 16
cert_test_block_3 16640 27 432 448 16
cert_test_block_3 16640 28 448 464 16
cert_test_block_3 16640 29 464 480 16
cert_test_block_3 16640 30 480 496 16
cert_test_block_3 16640 31 496 512 16
cert_test_block_3 16640 32 512 528 16
cert_test_block_3 16640 33 528 544 16
cert_test_block_3 16640 34 544 560 16
cert_test_block_3 16640 35 560 576 16
cert_test_block_3 16640 36 576 592 16
cert_test_block_3 16640 37 592 608 16
cert_test_block_3 16640 38 608 624 16
cert_test_block_3 16640 39 624 640 16
theorem test16640_complete : Interval test16640 0 640 :=
  (interval_append test16640 0 320 640
  (interval_append test16640 0 160 320
  (interval_append test16640 0 80 160
  (interval_append test16640 0 32 80
  (interval_append test16640 0 16 32
  test16640_block_0
  test16640_block_1)
  (interval_append test16640 32 48 80
  test16640_block_2
  (interval_append test16640 48 64 80
  test16640_block_3
  test16640_block_4)))
  (interval_append test16640 80 112 160
  (interval_append test16640 80 96 112
  test16640_block_5
  test16640_block_6)
  (interval_append test16640 112 128 160
  test16640_block_7
  (interval_append test16640 128 144 160
  test16640_block_8
  test16640_block_9))))
  (interval_append test16640 160 240 320
  (interval_append test16640 160 192 240
  (interval_append test16640 160 176 192
  test16640_block_10
  test16640_block_11)
  (interval_append test16640 192 208 240
  test16640_block_12
  (interval_append test16640 208 224 240
  test16640_block_13
  test16640_block_14)))
  (interval_append test16640 240 272 320
  (interval_append test16640 240 256 272
  test16640_block_15
  test16640_block_16)
  (interval_append test16640 272 288 320
  test16640_block_17
  (interval_append test16640 288 304 320
  test16640_block_18
  test16640_block_19)))))
  (interval_append test16640 320 480 640
  (interval_append test16640 320 400 480
  (interval_append test16640 320 352 400
  (interval_append test16640 320 336 352
  test16640_block_20
  test16640_block_21)
  (interval_append test16640 352 368 400
  test16640_block_22
  (interval_append test16640 368 384 400
  test16640_block_23
  test16640_block_24)))
  (interval_append test16640 400 432 480
  (interval_append test16640 400 416 432
  test16640_block_25
  test16640_block_26)
  (interval_append test16640 432 448 480
  test16640_block_27
  (interval_append test16640 448 464 480
  test16640_block_28
  test16640_block_29))))
  (interval_append test16640 480 560 640
  (interval_append test16640 480 512 560
  (interval_append test16640 480 496 512
  test16640_block_30
  test16640_block_31)
  (interval_append test16640 512 528 560
  test16640_block_32
  (interval_append test16640 528 544 560
  test16640_block_33
  test16640_block_34)))
  (interval_append test16640 560 592 640
  (interval_append test16640 560 576 592
  test16640_block_35
  test16640_block_36)
  (interval_append test16640 592 608 640
  test16640_block_37
  (interval_append test16640 608 624 640
  test16640_block_38
  test16640_block_39))))))
cert_nodeInterval_3 16640 17280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 17280
cert_test_block_3 17280 0 0 16 16
cert_test_block_3 17280 1 16 32 16
cert_test_block_3 17280 2 32 48 16
cert_test_block_3 17280 3 48 64 16
cert_test_block_3 17280 4 64 80 16
cert_test_block_3 17280 5 80 96 16
cert_test_block_3 17280 6 96 112 16
cert_test_block_3 17280 7 112 128 16
cert_test_block_3 17280 8 128 144 16
cert_test_block_3 17280 9 144 160 16
cert_test_block_3 17280 10 160 176 16
cert_test_block_3 17280 11 176 192 16
cert_test_block_3 17280 12 192 208 16
cert_test_block_3 17280 13 208 224 16
cert_test_block_3 17280 14 224 240 16
cert_test_block_3 17280 15 240 256 16
cert_test_block_3 17280 16 256 272 16
cert_test_block_3 17280 17 272 288 16
cert_test_block_3 17280 18 288 304 16
cert_test_block_3 17280 19 304 320 16
cert_test_block_3 17280 20 320 336 16
cert_test_block_3 17280 21 336 352 16
cert_test_block_3 17280 22 352 368 16
cert_test_block_3 17280 23 368 384 16
cert_test_block_3 17280 24 384 400 16
cert_test_block_3 17280 25 400 416 16
cert_test_block_3 17280 26 416 432 16
cert_test_block_3 17280 27 432 448 16
cert_test_block_3 17280 28 448 464 16
cert_test_block_3 17280 29 464 480 16
cert_test_block_3 17280 30 480 496 16
cert_test_block_3 17280 31 496 512 16
cert_test_block_3 17280 32 512 528 16
cert_test_block_3 17280 33 528 544 16
cert_test_block_3 17280 34 544 560 16
cert_test_block_3 17280 35 560 576 16
cert_test_block_3 17280 36 576 592 16
cert_test_block_3 17280 37 592 608 16
cert_test_block_3 17280 38 608 624 16
cert_test_block_3 17280 39 624 640 16
theorem test17280_complete : Interval test17280 0 640 :=
  (interval_append test17280 0 320 640
  (interval_append test17280 0 160 320
  (interval_append test17280 0 80 160
  (interval_append test17280 0 32 80
  (interval_append test17280 0 16 32
  test17280_block_0
  test17280_block_1)
  (interval_append test17280 32 48 80
  test17280_block_2
  (interval_append test17280 48 64 80
  test17280_block_3
  test17280_block_4)))
  (interval_append test17280 80 112 160
  (interval_append test17280 80 96 112
  test17280_block_5
  test17280_block_6)
  (interval_append test17280 112 128 160
  test17280_block_7
  (interval_append test17280 128 144 160
  test17280_block_8
  test17280_block_9))))
  (interval_append test17280 160 240 320
  (interval_append test17280 160 192 240
  (interval_append test17280 160 176 192
  test17280_block_10
  test17280_block_11)
  (interval_append test17280 192 208 240
  test17280_block_12
  (interval_append test17280 208 224 240
  test17280_block_13
  test17280_block_14)))
  (interval_append test17280 240 272 320
  (interval_append test17280 240 256 272
  test17280_block_15
  test17280_block_16)
  (interval_append test17280 272 288 320
  test17280_block_17
  (interval_append test17280 288 304 320
  test17280_block_18
  test17280_block_19)))))
  (interval_append test17280 320 480 640
  (interval_append test17280 320 400 480
  (interval_append test17280 320 352 400
  (interval_append test17280 320 336 352
  test17280_block_20
  test17280_block_21)
  (interval_append test17280 352 368 400
  test17280_block_22
  (interval_append test17280 368 384 400
  test17280_block_23
  test17280_block_24)))
  (interval_append test17280 400 432 480
  (interval_append test17280 400 416 432
  test17280_block_25
  test17280_block_26)
  (interval_append test17280 432 448 480
  test17280_block_27
  (interval_append test17280 448 464 480
  test17280_block_28
  test17280_block_29))))
  (interval_append test17280 480 560 640
  (interval_append test17280 480 512 560
  (interval_append test17280 480 496 512
  test17280_block_30
  test17280_block_31)
  (interval_append test17280 512 528 560
  test17280_block_32
  (interval_append test17280 528 544 560
  test17280_block_33
  test17280_block_34)))
  (interval_append test17280 560 592 640
  (interval_append test17280 560 576 592
  test17280_block_35
  test17280_block_36)
  (interval_append test17280 592 608 640
  test17280_block_37
  (interval_append test17280 608 624 640
  test17280_block_38
  test17280_block_39))))))
cert_nodeInterval_3 17280 17920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 18560
cert_test_block_3 18560 0 0 16 16
cert_test_block_3 18560 1 16 32 16
cert_test_block_3 18560 2 32 48 16
cert_test_block_3 18560 3 48 64 16
cert_test_block_3 18560 4 64 80 16
cert_test_block_3 18560 5 80 96 16
cert_test_block_3 18560 6 96 112 16
cert_test_block_3 18560 7 112 128 16
cert_test_block_3 18560 8 128 144 16
cert_test_block_3 18560 9 144 160 16
cert_test_block_3 18560 10 160 176 16
cert_test_block_3 18560 11 176 192 16
cert_test_block_3 18560 12 192 208 16
cert_test_block_3 18560 13 208 224 16
cert_test_block_3 18560 14 224 240 16
cert_test_block_3 18560 15 240 256 16
cert_test_block_3 18560 16 256 272 16
cert_test_block_3 18560 17 272 288 16
cert_test_block_3 18560 18 288 304 16
cert_test_block_3 18560 19 304 320 16
cert_test_block_3 18560 20 320 336 16
cert_test_block_3 18560 21 336 352 16
cert_test_block_3 18560 22 352 368 16
cert_test_block_3 18560 23 368 384 16
cert_test_block_3 18560 24 384 400 16
cert_test_block_3 18560 25 400 416 16
cert_test_block_3 18560 26 416 432 16
cert_test_block_3 18560 27 432 448 16
cert_test_block_3 18560 28 448 464 16
cert_test_block_3 18560 29 464 480 16
cert_test_block_3 18560 30 480 496 16
cert_test_block_3 18560 31 496 512 16
cert_test_block_3 18560 32 512 528 16
cert_test_block_3 18560 33 528 544 16
cert_test_block_3 18560 34 544 560 16
cert_test_block_3 18560 35 560 576 16
cert_test_block_3 18560 36 576 592 16
cert_test_block_3 18560 37 592 608 16
cert_test_block_3 18560 38 608 624 16
cert_test_block_3 18560 39 624 640 16
theorem test18560_complete : Interval test18560 0 640 :=
  (interval_append test18560 0 320 640
  (interval_append test18560 0 160 320
  (interval_append test18560 0 80 160
  (interval_append test18560 0 32 80
  (interval_append test18560 0 16 32
  test18560_block_0
  test18560_block_1)
  (interval_append test18560 32 48 80
  test18560_block_2
  (interval_append test18560 48 64 80
  test18560_block_3
  test18560_block_4)))
  (interval_append test18560 80 112 160
  (interval_append test18560 80 96 112
  test18560_block_5
  test18560_block_6)
  (interval_append test18560 112 128 160
  test18560_block_7
  (interval_append test18560 128 144 160
  test18560_block_8
  test18560_block_9))))
  (interval_append test18560 160 240 320
  (interval_append test18560 160 192 240
  (interval_append test18560 160 176 192
  test18560_block_10
  test18560_block_11)
  (interval_append test18560 192 208 240
  test18560_block_12
  (interval_append test18560 208 224 240
  test18560_block_13
  test18560_block_14)))
  (interval_append test18560 240 272 320
  (interval_append test18560 240 256 272
  test18560_block_15
  test18560_block_16)
  (interval_append test18560 272 288 320
  test18560_block_17
  (interval_append test18560 288 304 320
  test18560_block_18
  test18560_block_19)))))
  (interval_append test18560 320 480 640
  (interval_append test18560 320 400 480
  (interval_append test18560 320 352 400
  (interval_append test18560 320 336 352
  test18560_block_20
  test18560_block_21)
  (interval_append test18560 352 368 400
  test18560_block_22
  (interval_append test18560 368 384 400
  test18560_block_23
  test18560_block_24)))
  (interval_append test18560 400 432 480
  (interval_append test18560 400 416 432
  test18560_block_25
  test18560_block_26)
  (interval_append test18560 432 448 480
  test18560_block_27
  (interval_append test18560 448 464 480
  test18560_block_28
  test18560_block_29))))
  (interval_append test18560 480 560 640
  (interval_append test18560 480 512 560
  (interval_append test18560 480 496 512
  test18560_block_30
  test18560_block_31)
  (interval_append test18560 512 528 560
  test18560_block_32
  (interval_append test18560 528 544 560
  test18560_block_33
  test18560_block_34)))
  (interval_append test18560 560 592 640
  (interval_append test18560 560 576 592
  test18560_block_35
  test18560_block_36)
  (interval_append test18560 592 608 640
  test18560_block_37
  (interval_append test18560 608 624 640
  test18560_block_38
  test18560_block_39))))))
cert_nodeInterval_3 18560 19200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 19200
cert_test_block_3 19200 0 0 16 16
cert_test_block_3 19200 1 16 32 16
cert_test_block_3 19200 2 32 48 16
cert_test_block_3 19200 3 48 64 16
cert_test_block_3 19200 4 64 80 16
cert_test_block_3 19200 5 80 96 16
cert_test_block_3 19200 6 96 112 16
cert_test_block_3 19200 7 112 128 16
cert_test_block_3 19200 8 128 144 16
cert_test_block_3 19200 9 144 160 16
cert_test_block_3 19200 10 160 176 16
cert_test_block_3 19200 11 176 192 16
cert_test_block_3 19200 12 192 208 16
cert_test_block_3 19200 13 208 224 16
cert_test_block_3 19200 14 224 240 16
cert_test_block_3 19200 15 240 256 16
cert_test_block_3 19200 16 256 272 16
cert_test_block_3 19200 17 272 288 16
cert_test_block_3 19200 18 288 304 16
cert_test_block_3 19200 19 304 320 16
cert_test_block_3 19200 20 320 336 16
cert_test_block_3 19200 21 336 352 16
cert_test_block_3 19200 22 352 368 16
cert_test_block_3 19200 23 368 384 16
cert_test_block_3 19200 24 384 400 16
cert_test_block_3 19200 25 400 416 16
cert_test_block_3 19200 26 416 432 16
cert_test_block_3 19200 27 432 448 16
cert_test_block_3 19200 28 448 464 16
cert_test_block_3 19200 29 464 480 16
cert_test_block_3 19200 30 480 496 16
cert_test_block_3 19200 31 496 512 16
cert_test_block_3 19200 32 512 528 16
cert_test_block_3 19200 33 528 544 16
cert_test_block_3 19200 34 544 560 16
cert_test_block_3 19200 35 560 576 16
cert_test_block_3 19200 36 576 592 16
cert_test_block_3 19200 37 592 608 16
cert_test_block_3 19200 38 608 624 16
cert_test_block_3 19200 39 624 640 16
theorem test19200_complete : Interval test19200 0 640 :=
  (interval_append test19200 0 320 640
  (interval_append test19200 0 160 320
  (interval_append test19200 0 80 160
  (interval_append test19200 0 32 80
  (interval_append test19200 0 16 32
  test19200_block_0
  test19200_block_1)
  (interval_append test19200 32 48 80
  test19200_block_2
  (interval_append test19200 48 64 80
  test19200_block_3
  test19200_block_4)))
  (interval_append test19200 80 112 160
  (interval_append test19200 80 96 112
  test19200_block_5
  test19200_block_6)
  (interval_append test19200 112 128 160
  test19200_block_7
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9))))
  (interval_append test19200 160 240 320
  (interval_append test19200 160 192 240
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11)
  (interval_append test19200 192 208 240
  test19200_block_12
  (interval_append test19200 208 224 240
  test19200_block_13
  test19200_block_14)))
  (interval_append test19200 240 272 320
  (interval_append test19200 240 256 272
  test19200_block_15
  test19200_block_16)
  (interval_append test19200 272 288 320
  test19200_block_17
  (interval_append test19200 288 304 320
  test19200_block_18
  test19200_block_19)))))
  (interval_append test19200 320 480 640
  (interval_append test19200 320 400 480
  (interval_append test19200 320 352 400
  (interval_append test19200 320 336 352
  test19200_block_20
  test19200_block_21)
  (interval_append test19200 352 368 400
  test19200_block_22
  (interval_append test19200 368 384 400
  test19200_block_23
  test19200_block_24)))
  (interval_append test19200 400 432 480
  (interval_append test19200 400 416 432
  test19200_block_25
  test19200_block_26)
  (interval_append test19200 432 448 480
  test19200_block_27
  (interval_append test19200 448 464 480
  test19200_block_28
  test19200_block_29))))
  (interval_append test19200 480 560 640
  (interval_append test19200 480 512 560
  (interval_append test19200 480 496 512
  test19200_block_30
  test19200_block_31)
  (interval_append test19200 512 528 560
  test19200_block_32
  (interval_append test19200 528 544 560
  test19200_block_33
  test19200_block_34)))
  (interval_append test19200 560 592 640
  (interval_append test19200 560 576 592
  test19200_block_35
  test19200_block_36)
  (interval_append test19200 592 608 640
  test19200_block_37
  (interval_append test19200 608 624 640
  test19200_block_38
  test19200_block_39))))))
cert_nodeInterval_3 19200 19840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 19840
cert_test_block_3 19840 0 0 16 16
cert_test_block_3 19840 1 16 32 16
cert_test_block_3 19840 2 32 48 16
cert_test_block_3 19840 3 48 64 16
cert_test_block_3 19840 4 64 80 16
cert_test_block_3 19840 5 80 96 16
cert_test_block_3 19840 6 96 112 16
cert_test_block_3 19840 7 112 128 16
cert_test_block_3 19840 8 128 144 16
cert_test_block_3 19840 9 144 160 16
cert_test_block_3 19840 10 160 176 16
cert_test_block_3 19840 11 176 192 16
cert_test_block_3 19840 12 192 208 16
cert_test_block_3 19840 13 208 224 16
cert_test_block_3 19840 14 224 240 16
cert_test_block_3 19840 15 240 256 16
cert_test_block_3 19840 16 256 272 16
cert_test_block_3 19840 17 272 288 16
cert_test_block_3 19840 18 288 304 16
cert_test_block_3 19840 19 304 320 16
cert_test_block_3 19840 20 320 336 16
cert_test_block_3 19840 21 336 352 16
cert_test_block_3 19840 22 352 368 16
cert_test_block_3 19840 23 368 384 16
cert_test_block_3 19840 24 384 400 16
cert_test_block_3 19840 25 400 416 16
cert_test_block_3 19840 26 416 432 16
cert_test_block_3 19840 27 432 448 16
cert_test_block_3 19840 28 448 464 16
cert_test_block_3 19840 29 464 480 16
cert_test_block_3 19840 30 480 496 16
cert_test_block_3 19840 31 496 512 16
cert_test_block_3 19840 32 512 528 16
cert_test_block_3 19840 33 528 544 16
cert_test_block_3 19840 34 544 560 16
cert_test_block_3 19840 35 560 576 16
cert_test_block_3 19840 36 576 592 16
cert_test_block_3 19840 37 592 608 16
cert_test_block_3 19840 38 608 624 16
cert_test_block_3 19840 39 624 640 16
theorem test19840_complete : Interval test19840 0 640 :=
  (interval_append test19840 0 320 640
  (interval_append test19840 0 160 320
  (interval_append test19840 0 80 160
  (interval_append test19840 0 32 80
  (interval_append test19840 0 16 32
  test19840_block_0
  test19840_block_1)
  (interval_append test19840 32 48 80
  test19840_block_2
  (interval_append test19840 48 64 80
  test19840_block_3
  test19840_block_4)))
  (interval_append test19840 80 112 160
  (interval_append test19840 80 96 112
  test19840_block_5
  test19840_block_6)
  (interval_append test19840 112 128 160
  test19840_block_7
  (interval_append test19840 128 144 160
  test19840_block_8
  test19840_block_9))))
  (interval_append test19840 160 240 320
  (interval_append test19840 160 192 240
  (interval_append test19840 160 176 192
  test19840_block_10
  test19840_block_11)
  (interval_append test19840 192 208 240
  test19840_block_12
  (interval_append test19840 208 224 240
  test19840_block_13
  test19840_block_14)))
  (interval_append test19840 240 272 320
  (interval_append test19840 240 256 272
  test19840_block_15
  test19840_block_16)
  (interval_append test19840 272 288 320
  test19840_block_17
  (interval_append test19840 288 304 320
  test19840_block_18
  test19840_block_19)))))
  (interval_append test19840 320 480 640
  (interval_append test19840 320 400 480
  (interval_append test19840 320 352 400
  (interval_append test19840 320 336 352
  test19840_block_20
  test19840_block_21)
  (interval_append test19840 352 368 400
  test19840_block_22
  (interval_append test19840 368 384 400
  test19840_block_23
  test19840_block_24)))
  (interval_append test19840 400 432 480
  (interval_append test19840 400 416 432
  test19840_block_25
  test19840_block_26)
  (interval_append test19840 432 448 480
  test19840_block_27
  (interval_append test19840 448 464 480
  test19840_block_28
  test19840_block_29))))
  (interval_append test19840 480 560 640
  (interval_append test19840 480 512 560
  (interval_append test19840 480 496 512
  test19840_block_30
  test19840_block_31)
  (interval_append test19840 512 528 560
  test19840_block_32
  (interval_append test19840 528 544 560
  test19840_block_33
  test19840_block_34)))
  (interval_append test19840 560 592 640
  (interval_append test19840 560 576 592
  test19840_block_35
  test19840_block_36)
  (interval_append test19840 592 608 640
  test19840_block_37
  (interval_append test19840 608 624 640
  test19840_block_38
  test19840_block_39))))))
cert_nodeInterval_3 19840 20480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 20480
cert_test_block_3 20480 0 0 16 16
cert_test_block_3 20480 1 16 32 16
cert_test_block_3 20480 2 32 48 16
cert_test_block_3 20480 3 48 64 16
cert_test_block_3 20480 4 64 80 16
cert_test_block_3 20480 5 80 96 16
cert_test_block_3 20480 6 96 112 16
cert_test_block_3 20480 7 112 128 16
cert_test_block_3 20480 8 128 144 16
cert_test_block_3 20480 9 144 160 16
cert_test_block_3 20480 10 160 176 16
cert_test_block_3 20480 11 176 192 16
cert_test_block_3 20480 12 192 208 16
cert_test_block_3 20480 13 208 224 16
cert_test_block_3 20480 14 224 240 16
cert_test_block_3 20480 15 240 256 16
cert_test_block_3 20480 16 256 272 16
cert_test_block_3 20480 17 272 288 16
cert_test_block_3 20480 18 288 304 16
cert_test_block_3 20480 19 304 320 16
cert_test_block_3 20480 20 320 336 16
cert_test_block_3 20480 21 336 352 16
cert_test_block_3 20480 22 352 368 16
cert_test_block_3 20480 23 368 384 16
cert_test_block_3 20480 24 384 400 16
cert_test_block_3 20480 25 400 416 16
cert_test_block_3 20480 26 416 432 16
cert_test_block_3 20480 27 432 448 16
cert_test_block_3 20480 28 448 464 16
cert_test_block_3 20480 29 464 480 16
cert_test_block_3 20480 30 480 496 16
cert_test_block_3 20480 31 496 512 16
cert_test_block_3 20480 32 512 528 16
cert_test_block_3 20480 33 528 544 16
cert_test_block_3 20480 34 544 560 16
cert_test_block_3 20480 35 560 576 16
cert_test_block_3 20480 36 576 592 16
cert_test_block_3 20480 37 592 608 16
cert_test_block_3 20480 38 608 624 16
cert_test_block_3 20480 39 624 640 16
theorem test20480_complete : Interval test20480 0 640 :=
  (interval_append test20480 0 320 640
  (interval_append test20480 0 160 320
  (interval_append test20480 0 80 160
  (interval_append test20480 0 32 80
  (interval_append test20480 0 16 32
  test20480_block_0
  test20480_block_1)
  (interval_append test20480 32 48 80
  test20480_block_2
  (interval_append test20480 48 64 80
  test20480_block_3
  test20480_block_4)))
  (interval_append test20480 80 112 160
  (interval_append test20480 80 96 112
  test20480_block_5
  test20480_block_6)
  (interval_append test20480 112 128 160
  test20480_block_7
  (interval_append test20480 128 144 160
  test20480_block_8
  test20480_block_9))))
  (interval_append test20480 160 240 320
  (interval_append test20480 160 192 240
  (interval_append test20480 160 176 192
  test20480_block_10
  test20480_block_11)
  (interval_append test20480 192 208 240
  test20480_block_12
  (interval_append test20480 208 224 240
  test20480_block_13
  test20480_block_14)))
  (interval_append test20480 240 272 320
  (interval_append test20480 240 256 272
  test20480_block_15
  test20480_block_16)
  (interval_append test20480 272 288 320
  test20480_block_17
  (interval_append test20480 288 304 320
  test20480_block_18
  test20480_block_19)))))
  (interval_append test20480 320 480 640
  (interval_append test20480 320 400 480
  (interval_append test20480 320 352 400
  (interval_append test20480 320 336 352
  test20480_block_20
  test20480_block_21)
  (interval_append test20480 352 368 400
  test20480_block_22
  (interval_append test20480 368 384 400
  test20480_block_23
  test20480_block_24)))
  (interval_append test20480 400 432 480
  (interval_append test20480 400 416 432
  test20480_block_25
  test20480_block_26)
  (interval_append test20480 432 448 480
  test20480_block_27
  (interval_append test20480 448 464 480
  test20480_block_28
  test20480_block_29))))
  (interval_append test20480 480 560 640
  (interval_append test20480 480 512 560
  (interval_append test20480 480 496 512
  test20480_block_30
  test20480_block_31)
  (interval_append test20480 512 528 560
  test20480_block_32
  (interval_append test20480 528 544 560
  test20480_block_33
  test20480_block_34)))
  (interval_append test20480 560 592 640
  (interval_append test20480 560 576 592
  test20480_block_35
  test20480_block_36)
  (interval_append test20480 592 608 640
  test20480_block_37
  (interval_append test20480 608 624 640
  test20480_block_38
  test20480_block_39))))))
cert_nodeInterval_3 20480 21120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 21120
cert_test_block_3 21120 0 0 16 16
cert_test_block_3 21120 1 16 32 16
cert_test_block_3 21120 2 32 48 16
cert_test_block_3 21120 3 48 64 16
cert_test_block_3 21120 4 64 80 16
cert_test_block_3 21120 5 80 96 16
cert_test_block_3 21120 6 96 112 16
cert_test_block_3 21120 7 112 128 16
cert_test_block_3 21120 8 128 144 16
cert_test_block_3 21120 9 144 160 16
cert_test_block_3 21120 10 160 176 16
cert_test_block_3 21120 11 176 192 16
cert_test_block_3 21120 12 192 208 16
cert_test_block_3 21120 13 208 224 16
cert_test_block_3 21120 14 224 240 16
cert_test_block_3 21120 15 240 256 16
cert_test_block_3 21120 16 256 272 16
cert_test_block_3 21120 17 272 288 16
cert_test_block_3 21120 18 288 304 16
cert_test_block_3 21120 19 304 320 16
cert_test_block_3 21120 20 320 336 16
cert_test_block_3 21120 21 336 352 16
cert_test_block_3 21120 22 352 368 16
cert_test_block_3 21120 23 368 384 16
cert_test_block_3 21120 24 384 400 16
cert_test_block_3 21120 25 400 416 16
cert_test_block_3 21120 26 416 432 16
cert_test_block_3 21120 27 432 448 16
cert_test_block_3 21120 28 448 464 16
cert_test_block_3 21120 29 464 480 16
cert_test_block_3 21120 30 480 496 16
cert_test_block_3 21120 31 496 512 16
cert_test_block_3 21120 32 512 528 16
cert_test_block_3 21120 33 528 544 16
cert_test_block_3 21120 34 544 560 16
cert_test_block_3 21120 35 560 576 16
cert_test_block_3 21120 36 576 592 16
cert_test_block_3 21120 37 592 608 16
cert_test_block_3 21120 38 608 624 16
cert_test_block_3 21120 39 624 640 16
theorem test21120_complete : Interval test21120 0 640 :=
  (interval_append test21120 0 320 640
  (interval_append test21120 0 160 320
  (interval_append test21120 0 80 160
  (interval_append test21120 0 32 80
  (interval_append test21120 0 16 32
  test21120_block_0
  test21120_block_1)
  (interval_append test21120 32 48 80
  test21120_block_2
  (interval_append test21120 48 64 80
  test21120_block_3
  test21120_block_4)))
  (interval_append test21120 80 112 160
  (interval_append test21120 80 96 112
  test21120_block_5
  test21120_block_6)
  (interval_append test21120 112 128 160
  test21120_block_7
  (interval_append test21120 128 144 160
  test21120_block_8
  test21120_block_9))))
  (interval_append test21120 160 240 320
  (interval_append test21120 160 192 240
  (interval_append test21120 160 176 192
  test21120_block_10
  test21120_block_11)
  (interval_append test21120 192 208 240
  test21120_block_12
  (interval_append test21120 208 224 240
  test21120_block_13
  test21120_block_14)))
  (interval_append test21120 240 272 320
  (interval_append test21120 240 256 272
  test21120_block_15
  test21120_block_16)
  (interval_append test21120 272 288 320
  test21120_block_17
  (interval_append test21120 288 304 320
  test21120_block_18
  test21120_block_19)))))
  (interval_append test21120 320 480 640
  (interval_append test21120 320 400 480
  (interval_append test21120 320 352 400
  (interval_append test21120 320 336 352
  test21120_block_20
  test21120_block_21)
  (interval_append test21120 352 368 400
  test21120_block_22
  (interval_append test21120 368 384 400
  test21120_block_23
  test21120_block_24)))
  (interval_append test21120 400 432 480
  (interval_append test21120 400 416 432
  test21120_block_25
  test21120_block_26)
  (interval_append test21120 432 448 480
  test21120_block_27
  (interval_append test21120 448 464 480
  test21120_block_28
  test21120_block_29))))
  (interval_append test21120 480 560 640
  (interval_append test21120 480 512 560
  (interval_append test21120 480 496 512
  test21120_block_30
  test21120_block_31)
  (interval_append test21120 512 528 560
  test21120_block_32
  (interval_append test21120 528 544 560
  test21120_block_33
  test21120_block_34)))
  (interval_append test21120 560 592 640
  (interval_append test21120 560 576 592
  test21120_block_35
  test21120_block_36)
  (interval_append test21120 592 608 640
  test21120_block_37
  (interval_append test21120 608 624 640
  test21120_block_38
  test21120_block_39))))))
cert_nodeInterval_3 21120 21760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 21760
cert_test_block_3 21760 0 0 16 16
cert_test_block_3 21760 1 16 32 16
cert_test_block_3 21760 2 32 48 16
cert_test_block_3 21760 3 48 64 16
cert_test_block_3 21760 4 64 80 16
cert_test_block_3 21760 5 80 96 16
cert_test_block_3 21760 6 96 112 16
cert_test_block_3 21760 7 112 128 16
cert_test_block_3 21760 8 128 144 16
cert_test_block_3 21760 9 144 160 16
cert_test_block_3 21760 10 160 176 16
cert_test_block_3 21760 11 176 192 16
cert_test_block_3 21760 12 192 208 16
cert_test_block_3 21760 13 208 224 16
cert_test_block_3 21760 14 224 240 16
cert_test_block_3 21760 15 240 256 16
cert_test_block_3 21760 16 256 272 16
cert_test_block_3 21760 17 272 288 16
cert_test_block_3 21760 18 288 304 16
cert_test_block_3 21760 19 304 320 16
cert_test_block_3 21760 20 320 336 16
cert_test_block_3 21760 21 336 352 16
cert_test_block_3 21760 22 352 368 16
cert_test_block_3 21760 23 368 384 16
cert_test_block_3 21760 24 384 400 16
cert_test_block_3 21760 25 400 416 16
cert_test_block_3 21760 26 416 432 16
cert_test_block_3 21760 27 432 448 16
cert_test_block_3 21760 28 448 464 16
cert_test_block_3 21760 29 464 480 16
cert_test_block_3 21760 30 480 496 16
cert_test_block_3 21760 31 496 512 16
cert_test_block_3 21760 32 512 528 16
cert_test_block_3 21760 33 528 544 16
cert_test_block_3 21760 34 544 560 16
cert_test_block_3 21760 35 560 576 16
cert_test_block_3 21760 36 576 592 16
cert_test_block_3 21760 37 592 608 16
cert_test_block_3 21760 38 608 624 16
cert_test_block_3 21760 39 624 640 16
theorem test21760_complete : Interval test21760 0 640 :=
  (interval_append test21760 0 320 640
  (interval_append test21760 0 160 320
  (interval_append test21760 0 80 160
  (interval_append test21760 0 32 80
  (interval_append test21760 0 16 32
  test21760_block_0
  test21760_block_1)
  (interval_append test21760 32 48 80
  test21760_block_2
  (interval_append test21760 48 64 80
  test21760_block_3
  test21760_block_4)))
  (interval_append test21760 80 112 160
  (interval_append test21760 80 96 112
  test21760_block_5
  test21760_block_6)
  (interval_append test21760 112 128 160
  test21760_block_7
  (interval_append test21760 128 144 160
  test21760_block_8
  test21760_block_9))))
  (interval_append test21760 160 240 320
  (interval_append test21760 160 192 240
  (interval_append test21760 160 176 192
  test21760_block_10
  test21760_block_11)
  (interval_append test21760 192 208 240
  test21760_block_12
  (interval_append test21760 208 224 240
  test21760_block_13
  test21760_block_14)))
  (interval_append test21760 240 272 320
  (interval_append test21760 240 256 272
  test21760_block_15
  test21760_block_16)
  (interval_append test21760 272 288 320
  test21760_block_17
  (interval_append test21760 288 304 320
  test21760_block_18
  test21760_block_19)))))
  (interval_append test21760 320 480 640
  (interval_append test21760 320 400 480
  (interval_append test21760 320 352 400
  (interval_append test21760 320 336 352
  test21760_block_20
  test21760_block_21)
  (interval_append test21760 352 368 400
  test21760_block_22
  (interval_append test21760 368 384 400
  test21760_block_23
  test21760_block_24)))
  (interval_append test21760 400 432 480
  (interval_append test21760 400 416 432
  test21760_block_25
  test21760_block_26)
  (interval_append test21760 432 448 480
  test21760_block_27
  (interval_append test21760 448 464 480
  test21760_block_28
  test21760_block_29))))
  (interval_append test21760 480 560 640
  (interval_append test21760 480 512 560
  (interval_append test21760 480 496 512
  test21760_block_30
  test21760_block_31)
  (interval_append test21760 512 528 560
  test21760_block_32
  (interval_append test21760 528 544 560
  test21760_block_33
  test21760_block_34)))
  (interval_append test21760 560 592 640
  (interval_append test21760 560 576 592
  test21760_block_35
  test21760_block_36)
  (interval_append test21760 592 608 640
  test21760_block_37
  (interval_append test21760 608 624 640
  test21760_block_38
  test21760_block_39))))))
cert_nodeInterval_3 21760 22400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 22400
cert_test_block_3 22400 0 0 16 16
cert_test_block_3 22400 1 16 32 16
cert_test_block_3 22400 2 32 48 16
cert_test_block_3 22400 3 48 64 16
cert_test_block_3 22400 4 64 80 16
cert_test_block_3 22400 5 80 96 16
cert_test_block_3 22400 6 96 112 16
cert_test_block_3 22400 7 112 128 16
cert_test_block_3 22400 8 128 144 16
cert_test_block_3 22400 9 144 160 16
cert_test_block_3 22400 10 160 176 16
cert_test_block_3 22400 11 176 192 16
cert_test_block_3 22400 12 192 208 16
cert_test_block_3 22400 13 208 224 16
cert_test_block_3 22400 14 224 240 16
cert_test_block_3 22400 15 240 256 16
cert_test_block_3 22400 16 256 272 16
cert_test_block_3 22400 17 272 288 16
cert_test_block_3 22400 18 288 304 16
cert_test_block_3 22400 19 304 320 16
cert_test_block_3 22400 20 320 336 16
cert_test_block_3 22400 21 336 352 16
cert_test_block_3 22400 22 352 368 16
cert_test_block_3 22400 23 368 384 16
cert_test_block_3 22400 24 384 400 16
cert_test_block_3 22400 25 400 416 16
cert_test_block_3 22400 26 416 432 16
cert_test_block_3 22400 27 432 448 16
cert_test_block_3 22400 28 448 464 16
cert_test_block_3 22400 29 464 480 16
cert_test_block_3 22400 30 480 496 16
cert_test_block_3 22400 31 496 512 16
cert_test_block_3 22400 32 512 528 16
cert_test_block_3 22400 33 528 544 16
cert_test_block_3 22400 34 544 560 16
cert_test_block_3 22400 35 560 576 16
cert_test_block_3 22400 36 576 592 16
cert_test_block_3 22400 37 592 608 16
cert_test_block_3 22400 38 608 624 16
cert_test_block_3 22400 39 624 640 16
theorem test22400_complete : Interval test22400 0 640 :=
  (interval_append test22400 0 320 640
  (interval_append test22400 0 160 320
  (interval_append test22400 0 80 160
  (interval_append test22400 0 32 80
  (interval_append test22400 0 16 32
  test22400_block_0
  test22400_block_1)
  (interval_append test22400 32 48 80
  test22400_block_2
  (interval_append test22400 48 64 80
  test22400_block_3
  test22400_block_4)))
  (interval_append test22400 80 112 160
  (interval_append test22400 80 96 112
  test22400_block_5
  test22400_block_6)
  (interval_append test22400 112 128 160
  test22400_block_7
  (interval_append test22400 128 144 160
  test22400_block_8
  test22400_block_9))))
  (interval_append test22400 160 240 320
  (interval_append test22400 160 192 240
  (interval_append test22400 160 176 192
  test22400_block_10
  test22400_block_11)
  (interval_append test22400 192 208 240
  test22400_block_12
  (interval_append test22400 208 224 240
  test22400_block_13
  test22400_block_14)))
  (interval_append test22400 240 272 320
  (interval_append test22400 240 256 272
  test22400_block_15
  test22400_block_16)
  (interval_append test22400 272 288 320
  test22400_block_17
  (interval_append test22400 288 304 320
  test22400_block_18
  test22400_block_19)))))
  (interval_append test22400 320 480 640
  (interval_append test22400 320 400 480
  (interval_append test22400 320 352 400
  (interval_append test22400 320 336 352
  test22400_block_20
  test22400_block_21)
  (interval_append test22400 352 368 400
  test22400_block_22
  (interval_append test22400 368 384 400
  test22400_block_23
  test22400_block_24)))
  (interval_append test22400 400 432 480
  (interval_append test22400 400 416 432
  test22400_block_25
  test22400_block_26)
  (interval_append test22400 432 448 480
  test22400_block_27
  (interval_append test22400 448 464 480
  test22400_block_28
  test22400_block_29))))
  (interval_append test22400 480 560 640
  (interval_append test22400 480 512 560
  (interval_append test22400 480 496 512
  test22400_block_30
  test22400_block_31)
  (interval_append test22400 512 528 560
  test22400_block_32
  (interval_append test22400 528 544 560
  test22400_block_33
  test22400_block_34)))
  (interval_append test22400 560 592 640
  (interval_append test22400 560 576 592
  test22400_block_35
  test22400_block_36)
  (interval_append test22400 592 608 640
  test22400_block_37
  (interval_append test22400 608 624 640
  test22400_block_38
  test22400_block_39))))))
cert_nodeInterval_3 22400 23040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 23040
cert_test_block_3 23040 0 0 16 16
cert_test_block_3 23040 1 16 32 16
cert_test_block_3 23040 2 32 48 16
cert_test_block_3 23040 3 48 64 16
cert_test_block_3 23040 4 64 80 16
cert_test_block_3 23040 5 80 96 16
cert_test_block_3 23040 6 96 112 16
cert_test_block_3 23040 7 112 128 16
cert_test_block_3 23040 8 128 144 16
cert_test_block_3 23040 9 144 160 16
cert_test_block_3 23040 10 160 176 16
cert_test_block_3 23040 11 176 192 16
cert_test_block_3 23040 12 192 208 16
cert_test_block_3 23040 13 208 224 16
cert_test_block_3 23040 14 224 240 16
cert_test_block_3 23040 15 240 256 16
cert_test_block_3 23040 16 256 272 16
cert_test_block_3 23040 17 272 288 16
cert_test_block_3 23040 18 288 304 16
cert_test_block_3 23040 19 304 320 16
cert_test_block_3 23040 20 320 336 16
cert_test_block_3 23040 21 336 352 16
cert_test_block_3 23040 22 352 368 16
cert_test_block_3 23040 23 368 384 16
cert_test_block_3 23040 24 384 400 16
cert_test_block_3 23040 25 400 416 16
cert_test_block_3 23040 26 416 432 16
cert_test_block_3 23040 27 432 448 16
cert_test_block_3 23040 28 448 464 16
cert_test_block_3 23040 29 464 480 16
cert_test_block_3 23040 30 480 496 16
cert_test_block_3 23040 31 496 512 16
cert_test_block_3 23040 32 512 528 16
cert_test_block_3 23040 33 528 544 16
cert_test_block_3 23040 34 544 560 16
cert_test_block_3 23040 35 560 576 16
cert_test_block_3 23040 36 576 592 16
cert_test_block_3 23040 37 592 608 16
cert_test_block_3 23040 38 608 624 16
cert_test_block_3 23040 39 624 640 16
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
cert_nodeInterval_3 23040 23680
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
end
end
