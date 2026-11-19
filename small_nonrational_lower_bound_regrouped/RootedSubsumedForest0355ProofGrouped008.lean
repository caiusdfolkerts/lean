module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
cert_test_11 61440
cert_test_block_3 61440 0 0 16 16
cert_test_block_3 61440 1 16 32 16
cert_test_block_3 61440 2 32 48 16
cert_test_block_3 61440 3 48 64 16
cert_test_block_3 61440 4 64 80 16
cert_test_block_3 61440 5 80 96 16
cert_test_block_3 61440 6 96 112 16
cert_test_block_3 61440 7 112 128 16
cert_test_block_3 61440 8 128 144 16
cert_test_block_3 61440 9 144 160 16
cert_test_block_3 61440 10 160 176 16
cert_test_block_3 61440 11 176 192 16
cert_test_block_3 61440 12 192 208 16
cert_test_block_3 61440 13 208 224 16
cert_test_block_3 61440 14 224 240 16
cert_test_block_3 61440 15 240 256 16
cert_test_block_3 61440 16 256 272 16
cert_test_block_3 61440 17 272 288 16
cert_test_block_3 61440 18 288 304 16
cert_test_block_3 61440 19 304 320 16
cert_test_block_3 61440 20 320 336 16
cert_test_block_3 61440 21 336 352 16
cert_test_block_3 61440 22 352 368 16
cert_test_block_3 61440 23 368 384 16
cert_test_block_3 61440 24 384 400 16
cert_test_block_3 61440 25 400 416 16
cert_test_block_3 61440 26 416 432 16
cert_test_block_3 61440 27 432 448 16
cert_test_block_3 61440 28 448 464 16
cert_test_block_3 61440 29 464 480 16
cert_test_block_3 61440 30 480 496 16
cert_test_block_3 61440 31 496 512 16
cert_test_block_3 61440 32 512 528 16
cert_test_block_3 61440 33 528 544 16
cert_test_block_3 61440 34 544 560 16
cert_test_block_3 61440 35 560 576 16
cert_test_block_3 61440 36 576 592 16
cert_test_block_3 61440 37 592 608 16
cert_test_block_3 61440 38 608 624 16
cert_test_block_3 61440 39 624 640 16
theorem test61440_complete : Interval test61440 0 640 :=
  (interval_append test61440 0 320 640
  (interval_append test61440 0 160 320
  (interval_append test61440 0 80 160
  (interval_append test61440 0 32 80
  (interval_append test61440 0 16 32
  test61440_block_0
  test61440_block_1)
  (interval_append test61440 32 48 80
  test61440_block_2
  (interval_append test61440 48 64 80
  test61440_block_3
  test61440_block_4)))
  (interval_append test61440 80 112 160
  (interval_append test61440 80 96 112
  test61440_block_5
  test61440_block_6)
  (interval_append test61440 112 128 160
  test61440_block_7
  (interval_append test61440 128 144 160
  test61440_block_8
  test61440_block_9))))
  (interval_append test61440 160 240 320
  (interval_append test61440 160 192 240
  (interval_append test61440 160 176 192
  test61440_block_10
  test61440_block_11)
  (interval_append test61440 192 208 240
  test61440_block_12
  (interval_append test61440 208 224 240
  test61440_block_13
  test61440_block_14)))
  (interval_append test61440 240 272 320
  (interval_append test61440 240 256 272
  test61440_block_15
  test61440_block_16)
  (interval_append test61440 272 288 320
  test61440_block_17
  (interval_append test61440 288 304 320
  test61440_block_18
  test61440_block_19)))))
  (interval_append test61440 320 480 640
  (interval_append test61440 320 400 480
  (interval_append test61440 320 352 400
  (interval_append test61440 320 336 352
  test61440_block_20
  test61440_block_21)
  (interval_append test61440 352 368 400
  test61440_block_22
  (interval_append test61440 368 384 400
  test61440_block_23
  test61440_block_24)))
  (interval_append test61440 400 432 480
  (interval_append test61440 400 416 432
  test61440_block_25
  test61440_block_26)
  (interval_append test61440 432 448 480
  test61440_block_27
  (interval_append test61440 448 464 480
  test61440_block_28
  test61440_block_29))))
  (interval_append test61440 480 560 640
  (interval_append test61440 480 512 560
  (interval_append test61440 480 496 512
  test61440_block_30
  test61440_block_31)
  (interval_append test61440 512 528 560
  test61440_block_32
  (interval_append test61440 528 544 560
  test61440_block_33
  test61440_block_34)))
  (interval_append test61440 560 592 640
  (interval_append test61440 560 576 592
  test61440_block_35
  test61440_block_36)
  (interval_append test61440 592 608 640
  test61440_block_37
  (interval_append test61440 608 624 640
  test61440_block_38
  test61440_block_39))))))
cert_nodeInterval_3 61440 62080
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 62080
cert_test_block_3 62080 0 0 16 16
cert_test_block_3 62080 1 16 32 16
cert_test_block_3 62080 2 32 48 16
cert_test_block_3 62080 3 48 64 16
cert_test_block_3 62080 4 64 80 16
cert_test_block_3 62080 5 80 96 16
cert_test_block_3 62080 6 96 112 16
cert_test_block_3 62080 7 112 128 16
cert_test_block_3 62080 8 128 144 16
cert_test_block_3 62080 9 144 160 16
cert_test_block_3 62080 10 160 176 16
cert_test_block_3 62080 11 176 192 16
cert_test_block_3 62080 12 192 208 16
cert_test_block_3 62080 13 208 224 16
cert_test_block_3 62080 14 224 240 16
cert_test_block_3 62080 15 240 256 16
cert_test_block_3 62080 16 256 272 16
cert_test_block_3 62080 17 272 288 16
cert_test_block_3 62080 18 288 304 16
cert_test_block_3 62080 19 304 320 16
cert_test_block_3 62080 20 320 336 16
cert_test_block_3 62080 21 336 352 16
cert_test_block_3 62080 22 352 368 16
cert_test_block_3 62080 23 368 384 16
cert_test_block_3 62080 24 384 400 16
cert_test_block_3 62080 25 400 416 16
cert_test_block_3 62080 26 416 432 16
cert_test_block_3 62080 27 432 448 16
cert_test_block_3 62080 28 448 464 16
cert_test_block_3 62080 29 464 480 16
cert_test_block_3 62080 30 480 496 16
cert_test_block_3 62080 31 496 512 16
cert_test_block_3 62080 32 512 528 16
cert_test_block_3 62080 33 528 544 16
cert_test_block_3 62080 34 544 560 16
cert_test_block_3 62080 35 560 576 16
cert_test_block_3 62080 36 576 592 16
cert_test_block_3 62080 37 592 608 16
cert_test_block_3 62080 38 608 624 16
cert_test_block_3 62080 39 624 640 16
theorem test62080_complete : Interval test62080 0 640 :=
  (interval_append test62080 0 320 640
  (interval_append test62080 0 160 320
  (interval_append test62080 0 80 160
  (interval_append test62080 0 32 80
  (interval_append test62080 0 16 32
  test62080_block_0
  test62080_block_1)
  (interval_append test62080 32 48 80
  test62080_block_2
  (interval_append test62080 48 64 80
  test62080_block_3
  test62080_block_4)))
  (interval_append test62080 80 112 160
  (interval_append test62080 80 96 112
  test62080_block_5
  test62080_block_6)
  (interval_append test62080 112 128 160
  test62080_block_7
  (interval_append test62080 128 144 160
  test62080_block_8
  test62080_block_9))))
  (interval_append test62080 160 240 320
  (interval_append test62080 160 192 240
  (interval_append test62080 160 176 192
  test62080_block_10
  test62080_block_11)
  (interval_append test62080 192 208 240
  test62080_block_12
  (interval_append test62080 208 224 240
  test62080_block_13
  test62080_block_14)))
  (interval_append test62080 240 272 320
  (interval_append test62080 240 256 272
  test62080_block_15
  test62080_block_16)
  (interval_append test62080 272 288 320
  test62080_block_17
  (interval_append test62080 288 304 320
  test62080_block_18
  test62080_block_19)))))
  (interval_append test62080 320 480 640
  (interval_append test62080 320 400 480
  (interval_append test62080 320 352 400
  (interval_append test62080 320 336 352
  test62080_block_20
  test62080_block_21)
  (interval_append test62080 352 368 400
  test62080_block_22
  (interval_append test62080 368 384 400
  test62080_block_23
  test62080_block_24)))
  (interval_append test62080 400 432 480
  (interval_append test62080 400 416 432
  test62080_block_25
  test62080_block_26)
  (interval_append test62080 432 448 480
  test62080_block_27
  (interval_append test62080 448 464 480
  test62080_block_28
  test62080_block_29))))
  (interval_append test62080 480 560 640
  (interval_append test62080 480 512 560
  (interval_append test62080 480 496 512
  test62080_block_30
  test62080_block_31)
  (interval_append test62080 512 528 560
  test62080_block_32
  (interval_append test62080 528 544 560
  test62080_block_33
  test62080_block_34)))
  (interval_append test62080 560 592 640
  (interval_append test62080 560 576 592
  test62080_block_35
  test62080_block_36)
  (interval_append test62080 592 608 640
  test62080_block_37
  (interval_append test62080 608 624 640
  test62080_block_38
  test62080_block_39))))))
cert_nodeInterval_3 62080 62720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 62720
cert_test_block_3 62720 0 0 16 16
cert_test_block_3 62720 1 16 32 16
cert_test_block_3 62720 2 32 48 16
cert_test_block_3 62720 3 48 64 16
cert_test_block_3 62720 4 64 80 16
cert_test_block_3 62720 5 80 96 16
cert_test_block_3 62720 6 96 112 16
cert_test_block_3 62720 7 112 128 16
cert_test_block_3 62720 8 128 144 16
cert_test_block_3 62720 9 144 160 16
cert_test_block_3 62720 10 160 176 16
cert_test_block_3 62720 11 176 192 16
cert_test_block_3 62720 12 192 208 16
cert_test_block_3 62720 13 208 224 16
cert_test_block_3 62720 14 224 240 16
cert_test_block_3 62720 15 240 256 16
cert_test_block_3 62720 16 256 272 16
cert_test_block_3 62720 17 272 288 16
cert_test_block_3 62720 18 288 304 16
cert_test_block_3 62720 19 304 320 16
cert_test_block_3 62720 20 320 336 16
cert_test_block_3 62720 21 336 352 16
cert_test_block_3 62720 22 352 368 16
cert_test_block_3 62720 23 368 384 16
cert_test_block_3 62720 24 384 400 16
cert_test_block_3 62720 25 400 416 16
cert_test_block_3 62720 26 416 432 16
cert_test_block_3 62720 27 432 448 16
cert_test_block_3 62720 28 448 464 16
cert_test_block_3 62720 29 464 480 16
cert_test_block_3 62720 30 480 496 16
cert_test_block_3 62720 31 496 512 16
cert_test_block_3 62720 32 512 528 16
cert_test_block_3 62720 33 528 544 16
cert_test_block_3 62720 34 544 560 16
cert_test_block_3 62720 35 560 576 16
cert_test_block_3 62720 36 576 592 16
cert_test_block_3 62720 37 592 608 16
cert_test_block_3 62720 38 608 624 16
cert_test_block_3 62720 39 624 640 16
theorem test62720_complete : Interval test62720 0 640 :=
  (interval_append test62720 0 320 640
  (interval_append test62720 0 160 320
  (interval_append test62720 0 80 160
  (interval_append test62720 0 32 80
  (interval_append test62720 0 16 32
  test62720_block_0
  test62720_block_1)
  (interval_append test62720 32 48 80
  test62720_block_2
  (interval_append test62720 48 64 80
  test62720_block_3
  test62720_block_4)))
  (interval_append test62720 80 112 160
  (interval_append test62720 80 96 112
  test62720_block_5
  test62720_block_6)
  (interval_append test62720 112 128 160
  test62720_block_7
  (interval_append test62720 128 144 160
  test62720_block_8
  test62720_block_9))))
  (interval_append test62720 160 240 320
  (interval_append test62720 160 192 240
  (interval_append test62720 160 176 192
  test62720_block_10
  test62720_block_11)
  (interval_append test62720 192 208 240
  test62720_block_12
  (interval_append test62720 208 224 240
  test62720_block_13
  test62720_block_14)))
  (interval_append test62720 240 272 320
  (interval_append test62720 240 256 272
  test62720_block_15
  test62720_block_16)
  (interval_append test62720 272 288 320
  test62720_block_17
  (interval_append test62720 288 304 320
  test62720_block_18
  test62720_block_19)))))
  (interval_append test62720 320 480 640
  (interval_append test62720 320 400 480
  (interval_append test62720 320 352 400
  (interval_append test62720 320 336 352
  test62720_block_20
  test62720_block_21)
  (interval_append test62720 352 368 400
  test62720_block_22
  (interval_append test62720 368 384 400
  test62720_block_23
  test62720_block_24)))
  (interval_append test62720 400 432 480
  (interval_append test62720 400 416 432
  test62720_block_25
  test62720_block_26)
  (interval_append test62720 432 448 480
  test62720_block_27
  (interval_append test62720 448 464 480
  test62720_block_28
  test62720_block_29))))
  (interval_append test62720 480 560 640
  (interval_append test62720 480 512 560
  (interval_append test62720 480 496 512
  test62720_block_30
  test62720_block_31)
  (interval_append test62720 512 528 560
  test62720_block_32
  (interval_append test62720 528 544 560
  test62720_block_33
  test62720_block_34)))
  (interval_append test62720 560 592 640
  (interval_append test62720 560 576 592
  test62720_block_35
  test62720_block_36)
  (interval_append test62720 592 608 640
  test62720_block_37
  (interval_append test62720 608 624 640
  test62720_block_38
  test62720_block_39))))))
cert_nodeInterval_3 62720 63360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 63360
cert_test_block_3 63360 0 0 16 16
cert_test_block_3 63360 1 16 32 16
cert_test_block_3 63360 2 32 48 16
cert_test_block_3 63360 3 48 64 16
cert_test_block_3 63360 4 64 80 16
cert_test_block_3 63360 5 80 96 16
cert_test_block_3 63360 6 96 112 16
cert_test_block_3 63360 7 112 128 16
cert_test_block_3 63360 8 128 144 16
cert_test_block_3 63360 9 144 160 16
cert_test_block_3 63360 10 160 176 16
cert_test_block_3 63360 11 176 192 16
cert_test_block_3 63360 12 192 208 16
cert_test_block_3 63360 13 208 224 16
cert_test_block_3 63360 14 224 240 16
cert_test_block_3 63360 15 240 256 16
cert_test_block_3 63360 16 256 272 16
cert_test_block_3 63360 17 272 288 16
cert_test_block_3 63360 18 288 304 16
cert_test_block_3 63360 19 304 320 16
cert_test_block_3 63360 20 320 336 16
cert_test_block_3 63360 21 336 352 16
cert_test_block_3 63360 22 352 368 16
cert_test_block_3 63360 23 368 384 16
cert_test_block_3 63360 24 384 400 16
cert_test_block_3 63360 25 400 416 16
cert_test_block_3 63360 26 416 432 16
cert_test_block_3 63360 27 432 448 16
cert_test_block_3 63360 28 448 464 16
cert_test_block_3 63360 29 464 480 16
cert_test_block_3 63360 30 480 496 16
cert_test_block_3 63360 31 496 512 16
cert_test_block_3 63360 32 512 528 16
cert_test_block_3 63360 33 528 544 16
cert_test_block_3 63360 34 544 560 16
cert_test_block_3 63360 35 560 576 16
cert_test_block_3 63360 36 576 592 16
cert_test_block_3 63360 37 592 608 16
cert_test_block_3 63360 38 608 624 16
cert_test_block_3 63360 39 624 640 16
theorem test63360_complete : Interval test63360 0 640 :=
  (interval_append test63360 0 320 640
  (interval_append test63360 0 160 320
  (interval_append test63360 0 80 160
  (interval_append test63360 0 32 80
  (interval_append test63360 0 16 32
  test63360_block_0
  test63360_block_1)
  (interval_append test63360 32 48 80
  test63360_block_2
  (interval_append test63360 48 64 80
  test63360_block_3
  test63360_block_4)))
  (interval_append test63360 80 112 160
  (interval_append test63360 80 96 112
  test63360_block_5
  test63360_block_6)
  (interval_append test63360 112 128 160
  test63360_block_7
  (interval_append test63360 128 144 160
  test63360_block_8
  test63360_block_9))))
  (interval_append test63360 160 240 320
  (interval_append test63360 160 192 240
  (interval_append test63360 160 176 192
  test63360_block_10
  test63360_block_11)
  (interval_append test63360 192 208 240
  test63360_block_12
  (interval_append test63360 208 224 240
  test63360_block_13
  test63360_block_14)))
  (interval_append test63360 240 272 320
  (interval_append test63360 240 256 272
  test63360_block_15
  test63360_block_16)
  (interval_append test63360 272 288 320
  test63360_block_17
  (interval_append test63360 288 304 320
  test63360_block_18
  test63360_block_19)))))
  (interval_append test63360 320 480 640
  (interval_append test63360 320 400 480
  (interval_append test63360 320 352 400
  (interval_append test63360 320 336 352
  test63360_block_20
  test63360_block_21)
  (interval_append test63360 352 368 400
  test63360_block_22
  (interval_append test63360 368 384 400
  test63360_block_23
  test63360_block_24)))
  (interval_append test63360 400 432 480
  (interval_append test63360 400 416 432
  test63360_block_25
  test63360_block_26)
  (interval_append test63360 432 448 480
  test63360_block_27
  (interval_append test63360 448 464 480
  test63360_block_28
  test63360_block_29))))
  (interval_append test63360 480 560 640
  (interval_append test63360 480 512 560
  (interval_append test63360 480 496 512
  test63360_block_30
  test63360_block_31)
  (interval_append test63360 512 528 560
  test63360_block_32
  (interval_append test63360 528 544 560
  test63360_block_33
  test63360_block_34)))
  (interval_append test63360 560 592 640
  (interval_append test63360 560 576 592
  test63360_block_35
  test63360_block_36)
  (interval_append test63360 592 608 640
  test63360_block_37
  (interval_append test63360 608 624 640
  test63360_block_38
  test63360_block_39))))))
cert_nodeInterval_3 63360 64000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 64000
cert_test_block_3 64000 0 0 16 16
cert_test_block_3 64000 1 16 32 16
cert_test_block_3 64000 2 32 48 16
cert_test_block_3 64000 3 48 64 16
cert_test_block_3 64000 4 64 80 16
cert_test_block_3 64000 5 80 96 16
cert_test_block_3 64000 6 96 112 16
cert_test_block_3 64000 7 112 128 16
cert_test_block_3 64000 8 128 144 16
cert_test_block_3 64000 9 144 160 16
cert_test_block_3 64000 10 160 176 16
cert_test_block_3 64000 11 176 192 16
cert_test_block_3 64000 12 192 208 16
cert_test_block_3 64000 13 208 224 16
cert_test_block_3 64000 14 224 240 16
cert_test_block_3 64000 15 240 256 16
cert_test_block_3 64000 16 256 272 16
cert_test_block_3 64000 17 272 288 16
cert_test_block_3 64000 18 288 304 16
cert_test_block_3 64000 19 304 320 16
cert_test_block_3 64000 20 320 336 16
cert_test_block_3 64000 21 336 352 16
cert_test_block_3 64000 22 352 368 16
cert_test_block_3 64000 23 368 384 16
cert_test_block_3 64000 24 384 400 16
cert_test_block_3 64000 25 400 416 16
cert_test_block_3 64000 26 416 432 16
cert_test_block_3 64000 27 432 448 16
cert_test_block_3 64000 28 448 464 16
cert_test_block_3 64000 29 464 480 16
cert_test_block_3 64000 30 480 496 16
cert_test_block_3 64000 31 496 512 16
cert_test_block_3 64000 32 512 528 16
cert_test_block_3 64000 33 528 544 16
cert_test_block_3 64000 34 544 560 16
cert_test_block_3 64000 35 560 576 16
cert_test_block_3 64000 36 576 592 16
cert_test_block_3 64000 37 592 608 16
cert_test_block_3 64000 38 608 624 16
cert_test_block_3 64000 39 624 640 16
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
cert_nodeInterval_3 64000 64640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 64640
cert_test_block_3 64640 0 0 16 16
cert_test_block_3 64640 1 16 32 16
cert_test_block_3 64640 2 32 48 16
cert_test_block_3 64640 3 48 64 16
cert_test_block_3 64640 4 64 80 16
cert_test_block_3 64640 5 80 96 16
cert_test_block_3 64640 6 96 112 16
cert_test_block_3 64640 7 112 128 16
cert_test_block_3 64640 8 128 144 16
cert_test_block_3 64640 9 144 160 16
cert_test_block_3 64640 10 160 176 16
cert_test_block_3 64640 11 176 192 16
cert_test_block_3 64640 12 192 208 16
cert_test_block_3 64640 13 208 224 16
cert_test_block_3 64640 14 224 240 16
cert_test_block_3 64640 15 240 256 16
cert_test_block_3 64640 16 256 272 16
cert_test_block_3 64640 17 272 288 16
cert_test_block_3 64640 18 288 304 16
cert_test_block_3 64640 19 304 320 16
cert_test_block_3 64640 20 320 336 16
cert_test_block_3 64640 21 336 352 16
cert_test_block_3 64640 22 352 368 16
cert_test_block_3 64640 23 368 384 16
cert_test_block_3 64640 24 384 400 16
cert_test_block_3 64640 25 400 416 16
cert_test_block_3 64640 26 416 432 16
cert_test_block_3 64640 27 432 448 16
cert_test_block_3 64640 28 448 464 16
cert_test_block_3 64640 29 464 480 16
cert_test_block_3 64640 30 480 496 16
cert_test_block_3 64640 31 496 512 16
cert_test_block_3 64640 32 512 528 16
cert_test_block_3 64640 33 528 544 16
cert_test_block_3 64640 34 544 560 16
cert_test_block_3 64640 35 560 576 16
cert_test_block_3 64640 36 576 592 16
cert_test_block_3 64640 37 592 608 16
cert_test_block_3 64640 38 608 624 16
cert_test_block_3 64640 39 624 640 16
theorem test64640_complete : Interval test64640 0 640 :=
  (interval_append test64640 0 320 640
  (interval_append test64640 0 160 320
  (interval_append test64640 0 80 160
  (interval_append test64640 0 32 80
  (interval_append test64640 0 16 32
  test64640_block_0
  test64640_block_1)
  (interval_append test64640 32 48 80
  test64640_block_2
  (interval_append test64640 48 64 80
  test64640_block_3
  test64640_block_4)))
  (interval_append test64640 80 112 160
  (interval_append test64640 80 96 112
  test64640_block_5
  test64640_block_6)
  (interval_append test64640 112 128 160
  test64640_block_7
  (interval_append test64640 128 144 160
  test64640_block_8
  test64640_block_9))))
  (interval_append test64640 160 240 320
  (interval_append test64640 160 192 240
  (interval_append test64640 160 176 192
  test64640_block_10
  test64640_block_11)
  (interval_append test64640 192 208 240
  test64640_block_12
  (interval_append test64640 208 224 240
  test64640_block_13
  test64640_block_14)))
  (interval_append test64640 240 272 320
  (interval_append test64640 240 256 272
  test64640_block_15
  test64640_block_16)
  (interval_append test64640 272 288 320
  test64640_block_17
  (interval_append test64640 288 304 320
  test64640_block_18
  test64640_block_19)))))
  (interval_append test64640 320 480 640
  (interval_append test64640 320 400 480
  (interval_append test64640 320 352 400
  (interval_append test64640 320 336 352
  test64640_block_20
  test64640_block_21)
  (interval_append test64640 352 368 400
  test64640_block_22
  (interval_append test64640 368 384 400
  test64640_block_23
  test64640_block_24)))
  (interval_append test64640 400 432 480
  (interval_append test64640 400 416 432
  test64640_block_25
  test64640_block_26)
  (interval_append test64640 432 448 480
  test64640_block_27
  (interval_append test64640 448 464 480
  test64640_block_28
  test64640_block_29))))
  (interval_append test64640 480 560 640
  (interval_append test64640 480 512 560
  (interval_append test64640 480 496 512
  test64640_block_30
  test64640_block_31)
  (interval_append test64640 512 528 560
  test64640_block_32
  (interval_append test64640 528 544 560
  test64640_block_33
  test64640_block_34)))
  (interval_append test64640 560 592 640
  (interval_append test64640 560 576 592
  test64640_block_35
  test64640_block_36)
  (interval_append test64640 592 608 640
  test64640_block_37
  (interval_append test64640 608 624 640
  test64640_block_38
  test64640_block_39))))))
cert_nodeInterval_3 64640 65280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 65280
cert_test_block_3 65280 0 0 16 16
cert_test_block_3 65280 1 16 32 16
cert_test_block_3 65280 2 32 48 16
cert_test_block_3 65280 3 48 64 16
cert_test_block_3 65280 4 64 80 16
cert_test_block_3 65280 5 80 96 16
cert_test_block_3 65280 6 96 112 16
cert_test_block_3 65280 7 112 128 16
cert_test_block_3 65280 8 128 144 16
cert_test_block_3 65280 9 144 160 16
cert_test_block_3 65280 10 160 176 16
cert_test_block_3 65280 11 176 192 16
cert_test_block_3 65280 12 192 208 16
cert_test_block_3 65280 13 208 224 16
cert_test_block_3 65280 14 224 240 16
cert_test_block_3 65280 15 240 256 16
cert_test_block_3 65280 16 256 272 16
cert_test_block_3 65280 17 272 288 16
cert_test_block_3 65280 18 288 304 16
cert_test_block_3 65280 19 304 320 16
cert_test_block_3 65280 20 320 336 16
cert_test_block_3 65280 21 336 352 16
cert_test_block_3 65280 22 352 368 16
cert_test_block_3 65280 23 368 384 16
cert_test_block_3 65280 24 384 400 16
cert_test_block_3 65280 25 400 416 16
cert_test_block_3 65280 26 416 432 16
cert_test_block_3 65280 27 432 448 16
cert_test_block_3 65280 28 448 464 16
cert_test_block_3 65280 29 464 480 16
cert_test_block_3 65280 30 480 496 16
cert_test_block_3 65280 31 496 512 16
cert_test_block_3 65280 32 512 528 16
cert_test_block_3 65280 33 528 544 16
cert_test_block_3 65280 34 544 560 16
cert_test_block_3 65280 35 560 576 16
cert_test_block_3 65280 36 576 592 16
cert_test_block_3 65280 37 592 608 16
cert_test_block_3 65280 38 608 624 16
cert_test_block_3 65280 39 624 640 16
theorem test65280_complete : Interval test65280 0 640 :=
  (interval_append test65280 0 320 640
  (interval_append test65280 0 160 320
  (interval_append test65280 0 80 160
  (interval_append test65280 0 32 80
  (interval_append test65280 0 16 32
  test65280_block_0
  test65280_block_1)
  (interval_append test65280 32 48 80
  test65280_block_2
  (interval_append test65280 48 64 80
  test65280_block_3
  test65280_block_4)))
  (interval_append test65280 80 112 160
  (interval_append test65280 80 96 112
  test65280_block_5
  test65280_block_6)
  (interval_append test65280 112 128 160
  test65280_block_7
  (interval_append test65280 128 144 160
  test65280_block_8
  test65280_block_9))))
  (interval_append test65280 160 240 320
  (interval_append test65280 160 192 240
  (interval_append test65280 160 176 192
  test65280_block_10
  test65280_block_11)
  (interval_append test65280 192 208 240
  test65280_block_12
  (interval_append test65280 208 224 240
  test65280_block_13
  test65280_block_14)))
  (interval_append test65280 240 272 320
  (interval_append test65280 240 256 272
  test65280_block_15
  test65280_block_16)
  (interval_append test65280 272 288 320
  test65280_block_17
  (interval_append test65280 288 304 320
  test65280_block_18
  test65280_block_19)))))
  (interval_append test65280 320 480 640
  (interval_append test65280 320 400 480
  (interval_append test65280 320 352 400
  (interval_append test65280 320 336 352
  test65280_block_20
  test65280_block_21)
  (interval_append test65280 352 368 400
  test65280_block_22
  (interval_append test65280 368 384 400
  test65280_block_23
  test65280_block_24)))
  (interval_append test65280 400 432 480
  (interval_append test65280 400 416 432
  test65280_block_25
  test65280_block_26)
  (interval_append test65280 432 448 480
  test65280_block_27
  (interval_append test65280 448 464 480
  test65280_block_28
  test65280_block_29))))
  (interval_append test65280 480 560 640
  (interval_append test65280 480 512 560
  (interval_append test65280 480 496 512
  test65280_block_30
  test65280_block_31)
  (interval_append test65280 512 528 560
  test65280_block_32
  (interval_append test65280 528 544 560
  test65280_block_33
  test65280_block_34)))
  (interval_append test65280 560 592 640
  (interval_append test65280 560 576 592
  test65280_block_35
  test65280_block_36)
  (interval_append test65280 592 608 640
  test65280_block_37
  (interval_append test65280 608 624 640
  test65280_block_38
  test65280_block_39))))))
cert_nodeInterval_3 65280 65920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 65920
cert_test_block_3 65920 0 0 16 16
cert_test_block_3 65920 1 16 32 16
cert_test_block_3 65920 2 32 48 16
cert_test_block_3 65920 3 48 64 16
cert_test_block_3 65920 4 64 80 16
cert_test_block_3 65920 5 80 96 16
cert_test_block_3 65920 6 96 112 16
cert_test_block_3 65920 7 112 128 16
cert_test_block_3 65920 8 128 144 16
cert_test_block_3 65920 9 144 160 16
cert_test_block_3 65920 10 160 176 16
cert_test_block_3 65920 11 176 192 16
cert_test_block_3 65920 12 192 208 16
cert_test_block_3 65920 13 208 224 16
cert_test_block_3 65920 14 224 240 16
cert_test_block_3 65920 15 240 256 16
cert_test_block_3 65920 16 256 272 16
cert_test_block_3 65920 17 272 288 16
cert_test_block_3 65920 18 288 304 16
cert_test_block_3 65920 19 304 320 16
cert_test_block_3 65920 20 320 336 16
cert_test_block_3 65920 21 336 352 16
cert_test_block_3 65920 22 352 368 16
cert_test_block_3 65920 23 368 384 16
cert_test_block_3 65920 24 384 400 16
cert_test_block_3 65920 25 400 416 16
cert_test_block_3 65920 26 416 432 16
cert_test_block_3 65920 27 432 448 16
cert_test_block_3 65920 28 448 464 16
cert_test_block_3 65920 29 464 480 16
cert_test_block_3 65920 30 480 496 16
cert_test_block_3 65920 31 496 512 16
cert_test_block_3 65920 32 512 528 16
cert_test_block_3 65920 33 528 544 16
cert_test_block_3 65920 34 544 560 16
cert_test_block_3 65920 35 560 576 16
cert_test_block_3 65920 36 576 592 16
cert_test_block_3 65920 37 592 608 16
cert_test_block_3 65920 38 608 624 16
cert_test_block_3 65920 39 624 640 16
theorem test65920_complete : Interval test65920 0 640 :=
  (interval_append test65920 0 320 640
  (interval_append test65920 0 160 320
  (interval_append test65920 0 80 160
  (interval_append test65920 0 32 80
  (interval_append test65920 0 16 32
  test65920_block_0
  test65920_block_1)
  (interval_append test65920 32 48 80
  test65920_block_2
  (interval_append test65920 48 64 80
  test65920_block_3
  test65920_block_4)))
  (interval_append test65920 80 112 160
  (interval_append test65920 80 96 112
  test65920_block_5
  test65920_block_6)
  (interval_append test65920 112 128 160
  test65920_block_7
  (interval_append test65920 128 144 160
  test65920_block_8
  test65920_block_9))))
  (interval_append test65920 160 240 320
  (interval_append test65920 160 192 240
  (interval_append test65920 160 176 192
  test65920_block_10
  test65920_block_11)
  (interval_append test65920 192 208 240
  test65920_block_12
  (interval_append test65920 208 224 240
  test65920_block_13
  test65920_block_14)))
  (interval_append test65920 240 272 320
  (interval_append test65920 240 256 272
  test65920_block_15
  test65920_block_16)
  (interval_append test65920 272 288 320
  test65920_block_17
  (interval_append test65920 288 304 320
  test65920_block_18
  test65920_block_19)))))
  (interval_append test65920 320 480 640
  (interval_append test65920 320 400 480
  (interval_append test65920 320 352 400
  (interval_append test65920 320 336 352
  test65920_block_20
  test65920_block_21)
  (interval_append test65920 352 368 400
  test65920_block_22
  (interval_append test65920 368 384 400
  test65920_block_23
  test65920_block_24)))
  (interval_append test65920 400 432 480
  (interval_append test65920 400 416 432
  test65920_block_25
  test65920_block_26)
  (interval_append test65920 432 448 480
  test65920_block_27
  (interval_append test65920 448 464 480
  test65920_block_28
  test65920_block_29))))
  (interval_append test65920 480 560 640
  (interval_append test65920 480 512 560
  (interval_append test65920 480 496 512
  test65920_block_30
  test65920_block_31)
  (interval_append test65920 512 528 560
  test65920_block_32
  (interval_append test65920 528 544 560
  test65920_block_33
  test65920_block_34)))
  (interval_append test65920 560 592 640
  (interval_append test65920 560 576 592
  test65920_block_35
  test65920_block_36)
  (interval_append test65920 592 608 640
  test65920_block_37
  (interval_append test65920 608 624 640
  test65920_block_38
  test65920_block_39))))))
cert_nodeInterval_3 65920 66560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 66560
cert_test_block_3 66560 0 0 16 16
cert_test_block_3 66560 1 16 32 16
cert_test_block_3 66560 2 32 48 16
cert_test_block_3 66560 3 48 64 16
cert_test_block_3 66560 4 64 80 16
cert_test_block_3 66560 5 80 96 16
cert_test_block_3 66560 6 96 112 16
cert_test_block_3 66560 7 112 128 16
cert_test_block_3 66560 8 128 144 16
cert_test_block_3 66560 9 144 160 16
cert_test_block_3 66560 10 160 176 16
cert_test_block_3 66560 11 176 192 16
cert_test_block_3 66560 12 192 208 16
cert_test_block_3 66560 13 208 224 16
cert_test_block_3 66560 14 224 240 16
cert_test_block_3 66560 15 240 256 16
cert_test_block_3 66560 16 256 272 16
cert_test_block_3 66560 17 272 288 16
cert_test_block_3 66560 18 288 304 16
cert_test_block_3 66560 19 304 320 16
cert_test_block_3 66560 20 320 336 16
cert_test_block_3 66560 21 336 352 16
cert_test_block_3 66560 22 352 368 16
cert_test_block_3 66560 23 368 384 16
cert_test_block_3 66560 24 384 400 16
cert_test_block_3 66560 25 400 416 16
cert_test_block_3 66560 26 416 432 16
cert_test_block_3 66560 27 432 448 16
cert_test_block_3 66560 28 448 464 16
cert_test_block_3 66560 29 464 480 16
cert_test_block_3 66560 30 480 496 16
cert_test_block_3 66560 31 496 512 16
cert_test_block_3 66560 32 512 528 16
cert_test_block_3 66560 33 528 544 16
cert_test_block_3 66560 34 544 560 16
cert_test_block_3 66560 35 560 576 16
cert_test_block_3 66560 36 576 592 16
cert_test_block_3 66560 37 592 608 16
cert_test_block_3 66560 38 608 624 16
cert_test_block_3 66560 39 624 640 16
theorem test66560_complete : Interval test66560 0 640 :=
  (interval_append test66560 0 320 640
  (interval_append test66560 0 160 320
  (interval_append test66560 0 80 160
  (interval_append test66560 0 32 80
  (interval_append test66560 0 16 32
  test66560_block_0
  test66560_block_1)
  (interval_append test66560 32 48 80
  test66560_block_2
  (interval_append test66560 48 64 80
  test66560_block_3
  test66560_block_4)))
  (interval_append test66560 80 112 160
  (interval_append test66560 80 96 112
  test66560_block_5
  test66560_block_6)
  (interval_append test66560 112 128 160
  test66560_block_7
  (interval_append test66560 128 144 160
  test66560_block_8
  test66560_block_9))))
  (interval_append test66560 160 240 320
  (interval_append test66560 160 192 240
  (interval_append test66560 160 176 192
  test66560_block_10
  test66560_block_11)
  (interval_append test66560 192 208 240
  test66560_block_12
  (interval_append test66560 208 224 240
  test66560_block_13
  test66560_block_14)))
  (interval_append test66560 240 272 320
  (interval_append test66560 240 256 272
  test66560_block_15
  test66560_block_16)
  (interval_append test66560 272 288 320
  test66560_block_17
  (interval_append test66560 288 304 320
  test66560_block_18
  test66560_block_19)))))
  (interval_append test66560 320 480 640
  (interval_append test66560 320 400 480
  (interval_append test66560 320 352 400
  (interval_append test66560 320 336 352
  test66560_block_20
  test66560_block_21)
  (interval_append test66560 352 368 400
  test66560_block_22
  (interval_append test66560 368 384 400
  test66560_block_23
  test66560_block_24)))
  (interval_append test66560 400 432 480
  (interval_append test66560 400 416 432
  test66560_block_25
  test66560_block_26)
  (interval_append test66560 432 448 480
  test66560_block_27
  (interval_append test66560 448 464 480
  test66560_block_28
  test66560_block_29))))
  (interval_append test66560 480 560 640
  (interval_append test66560 480 512 560
  (interval_append test66560 480 496 512
  test66560_block_30
  test66560_block_31)
  (interval_append test66560 512 528 560
  test66560_block_32
  (interval_append test66560 528 544 560
  test66560_block_33
  test66560_block_34)))
  (interval_append test66560 560 592 640
  (interval_append test66560 560 576 592
  test66560_block_35
  test66560_block_36)
  (interval_append test66560 592 608 640
  test66560_block_37
  (interval_append test66560 608 624 640
  test66560_block_38
  test66560_block_39))))))
cert_nodeInterval_3 66560 67200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 67200
cert_test_block_3 67200 0 0 16 16
cert_test_block_3 67200 1 16 32 16
cert_test_block_3 67200 2 32 48 16
cert_test_block_3 67200 3 48 64 16
cert_test_block_3 67200 4 64 80 16
cert_test_block_3 67200 5 80 96 16
cert_test_block_3 67200 6 96 112 16
cert_test_block_3 67200 7 112 128 16
cert_test_block_3 67200 8 128 144 16
cert_test_block_3 67200 9 144 160 16
cert_test_block_3 67200 10 160 176 16
cert_test_block_3 67200 11 176 192 16
cert_test_block_3 67200 12 192 208 16
cert_test_block_3 67200 13 208 224 16
cert_test_block_3 67200 14 224 240 16
cert_test_block_3 67200 15 240 256 16
cert_test_block_3 67200 16 256 272 16
cert_test_block_3 67200 17 272 288 16
cert_test_block_3 67200 18 288 304 16
cert_test_block_3 67200 19 304 320 16
cert_test_block_3 67200 20 320 336 16
cert_test_block_3 67200 21 336 352 16
cert_test_block_3 67200 22 352 368 16
cert_test_block_3 67200 23 368 384 16
cert_test_block_3 67200 24 384 400 16
cert_test_block_3 67200 25 400 416 16
cert_test_block_3 67200 26 416 432 16
cert_test_block_3 67200 27 432 448 16
cert_test_block_3 67200 28 448 464 16
cert_test_block_3 67200 29 464 480 16
cert_test_block_3 67200 30 480 496 16
cert_test_block_3 67200 31 496 512 16
cert_test_block_3 67200 32 512 528 16
cert_test_block_3 67200 33 528 544 16
cert_test_block_3 67200 34 544 560 16
cert_test_block_3 67200 35 560 576 16
cert_test_block_3 67200 36 576 592 16
cert_test_block_3 67200 37 592 608 16
cert_test_block_3 67200 38 608 624 16
cert_test_block_3 67200 39 624 640 16
theorem test67200_complete : Interval test67200 0 640 :=
  (interval_append test67200 0 320 640
  (interval_append test67200 0 160 320
  (interval_append test67200 0 80 160
  (interval_append test67200 0 32 80
  (interval_append test67200 0 16 32
  test67200_block_0
  test67200_block_1)
  (interval_append test67200 32 48 80
  test67200_block_2
  (interval_append test67200 48 64 80
  test67200_block_3
  test67200_block_4)))
  (interval_append test67200 80 112 160
  (interval_append test67200 80 96 112
  test67200_block_5
  test67200_block_6)
  (interval_append test67200 112 128 160
  test67200_block_7
  (interval_append test67200 128 144 160
  test67200_block_8
  test67200_block_9))))
  (interval_append test67200 160 240 320
  (interval_append test67200 160 192 240
  (interval_append test67200 160 176 192
  test67200_block_10
  test67200_block_11)
  (interval_append test67200 192 208 240
  test67200_block_12
  (interval_append test67200 208 224 240
  test67200_block_13
  test67200_block_14)))
  (interval_append test67200 240 272 320
  (interval_append test67200 240 256 272
  test67200_block_15
  test67200_block_16)
  (interval_append test67200 272 288 320
  test67200_block_17
  (interval_append test67200 288 304 320
  test67200_block_18
  test67200_block_19)))))
  (interval_append test67200 320 480 640
  (interval_append test67200 320 400 480
  (interval_append test67200 320 352 400
  (interval_append test67200 320 336 352
  test67200_block_20
  test67200_block_21)
  (interval_append test67200 352 368 400
  test67200_block_22
  (interval_append test67200 368 384 400
  test67200_block_23
  test67200_block_24)))
  (interval_append test67200 400 432 480
  (interval_append test67200 400 416 432
  test67200_block_25
  test67200_block_26)
  (interval_append test67200 432 448 480
  test67200_block_27
  (interval_append test67200 448 464 480
  test67200_block_28
  test67200_block_29))))
  (interval_append test67200 480 560 640
  (interval_append test67200 480 512 560
  (interval_append test67200 480 496 512
  test67200_block_30
  test67200_block_31)
  (interval_append test67200 512 528 560
  test67200_block_32
  (interval_append test67200 528 544 560
  test67200_block_33
  test67200_block_34)))
  (interval_append test67200 560 592 640
  (interval_append test67200 560 576 592
  test67200_block_35
  test67200_block_36)
  (interval_append test67200 592 608 640
  test67200_block_37
  (interval_append test67200 608 624 640
  test67200_block_38
  test67200_block_39))))))
cert_nodeInterval_3 67200 67840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 67840
cert_test_block_3 67840 0 0 16 16
cert_test_block_3 67840 1 16 32 16
cert_test_block_3 67840 2 32 48 16
cert_test_block_3 67840 3 48 64 16
cert_test_block_3 67840 4 64 80 16
cert_test_block_3 67840 5 80 96 16
cert_test_block_3 67840 6 96 112 16
cert_test_block_3 67840 7 112 128 16
cert_test_block_3 67840 8 128 144 16
cert_test_block_3 67840 9 144 160 16
cert_test_block_3 67840 10 160 176 16
cert_test_block_3 67840 11 176 192 16
cert_test_block_3 67840 12 192 208 16
cert_test_block_3 67840 13 208 224 16
cert_test_block_3 67840 14 224 240 16
cert_test_block_3 67840 15 240 256 16
cert_test_block_3 67840 16 256 272 16
cert_test_block_3 67840 17 272 288 16
cert_test_block_3 67840 18 288 304 16
cert_test_block_3 67840 19 304 320 16
cert_test_block_3 67840 20 320 336 16
cert_test_block_3 67840 21 336 352 16
cert_test_block_3 67840 22 352 368 16
cert_test_block_3 67840 23 368 384 16
cert_test_block_3 67840 24 384 400 16
cert_test_block_3 67840 25 400 416 16
cert_test_block_3 67840 26 416 432 16
cert_test_block_3 67840 27 432 448 16
cert_test_block_3 67840 28 448 464 16
cert_test_block_3 67840 29 464 480 16
cert_test_block_3 67840 30 480 496 16
cert_test_block_3 67840 31 496 512 16
cert_test_block_3 67840 32 512 528 16
cert_test_block_3 67840 33 528 544 16
cert_test_block_3 67840 34 544 560 16
cert_test_block_3 67840 35 560 576 16
cert_test_block_3 67840 36 576 592 16
cert_test_block_3 67840 37 592 608 16
cert_test_block_3 67840 38 608 624 16
cert_test_block_3 67840 39 624 640 16
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
cert_nodeInterval_3 67840 68480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 68480
cert_test_block_3 68480 0 0 16 16
cert_test_block_3 68480 1 16 32 16
cert_test_block_3 68480 2 32 48 16
cert_test_block_3 68480 3 48 64 16
cert_test_block_3 68480 4 64 80 16
cert_test_block_3 68480 5 80 96 16
cert_test_block_3 68480 6 96 112 16
cert_test_block_3 68480 7 112 128 16
cert_test_block_3 68480 8 128 144 16
cert_test_block_3 68480 9 144 160 16
cert_test_block_3 68480 10 160 176 16
cert_test_block_3 68480 11 176 192 16
cert_test_block_3 68480 12 192 208 16
cert_test_block_3 68480 13 208 224 16
cert_test_block_3 68480 14 224 240 16
cert_test_block_3 68480 15 240 256 16
cert_test_block_3 68480 16 256 272 16
cert_test_block_3 68480 17 272 288 16
cert_test_block_3 68480 18 288 304 16
cert_test_block_3 68480 19 304 320 16
cert_test_block_3 68480 20 320 336 16
cert_test_block_3 68480 21 336 352 16
cert_test_block_3 68480 22 352 368 16
cert_test_block_3 68480 23 368 384 16
cert_test_block_3 68480 24 384 400 16
cert_test_block_3 68480 25 400 416 16
cert_test_block_3 68480 26 416 432 16
cert_test_block_3 68480 27 432 448 16
cert_test_block_3 68480 28 448 464 16
cert_test_block_3 68480 29 464 480 16
cert_test_block_3 68480 30 480 496 16
cert_test_block_3 68480 31 496 512 16
cert_test_block_3 68480 32 512 528 16
cert_test_block_3 68480 33 528 544 16
cert_test_block_3 68480 34 544 560 16
cert_test_block_3 68480 35 560 576 16
cert_test_block_3 68480 36 576 592 16
cert_test_block_3 68480 37 592 608 16
cert_test_block_3 68480 38 608 624 16
cert_test_block_3 68480 39 624 640 16
theorem test68480_complete : Interval test68480 0 640 :=
  (interval_append test68480 0 320 640
  (interval_append test68480 0 160 320
  (interval_append test68480 0 80 160
  (interval_append test68480 0 32 80
  (interval_append test68480 0 16 32
  test68480_block_0
  test68480_block_1)
  (interval_append test68480 32 48 80
  test68480_block_2
  (interval_append test68480 48 64 80
  test68480_block_3
  test68480_block_4)))
  (interval_append test68480 80 112 160
  (interval_append test68480 80 96 112
  test68480_block_5
  test68480_block_6)
  (interval_append test68480 112 128 160
  test68480_block_7
  (interval_append test68480 128 144 160
  test68480_block_8
  test68480_block_9))))
  (interval_append test68480 160 240 320
  (interval_append test68480 160 192 240
  (interval_append test68480 160 176 192
  test68480_block_10
  test68480_block_11)
  (interval_append test68480 192 208 240
  test68480_block_12
  (interval_append test68480 208 224 240
  test68480_block_13
  test68480_block_14)))
  (interval_append test68480 240 272 320
  (interval_append test68480 240 256 272
  test68480_block_15
  test68480_block_16)
  (interval_append test68480 272 288 320
  test68480_block_17
  (interval_append test68480 288 304 320
  test68480_block_18
  test68480_block_19)))))
  (interval_append test68480 320 480 640
  (interval_append test68480 320 400 480
  (interval_append test68480 320 352 400
  (interval_append test68480 320 336 352
  test68480_block_20
  test68480_block_21)
  (interval_append test68480 352 368 400
  test68480_block_22
  (interval_append test68480 368 384 400
  test68480_block_23
  test68480_block_24)))
  (interval_append test68480 400 432 480
  (interval_append test68480 400 416 432
  test68480_block_25
  test68480_block_26)
  (interval_append test68480 432 448 480
  test68480_block_27
  (interval_append test68480 448 464 480
  test68480_block_28
  test68480_block_29))))
  (interval_append test68480 480 560 640
  (interval_append test68480 480 512 560
  (interval_append test68480 480 496 512
  test68480_block_30
  test68480_block_31)
  (interval_append test68480 512 528 560
  test68480_block_32
  (interval_append test68480 528 544 560
  test68480_block_33
  test68480_block_34)))
  (interval_append test68480 560 592 640
  (interval_append test68480 560 576 592
  test68480_block_35
  test68480_block_36)
  (interval_append test68480 592 608 640
  test68480_block_37
  (interval_append test68480 608 624 640
  test68480_block_38
  test68480_block_39))))))
cert_nodeInterval_3 68480 69120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
