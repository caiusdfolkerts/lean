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
cert_test_11 76800
cert_test_block_3 76800 0 0 16 16
cert_test_block_3 76800 1 16 32 16
cert_test_block_3 76800 2 32 48 16
cert_test_block_3 76800 3 48 64 16
cert_test_block_3 76800 4 64 80 16
cert_test_block_3 76800 5 80 96 16
cert_test_block_3 76800 6 96 112 16
cert_test_block_3 76800 7 112 128 16
cert_test_block_3 76800 8 128 144 16
cert_test_block_3 76800 9 144 160 16
cert_test_block_3 76800 10 160 176 16
cert_test_block_3 76800 11 176 192 16
cert_test_block_3 76800 12 192 208 16
cert_test_block_3 76800 13 208 224 16
cert_test_block_3 76800 14 224 240 16
cert_test_block_3 76800 15 240 256 16
cert_test_block_3 76800 16 256 272 16
cert_test_block_3 76800 17 272 288 16
cert_test_block_3 76800 18 288 304 16
cert_test_block_3 76800 19 304 320 16
cert_test_block_3 76800 20 320 336 16
cert_test_block_3 76800 21 336 352 16
cert_test_block_3 76800 22 352 368 16
cert_test_block_3 76800 23 368 384 16
cert_test_block_3 76800 24 384 400 16
cert_test_block_3 76800 25 400 416 16
cert_test_block_3 76800 26 416 432 16
cert_test_block_3 76800 27 432 448 16
cert_test_block_3 76800 28 448 464 16
cert_test_block_3 76800 29 464 480 16
cert_test_block_3 76800 30 480 496 16
cert_test_block_3 76800 31 496 512 16
cert_test_block_3 76800 32 512 528 16
cert_test_block_3 76800 33 528 544 16
cert_test_block_3 76800 34 544 560 16
cert_test_block_3 76800 35 560 576 16
cert_test_block_3 76800 36 576 592 16
cert_test_block_3 76800 37 592 608 16
cert_test_block_3 76800 38 608 624 16
cert_test_block_3 76800 39 624 640 16
theorem test76800_complete : Interval test76800 0 640 :=
  (interval_append test76800 0 320 640
  (interval_append test76800 0 160 320
  (interval_append test76800 0 80 160
  (interval_append test76800 0 32 80
  (interval_append test76800 0 16 32
  test76800_block_0
  test76800_block_1)
  (interval_append test76800 32 48 80
  test76800_block_2
  (interval_append test76800 48 64 80
  test76800_block_3
  test76800_block_4)))
  (interval_append test76800 80 112 160
  (interval_append test76800 80 96 112
  test76800_block_5
  test76800_block_6)
  (interval_append test76800 112 128 160
  test76800_block_7
  (interval_append test76800 128 144 160
  test76800_block_8
  test76800_block_9))))
  (interval_append test76800 160 240 320
  (interval_append test76800 160 192 240
  (interval_append test76800 160 176 192
  test76800_block_10
  test76800_block_11)
  (interval_append test76800 192 208 240
  test76800_block_12
  (interval_append test76800 208 224 240
  test76800_block_13
  test76800_block_14)))
  (interval_append test76800 240 272 320
  (interval_append test76800 240 256 272
  test76800_block_15
  test76800_block_16)
  (interval_append test76800 272 288 320
  test76800_block_17
  (interval_append test76800 288 304 320
  test76800_block_18
  test76800_block_19)))))
  (interval_append test76800 320 480 640
  (interval_append test76800 320 400 480
  (interval_append test76800 320 352 400
  (interval_append test76800 320 336 352
  test76800_block_20
  test76800_block_21)
  (interval_append test76800 352 368 400
  test76800_block_22
  (interval_append test76800 368 384 400
  test76800_block_23
  test76800_block_24)))
  (interval_append test76800 400 432 480
  (interval_append test76800 400 416 432
  test76800_block_25
  test76800_block_26)
  (interval_append test76800 432 448 480
  test76800_block_27
  (interval_append test76800 448 464 480
  test76800_block_28
  test76800_block_29))))
  (interval_append test76800 480 560 640
  (interval_append test76800 480 512 560
  (interval_append test76800 480 496 512
  test76800_block_30
  test76800_block_31)
  (interval_append test76800 512 528 560
  test76800_block_32
  (interval_append test76800 528 544 560
  test76800_block_33
  test76800_block_34)))
  (interval_append test76800 560 592 640
  (interval_append test76800 560 576 592
  test76800_block_35
  test76800_block_36)
  (interval_append test76800 592 608 640
  test76800_block_37
  (interval_append test76800 608 624 640
  test76800_block_38
  test76800_block_39))))))
cert_nodeInterval_3 76800 77440
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
cert_test_11 77440
cert_test_block_3 77440 0 0 16 16
cert_test_block_3 77440 1 16 32 16
cert_test_block_3 77440 2 32 48 16
cert_test_block_3 77440 3 48 64 16
cert_test_block_3 77440 4 64 80 16
cert_test_block_3 77440 5 80 96 16
cert_test_block_3 77440 6 96 112 16
cert_test_block_3 77440 7 112 128 16
cert_test_block_3 77440 8 128 144 16
cert_test_block_3 77440 9 144 160 16
cert_test_block_3 77440 10 160 176 16
cert_test_block_3 77440 11 176 192 16
cert_test_block_3 77440 12 192 208 16
cert_test_block_3 77440 13 208 224 16
cert_test_block_3 77440 14 224 240 16
cert_test_block_3 77440 15 240 256 16
cert_test_block_3 77440 16 256 272 16
cert_test_block_3 77440 17 272 288 16
cert_test_block_3 77440 18 288 304 16
cert_test_block_3 77440 19 304 320 16
cert_test_block_3 77440 20 320 336 16
cert_test_block_3 77440 21 336 352 16
cert_test_block_3 77440 22 352 368 16
cert_test_block_3 77440 23 368 384 16
cert_test_block_3 77440 24 384 400 16
cert_test_block_3 77440 25 400 416 16
cert_test_block_3 77440 26 416 432 16
cert_test_block_3 77440 27 432 448 16
cert_test_block_3 77440 28 448 464 16
cert_test_block_3 77440 29 464 480 16
cert_test_block_3 77440 30 480 496 16
cert_test_block_3 77440 31 496 512 16
cert_test_block_3 77440 32 512 528 16
cert_test_block_3 77440 33 528 544 16
cert_test_block_3 77440 34 544 560 16
cert_test_block_3 77440 35 560 576 16
cert_test_block_3 77440 36 576 592 16
cert_test_block_3 77440 37 592 608 16
cert_test_block_3 77440 38 608 624 16
cert_test_block_3 77440 39 624 640 16
theorem test77440_complete : Interval test77440 0 640 :=
  (interval_append test77440 0 320 640
  (interval_append test77440 0 160 320
  (interval_append test77440 0 80 160
  (interval_append test77440 0 32 80
  (interval_append test77440 0 16 32
  test77440_block_0
  test77440_block_1)
  (interval_append test77440 32 48 80
  test77440_block_2
  (interval_append test77440 48 64 80
  test77440_block_3
  test77440_block_4)))
  (interval_append test77440 80 112 160
  (interval_append test77440 80 96 112
  test77440_block_5
  test77440_block_6)
  (interval_append test77440 112 128 160
  test77440_block_7
  (interval_append test77440 128 144 160
  test77440_block_8
  test77440_block_9))))
  (interval_append test77440 160 240 320
  (interval_append test77440 160 192 240
  (interval_append test77440 160 176 192
  test77440_block_10
  test77440_block_11)
  (interval_append test77440 192 208 240
  test77440_block_12
  (interval_append test77440 208 224 240
  test77440_block_13
  test77440_block_14)))
  (interval_append test77440 240 272 320
  (interval_append test77440 240 256 272
  test77440_block_15
  test77440_block_16)
  (interval_append test77440 272 288 320
  test77440_block_17
  (interval_append test77440 288 304 320
  test77440_block_18
  test77440_block_19)))))
  (interval_append test77440 320 480 640
  (interval_append test77440 320 400 480
  (interval_append test77440 320 352 400
  (interval_append test77440 320 336 352
  test77440_block_20
  test77440_block_21)
  (interval_append test77440 352 368 400
  test77440_block_22
  (interval_append test77440 368 384 400
  test77440_block_23
  test77440_block_24)))
  (interval_append test77440 400 432 480
  (interval_append test77440 400 416 432
  test77440_block_25
  test77440_block_26)
  (interval_append test77440 432 448 480
  test77440_block_27
  (interval_append test77440 448 464 480
  test77440_block_28
  test77440_block_29))))
  (interval_append test77440 480 560 640
  (interval_append test77440 480 512 560
  (interval_append test77440 480 496 512
  test77440_block_30
  test77440_block_31)
  (interval_append test77440 512 528 560
  test77440_block_32
  (interval_append test77440 528 544 560
  test77440_block_33
  test77440_block_34)))
  (interval_append test77440 560 592 640
  (interval_append test77440 560 576 592
  test77440_block_35
  test77440_block_36)
  (interval_append test77440 592 608 640
  test77440_block_37
  (interval_append test77440 608 624 640
  test77440_block_38
  test77440_block_39))))))
cert_nodeInterval_3 77440 78080
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
cert_test_11 78080
cert_test_block_3 78080 0 0 16 16
cert_test_block_3 78080 1 16 32 16
cert_test_block_3 78080 2 32 48 16
cert_test_block_3 78080 3 48 64 16
cert_test_block_3 78080 4 64 80 16
cert_test_block_3 78080 5 80 96 16
cert_test_block_3 78080 6 96 112 16
cert_test_block_3 78080 7 112 128 16
cert_test_block_3 78080 8 128 144 16
cert_test_block_3 78080 9 144 160 16
cert_test_block_3 78080 10 160 176 16
cert_test_block_3 78080 11 176 192 16
cert_test_block_3 78080 12 192 208 16
cert_test_block_3 78080 13 208 224 16
cert_test_block_3 78080 14 224 240 16
cert_test_block_3 78080 15 240 256 16
cert_test_block_3 78080 16 256 272 16
cert_test_block_3 78080 17 272 288 16
cert_test_block_3 78080 18 288 304 16
cert_test_block_3 78080 19 304 320 16
cert_test_block_3 78080 20 320 336 16
cert_test_block_3 78080 21 336 352 16
cert_test_block_3 78080 22 352 368 16
cert_test_block_3 78080 23 368 384 16
cert_test_block_3 78080 24 384 400 16
cert_test_block_3 78080 25 400 416 16
cert_test_block_3 78080 26 416 432 16
cert_test_block_3 78080 27 432 448 16
cert_test_block_3 78080 28 448 464 16
cert_test_block_3 78080 29 464 480 16
cert_test_block_3 78080 30 480 496 16
cert_test_block_3 78080 31 496 512 16
cert_test_block_3 78080 32 512 528 16
cert_test_block_3 78080 33 528 544 16
cert_test_block_3 78080 34 544 560 16
cert_test_block_3 78080 35 560 576 16
cert_test_block_3 78080 36 576 592 16
cert_test_block_3 78080 37 592 608 16
cert_test_block_3 78080 38 608 624 16
cert_test_block_3 78080 39 624 640 16
theorem test78080_complete : Interval test78080 0 640 :=
  (interval_append test78080 0 320 640
  (interval_append test78080 0 160 320
  (interval_append test78080 0 80 160
  (interval_append test78080 0 32 80
  (interval_append test78080 0 16 32
  test78080_block_0
  test78080_block_1)
  (interval_append test78080 32 48 80
  test78080_block_2
  (interval_append test78080 48 64 80
  test78080_block_3
  test78080_block_4)))
  (interval_append test78080 80 112 160
  (interval_append test78080 80 96 112
  test78080_block_5
  test78080_block_6)
  (interval_append test78080 112 128 160
  test78080_block_7
  (interval_append test78080 128 144 160
  test78080_block_8
  test78080_block_9))))
  (interval_append test78080 160 240 320
  (interval_append test78080 160 192 240
  (interval_append test78080 160 176 192
  test78080_block_10
  test78080_block_11)
  (interval_append test78080 192 208 240
  test78080_block_12
  (interval_append test78080 208 224 240
  test78080_block_13
  test78080_block_14)))
  (interval_append test78080 240 272 320
  (interval_append test78080 240 256 272
  test78080_block_15
  test78080_block_16)
  (interval_append test78080 272 288 320
  test78080_block_17
  (interval_append test78080 288 304 320
  test78080_block_18
  test78080_block_19)))))
  (interval_append test78080 320 480 640
  (interval_append test78080 320 400 480
  (interval_append test78080 320 352 400
  (interval_append test78080 320 336 352
  test78080_block_20
  test78080_block_21)
  (interval_append test78080 352 368 400
  test78080_block_22
  (interval_append test78080 368 384 400
  test78080_block_23
  test78080_block_24)))
  (interval_append test78080 400 432 480
  (interval_append test78080 400 416 432
  test78080_block_25
  test78080_block_26)
  (interval_append test78080 432 448 480
  test78080_block_27
  (interval_append test78080 448 464 480
  test78080_block_28
  test78080_block_29))))
  (interval_append test78080 480 560 640
  (interval_append test78080 480 512 560
  (interval_append test78080 480 496 512
  test78080_block_30
  test78080_block_31)
  (interval_append test78080 512 528 560
  test78080_block_32
  (interval_append test78080 528 544 560
  test78080_block_33
  test78080_block_34)))
  (interval_append test78080 560 592 640
  (interval_append test78080 560 576 592
  test78080_block_35
  test78080_block_36)
  (interval_append test78080 592 608 640
  test78080_block_37
  (interval_append test78080 608 624 640
  test78080_block_38
  test78080_block_39))))))
cert_nodeInterval_3 78080 78720
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
cert_test_11 78720
cert_test_block_3 78720 0 0 16 16
cert_test_block_3 78720 1 16 32 16
cert_test_block_3 78720 2 32 48 16
cert_test_block_3 78720 3 48 64 16
cert_test_block_3 78720 4 64 80 16
cert_test_block_3 78720 5 80 96 16
cert_test_block_3 78720 6 96 112 16
cert_test_block_3 78720 7 112 128 16
cert_test_block_3 78720 8 128 144 16
cert_test_block_3 78720 9 144 160 16
cert_test_block_3 78720 10 160 176 16
cert_test_block_3 78720 11 176 192 16
cert_test_block_3 78720 12 192 208 16
cert_test_block_3 78720 13 208 224 16
cert_test_block_3 78720 14 224 240 16
cert_test_block_3 78720 15 240 256 16
cert_test_block_3 78720 16 256 272 16
cert_test_block_3 78720 17 272 288 16
cert_test_block_3 78720 18 288 304 16
cert_test_block_3 78720 19 304 320 16
cert_test_block_3 78720 20 320 336 16
cert_test_block_3 78720 21 336 352 16
cert_test_block_3 78720 22 352 368 16
cert_test_block_3 78720 23 368 384 16
cert_test_block_3 78720 24 384 400 16
cert_test_block_3 78720 25 400 416 16
cert_test_block_3 78720 26 416 432 16
cert_test_block_3 78720 27 432 448 16
cert_test_block_3 78720 28 448 464 16
cert_test_block_3 78720 29 464 480 16
cert_test_block_3 78720 30 480 496 16
cert_test_block_3 78720 31 496 512 16
cert_test_block_3 78720 32 512 528 16
cert_test_block_3 78720 33 528 544 16
cert_test_block_3 78720 34 544 560 16
cert_test_block_3 78720 35 560 576 16
cert_test_block_3 78720 36 576 592 16
cert_test_block_3 78720 37 592 608 16
cert_test_block_3 78720 38 608 624 16
cert_test_block_3 78720 39 624 640 16
theorem test78720_complete : Interval test78720 0 640 :=
  (interval_append test78720 0 320 640
  (interval_append test78720 0 160 320
  (interval_append test78720 0 80 160
  (interval_append test78720 0 32 80
  (interval_append test78720 0 16 32
  test78720_block_0
  test78720_block_1)
  (interval_append test78720 32 48 80
  test78720_block_2
  (interval_append test78720 48 64 80
  test78720_block_3
  test78720_block_4)))
  (interval_append test78720 80 112 160
  (interval_append test78720 80 96 112
  test78720_block_5
  test78720_block_6)
  (interval_append test78720 112 128 160
  test78720_block_7
  (interval_append test78720 128 144 160
  test78720_block_8
  test78720_block_9))))
  (interval_append test78720 160 240 320
  (interval_append test78720 160 192 240
  (interval_append test78720 160 176 192
  test78720_block_10
  test78720_block_11)
  (interval_append test78720 192 208 240
  test78720_block_12
  (interval_append test78720 208 224 240
  test78720_block_13
  test78720_block_14)))
  (interval_append test78720 240 272 320
  (interval_append test78720 240 256 272
  test78720_block_15
  test78720_block_16)
  (interval_append test78720 272 288 320
  test78720_block_17
  (interval_append test78720 288 304 320
  test78720_block_18
  test78720_block_19)))))
  (interval_append test78720 320 480 640
  (interval_append test78720 320 400 480
  (interval_append test78720 320 352 400
  (interval_append test78720 320 336 352
  test78720_block_20
  test78720_block_21)
  (interval_append test78720 352 368 400
  test78720_block_22
  (interval_append test78720 368 384 400
  test78720_block_23
  test78720_block_24)))
  (interval_append test78720 400 432 480
  (interval_append test78720 400 416 432
  test78720_block_25
  test78720_block_26)
  (interval_append test78720 432 448 480
  test78720_block_27
  (interval_append test78720 448 464 480
  test78720_block_28
  test78720_block_29))))
  (interval_append test78720 480 560 640
  (interval_append test78720 480 512 560
  (interval_append test78720 480 496 512
  test78720_block_30
  test78720_block_31)
  (interval_append test78720 512 528 560
  test78720_block_32
  (interval_append test78720 528 544 560
  test78720_block_33
  test78720_block_34)))
  (interval_append test78720 560 592 640
  (interval_append test78720 560 576 592
  test78720_block_35
  test78720_block_36)
  (interval_append test78720 592 608 640
  test78720_block_37
  (interval_append test78720 608 624 640
  test78720_block_38
  test78720_block_39))))))
cert_nodeInterval_3 78720 79360
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
cert_test_11 79360
cert_test_block_3 79360 0 0 16 16
cert_test_block_3 79360 1 16 32 16
cert_test_block_3 79360 2 32 48 16
cert_test_block_3 79360 3 48 64 16
cert_test_block_3 79360 4 64 80 16
cert_test_block_3 79360 5 80 96 16
cert_test_block_3 79360 6 96 112 16
cert_test_block_3 79360 7 112 128 16
cert_test_block_3 79360 8 128 144 16
cert_test_block_3 79360 9 144 160 16
cert_test_block_3 79360 10 160 176 16
cert_test_block_3 79360 11 176 192 16
cert_test_block_3 79360 12 192 208 16
cert_test_block_3 79360 13 208 224 16
cert_test_block_3 79360 14 224 240 16
cert_test_block_3 79360 15 240 256 16
cert_test_block_3 79360 16 256 272 16
cert_test_block_3 79360 17 272 288 16
cert_test_block_3 79360 18 288 304 16
cert_test_block_3 79360 19 304 320 16
cert_test_block_3 79360 20 320 336 16
cert_test_block_3 79360 21 336 352 16
cert_test_block_3 79360 22 352 368 16
cert_test_block_3 79360 23 368 384 16
cert_test_block_3 79360 24 384 400 16
cert_test_block_3 79360 25 400 416 16
cert_test_block_3 79360 26 416 432 16
cert_test_block_3 79360 27 432 448 16
cert_test_block_3 79360 28 448 464 16
cert_test_block_3 79360 29 464 480 16
cert_test_block_3 79360 30 480 496 16
cert_test_block_3 79360 31 496 512 16
cert_test_block_3 79360 32 512 528 16
cert_test_block_3 79360 33 528 544 16
cert_test_block_3 79360 34 544 560 16
cert_test_block_3 79360 35 560 576 16
cert_test_block_3 79360 36 576 592 16
cert_test_block_3 79360 37 592 608 16
cert_test_block_3 79360 38 608 624 16
cert_test_block_3 79360 39 624 640 16
theorem test79360_complete : Interval test79360 0 640 :=
  (interval_append test79360 0 320 640
  (interval_append test79360 0 160 320
  (interval_append test79360 0 80 160
  (interval_append test79360 0 32 80
  (interval_append test79360 0 16 32
  test79360_block_0
  test79360_block_1)
  (interval_append test79360 32 48 80
  test79360_block_2
  (interval_append test79360 48 64 80
  test79360_block_3
  test79360_block_4)))
  (interval_append test79360 80 112 160
  (interval_append test79360 80 96 112
  test79360_block_5
  test79360_block_6)
  (interval_append test79360 112 128 160
  test79360_block_7
  (interval_append test79360 128 144 160
  test79360_block_8
  test79360_block_9))))
  (interval_append test79360 160 240 320
  (interval_append test79360 160 192 240
  (interval_append test79360 160 176 192
  test79360_block_10
  test79360_block_11)
  (interval_append test79360 192 208 240
  test79360_block_12
  (interval_append test79360 208 224 240
  test79360_block_13
  test79360_block_14)))
  (interval_append test79360 240 272 320
  (interval_append test79360 240 256 272
  test79360_block_15
  test79360_block_16)
  (interval_append test79360 272 288 320
  test79360_block_17
  (interval_append test79360 288 304 320
  test79360_block_18
  test79360_block_19)))))
  (interval_append test79360 320 480 640
  (interval_append test79360 320 400 480
  (interval_append test79360 320 352 400
  (interval_append test79360 320 336 352
  test79360_block_20
  test79360_block_21)
  (interval_append test79360 352 368 400
  test79360_block_22
  (interval_append test79360 368 384 400
  test79360_block_23
  test79360_block_24)))
  (interval_append test79360 400 432 480
  (interval_append test79360 400 416 432
  test79360_block_25
  test79360_block_26)
  (interval_append test79360 432 448 480
  test79360_block_27
  (interval_append test79360 448 464 480
  test79360_block_28
  test79360_block_29))))
  (interval_append test79360 480 560 640
  (interval_append test79360 480 512 560
  (interval_append test79360 480 496 512
  test79360_block_30
  test79360_block_31)
  (interval_append test79360 512 528 560
  test79360_block_32
  (interval_append test79360 528 544 560
  test79360_block_33
  test79360_block_34)))
  (interval_append test79360 560 592 640
  (interval_append test79360 560 576 592
  test79360_block_35
  test79360_block_36)
  (interval_append test79360 592 608 640
  test79360_block_37
  (interval_append test79360 608 624 640
  test79360_block_38
  test79360_block_39))))))
cert_nodeInterval_3 79360 80000
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
cert_test_11 80000
cert_test_block_3 80000 0 0 16 16
cert_test_block_3 80000 1 16 32 16
cert_test_block_3 80000 2 32 48 16
cert_test_block_3 80000 3 48 64 16
cert_test_block_3 80000 4 64 80 16
cert_test_block_3 80000 5 80 96 16
cert_test_block_3 80000 6 96 112 16
cert_test_block_3 80000 7 112 128 16
cert_test_block_3 80000 8 128 144 16
cert_test_block_3 80000 9 144 160 16
cert_test_block_3 80000 10 160 176 16
cert_test_block_3 80000 11 176 192 16
cert_test_block_3 80000 12 192 208 16
cert_test_block_3 80000 13 208 224 16
cert_test_block_3 80000 14 224 240 16
cert_test_block_3 80000 15 240 256 16
cert_test_block_3 80000 16 256 272 16
cert_test_block_3 80000 17 272 288 16
cert_test_block_3 80000 18 288 304 16
cert_test_block_3 80000 19 304 320 16
cert_test_block_3 80000 20 320 336 16
cert_test_block_3 80000 21 336 352 16
cert_test_block_3 80000 22 352 368 16
cert_test_block_3 80000 23 368 384 16
cert_test_block_3 80000 24 384 400 16
cert_test_block_3 80000 25 400 416 16
cert_test_block_3 80000 26 416 432 16
cert_test_block_3 80000 27 432 448 16
cert_test_block_3 80000 28 448 464 16
cert_test_block_3 80000 29 464 480 16
cert_test_block_3 80000 30 480 496 16
cert_test_block_3 80000 31 496 512 16
cert_test_block_3 80000 32 512 528 16
cert_test_block_3 80000 33 528 544 16
cert_test_block_3 80000 34 544 560 16
cert_test_block_3 80000 35 560 576 16
cert_test_block_3 80000 36 576 592 16
cert_test_block_3 80000 37 592 608 16
cert_test_block_3 80000 38 608 624 16
cert_test_block_3 80000 39 624 640 16
theorem test80000_complete : Interval test80000 0 640 :=
  (interval_append test80000 0 320 640
  (interval_append test80000 0 160 320
  (interval_append test80000 0 80 160
  (interval_append test80000 0 32 80
  (interval_append test80000 0 16 32
  test80000_block_0
  test80000_block_1)
  (interval_append test80000 32 48 80
  test80000_block_2
  (interval_append test80000 48 64 80
  test80000_block_3
  test80000_block_4)))
  (interval_append test80000 80 112 160
  (interval_append test80000 80 96 112
  test80000_block_5
  test80000_block_6)
  (interval_append test80000 112 128 160
  test80000_block_7
  (interval_append test80000 128 144 160
  test80000_block_8
  test80000_block_9))))
  (interval_append test80000 160 240 320
  (interval_append test80000 160 192 240
  (interval_append test80000 160 176 192
  test80000_block_10
  test80000_block_11)
  (interval_append test80000 192 208 240
  test80000_block_12
  (interval_append test80000 208 224 240
  test80000_block_13
  test80000_block_14)))
  (interval_append test80000 240 272 320
  (interval_append test80000 240 256 272
  test80000_block_15
  test80000_block_16)
  (interval_append test80000 272 288 320
  test80000_block_17
  (interval_append test80000 288 304 320
  test80000_block_18
  test80000_block_19)))))
  (interval_append test80000 320 480 640
  (interval_append test80000 320 400 480
  (interval_append test80000 320 352 400
  (interval_append test80000 320 336 352
  test80000_block_20
  test80000_block_21)
  (interval_append test80000 352 368 400
  test80000_block_22
  (interval_append test80000 368 384 400
  test80000_block_23
  test80000_block_24)))
  (interval_append test80000 400 432 480
  (interval_append test80000 400 416 432
  test80000_block_25
  test80000_block_26)
  (interval_append test80000 432 448 480
  test80000_block_27
  (interval_append test80000 448 464 480
  test80000_block_28
  test80000_block_29))))
  (interval_append test80000 480 560 640
  (interval_append test80000 480 512 560
  (interval_append test80000 480 496 512
  test80000_block_30
  test80000_block_31)
  (interval_append test80000 512 528 560
  test80000_block_32
  (interval_append test80000 528 544 560
  test80000_block_33
  test80000_block_34)))
  (interval_append test80000 560 592 640
  (interval_append test80000 560 576 592
  test80000_block_35
  test80000_block_36)
  (interval_append test80000 592 608 640
  test80000_block_37
  (interval_append test80000 608 624 640
  test80000_block_38
  test80000_block_39))))))
cert_nodeInterval_3 80000 80640
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
cert_test_11 80640
cert_test_block_3 80640 0 0 16 16
cert_test_block_3 80640 1 16 32 16
cert_test_block_3 80640 2 32 48 16
cert_test_block_3 80640 3 48 64 16
cert_test_block_3 80640 4 64 80 16
cert_test_block_3 80640 5 80 96 16
cert_test_block_3 80640 6 96 112 16
cert_test_block_3 80640 7 112 128 16
cert_test_block_3 80640 8 128 144 16
cert_test_block_3 80640 9 144 160 16
cert_test_block_3 80640 10 160 176 16
cert_test_block_3 80640 11 176 192 16
cert_test_block_3 80640 12 192 208 16
cert_test_block_3 80640 13 208 224 16
cert_test_block_3 80640 14 224 240 16
cert_test_block_3 80640 15 240 256 16
cert_test_block_3 80640 16 256 272 16
cert_test_block_3 80640 17 272 288 16
cert_test_block_3 80640 18 288 304 16
cert_test_block_3 80640 19 304 320 16
cert_test_block_3 80640 20 320 336 16
cert_test_block_3 80640 21 336 352 16
cert_test_block_3 80640 22 352 368 16
cert_test_block_3 80640 23 368 384 16
cert_test_block_3 80640 24 384 400 16
cert_test_block_3 80640 25 400 416 16
cert_test_block_3 80640 26 416 432 16
cert_test_block_3 80640 27 432 448 16
cert_test_block_3 80640 28 448 464 16
cert_test_block_3 80640 29 464 480 16
cert_test_block_3 80640 30 480 496 16
cert_test_block_3 80640 31 496 512 16
cert_test_block_3 80640 32 512 528 16
cert_test_block_3 80640 33 528 544 16
cert_test_block_3 80640 34 544 560 16
cert_test_block_3 80640 35 560 576 16
cert_test_block_3 80640 36 576 592 16
cert_test_block_3 80640 37 592 608 16
cert_test_block_3 80640 38 608 624 16
cert_test_block_3 80640 39 624 640 16
theorem test80640_complete : Interval test80640 0 640 :=
  (interval_append test80640 0 320 640
  (interval_append test80640 0 160 320
  (interval_append test80640 0 80 160
  (interval_append test80640 0 32 80
  (interval_append test80640 0 16 32
  test80640_block_0
  test80640_block_1)
  (interval_append test80640 32 48 80
  test80640_block_2
  (interval_append test80640 48 64 80
  test80640_block_3
  test80640_block_4)))
  (interval_append test80640 80 112 160
  (interval_append test80640 80 96 112
  test80640_block_5
  test80640_block_6)
  (interval_append test80640 112 128 160
  test80640_block_7
  (interval_append test80640 128 144 160
  test80640_block_8
  test80640_block_9))))
  (interval_append test80640 160 240 320
  (interval_append test80640 160 192 240
  (interval_append test80640 160 176 192
  test80640_block_10
  test80640_block_11)
  (interval_append test80640 192 208 240
  test80640_block_12
  (interval_append test80640 208 224 240
  test80640_block_13
  test80640_block_14)))
  (interval_append test80640 240 272 320
  (interval_append test80640 240 256 272
  test80640_block_15
  test80640_block_16)
  (interval_append test80640 272 288 320
  test80640_block_17
  (interval_append test80640 288 304 320
  test80640_block_18
  test80640_block_19)))))
  (interval_append test80640 320 480 640
  (interval_append test80640 320 400 480
  (interval_append test80640 320 352 400
  (interval_append test80640 320 336 352
  test80640_block_20
  test80640_block_21)
  (interval_append test80640 352 368 400
  test80640_block_22
  (interval_append test80640 368 384 400
  test80640_block_23
  test80640_block_24)))
  (interval_append test80640 400 432 480
  (interval_append test80640 400 416 432
  test80640_block_25
  test80640_block_26)
  (interval_append test80640 432 448 480
  test80640_block_27
  (interval_append test80640 448 464 480
  test80640_block_28
  test80640_block_29))))
  (interval_append test80640 480 560 640
  (interval_append test80640 480 512 560
  (interval_append test80640 480 496 512
  test80640_block_30
  test80640_block_31)
  (interval_append test80640 512 528 560
  test80640_block_32
  (interval_append test80640 528 544 560
  test80640_block_33
  test80640_block_34)))
  (interval_append test80640 560 592 640
  (interval_append test80640 560 576 592
  test80640_block_35
  test80640_block_36)
  (interval_append test80640 592 608 640
  test80640_block_37
  (interval_append test80640 608 624 640
  test80640_block_38
  test80640_block_39))))))
cert_nodeInterval_3 80640 81280
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
cert_test_11 81280
cert_test_block_3 81280 0 0 16 16
cert_test_block_3 81280 1 16 32 16
cert_test_block_3 81280 2 32 48 16
cert_test_block_3 81280 3 48 64 16
cert_test_block_3 81280 4 64 80 16
cert_test_block_3 81280 5 80 96 16
cert_test_block_3 81280 6 96 112 16
cert_test_block_3 81280 7 112 128 16
cert_test_block_3 81280 8 128 144 16
cert_test_block_3 81280 9 144 160 16
cert_test_block_3 81280 10 160 176 16
cert_test_block_3 81280 11 176 192 16
cert_test_block_3 81280 12 192 208 16
cert_test_block_3 81280 13 208 224 16
cert_test_block_3 81280 14 224 240 16
cert_test_block_3 81280 15 240 256 16
cert_test_block_3 81280 16 256 272 16
cert_test_block_3 81280 17 272 288 16
cert_test_block_3 81280 18 288 304 16
cert_test_block_3 81280 19 304 320 16
cert_test_block_3 81280 20 320 336 16
cert_test_block_3 81280 21 336 352 16
cert_test_block_3 81280 22 352 368 16
cert_test_block_3 81280 23 368 384 16
cert_test_block_3 81280 24 384 400 16
cert_test_block_3 81280 25 400 416 16
cert_test_block_3 81280 26 416 432 16
cert_test_block_3 81280 27 432 448 16
cert_test_block_3 81280 28 448 464 16
cert_test_block_3 81280 29 464 480 16
cert_test_block_3 81280 30 480 496 16
cert_test_block_3 81280 31 496 512 16
cert_test_block_3 81280 32 512 528 16
cert_test_block_3 81280 33 528 544 16
cert_test_block_3 81280 34 544 560 16
cert_test_block_3 81280 35 560 576 16
cert_test_block_3 81280 36 576 592 16
cert_test_block_3 81280 37 592 608 16
cert_test_block_3 81280 38 608 624 16
cert_test_block_3 81280 39 624 640 16
theorem test81280_complete : Interval test81280 0 640 :=
  (interval_append test81280 0 320 640
  (interval_append test81280 0 160 320
  (interval_append test81280 0 80 160
  (interval_append test81280 0 32 80
  (interval_append test81280 0 16 32
  test81280_block_0
  test81280_block_1)
  (interval_append test81280 32 48 80
  test81280_block_2
  (interval_append test81280 48 64 80
  test81280_block_3
  test81280_block_4)))
  (interval_append test81280 80 112 160
  (interval_append test81280 80 96 112
  test81280_block_5
  test81280_block_6)
  (interval_append test81280 112 128 160
  test81280_block_7
  (interval_append test81280 128 144 160
  test81280_block_8
  test81280_block_9))))
  (interval_append test81280 160 240 320
  (interval_append test81280 160 192 240
  (interval_append test81280 160 176 192
  test81280_block_10
  test81280_block_11)
  (interval_append test81280 192 208 240
  test81280_block_12
  (interval_append test81280 208 224 240
  test81280_block_13
  test81280_block_14)))
  (interval_append test81280 240 272 320
  (interval_append test81280 240 256 272
  test81280_block_15
  test81280_block_16)
  (interval_append test81280 272 288 320
  test81280_block_17
  (interval_append test81280 288 304 320
  test81280_block_18
  test81280_block_19)))))
  (interval_append test81280 320 480 640
  (interval_append test81280 320 400 480
  (interval_append test81280 320 352 400
  (interval_append test81280 320 336 352
  test81280_block_20
  test81280_block_21)
  (interval_append test81280 352 368 400
  test81280_block_22
  (interval_append test81280 368 384 400
  test81280_block_23
  test81280_block_24)))
  (interval_append test81280 400 432 480
  (interval_append test81280 400 416 432
  test81280_block_25
  test81280_block_26)
  (interval_append test81280 432 448 480
  test81280_block_27
  (interval_append test81280 448 464 480
  test81280_block_28
  test81280_block_29))))
  (interval_append test81280 480 560 640
  (interval_append test81280 480 512 560
  (interval_append test81280 480 496 512
  test81280_block_30
  test81280_block_31)
  (interval_append test81280 512 528 560
  test81280_block_32
  (interval_append test81280 528 544 560
  test81280_block_33
  test81280_block_34)))
  (interval_append test81280 560 592 640
  (interval_append test81280 560 576 592
  test81280_block_35
  test81280_block_36)
  (interval_append test81280 592 608 640
  test81280_block_37
  (interval_append test81280 608 624 640
  test81280_block_38
  test81280_block_39))))))
cert_nodeInterval_3 81280 81920
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
cert_test_11 81920
cert_test_block_3 81920 0 0 16 16
cert_test_block_3 81920 1 16 32 16
cert_test_block_3 81920 2 32 48 16
cert_test_block_3 81920 3 48 64 16
cert_test_block_3 81920 4 64 80 16
cert_test_block_3 81920 5 80 96 16
cert_test_block_3 81920 6 96 112 16
cert_test_block_3 81920 7 112 128 16
cert_test_block_3 81920 8 128 144 16
cert_test_block_3 81920 9 144 160 16
cert_test_block_3 81920 10 160 176 16
cert_test_block_3 81920 11 176 192 16
cert_test_block_3 81920 12 192 208 16
cert_test_block_3 81920 13 208 224 16
cert_test_block_3 81920 14 224 240 16
cert_test_block_3 81920 15 240 256 16
cert_test_block_3 81920 16 256 272 16
cert_test_block_3 81920 17 272 288 16
cert_test_block_3 81920 18 288 304 16
cert_test_block_3 81920 19 304 320 16
cert_test_block_3 81920 20 320 336 16
cert_test_block_3 81920 21 336 352 16
cert_test_block_3 81920 22 352 368 16
cert_test_block_3 81920 23 368 384 16
cert_test_block_3 81920 24 384 400 16
cert_test_block_3 81920 25 400 416 16
cert_test_block_3 81920 26 416 432 16
cert_test_block_3 81920 27 432 448 16
cert_test_block_3 81920 28 448 464 16
cert_test_block_3 81920 29 464 480 16
cert_test_block_3 81920 30 480 496 16
cert_test_block_3 81920 31 496 512 16
cert_test_block_3 81920 32 512 528 16
cert_test_block_3 81920 33 528 544 16
cert_test_block_3 81920 34 544 560 16
cert_test_block_3 81920 35 560 576 16
cert_test_block_3 81920 36 576 592 16
cert_test_block_3 81920 37 592 608 16
cert_test_block_3 81920 38 608 624 16
cert_test_block_3 81920 39 624 640 16
theorem test81920_complete : Interval test81920 0 640 :=
  (interval_append test81920 0 320 640
  (interval_append test81920 0 160 320
  (interval_append test81920 0 80 160
  (interval_append test81920 0 32 80
  (interval_append test81920 0 16 32
  test81920_block_0
  test81920_block_1)
  (interval_append test81920 32 48 80
  test81920_block_2
  (interval_append test81920 48 64 80
  test81920_block_3
  test81920_block_4)))
  (interval_append test81920 80 112 160
  (interval_append test81920 80 96 112
  test81920_block_5
  test81920_block_6)
  (interval_append test81920 112 128 160
  test81920_block_7
  (interval_append test81920 128 144 160
  test81920_block_8
  test81920_block_9))))
  (interval_append test81920 160 240 320
  (interval_append test81920 160 192 240
  (interval_append test81920 160 176 192
  test81920_block_10
  test81920_block_11)
  (interval_append test81920 192 208 240
  test81920_block_12
  (interval_append test81920 208 224 240
  test81920_block_13
  test81920_block_14)))
  (interval_append test81920 240 272 320
  (interval_append test81920 240 256 272
  test81920_block_15
  test81920_block_16)
  (interval_append test81920 272 288 320
  test81920_block_17
  (interval_append test81920 288 304 320
  test81920_block_18
  test81920_block_19)))))
  (interval_append test81920 320 480 640
  (interval_append test81920 320 400 480
  (interval_append test81920 320 352 400
  (interval_append test81920 320 336 352
  test81920_block_20
  test81920_block_21)
  (interval_append test81920 352 368 400
  test81920_block_22
  (interval_append test81920 368 384 400
  test81920_block_23
  test81920_block_24)))
  (interval_append test81920 400 432 480
  (interval_append test81920 400 416 432
  test81920_block_25
  test81920_block_26)
  (interval_append test81920 432 448 480
  test81920_block_27
  (interval_append test81920 448 464 480
  test81920_block_28
  test81920_block_29))))
  (interval_append test81920 480 560 640
  (interval_append test81920 480 512 560
  (interval_append test81920 480 496 512
  test81920_block_30
  test81920_block_31)
  (interval_append test81920 512 528 560
  test81920_block_32
  (interval_append test81920 528 544 560
  test81920_block_33
  test81920_block_34)))
  (interval_append test81920 560 592 640
  (interval_append test81920 560 576 592
  test81920_block_35
  test81920_block_36)
  (interval_append test81920 592 608 640
  test81920_block_37
  (interval_append test81920 608 624 640
  test81920_block_38
  test81920_block_39))))))
cert_nodeInterval_3 81920 82560
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
cert_test_11 82560
cert_test_block_3 82560 0 0 16 16
cert_test_block_3 82560 1 16 32 16
cert_test_block_3 82560 2 32 48 16
cert_test_block_3 82560 3 48 64 16
cert_test_block_3 82560 4 64 80 16
cert_test_block_3 82560 5 80 96 16
cert_test_block_3 82560 6 96 112 16
cert_test_block_3 82560 7 112 128 16
cert_test_block_3 82560 8 128 144 16
cert_test_block_3 82560 9 144 160 16
cert_test_block_3 82560 10 160 176 16
cert_test_block_3 82560 11 176 192 16
cert_test_block_3 82560 12 192 208 16
cert_test_block_3 82560 13 208 224 16
cert_test_block_3 82560 14 224 240 16
cert_test_block_3 82560 15 240 256 16
cert_test_block_3 82560 16 256 272 16
cert_test_block_3 82560 17 272 288 16
cert_test_block_3 82560 18 288 304 16
cert_test_block_3 82560 19 304 320 16
cert_test_block_3 82560 20 320 336 16
cert_test_block_3 82560 21 336 352 16
cert_test_block_3 82560 22 352 368 16
cert_test_block_3 82560 23 368 384 16
cert_test_block_3 82560 24 384 400 16
cert_test_block_3 82560 25 400 416 16
cert_test_block_3 82560 26 416 432 16
cert_test_block_3 82560 27 432 448 16
cert_test_block_3 82560 28 448 464 16
cert_test_block_3 82560 29 464 480 16
cert_test_block_3 82560 30 480 496 16
cert_test_block_3 82560 31 496 512 16
cert_test_block_3 82560 32 512 528 16
cert_test_block_3 82560 33 528 544 16
cert_test_block_3 82560 34 544 560 16
cert_test_block_3 82560 35 560 576 16
cert_test_block_3 82560 36 576 592 16
cert_test_block_3 82560 37 592 608 16
cert_test_block_3 82560 38 608 624 16
cert_test_block_3 82560 39 624 640 16
theorem test82560_complete : Interval test82560 0 640 :=
  (interval_append test82560 0 320 640
  (interval_append test82560 0 160 320
  (interval_append test82560 0 80 160
  (interval_append test82560 0 32 80
  (interval_append test82560 0 16 32
  test82560_block_0
  test82560_block_1)
  (interval_append test82560 32 48 80
  test82560_block_2
  (interval_append test82560 48 64 80
  test82560_block_3
  test82560_block_4)))
  (interval_append test82560 80 112 160
  (interval_append test82560 80 96 112
  test82560_block_5
  test82560_block_6)
  (interval_append test82560 112 128 160
  test82560_block_7
  (interval_append test82560 128 144 160
  test82560_block_8
  test82560_block_9))))
  (interval_append test82560 160 240 320
  (interval_append test82560 160 192 240
  (interval_append test82560 160 176 192
  test82560_block_10
  test82560_block_11)
  (interval_append test82560 192 208 240
  test82560_block_12
  (interval_append test82560 208 224 240
  test82560_block_13
  test82560_block_14)))
  (interval_append test82560 240 272 320
  (interval_append test82560 240 256 272
  test82560_block_15
  test82560_block_16)
  (interval_append test82560 272 288 320
  test82560_block_17
  (interval_append test82560 288 304 320
  test82560_block_18
  test82560_block_19)))))
  (interval_append test82560 320 480 640
  (interval_append test82560 320 400 480
  (interval_append test82560 320 352 400
  (interval_append test82560 320 336 352
  test82560_block_20
  test82560_block_21)
  (interval_append test82560 352 368 400
  test82560_block_22
  (interval_append test82560 368 384 400
  test82560_block_23
  test82560_block_24)))
  (interval_append test82560 400 432 480
  (interval_append test82560 400 416 432
  test82560_block_25
  test82560_block_26)
  (interval_append test82560 432 448 480
  test82560_block_27
  (interval_append test82560 448 464 480
  test82560_block_28
  test82560_block_29))))
  (interval_append test82560 480 560 640
  (interval_append test82560 480 512 560
  (interval_append test82560 480 496 512
  test82560_block_30
  test82560_block_31)
  (interval_append test82560 512 528 560
  test82560_block_32
  (interval_append test82560 528 544 560
  test82560_block_33
  test82560_block_34)))
  (interval_append test82560 560 592 640
  (interval_append test82560 560 576 592
  test82560_block_35
  test82560_block_36)
  (interval_append test82560 592 608 640
  test82560_block_37
  (interval_append test82560 608 624 640
  test82560_block_38
  test82560_block_39))))))
cert_nodeInterval_3 82560 83200
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
cert_test_11 83200
cert_test_block_3 83200 0 0 16 16
cert_test_block_3 83200 1 16 32 16
cert_test_block_3 83200 2 32 48 16
cert_test_block_3 83200 3 48 64 16
cert_test_block_3 83200 4 64 80 16
cert_test_block_3 83200 5 80 96 16
cert_test_block_3 83200 6 96 112 16
cert_test_block_3 83200 7 112 128 16
cert_test_block_3 83200 8 128 144 16
cert_test_block_3 83200 9 144 160 16
cert_test_block_3 83200 10 160 176 16
cert_test_block_3 83200 11 176 192 16
cert_test_block_3 83200 12 192 208 16
cert_test_block_3 83200 13 208 224 16
cert_test_block_3 83200 14 224 240 16
cert_test_block_3 83200 15 240 256 16
cert_test_block_3 83200 16 256 272 16
cert_test_block_3 83200 17 272 288 16
cert_test_block_3 83200 18 288 304 16
cert_test_block_3 83200 19 304 320 16
cert_test_block_3 83200 20 320 336 16
cert_test_block_3 83200 21 336 352 16
cert_test_block_3 83200 22 352 368 16
cert_test_block_3 83200 23 368 384 16
cert_test_block_3 83200 24 384 400 16
cert_test_block_3 83200 25 400 416 16
cert_test_block_3 83200 26 416 432 16
cert_test_block_3 83200 27 432 448 16
cert_test_block_3 83200 28 448 464 16
cert_test_block_3 83200 29 464 480 16
cert_test_block_3 83200 30 480 496 16
cert_test_block_3 83200 31 496 512 16
cert_test_block_3 83200 32 512 528 16
cert_test_block_3 83200 33 528 544 16
cert_test_block_3 83200 34 544 560 16
cert_test_block_3 83200 35 560 576 16
cert_test_block_3 83200 36 576 592 16
cert_test_block_3 83200 37 592 608 16
cert_test_block_3 83200 38 608 624 16
cert_test_block_3 83200 39 624 640 16
theorem test83200_complete : Interval test83200 0 640 :=
  (interval_append test83200 0 320 640
  (interval_append test83200 0 160 320
  (interval_append test83200 0 80 160
  (interval_append test83200 0 32 80
  (interval_append test83200 0 16 32
  test83200_block_0
  test83200_block_1)
  (interval_append test83200 32 48 80
  test83200_block_2
  (interval_append test83200 48 64 80
  test83200_block_3
  test83200_block_4)))
  (interval_append test83200 80 112 160
  (interval_append test83200 80 96 112
  test83200_block_5
  test83200_block_6)
  (interval_append test83200 112 128 160
  test83200_block_7
  (interval_append test83200 128 144 160
  test83200_block_8
  test83200_block_9))))
  (interval_append test83200 160 240 320
  (interval_append test83200 160 192 240
  (interval_append test83200 160 176 192
  test83200_block_10
  test83200_block_11)
  (interval_append test83200 192 208 240
  test83200_block_12
  (interval_append test83200 208 224 240
  test83200_block_13
  test83200_block_14)))
  (interval_append test83200 240 272 320
  (interval_append test83200 240 256 272
  test83200_block_15
  test83200_block_16)
  (interval_append test83200 272 288 320
  test83200_block_17
  (interval_append test83200 288 304 320
  test83200_block_18
  test83200_block_19)))))
  (interval_append test83200 320 480 640
  (interval_append test83200 320 400 480
  (interval_append test83200 320 352 400
  (interval_append test83200 320 336 352
  test83200_block_20
  test83200_block_21)
  (interval_append test83200 352 368 400
  test83200_block_22
  (interval_append test83200 368 384 400
  test83200_block_23
  test83200_block_24)))
  (interval_append test83200 400 432 480
  (interval_append test83200 400 416 432
  test83200_block_25
  test83200_block_26)
  (interval_append test83200 432 448 480
  test83200_block_27
  (interval_append test83200 448 464 480
  test83200_block_28
  test83200_block_29))))
  (interval_append test83200 480 560 640
  (interval_append test83200 480 512 560
  (interval_append test83200 480 496 512
  test83200_block_30
  test83200_block_31)
  (interval_append test83200 512 528 560
  test83200_block_32
  (interval_append test83200 528 544 560
  test83200_block_33
  test83200_block_34)))
  (interval_append test83200 560 592 640
  (interval_append test83200 560 576 592
  test83200_block_35
  test83200_block_36)
  (interval_append test83200 592 608 640
  test83200_block_37
  (interval_append test83200 608 624 640
  test83200_block_38
  test83200_block_39))))))
cert_nodeInterval_3 83200 83840
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
cert_test_11 83840
cert_test_block_3 83840 0 0 16 16
cert_test_block_3 83840 1 16 32 16
cert_test_block_3 83840 2 32 48 16
cert_test_block_3 83840 3 48 64 16
cert_test_block_3 83840 4 64 80 16
cert_test_block_3 83840 5 80 96 16
cert_test_block_3 83840 6 96 112 16
cert_test_block_3 83840 7 112 128 16
cert_test_block_3 83840 8 128 144 16
cert_test_block_3 83840 9 144 160 16
cert_test_block_3 83840 10 160 176 16
cert_test_block_3 83840 11 176 192 16
cert_test_block_3 83840 12 192 208 16
cert_test_block_3 83840 13 208 224 16
cert_test_block_3 83840 14 224 240 16
cert_test_block_3 83840 15 240 256 16
cert_test_block_3 83840 16 256 272 16
cert_test_block_3 83840 17 272 288 16
cert_test_block_3 83840 18 288 304 16
cert_test_block_3 83840 19 304 320 16
cert_test_block_3 83840 20 320 336 16
cert_test_block_3 83840 21 336 352 16
cert_test_block_3 83840 22 352 368 16
cert_test_block_3 83840 23 368 384 16
cert_test_block_3 83840 24 384 400 16
cert_test_block_3 83840 25 400 416 16
cert_test_block_3 83840 26 416 432 16
cert_test_block_3 83840 27 432 448 16
cert_test_block_3 83840 28 448 464 16
cert_test_block_3 83840 29 464 480 16
cert_test_block_3 83840 30 480 496 16
cert_test_block_3 83840 31 496 512 16
cert_test_block_3 83840 32 512 528 16
cert_test_block_3 83840 33 528 544 16
cert_test_block_3 83840 34 544 560 16
cert_test_block_3 83840 35 560 576 16
cert_test_block_3 83840 36 576 592 16
cert_test_block_3 83840 37 592 608 16
cert_test_block_3 83840 38 608 624 16
cert_test_block_3 83840 39 624 640 16
theorem test83840_complete : Interval test83840 0 640 :=
  (interval_append test83840 0 320 640
  (interval_append test83840 0 160 320
  (interval_append test83840 0 80 160
  (interval_append test83840 0 32 80
  (interval_append test83840 0 16 32
  test83840_block_0
  test83840_block_1)
  (interval_append test83840 32 48 80
  test83840_block_2
  (interval_append test83840 48 64 80
  test83840_block_3
  test83840_block_4)))
  (interval_append test83840 80 112 160
  (interval_append test83840 80 96 112
  test83840_block_5
  test83840_block_6)
  (interval_append test83840 112 128 160
  test83840_block_7
  (interval_append test83840 128 144 160
  test83840_block_8
  test83840_block_9))))
  (interval_append test83840 160 240 320
  (interval_append test83840 160 192 240
  (interval_append test83840 160 176 192
  test83840_block_10
  test83840_block_11)
  (interval_append test83840 192 208 240
  test83840_block_12
  (interval_append test83840 208 224 240
  test83840_block_13
  test83840_block_14)))
  (interval_append test83840 240 272 320
  (interval_append test83840 240 256 272
  test83840_block_15
  test83840_block_16)
  (interval_append test83840 272 288 320
  test83840_block_17
  (interval_append test83840 288 304 320
  test83840_block_18
  test83840_block_19)))))
  (interval_append test83840 320 480 640
  (interval_append test83840 320 400 480
  (interval_append test83840 320 352 400
  (interval_append test83840 320 336 352
  test83840_block_20
  test83840_block_21)
  (interval_append test83840 352 368 400
  test83840_block_22
  (interval_append test83840 368 384 400
  test83840_block_23
  test83840_block_24)))
  (interval_append test83840 400 432 480
  (interval_append test83840 400 416 432
  test83840_block_25
  test83840_block_26)
  (interval_append test83840 432 448 480
  test83840_block_27
  (interval_append test83840 448 464 480
  test83840_block_28
  test83840_block_29))))
  (interval_append test83840 480 560 640
  (interval_append test83840 480 512 560
  (interval_append test83840 480 496 512
  test83840_block_30
  test83840_block_31)
  (interval_append test83840 512 528 560
  test83840_block_32
  (interval_append test83840 528 544 560
  test83840_block_33
  test83840_block_34)))
  (interval_append test83840 560 592 640
  (interval_append test83840 560 576 592
  test83840_block_35
  test83840_block_36)
  (interval_append test83840 592 608 640
  test83840_block_37
  (interval_append test83840 608 624 640
  test83840_block_38
  test83840_block_39))))))
cert_nodeInterval_3 83840 84480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
