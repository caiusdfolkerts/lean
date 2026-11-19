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
cert_test_11 46080
cert_test_block_3 46080 0 0 16 16
cert_test_block_3 46080 1 16 32 16
cert_test_block_3 46080 2 32 48 16
cert_test_block_3 46080 3 48 64 16
cert_test_block_3 46080 4 64 80 16
cert_test_block_3 46080 5 80 96 16
cert_test_block_3 46080 6 96 112 16
cert_test_block_3 46080 7 112 128 16
cert_test_block_3 46080 8 128 144 16
cert_test_block_3 46080 9 144 160 16
cert_test_block_3 46080 10 160 176 16
cert_test_block_3 46080 11 176 192 16
cert_test_block_3 46080 12 192 208 16
cert_test_block_3 46080 13 208 224 16
cert_test_block_3 46080 14 224 240 16
cert_test_block_3 46080 15 240 256 16
cert_test_block_3 46080 16 256 272 16
cert_test_block_3 46080 17 272 288 16
cert_test_block_3 46080 18 288 304 16
cert_test_block_3 46080 19 304 320 16
cert_test_block_3 46080 20 320 336 16
cert_test_block_3 46080 21 336 352 16
cert_test_block_3 46080 22 352 368 16
cert_test_block_3 46080 23 368 384 16
cert_test_block_3 46080 24 384 400 16
cert_test_block_3 46080 25 400 416 16
cert_test_block_3 46080 26 416 432 16
cert_test_block_3 46080 27 432 448 16
cert_test_block_3 46080 28 448 464 16
cert_test_block_3 46080 29 464 480 16
cert_test_block_3 46080 30 480 496 16
cert_test_block_3 46080 31 496 512 16
cert_test_block_3 46080 32 512 528 16
cert_test_block_3 46080 33 528 544 16
cert_test_block_3 46080 34 544 560 16
cert_test_block_3 46080 35 560 576 16
cert_test_block_3 46080 36 576 592 16
cert_test_block_3 46080 37 592 608 16
cert_test_block_3 46080 38 608 624 16
cert_test_block_3 46080 39 624 640 16
theorem test46080_complete : Interval test46080 0 640 :=
  (interval_append test46080 0 320 640
  (interval_append test46080 0 160 320
  (interval_append test46080 0 80 160
  (interval_append test46080 0 32 80
  (interval_append test46080 0 16 32
  test46080_block_0
  test46080_block_1)
  (interval_append test46080 32 48 80
  test46080_block_2
  (interval_append test46080 48 64 80
  test46080_block_3
  test46080_block_4)))
  (interval_append test46080 80 112 160
  (interval_append test46080 80 96 112
  test46080_block_5
  test46080_block_6)
  (interval_append test46080 112 128 160
  test46080_block_7
  (interval_append test46080 128 144 160
  test46080_block_8
  test46080_block_9))))
  (interval_append test46080 160 240 320
  (interval_append test46080 160 192 240
  (interval_append test46080 160 176 192
  test46080_block_10
  test46080_block_11)
  (interval_append test46080 192 208 240
  test46080_block_12
  (interval_append test46080 208 224 240
  test46080_block_13
  test46080_block_14)))
  (interval_append test46080 240 272 320
  (interval_append test46080 240 256 272
  test46080_block_15
  test46080_block_16)
  (interval_append test46080 272 288 320
  test46080_block_17
  (interval_append test46080 288 304 320
  test46080_block_18
  test46080_block_19)))))
  (interval_append test46080 320 480 640
  (interval_append test46080 320 400 480
  (interval_append test46080 320 352 400
  (interval_append test46080 320 336 352
  test46080_block_20
  test46080_block_21)
  (interval_append test46080 352 368 400
  test46080_block_22
  (interval_append test46080 368 384 400
  test46080_block_23
  test46080_block_24)))
  (interval_append test46080 400 432 480
  (interval_append test46080 400 416 432
  test46080_block_25
  test46080_block_26)
  (interval_append test46080 432 448 480
  test46080_block_27
  (interval_append test46080 448 464 480
  test46080_block_28
  test46080_block_29))))
  (interval_append test46080 480 560 640
  (interval_append test46080 480 512 560
  (interval_append test46080 480 496 512
  test46080_block_30
  test46080_block_31)
  (interval_append test46080 512 528 560
  test46080_block_32
  (interval_append test46080 528 544 560
  test46080_block_33
  test46080_block_34)))
  (interval_append test46080 560 592 640
  (interval_append test46080 560 576 592
  test46080_block_35
  test46080_block_36)
  (interval_append test46080 592 608 640
  test46080_block_37
  (interval_append test46080 608 624 640
  test46080_block_38
  test46080_block_39))))))
cert_nodeInterval_3 46080 46720
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
cert_test_11 46720
cert_test_block_3 46720 0 0 16 16
cert_test_block_3 46720 1 16 32 16
cert_test_block_3 46720 2 32 48 16
cert_test_block_3 46720 3 48 64 16
cert_test_block_3 46720 4 64 80 16
cert_test_block_3 46720 5 80 96 16
cert_test_block_3 46720 6 96 112 16
cert_test_block_3 46720 7 112 128 16
cert_test_block_3 46720 8 128 144 16
cert_test_block_3 46720 9 144 160 16
cert_test_block_3 46720 10 160 176 16
cert_test_block_3 46720 11 176 192 16
cert_test_block_3 46720 12 192 208 16
cert_test_block_3 46720 13 208 224 16
cert_test_block_3 46720 14 224 240 16
cert_test_block_3 46720 15 240 256 16
cert_test_block_3 46720 16 256 272 16
cert_test_block_3 46720 17 272 288 16
cert_test_block_3 46720 18 288 304 16
cert_test_block_3 46720 19 304 320 16
cert_test_block_3 46720 20 320 336 16
cert_test_block_3 46720 21 336 352 16
cert_test_block_3 46720 22 352 368 16
cert_test_block_3 46720 23 368 384 16
cert_test_block_3 46720 24 384 400 16
cert_test_block_3 46720 25 400 416 16
cert_test_block_3 46720 26 416 432 16
cert_test_block_3 46720 27 432 448 16
cert_test_block_3 46720 28 448 464 16
cert_test_block_3 46720 29 464 480 16
cert_test_block_3 46720 30 480 496 16
cert_test_block_3 46720 31 496 512 16
cert_test_block_3 46720 32 512 528 16
cert_test_block_3 46720 33 528 544 16
cert_test_block_3 46720 34 544 560 16
cert_test_block_3 46720 35 560 576 16
cert_test_block_3 46720 36 576 592 16
cert_test_block_3 46720 37 592 608 16
cert_test_block_3 46720 38 608 624 16
cert_test_block_3 46720 39 624 640 16
theorem test46720_complete : Interval test46720 0 640 :=
  (interval_append test46720 0 320 640
  (interval_append test46720 0 160 320
  (interval_append test46720 0 80 160
  (interval_append test46720 0 32 80
  (interval_append test46720 0 16 32
  test46720_block_0
  test46720_block_1)
  (interval_append test46720 32 48 80
  test46720_block_2
  (interval_append test46720 48 64 80
  test46720_block_3
  test46720_block_4)))
  (interval_append test46720 80 112 160
  (interval_append test46720 80 96 112
  test46720_block_5
  test46720_block_6)
  (interval_append test46720 112 128 160
  test46720_block_7
  (interval_append test46720 128 144 160
  test46720_block_8
  test46720_block_9))))
  (interval_append test46720 160 240 320
  (interval_append test46720 160 192 240
  (interval_append test46720 160 176 192
  test46720_block_10
  test46720_block_11)
  (interval_append test46720 192 208 240
  test46720_block_12
  (interval_append test46720 208 224 240
  test46720_block_13
  test46720_block_14)))
  (interval_append test46720 240 272 320
  (interval_append test46720 240 256 272
  test46720_block_15
  test46720_block_16)
  (interval_append test46720 272 288 320
  test46720_block_17
  (interval_append test46720 288 304 320
  test46720_block_18
  test46720_block_19)))))
  (interval_append test46720 320 480 640
  (interval_append test46720 320 400 480
  (interval_append test46720 320 352 400
  (interval_append test46720 320 336 352
  test46720_block_20
  test46720_block_21)
  (interval_append test46720 352 368 400
  test46720_block_22
  (interval_append test46720 368 384 400
  test46720_block_23
  test46720_block_24)))
  (interval_append test46720 400 432 480
  (interval_append test46720 400 416 432
  test46720_block_25
  test46720_block_26)
  (interval_append test46720 432 448 480
  test46720_block_27
  (interval_append test46720 448 464 480
  test46720_block_28
  test46720_block_29))))
  (interval_append test46720 480 560 640
  (interval_append test46720 480 512 560
  (interval_append test46720 480 496 512
  test46720_block_30
  test46720_block_31)
  (interval_append test46720 512 528 560
  test46720_block_32
  (interval_append test46720 528 544 560
  test46720_block_33
  test46720_block_34)))
  (interval_append test46720 560 592 640
  (interval_append test46720 560 576 592
  test46720_block_35
  test46720_block_36)
  (interval_append test46720 592 608 640
  test46720_block_37
  (interval_append test46720 608 624 640
  test46720_block_38
  test46720_block_39))))))
cert_nodeInterval_3 46720 47360
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
cert_test_11 47360
cert_test_block_3 47360 0 0 16 16
cert_test_block_3 47360 1 16 32 16
cert_test_block_3 47360 2 32 48 16
cert_test_block_3 47360 3 48 64 16
cert_test_block_3 47360 4 64 80 16
cert_test_block_3 47360 5 80 96 16
cert_test_block_3 47360 6 96 112 16
cert_test_block_3 47360 7 112 128 16
cert_test_block_3 47360 8 128 144 16
cert_test_block_3 47360 9 144 160 16
cert_test_block_3 47360 10 160 176 16
cert_test_block_3 47360 11 176 192 16
cert_test_block_3 47360 12 192 208 16
cert_test_block_3 47360 13 208 224 16
cert_test_block_3 47360 14 224 240 16
cert_test_block_3 47360 15 240 256 16
cert_test_block_3 47360 16 256 272 16
cert_test_block_3 47360 17 272 288 16
cert_test_block_3 47360 18 288 304 16
cert_test_block_3 47360 19 304 320 16
cert_test_block_3 47360 20 320 336 16
cert_test_block_3 47360 21 336 352 16
cert_test_block_3 47360 22 352 368 16
cert_test_block_3 47360 23 368 384 16
cert_test_block_3 47360 24 384 400 16
cert_test_block_3 47360 25 400 416 16
cert_test_block_3 47360 26 416 432 16
cert_test_block_3 47360 27 432 448 16
cert_test_block_3 47360 28 448 464 16
cert_test_block_3 47360 29 464 480 16
cert_test_block_3 47360 30 480 496 16
cert_test_block_3 47360 31 496 512 16
cert_test_block_3 47360 32 512 528 16
cert_test_block_3 47360 33 528 544 16
cert_test_block_3 47360 34 544 560 16
cert_test_block_3 47360 35 560 576 16
cert_test_block_3 47360 36 576 592 16
cert_test_block_3 47360 37 592 608 16
cert_test_block_3 47360 38 608 624 16
cert_test_block_3 47360 39 624 640 16
theorem test47360_complete : Interval test47360 0 640 :=
  (interval_append test47360 0 320 640
  (interval_append test47360 0 160 320
  (interval_append test47360 0 80 160
  (interval_append test47360 0 32 80
  (interval_append test47360 0 16 32
  test47360_block_0
  test47360_block_1)
  (interval_append test47360 32 48 80
  test47360_block_2
  (interval_append test47360 48 64 80
  test47360_block_3
  test47360_block_4)))
  (interval_append test47360 80 112 160
  (interval_append test47360 80 96 112
  test47360_block_5
  test47360_block_6)
  (interval_append test47360 112 128 160
  test47360_block_7
  (interval_append test47360 128 144 160
  test47360_block_8
  test47360_block_9))))
  (interval_append test47360 160 240 320
  (interval_append test47360 160 192 240
  (interval_append test47360 160 176 192
  test47360_block_10
  test47360_block_11)
  (interval_append test47360 192 208 240
  test47360_block_12
  (interval_append test47360 208 224 240
  test47360_block_13
  test47360_block_14)))
  (interval_append test47360 240 272 320
  (interval_append test47360 240 256 272
  test47360_block_15
  test47360_block_16)
  (interval_append test47360 272 288 320
  test47360_block_17
  (interval_append test47360 288 304 320
  test47360_block_18
  test47360_block_19)))))
  (interval_append test47360 320 480 640
  (interval_append test47360 320 400 480
  (interval_append test47360 320 352 400
  (interval_append test47360 320 336 352
  test47360_block_20
  test47360_block_21)
  (interval_append test47360 352 368 400
  test47360_block_22
  (interval_append test47360 368 384 400
  test47360_block_23
  test47360_block_24)))
  (interval_append test47360 400 432 480
  (interval_append test47360 400 416 432
  test47360_block_25
  test47360_block_26)
  (interval_append test47360 432 448 480
  test47360_block_27
  (interval_append test47360 448 464 480
  test47360_block_28
  test47360_block_29))))
  (interval_append test47360 480 560 640
  (interval_append test47360 480 512 560
  (interval_append test47360 480 496 512
  test47360_block_30
  test47360_block_31)
  (interval_append test47360 512 528 560
  test47360_block_32
  (interval_append test47360 528 544 560
  test47360_block_33
  test47360_block_34)))
  (interval_append test47360 560 592 640
  (interval_append test47360 560 576 592
  test47360_block_35
  test47360_block_36)
  (interval_append test47360 592 608 640
  test47360_block_37
  (interval_append test47360 608 624 640
  test47360_block_38
  test47360_block_39))))))
cert_nodeInterval_3 47360 48000
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
cert_test_11 48000
cert_test_block_3 48000 0 0 16 16
cert_test_block_3 48000 1 16 32 16
cert_test_block_3 48000 2 32 48 16
cert_test_block_3 48000 3 48 64 16
cert_test_block_3 48000 4 64 80 16
cert_test_block_3 48000 5 80 96 16
cert_test_block_3 48000 6 96 112 16
cert_test_block_3 48000 7 112 128 16
cert_test_block_3 48000 8 128 144 16
cert_test_block_3 48000 9 144 160 16
cert_test_block_3 48000 10 160 176 16
cert_test_block_3 48000 11 176 192 16
cert_test_block_3 48000 12 192 208 16
cert_test_block_3 48000 13 208 224 16
cert_test_block_3 48000 14 224 240 16
cert_test_block_3 48000 15 240 256 16
cert_test_block_3 48000 16 256 272 16
cert_test_block_3 48000 17 272 288 16
cert_test_block_3 48000 18 288 304 16
cert_test_block_3 48000 19 304 320 16
cert_test_block_3 48000 20 320 336 16
cert_test_block_3 48000 21 336 352 16
cert_test_block_3 48000 22 352 368 16
cert_test_block_3 48000 23 368 384 16
cert_test_block_3 48000 24 384 400 16
cert_test_block_3 48000 25 400 416 16
cert_test_block_3 48000 26 416 432 16
cert_test_block_3 48000 27 432 448 16
cert_test_block_3 48000 28 448 464 16
cert_test_block_3 48000 29 464 480 16
cert_test_block_3 48000 30 480 496 16
cert_test_block_3 48000 31 496 512 16
cert_test_block_3 48000 32 512 528 16
cert_test_block_3 48000 33 528 544 16
cert_test_block_3 48000 34 544 560 16
cert_test_block_3 48000 35 560 576 16
cert_test_block_3 48000 36 576 592 16
cert_test_block_3 48000 37 592 608 16
cert_test_block_3 48000 38 608 624 16
cert_test_block_3 48000 39 624 640 16
theorem test48000_complete : Interval test48000 0 640 :=
  (interval_append test48000 0 320 640
  (interval_append test48000 0 160 320
  (interval_append test48000 0 80 160
  (interval_append test48000 0 32 80
  (interval_append test48000 0 16 32
  test48000_block_0
  test48000_block_1)
  (interval_append test48000 32 48 80
  test48000_block_2
  (interval_append test48000 48 64 80
  test48000_block_3
  test48000_block_4)))
  (interval_append test48000 80 112 160
  (interval_append test48000 80 96 112
  test48000_block_5
  test48000_block_6)
  (interval_append test48000 112 128 160
  test48000_block_7
  (interval_append test48000 128 144 160
  test48000_block_8
  test48000_block_9))))
  (interval_append test48000 160 240 320
  (interval_append test48000 160 192 240
  (interval_append test48000 160 176 192
  test48000_block_10
  test48000_block_11)
  (interval_append test48000 192 208 240
  test48000_block_12
  (interval_append test48000 208 224 240
  test48000_block_13
  test48000_block_14)))
  (interval_append test48000 240 272 320
  (interval_append test48000 240 256 272
  test48000_block_15
  test48000_block_16)
  (interval_append test48000 272 288 320
  test48000_block_17
  (interval_append test48000 288 304 320
  test48000_block_18
  test48000_block_19)))))
  (interval_append test48000 320 480 640
  (interval_append test48000 320 400 480
  (interval_append test48000 320 352 400
  (interval_append test48000 320 336 352
  test48000_block_20
  test48000_block_21)
  (interval_append test48000 352 368 400
  test48000_block_22
  (interval_append test48000 368 384 400
  test48000_block_23
  test48000_block_24)))
  (interval_append test48000 400 432 480
  (interval_append test48000 400 416 432
  test48000_block_25
  test48000_block_26)
  (interval_append test48000 432 448 480
  test48000_block_27
  (interval_append test48000 448 464 480
  test48000_block_28
  test48000_block_29))))
  (interval_append test48000 480 560 640
  (interval_append test48000 480 512 560
  (interval_append test48000 480 496 512
  test48000_block_30
  test48000_block_31)
  (interval_append test48000 512 528 560
  test48000_block_32
  (interval_append test48000 528 544 560
  test48000_block_33
  test48000_block_34)))
  (interval_append test48000 560 592 640
  (interval_append test48000 560 576 592
  test48000_block_35
  test48000_block_36)
  (interval_append test48000 592 608 640
  test48000_block_37
  (interval_append test48000 608 624 640
  test48000_block_38
  test48000_block_39))))))
cert_nodeInterval_3 48000 48640
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
cert_test_11 48640
cert_test_block_3 48640 0 0 16 16
cert_test_block_3 48640 1 16 32 16
cert_test_block_3 48640 2 32 48 16
cert_test_block_3 48640 3 48 64 16
cert_test_block_3 48640 4 64 80 16
cert_test_block_3 48640 5 80 96 16
cert_test_block_3 48640 6 96 112 16
cert_test_block_3 48640 7 112 128 16
cert_test_block_3 48640 8 128 144 16
cert_test_block_3 48640 9 144 160 16
cert_test_block_3 48640 10 160 176 16
cert_test_block_3 48640 11 176 192 16
cert_test_block_3 48640 12 192 208 16
cert_test_block_3 48640 13 208 224 16
cert_test_block_3 48640 14 224 240 16
cert_test_block_3 48640 15 240 256 16
cert_test_block_3 48640 16 256 272 16
cert_test_block_3 48640 17 272 288 16
cert_test_block_3 48640 18 288 304 16
cert_test_block_3 48640 19 304 320 16
cert_test_block_3 48640 20 320 336 16
cert_test_block_3 48640 21 336 352 16
cert_test_block_3 48640 22 352 368 16
cert_test_block_3 48640 23 368 384 16
cert_test_block_3 48640 24 384 400 16
cert_test_block_3 48640 25 400 416 16
cert_test_block_3 48640 26 416 432 16
cert_test_block_3 48640 27 432 448 16
cert_test_block_3 48640 28 448 464 16
cert_test_block_3 48640 29 464 480 16
cert_test_block_3 48640 30 480 496 16
cert_test_block_3 48640 31 496 512 16
cert_test_block_3 48640 32 512 528 16
cert_test_block_3 48640 33 528 544 16
cert_test_block_3 48640 34 544 560 16
cert_test_block_3 48640 35 560 576 16
cert_test_block_3 48640 36 576 592 16
cert_test_block_3 48640 37 592 608 16
cert_test_block_3 48640 38 608 624 16
cert_test_block_3 48640 39 624 640 16
theorem test48640_complete : Interval test48640 0 640 :=
  (interval_append test48640 0 320 640
  (interval_append test48640 0 160 320
  (interval_append test48640 0 80 160
  (interval_append test48640 0 32 80
  (interval_append test48640 0 16 32
  test48640_block_0
  test48640_block_1)
  (interval_append test48640 32 48 80
  test48640_block_2
  (interval_append test48640 48 64 80
  test48640_block_3
  test48640_block_4)))
  (interval_append test48640 80 112 160
  (interval_append test48640 80 96 112
  test48640_block_5
  test48640_block_6)
  (interval_append test48640 112 128 160
  test48640_block_7
  (interval_append test48640 128 144 160
  test48640_block_8
  test48640_block_9))))
  (interval_append test48640 160 240 320
  (interval_append test48640 160 192 240
  (interval_append test48640 160 176 192
  test48640_block_10
  test48640_block_11)
  (interval_append test48640 192 208 240
  test48640_block_12
  (interval_append test48640 208 224 240
  test48640_block_13
  test48640_block_14)))
  (interval_append test48640 240 272 320
  (interval_append test48640 240 256 272
  test48640_block_15
  test48640_block_16)
  (interval_append test48640 272 288 320
  test48640_block_17
  (interval_append test48640 288 304 320
  test48640_block_18
  test48640_block_19)))))
  (interval_append test48640 320 480 640
  (interval_append test48640 320 400 480
  (interval_append test48640 320 352 400
  (interval_append test48640 320 336 352
  test48640_block_20
  test48640_block_21)
  (interval_append test48640 352 368 400
  test48640_block_22
  (interval_append test48640 368 384 400
  test48640_block_23
  test48640_block_24)))
  (interval_append test48640 400 432 480
  (interval_append test48640 400 416 432
  test48640_block_25
  test48640_block_26)
  (interval_append test48640 432 448 480
  test48640_block_27
  (interval_append test48640 448 464 480
  test48640_block_28
  test48640_block_29))))
  (interval_append test48640 480 560 640
  (interval_append test48640 480 512 560
  (interval_append test48640 480 496 512
  test48640_block_30
  test48640_block_31)
  (interval_append test48640 512 528 560
  test48640_block_32
  (interval_append test48640 528 544 560
  test48640_block_33
  test48640_block_34)))
  (interval_append test48640 560 592 640
  (interval_append test48640 560 576 592
  test48640_block_35
  test48640_block_36)
  (interval_append test48640 592 608 640
  test48640_block_37
  (interval_append test48640 608 624 640
  test48640_block_38
  test48640_block_39))))))
cert_nodeInterval_3 48640 49280
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
cert_test_11 49280
cert_test_block_3 49280 0 0 16 16
cert_test_block_3 49280 1 16 32 16
cert_test_block_3 49280 2 32 48 16
cert_test_block_3 49280 3 48 64 16
cert_test_block_3 49280 4 64 80 16
cert_test_block_3 49280 5 80 96 16
cert_test_block_3 49280 6 96 112 16
cert_test_block_3 49280 7 112 128 16
cert_test_block_3 49280 8 128 144 16
cert_test_block_3 49280 9 144 160 16
cert_test_block_3 49280 10 160 176 16
cert_test_block_3 49280 11 176 192 16
cert_test_block_3 49280 12 192 208 16
cert_test_block_3 49280 13 208 224 16
cert_test_block_3 49280 14 224 240 16
cert_test_block_3 49280 15 240 256 16
cert_test_block_3 49280 16 256 272 16
cert_test_block_3 49280 17 272 288 16
cert_test_block_3 49280 18 288 304 16
cert_test_block_3 49280 19 304 320 16
cert_test_block_3 49280 20 320 336 16
cert_test_block_3 49280 21 336 352 16
cert_test_block_3 49280 22 352 368 16
cert_test_block_3 49280 23 368 384 16
cert_test_block_3 49280 24 384 400 16
cert_test_block_3 49280 25 400 416 16
cert_test_block_3 49280 26 416 432 16
cert_test_block_3 49280 27 432 448 16
cert_test_block_3 49280 28 448 464 16
cert_test_block_3 49280 29 464 480 16
cert_test_block_3 49280 30 480 496 16
cert_test_block_3 49280 31 496 512 16
cert_test_block_3 49280 32 512 528 16
cert_test_block_3 49280 33 528 544 16
cert_test_block_3 49280 34 544 560 16
cert_test_block_3 49280 35 560 576 16
cert_test_block_3 49280 36 576 592 16
cert_test_block_3 49280 37 592 608 16
cert_test_block_3 49280 38 608 624 16
cert_test_block_3 49280 39 624 640 16
theorem test49280_complete : Interval test49280 0 640 :=
  (interval_append test49280 0 320 640
  (interval_append test49280 0 160 320
  (interval_append test49280 0 80 160
  (interval_append test49280 0 32 80
  (interval_append test49280 0 16 32
  test49280_block_0
  test49280_block_1)
  (interval_append test49280 32 48 80
  test49280_block_2
  (interval_append test49280 48 64 80
  test49280_block_3
  test49280_block_4)))
  (interval_append test49280 80 112 160
  (interval_append test49280 80 96 112
  test49280_block_5
  test49280_block_6)
  (interval_append test49280 112 128 160
  test49280_block_7
  (interval_append test49280 128 144 160
  test49280_block_8
  test49280_block_9))))
  (interval_append test49280 160 240 320
  (interval_append test49280 160 192 240
  (interval_append test49280 160 176 192
  test49280_block_10
  test49280_block_11)
  (interval_append test49280 192 208 240
  test49280_block_12
  (interval_append test49280 208 224 240
  test49280_block_13
  test49280_block_14)))
  (interval_append test49280 240 272 320
  (interval_append test49280 240 256 272
  test49280_block_15
  test49280_block_16)
  (interval_append test49280 272 288 320
  test49280_block_17
  (interval_append test49280 288 304 320
  test49280_block_18
  test49280_block_19)))))
  (interval_append test49280 320 480 640
  (interval_append test49280 320 400 480
  (interval_append test49280 320 352 400
  (interval_append test49280 320 336 352
  test49280_block_20
  test49280_block_21)
  (interval_append test49280 352 368 400
  test49280_block_22
  (interval_append test49280 368 384 400
  test49280_block_23
  test49280_block_24)))
  (interval_append test49280 400 432 480
  (interval_append test49280 400 416 432
  test49280_block_25
  test49280_block_26)
  (interval_append test49280 432 448 480
  test49280_block_27
  (interval_append test49280 448 464 480
  test49280_block_28
  test49280_block_29))))
  (interval_append test49280 480 560 640
  (interval_append test49280 480 512 560
  (interval_append test49280 480 496 512
  test49280_block_30
  test49280_block_31)
  (interval_append test49280 512 528 560
  test49280_block_32
  (interval_append test49280 528 544 560
  test49280_block_33
  test49280_block_34)))
  (interval_append test49280 560 592 640
  (interval_append test49280 560 576 592
  test49280_block_35
  test49280_block_36)
  (interval_append test49280 592 608 640
  test49280_block_37
  (interval_append test49280 608 624 640
  test49280_block_38
  test49280_block_39))))))
cert_nodeInterval_3 49280 49920
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
cert_test_11 49920
cert_test_block_3 49920 0 0 16 16
cert_test_block_3 49920 1 16 32 16
cert_test_block_3 49920 2 32 48 16
cert_test_block_3 49920 3 48 64 16
cert_test_block_3 49920 4 64 80 16
cert_test_block_3 49920 5 80 96 16
cert_test_block_3 49920 6 96 112 16
cert_test_block_3 49920 7 112 128 16
cert_test_block_3 49920 8 128 144 16
cert_test_block_3 49920 9 144 160 16
cert_test_block_3 49920 10 160 176 16
cert_test_block_3 49920 11 176 192 16
cert_test_block_3 49920 12 192 208 16
cert_test_block_3 49920 13 208 224 16
cert_test_block_3 49920 14 224 240 16
cert_test_block_3 49920 15 240 256 16
cert_test_block_3 49920 16 256 272 16
cert_test_block_3 49920 17 272 288 16
cert_test_block_3 49920 18 288 304 16
cert_test_block_3 49920 19 304 320 16
cert_test_block_3 49920 20 320 336 16
cert_test_block_3 49920 21 336 352 16
cert_test_block_3 49920 22 352 368 16
cert_test_block_3 49920 23 368 384 16
cert_test_block_3 49920 24 384 400 16
cert_test_block_3 49920 25 400 416 16
cert_test_block_3 49920 26 416 432 16
cert_test_block_3 49920 27 432 448 16
cert_test_block_3 49920 28 448 464 16
cert_test_block_3 49920 29 464 480 16
cert_test_block_3 49920 30 480 496 16
cert_test_block_3 49920 31 496 512 16
cert_test_block_3 49920 32 512 528 16
cert_test_block_3 49920 33 528 544 16
cert_test_block_3 49920 34 544 560 16
cert_test_block_3 49920 35 560 576 16
cert_test_block_3 49920 36 576 592 16
cert_test_block_3 49920 37 592 608 16
cert_test_block_3 49920 38 608 624 16
cert_test_block_3 49920 39 624 640 16
theorem test49920_complete : Interval test49920 0 640 :=
  (interval_append test49920 0 320 640
  (interval_append test49920 0 160 320
  (interval_append test49920 0 80 160
  (interval_append test49920 0 32 80
  (interval_append test49920 0 16 32
  test49920_block_0
  test49920_block_1)
  (interval_append test49920 32 48 80
  test49920_block_2
  (interval_append test49920 48 64 80
  test49920_block_3
  test49920_block_4)))
  (interval_append test49920 80 112 160
  (interval_append test49920 80 96 112
  test49920_block_5
  test49920_block_6)
  (interval_append test49920 112 128 160
  test49920_block_7
  (interval_append test49920 128 144 160
  test49920_block_8
  test49920_block_9))))
  (interval_append test49920 160 240 320
  (interval_append test49920 160 192 240
  (interval_append test49920 160 176 192
  test49920_block_10
  test49920_block_11)
  (interval_append test49920 192 208 240
  test49920_block_12
  (interval_append test49920 208 224 240
  test49920_block_13
  test49920_block_14)))
  (interval_append test49920 240 272 320
  (interval_append test49920 240 256 272
  test49920_block_15
  test49920_block_16)
  (interval_append test49920 272 288 320
  test49920_block_17
  (interval_append test49920 288 304 320
  test49920_block_18
  test49920_block_19)))))
  (interval_append test49920 320 480 640
  (interval_append test49920 320 400 480
  (interval_append test49920 320 352 400
  (interval_append test49920 320 336 352
  test49920_block_20
  test49920_block_21)
  (interval_append test49920 352 368 400
  test49920_block_22
  (interval_append test49920 368 384 400
  test49920_block_23
  test49920_block_24)))
  (interval_append test49920 400 432 480
  (interval_append test49920 400 416 432
  test49920_block_25
  test49920_block_26)
  (interval_append test49920 432 448 480
  test49920_block_27
  (interval_append test49920 448 464 480
  test49920_block_28
  test49920_block_29))))
  (interval_append test49920 480 560 640
  (interval_append test49920 480 512 560
  (interval_append test49920 480 496 512
  test49920_block_30
  test49920_block_31)
  (interval_append test49920 512 528 560
  test49920_block_32
  (interval_append test49920 528 544 560
  test49920_block_33
  test49920_block_34)))
  (interval_append test49920 560 592 640
  (interval_append test49920 560 576 592
  test49920_block_35
  test49920_block_36)
  (interval_append test49920 592 608 640
  test49920_block_37
  (interval_append test49920 608 624 640
  test49920_block_38
  test49920_block_39))))))
cert_nodeInterval_3 49920 50560
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
cert_test_11 50560
cert_test_block_3 50560 0 0 16 16
cert_test_block_3 50560 1 16 32 16
cert_test_block_3 50560 2 32 48 16
cert_test_block_3 50560 3 48 64 16
cert_test_block_3 50560 4 64 80 16
cert_test_block_3 50560 5 80 96 16
cert_test_block_3 50560 6 96 112 16
cert_test_block_3 50560 7 112 128 16
cert_test_block_3 50560 8 128 144 16
cert_test_block_3 50560 9 144 160 16
cert_test_block_3 50560 10 160 176 16
cert_test_block_3 50560 11 176 192 16
cert_test_block_3 50560 12 192 208 16
cert_test_block_3 50560 13 208 224 16
cert_test_block_3 50560 14 224 240 16
cert_test_block_3 50560 15 240 256 16
cert_test_block_3 50560 16 256 272 16
cert_test_block_3 50560 17 272 288 16
cert_test_block_3 50560 18 288 304 16
cert_test_block_3 50560 19 304 320 16
cert_test_block_3 50560 20 320 336 16
cert_test_block_3 50560 21 336 352 16
cert_test_block_3 50560 22 352 368 16
cert_test_block_3 50560 23 368 384 16
cert_test_block_3 50560 24 384 400 16
cert_test_block_3 50560 25 400 416 16
cert_test_block_3 50560 26 416 432 16
cert_test_block_3 50560 27 432 448 16
cert_test_block_3 50560 28 448 464 16
cert_test_block_3 50560 29 464 480 16
cert_test_block_3 50560 30 480 496 16
cert_test_block_3 50560 31 496 512 16
cert_test_block_3 50560 32 512 528 16
cert_test_block_3 50560 33 528 544 16
cert_test_block_3 50560 34 544 560 16
cert_test_block_3 50560 35 560 576 16
cert_test_block_3 50560 36 576 592 16
cert_test_block_3 50560 37 592 608 16
cert_test_block_3 50560 38 608 624 16
cert_test_block_3 50560 39 624 640 16
theorem test50560_complete : Interval test50560 0 640 :=
  (interval_append test50560 0 320 640
  (interval_append test50560 0 160 320
  (interval_append test50560 0 80 160
  (interval_append test50560 0 32 80
  (interval_append test50560 0 16 32
  test50560_block_0
  test50560_block_1)
  (interval_append test50560 32 48 80
  test50560_block_2
  (interval_append test50560 48 64 80
  test50560_block_3
  test50560_block_4)))
  (interval_append test50560 80 112 160
  (interval_append test50560 80 96 112
  test50560_block_5
  test50560_block_6)
  (interval_append test50560 112 128 160
  test50560_block_7
  (interval_append test50560 128 144 160
  test50560_block_8
  test50560_block_9))))
  (interval_append test50560 160 240 320
  (interval_append test50560 160 192 240
  (interval_append test50560 160 176 192
  test50560_block_10
  test50560_block_11)
  (interval_append test50560 192 208 240
  test50560_block_12
  (interval_append test50560 208 224 240
  test50560_block_13
  test50560_block_14)))
  (interval_append test50560 240 272 320
  (interval_append test50560 240 256 272
  test50560_block_15
  test50560_block_16)
  (interval_append test50560 272 288 320
  test50560_block_17
  (interval_append test50560 288 304 320
  test50560_block_18
  test50560_block_19)))))
  (interval_append test50560 320 480 640
  (interval_append test50560 320 400 480
  (interval_append test50560 320 352 400
  (interval_append test50560 320 336 352
  test50560_block_20
  test50560_block_21)
  (interval_append test50560 352 368 400
  test50560_block_22
  (interval_append test50560 368 384 400
  test50560_block_23
  test50560_block_24)))
  (interval_append test50560 400 432 480
  (interval_append test50560 400 416 432
  test50560_block_25
  test50560_block_26)
  (interval_append test50560 432 448 480
  test50560_block_27
  (interval_append test50560 448 464 480
  test50560_block_28
  test50560_block_29))))
  (interval_append test50560 480 560 640
  (interval_append test50560 480 512 560
  (interval_append test50560 480 496 512
  test50560_block_30
  test50560_block_31)
  (interval_append test50560 512 528 560
  test50560_block_32
  (interval_append test50560 528 544 560
  test50560_block_33
  test50560_block_34)))
  (interval_append test50560 560 592 640
  (interval_append test50560 560 576 592
  test50560_block_35
  test50560_block_36)
  (interval_append test50560 592 608 640
  test50560_block_37
  (interval_append test50560 608 624 640
  test50560_block_38
  test50560_block_39))))))
cert_nodeInterval_3 50560 51200
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
cert_test_11 51200
cert_test_block_3 51200 0 0 16 16
cert_test_block_3 51200 1 16 32 16
cert_test_block_3 51200 2 32 48 16
cert_test_block_3 51200 3 48 64 16
cert_test_block_3 51200 4 64 80 16
cert_test_block_3 51200 5 80 96 16
cert_test_block_3 51200 6 96 112 16
cert_test_block_3 51200 7 112 128 16
cert_test_block_3 51200 8 128 144 16
cert_test_block_3 51200 9 144 160 16
cert_test_block_3 51200 10 160 176 16
cert_test_block_3 51200 11 176 192 16
cert_test_block_3 51200 12 192 208 16
cert_test_block_3 51200 13 208 224 16
cert_test_block_3 51200 14 224 240 16
cert_test_block_3 51200 15 240 256 16
cert_test_block_3 51200 16 256 272 16
cert_test_block_3 51200 17 272 288 16
cert_test_block_3 51200 18 288 304 16
cert_test_block_3 51200 19 304 320 16
cert_test_block_3 51200 20 320 336 16
cert_test_block_3 51200 21 336 352 16
cert_test_block_3 51200 22 352 368 16
cert_test_block_3 51200 23 368 384 16
cert_test_block_3 51200 24 384 400 16
cert_test_block_3 51200 25 400 416 16
cert_test_block_3 51200 26 416 432 16
cert_test_block_3 51200 27 432 448 16
cert_test_block_3 51200 28 448 464 16
cert_test_block_3 51200 29 464 480 16
cert_test_block_3 51200 30 480 496 16
cert_test_block_3 51200 31 496 512 16
cert_test_block_3 51200 32 512 528 16
cert_test_block_3 51200 33 528 544 16
cert_test_block_3 51200 34 544 560 16
cert_test_block_3 51200 35 560 576 16
cert_test_block_3 51200 36 576 592 16
cert_test_block_3 51200 37 592 608 16
cert_test_block_3 51200 38 608 624 16
cert_test_block_3 51200 39 624 640 16
theorem test51200_complete : Interval test51200 0 640 :=
  (interval_append test51200 0 320 640
  (interval_append test51200 0 160 320
  (interval_append test51200 0 80 160
  (interval_append test51200 0 32 80
  (interval_append test51200 0 16 32
  test51200_block_0
  test51200_block_1)
  (interval_append test51200 32 48 80
  test51200_block_2
  (interval_append test51200 48 64 80
  test51200_block_3
  test51200_block_4)))
  (interval_append test51200 80 112 160
  (interval_append test51200 80 96 112
  test51200_block_5
  test51200_block_6)
  (interval_append test51200 112 128 160
  test51200_block_7
  (interval_append test51200 128 144 160
  test51200_block_8
  test51200_block_9))))
  (interval_append test51200 160 240 320
  (interval_append test51200 160 192 240
  (interval_append test51200 160 176 192
  test51200_block_10
  test51200_block_11)
  (interval_append test51200 192 208 240
  test51200_block_12
  (interval_append test51200 208 224 240
  test51200_block_13
  test51200_block_14)))
  (interval_append test51200 240 272 320
  (interval_append test51200 240 256 272
  test51200_block_15
  test51200_block_16)
  (interval_append test51200 272 288 320
  test51200_block_17
  (interval_append test51200 288 304 320
  test51200_block_18
  test51200_block_19)))))
  (interval_append test51200 320 480 640
  (interval_append test51200 320 400 480
  (interval_append test51200 320 352 400
  (interval_append test51200 320 336 352
  test51200_block_20
  test51200_block_21)
  (interval_append test51200 352 368 400
  test51200_block_22
  (interval_append test51200 368 384 400
  test51200_block_23
  test51200_block_24)))
  (interval_append test51200 400 432 480
  (interval_append test51200 400 416 432
  test51200_block_25
  test51200_block_26)
  (interval_append test51200 432 448 480
  test51200_block_27
  (interval_append test51200 448 464 480
  test51200_block_28
  test51200_block_29))))
  (interval_append test51200 480 560 640
  (interval_append test51200 480 512 560
  (interval_append test51200 480 496 512
  test51200_block_30
  test51200_block_31)
  (interval_append test51200 512 528 560
  test51200_block_32
  (interval_append test51200 528 544 560
  test51200_block_33
  test51200_block_34)))
  (interval_append test51200 560 592 640
  (interval_append test51200 560 576 592
  test51200_block_35
  test51200_block_36)
  (interval_append test51200 592 608 640
  test51200_block_37
  (interval_append test51200 608 624 640
  test51200_block_38
  test51200_block_39))))))
cert_nodeInterval_3 51200 51840
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
cert_test_11 51840
cert_test_block_3 51840 0 0 16 16
cert_test_block_3 51840 1 16 32 16
cert_test_block_3 51840 2 32 48 16
cert_test_block_3 51840 3 48 64 16
cert_test_block_3 51840 4 64 80 16
cert_test_block_3 51840 5 80 96 16
cert_test_block_3 51840 6 96 112 16
cert_test_block_3 51840 7 112 128 16
cert_test_block_3 51840 8 128 144 16
cert_test_block_3 51840 9 144 160 16
cert_test_block_3 51840 10 160 176 16
cert_test_block_3 51840 11 176 192 16
cert_test_block_3 51840 12 192 208 16
cert_test_block_3 51840 13 208 224 16
cert_test_block_3 51840 14 224 240 16
cert_test_block_3 51840 15 240 256 16
cert_test_block_3 51840 16 256 272 16
cert_test_block_3 51840 17 272 288 16
cert_test_block_3 51840 18 288 304 16
cert_test_block_3 51840 19 304 320 16
cert_test_block_3 51840 20 320 336 16
cert_test_block_3 51840 21 336 352 16
cert_test_block_3 51840 22 352 368 16
cert_test_block_3 51840 23 368 384 16
cert_test_block_3 51840 24 384 400 16
cert_test_block_3 51840 25 400 416 16
cert_test_block_3 51840 26 416 432 16
cert_test_block_3 51840 27 432 448 16
cert_test_block_3 51840 28 448 464 16
cert_test_block_3 51840 29 464 480 16
cert_test_block_3 51840 30 480 496 16
cert_test_block_3 51840 31 496 512 16
cert_test_block_3 51840 32 512 528 16
cert_test_block_3 51840 33 528 544 16
cert_test_block_3 51840 34 544 560 16
cert_test_block_3 51840 35 560 576 16
cert_test_block_3 51840 36 576 592 16
cert_test_block_3 51840 37 592 608 16
cert_test_block_3 51840 38 608 624 16
cert_test_block_3 51840 39 624 640 16
theorem test51840_complete : Interval test51840 0 640 :=
  (interval_append test51840 0 320 640
  (interval_append test51840 0 160 320
  (interval_append test51840 0 80 160
  (interval_append test51840 0 32 80
  (interval_append test51840 0 16 32
  test51840_block_0
  test51840_block_1)
  (interval_append test51840 32 48 80
  test51840_block_2
  (interval_append test51840 48 64 80
  test51840_block_3
  test51840_block_4)))
  (interval_append test51840 80 112 160
  (interval_append test51840 80 96 112
  test51840_block_5
  test51840_block_6)
  (interval_append test51840 112 128 160
  test51840_block_7
  (interval_append test51840 128 144 160
  test51840_block_8
  test51840_block_9))))
  (interval_append test51840 160 240 320
  (interval_append test51840 160 192 240
  (interval_append test51840 160 176 192
  test51840_block_10
  test51840_block_11)
  (interval_append test51840 192 208 240
  test51840_block_12
  (interval_append test51840 208 224 240
  test51840_block_13
  test51840_block_14)))
  (interval_append test51840 240 272 320
  (interval_append test51840 240 256 272
  test51840_block_15
  test51840_block_16)
  (interval_append test51840 272 288 320
  test51840_block_17
  (interval_append test51840 288 304 320
  test51840_block_18
  test51840_block_19)))))
  (interval_append test51840 320 480 640
  (interval_append test51840 320 400 480
  (interval_append test51840 320 352 400
  (interval_append test51840 320 336 352
  test51840_block_20
  test51840_block_21)
  (interval_append test51840 352 368 400
  test51840_block_22
  (interval_append test51840 368 384 400
  test51840_block_23
  test51840_block_24)))
  (interval_append test51840 400 432 480
  (interval_append test51840 400 416 432
  test51840_block_25
  test51840_block_26)
  (interval_append test51840 432 448 480
  test51840_block_27
  (interval_append test51840 448 464 480
  test51840_block_28
  test51840_block_29))))
  (interval_append test51840 480 560 640
  (interval_append test51840 480 512 560
  (interval_append test51840 480 496 512
  test51840_block_30
  test51840_block_31)
  (interval_append test51840 512 528 560
  test51840_block_32
  (interval_append test51840 528 544 560
  test51840_block_33
  test51840_block_34)))
  (interval_append test51840 560 592 640
  (interval_append test51840 560 576 592
  test51840_block_35
  test51840_block_36)
  (interval_append test51840 592 608 640
  test51840_block_37
  (interval_append test51840 608 624 640
  test51840_block_38
  test51840_block_39))))))
cert_nodeInterval_3 51840 52480
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
cert_test_11 52480
cert_test_block_3 52480 0 0 16 16
cert_test_block_3 52480 1 16 32 16
cert_test_block_3 52480 2 32 48 16
cert_test_block_3 52480 3 48 64 16
cert_test_block_3 52480 4 64 80 16
cert_test_block_3 52480 5 80 96 16
cert_test_block_3 52480 6 96 112 16
cert_test_block_3 52480 7 112 128 16
cert_test_block_3 52480 8 128 144 16
cert_test_block_3 52480 9 144 160 16
cert_test_block_3 52480 10 160 176 16
cert_test_block_3 52480 11 176 192 16
cert_test_block_3 52480 12 192 208 16
cert_test_block_3 52480 13 208 224 16
cert_test_block_3 52480 14 224 240 16
cert_test_block_3 52480 15 240 256 16
cert_test_block_3 52480 16 256 272 16
cert_test_block_3 52480 17 272 288 16
cert_test_block_3 52480 18 288 304 16
cert_test_block_3 52480 19 304 320 16
cert_test_block_3 52480 20 320 336 16
cert_test_block_3 52480 21 336 352 16
cert_test_block_3 52480 22 352 368 16
cert_test_block_3 52480 23 368 384 16
cert_test_block_3 52480 24 384 400 16
cert_test_block_3 52480 25 400 416 16
cert_test_block_3 52480 26 416 432 16
cert_test_block_3 52480 27 432 448 16
cert_test_block_3 52480 28 448 464 16
cert_test_block_3 52480 29 464 480 16
cert_test_block_3 52480 30 480 496 16
cert_test_block_3 52480 31 496 512 16
cert_test_block_3 52480 32 512 528 16
cert_test_block_3 52480 33 528 544 16
cert_test_block_3 52480 34 544 560 16
cert_test_block_3 52480 35 560 576 16
cert_test_block_3 52480 36 576 592 16
cert_test_block_3 52480 37 592 608 16
cert_test_block_3 52480 38 608 624 16
cert_test_block_3 52480 39 624 640 16
theorem test52480_complete : Interval test52480 0 640 :=
  (interval_append test52480 0 320 640
  (interval_append test52480 0 160 320
  (interval_append test52480 0 80 160
  (interval_append test52480 0 32 80
  (interval_append test52480 0 16 32
  test52480_block_0
  test52480_block_1)
  (interval_append test52480 32 48 80
  test52480_block_2
  (interval_append test52480 48 64 80
  test52480_block_3
  test52480_block_4)))
  (interval_append test52480 80 112 160
  (interval_append test52480 80 96 112
  test52480_block_5
  test52480_block_6)
  (interval_append test52480 112 128 160
  test52480_block_7
  (interval_append test52480 128 144 160
  test52480_block_8
  test52480_block_9))))
  (interval_append test52480 160 240 320
  (interval_append test52480 160 192 240
  (interval_append test52480 160 176 192
  test52480_block_10
  test52480_block_11)
  (interval_append test52480 192 208 240
  test52480_block_12
  (interval_append test52480 208 224 240
  test52480_block_13
  test52480_block_14)))
  (interval_append test52480 240 272 320
  (interval_append test52480 240 256 272
  test52480_block_15
  test52480_block_16)
  (interval_append test52480 272 288 320
  test52480_block_17
  (interval_append test52480 288 304 320
  test52480_block_18
  test52480_block_19)))))
  (interval_append test52480 320 480 640
  (interval_append test52480 320 400 480
  (interval_append test52480 320 352 400
  (interval_append test52480 320 336 352
  test52480_block_20
  test52480_block_21)
  (interval_append test52480 352 368 400
  test52480_block_22
  (interval_append test52480 368 384 400
  test52480_block_23
  test52480_block_24)))
  (interval_append test52480 400 432 480
  (interval_append test52480 400 416 432
  test52480_block_25
  test52480_block_26)
  (interval_append test52480 432 448 480
  test52480_block_27
  (interval_append test52480 448 464 480
  test52480_block_28
  test52480_block_29))))
  (interval_append test52480 480 560 640
  (interval_append test52480 480 512 560
  (interval_append test52480 480 496 512
  test52480_block_30
  test52480_block_31)
  (interval_append test52480 512 528 560
  test52480_block_32
  (interval_append test52480 528 544 560
  test52480_block_33
  test52480_block_34)))
  (interval_append test52480 560 592 640
  (interval_append test52480 560 576 592
  test52480_block_35
  test52480_block_36)
  (interval_append test52480 592 608 640
  test52480_block_37
  (interval_append test52480 608 624 640
  test52480_block_38
  test52480_block_39))))))
cert_nodeInterval_3 52480 53120
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
cert_test_11 53120
cert_test_block_3 53120 0 0 16 16
cert_test_block_3 53120 1 16 32 16
cert_test_block_3 53120 2 32 48 16
cert_test_block_3 53120 3 48 64 16
cert_test_block_3 53120 4 64 80 16
cert_test_block_3 53120 5 80 96 16
cert_test_block_3 53120 6 96 112 16
cert_test_block_3 53120 7 112 128 16
cert_test_block_3 53120 8 128 144 16
cert_test_block_3 53120 9 144 160 16
cert_test_block_3 53120 10 160 176 16
cert_test_block_3 53120 11 176 192 16
cert_test_block_3 53120 12 192 208 16
cert_test_block_3 53120 13 208 224 16
cert_test_block_3 53120 14 224 240 16
cert_test_block_3 53120 15 240 256 16
cert_test_block_3 53120 16 256 272 16
cert_test_block_3 53120 17 272 288 16
cert_test_block_3 53120 18 288 304 16
cert_test_block_3 53120 19 304 320 16
cert_test_block_3 53120 20 320 336 16
cert_test_block_3 53120 21 336 352 16
cert_test_block_3 53120 22 352 368 16
cert_test_block_3 53120 23 368 384 16
cert_test_block_3 53120 24 384 400 16
cert_test_block_3 53120 25 400 416 16
cert_test_block_3 53120 26 416 432 16
cert_test_block_3 53120 27 432 448 16
cert_test_block_3 53120 28 448 464 16
cert_test_block_3 53120 29 464 480 16
cert_test_block_3 53120 30 480 496 16
cert_test_block_3 53120 31 496 512 16
cert_test_block_3 53120 32 512 528 16
cert_test_block_3 53120 33 528 544 16
cert_test_block_3 53120 34 544 560 16
cert_test_block_3 53120 35 560 576 16
cert_test_block_3 53120 36 576 592 16
cert_test_block_3 53120 37 592 608 16
cert_test_block_3 53120 38 608 624 16
cert_test_block_3 53120 39 624 640 16
theorem test53120_complete : Interval test53120 0 640 :=
  (interval_append test53120 0 320 640
  (interval_append test53120 0 160 320
  (interval_append test53120 0 80 160
  (interval_append test53120 0 32 80
  (interval_append test53120 0 16 32
  test53120_block_0
  test53120_block_1)
  (interval_append test53120 32 48 80
  test53120_block_2
  (interval_append test53120 48 64 80
  test53120_block_3
  test53120_block_4)))
  (interval_append test53120 80 112 160
  (interval_append test53120 80 96 112
  test53120_block_5
  test53120_block_6)
  (interval_append test53120 112 128 160
  test53120_block_7
  (interval_append test53120 128 144 160
  test53120_block_8
  test53120_block_9))))
  (interval_append test53120 160 240 320
  (interval_append test53120 160 192 240
  (interval_append test53120 160 176 192
  test53120_block_10
  test53120_block_11)
  (interval_append test53120 192 208 240
  test53120_block_12
  (interval_append test53120 208 224 240
  test53120_block_13
  test53120_block_14)))
  (interval_append test53120 240 272 320
  (interval_append test53120 240 256 272
  test53120_block_15
  test53120_block_16)
  (interval_append test53120 272 288 320
  test53120_block_17
  (interval_append test53120 288 304 320
  test53120_block_18
  test53120_block_19)))))
  (interval_append test53120 320 480 640
  (interval_append test53120 320 400 480
  (interval_append test53120 320 352 400
  (interval_append test53120 320 336 352
  test53120_block_20
  test53120_block_21)
  (interval_append test53120 352 368 400
  test53120_block_22
  (interval_append test53120 368 384 400
  test53120_block_23
  test53120_block_24)))
  (interval_append test53120 400 432 480
  (interval_append test53120 400 416 432
  test53120_block_25
  test53120_block_26)
  (interval_append test53120 432 448 480
  test53120_block_27
  (interval_append test53120 448 464 480
  test53120_block_28
  test53120_block_29))))
  (interval_append test53120 480 560 640
  (interval_append test53120 480 512 560
  (interval_append test53120 480 496 512
  test53120_block_30
  test53120_block_31)
  (interval_append test53120 512 528 560
  test53120_block_32
  (interval_append test53120 528 544 560
  test53120_block_33
  test53120_block_34)))
  (interval_append test53120 560 592 640
  (interval_append test53120 560 576 592
  test53120_block_35
  test53120_block_36)
  (interval_append test53120 592 608 640
  test53120_block_37
  (interval_append test53120 608 624 640
  test53120_block_38
  test53120_block_39))))))
cert_nodeInterval_3 53120 53760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
