module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 24960
cert_test_block_3 24960 0 0 16 16
cert_test_block_3 24960 1 16 32 16
cert_test_block_3 24960 2 32 48 16
cert_test_block_3 24960 3 48 64 16
cert_test_block_3 24960 4 64 80 16
cert_test_block_3 24960 5 80 96 16
cert_test_block_3 24960 6 96 112 16
cert_test_block_3 24960 7 112 128 16
cert_test_block_3 24960 8 128 144 16
cert_test_block_3 24960 9 144 160 16
cert_test_block_3 24960 10 160 176 16
cert_test_block_3 24960 11 176 192 16
cert_test_block_3 24960 12 192 208 16
cert_test_block_3 24960 13 208 224 16
cert_test_block_3 24960 14 224 240 16
cert_test_block_3 24960 15 240 256 16
cert_test_block_3 24960 16 256 272 16
cert_test_block_3 24960 17 272 288 16
cert_test_block_3 24960 18 288 304 16
cert_test_block_3 24960 19 304 320 16
cert_test_block_3 24960 20 320 336 16
cert_test_block_3 24960 21 336 352 16
cert_test_block_3 24960 22 352 368 16
cert_test_block_3 24960 23 368 384 16
cert_test_block_3 24960 24 384 400 16
cert_test_block_3 24960 25 400 416 16
cert_test_block_3 24960 26 416 432 16
cert_test_block_3 24960 27 432 448 16
cert_test_block_3 24960 28 448 464 16
cert_test_block_3 24960 29 464 480 16
cert_test_block_3 24960 30 480 496 16
cert_test_block_3 24960 31 496 512 16
cert_test_block_3 24960 32 512 528 16
cert_test_block_3 24960 33 528 544 16
cert_test_block_3 24960 34 544 560 16
cert_test_block_3 24960 35 560 576 16
cert_test_block_3 24960 36 576 592 16
cert_test_block_3 24960 37 592 608 16
cert_test_block_3 24960 38 608 624 16
cert_test_block_3 24960 39 624 640 16
theorem test24960_complete : Interval test24960 0 640 :=
  (interval_append test24960 0 320 640
  (interval_append test24960 0 160 320
  (interval_append test24960 0 80 160
  (interval_append test24960 0 32 80
  (interval_append test24960 0 16 32
  test24960_block_0
  test24960_block_1)
  (interval_append test24960 32 48 80
  test24960_block_2
  (interval_append test24960 48 64 80
  test24960_block_3
  test24960_block_4)))
  (interval_append test24960 80 112 160
  (interval_append test24960 80 96 112
  test24960_block_5
  test24960_block_6)
  (interval_append test24960 112 128 160
  test24960_block_7
  (interval_append test24960 128 144 160
  test24960_block_8
  test24960_block_9))))
  (interval_append test24960 160 240 320
  (interval_append test24960 160 192 240
  (interval_append test24960 160 176 192
  test24960_block_10
  test24960_block_11)
  (interval_append test24960 192 208 240
  test24960_block_12
  (interval_append test24960 208 224 240
  test24960_block_13
  test24960_block_14)))
  (interval_append test24960 240 272 320
  (interval_append test24960 240 256 272
  test24960_block_15
  test24960_block_16)
  (interval_append test24960 272 288 320
  test24960_block_17
  (interval_append test24960 288 304 320
  test24960_block_18
  test24960_block_19)))))
  (interval_append test24960 320 480 640
  (interval_append test24960 320 400 480
  (interval_append test24960 320 352 400
  (interval_append test24960 320 336 352
  test24960_block_20
  test24960_block_21)
  (interval_append test24960 352 368 400
  test24960_block_22
  (interval_append test24960 368 384 400
  test24960_block_23
  test24960_block_24)))
  (interval_append test24960 400 432 480
  (interval_append test24960 400 416 432
  test24960_block_25
  test24960_block_26)
  (interval_append test24960 432 448 480
  test24960_block_27
  (interval_append test24960 448 464 480
  test24960_block_28
  test24960_block_29))))
  (interval_append test24960 480 560 640
  (interval_append test24960 480 512 560
  (interval_append test24960 480 496 512
  test24960_block_30
  test24960_block_31)
  (interval_append test24960 512 528 560
  test24960_block_32
  (interval_append test24960 528 544 560
  test24960_block_33
  test24960_block_34)))
  (interval_append test24960 560 592 640
  (interval_append test24960 560 576 592
  test24960_block_35
  test24960_block_36)
  (interval_append test24960 592 608 640
  test24960_block_37
  (interval_append test24960 608 624 640
  test24960_block_38
  test24960_block_39))))))
cert_nodeInterval_3 24960 25600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 25600
cert_test_block_3 25600 0 0 16 16
cert_test_block_3 25600 1 16 32 16
cert_test_block_3 25600 2 32 48 16
cert_test_block_3 25600 3 48 64 16
cert_test_block_3 25600 4 64 80 16
cert_test_block_3 25600 5 80 96 16
cert_test_block_3 25600 6 96 112 16
cert_test_block_3 25600 7 112 128 16
cert_test_block_3 25600 8 128 144 16
cert_test_block_3 25600 9 144 160 16
cert_test_block_3 25600 10 160 176 16
cert_test_block_3 25600 11 176 192 16
cert_test_block_3 25600 12 192 208 16
cert_test_block_3 25600 13 208 224 16
cert_test_block_3 25600 14 224 240 16
cert_test_block_3 25600 15 240 256 16
cert_test_block_3 25600 16 256 272 16
cert_test_block_3 25600 17 272 288 16
cert_test_block_3 25600 18 288 304 16
cert_test_block_3 25600 19 304 320 16
cert_test_block_3 25600 20 320 336 16
cert_test_block_3 25600 21 336 352 16
cert_test_block_3 25600 22 352 368 16
cert_test_block_3 25600 23 368 384 16
cert_test_block_3 25600 24 384 400 16
cert_test_block_3 25600 25 400 416 16
cert_test_block_3 25600 26 416 432 16
cert_test_block_3 25600 27 432 448 16
cert_test_block_3 25600 28 448 464 16
cert_test_block_3 25600 29 464 480 16
cert_test_block_3 25600 30 480 496 16
cert_test_block_3 25600 31 496 512 16
cert_test_block_3 25600 32 512 528 16
cert_test_block_3 25600 33 528 544 16
cert_test_block_3 25600 34 544 560 16
cert_test_block_3 25600 35 560 576 16
cert_test_block_3 25600 36 576 592 16
cert_test_block_3 25600 37 592 608 16
cert_test_block_3 25600 38 608 624 16
cert_test_block_3 25600 39 624 640 16
theorem test25600_complete : Interval test25600 0 640 :=
  (interval_append test25600 0 320 640
  (interval_append test25600 0 160 320
  (interval_append test25600 0 80 160
  (interval_append test25600 0 32 80
  (interval_append test25600 0 16 32
  test25600_block_0
  test25600_block_1)
  (interval_append test25600 32 48 80
  test25600_block_2
  (interval_append test25600 48 64 80
  test25600_block_3
  test25600_block_4)))
  (interval_append test25600 80 112 160
  (interval_append test25600 80 96 112
  test25600_block_5
  test25600_block_6)
  (interval_append test25600 112 128 160
  test25600_block_7
  (interval_append test25600 128 144 160
  test25600_block_8
  test25600_block_9))))
  (interval_append test25600 160 240 320
  (interval_append test25600 160 192 240
  (interval_append test25600 160 176 192
  test25600_block_10
  test25600_block_11)
  (interval_append test25600 192 208 240
  test25600_block_12
  (interval_append test25600 208 224 240
  test25600_block_13
  test25600_block_14)))
  (interval_append test25600 240 272 320
  (interval_append test25600 240 256 272
  test25600_block_15
  test25600_block_16)
  (interval_append test25600 272 288 320
  test25600_block_17
  (interval_append test25600 288 304 320
  test25600_block_18
  test25600_block_19)))))
  (interval_append test25600 320 480 640
  (interval_append test25600 320 400 480
  (interval_append test25600 320 352 400
  (interval_append test25600 320 336 352
  test25600_block_20
  test25600_block_21)
  (interval_append test25600 352 368 400
  test25600_block_22
  (interval_append test25600 368 384 400
  test25600_block_23
  test25600_block_24)))
  (interval_append test25600 400 432 480
  (interval_append test25600 400 416 432
  test25600_block_25
  test25600_block_26)
  (interval_append test25600 432 448 480
  test25600_block_27
  (interval_append test25600 448 464 480
  test25600_block_28
  test25600_block_29))))
  (interval_append test25600 480 560 640
  (interval_append test25600 480 512 560
  (interval_append test25600 480 496 512
  test25600_block_30
  test25600_block_31)
  (interval_append test25600 512 528 560
  test25600_block_32
  (interval_append test25600 528 544 560
  test25600_block_33
  test25600_block_34)))
  (interval_append test25600 560 592 640
  (interval_append test25600 560 576 592
  test25600_block_35
  test25600_block_36)
  (interval_append test25600 592 608 640
  test25600_block_37
  (interval_append test25600 608 624 640
  test25600_block_38
  test25600_block_39))))))
cert_nodeInterval_3 25600 26240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 26240
cert_test_block_3 26240 0 0 16 16
cert_test_block_3 26240 1 16 32 16
cert_test_block_3 26240 2 32 48 16
cert_test_block_3 26240 3 48 64 16
cert_test_block_3 26240 4 64 80 16
cert_test_block_3 26240 5 80 96 16
cert_test_block_3 26240 6 96 112 16
cert_test_block_3 26240 7 112 128 16
cert_test_block_3 26240 8 128 144 16
cert_test_block_3 26240 9 144 160 16
cert_test_block_3 26240 10 160 176 16
cert_test_block_3 26240 11 176 192 16
cert_test_block_3 26240 12 192 208 16
cert_test_block_3 26240 13 208 224 16
cert_test_block_3 26240 14 224 240 16
cert_test_block_3 26240 15 240 256 16
cert_test_block_3 26240 16 256 272 16
cert_test_block_3 26240 17 272 288 16
cert_test_block_3 26240 18 288 304 16
cert_test_block_3 26240 19 304 320 16
cert_test_block_3 26240 20 320 336 16
cert_test_block_3 26240 21 336 352 16
cert_test_block_3 26240 22 352 368 16
cert_test_block_3 26240 23 368 384 16
cert_test_block_3 26240 24 384 400 16
cert_test_block_3 26240 25 400 416 16
cert_test_block_3 26240 26 416 432 16
cert_test_block_3 26240 27 432 448 16
cert_test_block_3 26240 28 448 464 16
cert_test_block_3 26240 29 464 480 16
cert_test_block_3 26240 30 480 496 16
cert_test_block_3 26240 31 496 512 16
cert_test_block_3 26240 32 512 528 16
cert_test_block_3 26240 33 528 544 16
cert_test_block_3 26240 34 544 560 16
cert_test_block_3 26240 35 560 576 16
cert_test_block_3 26240 36 576 592 16
cert_test_block_3 26240 37 592 608 16
cert_test_block_3 26240 38 608 624 16
cert_test_block_3 26240 39 624 640 16
theorem test26240_complete : Interval test26240 0 640 :=
  (interval_append test26240 0 320 640
  (interval_append test26240 0 160 320
  (interval_append test26240 0 80 160
  (interval_append test26240 0 32 80
  (interval_append test26240 0 16 32
  test26240_block_0
  test26240_block_1)
  (interval_append test26240 32 48 80
  test26240_block_2
  (interval_append test26240 48 64 80
  test26240_block_3
  test26240_block_4)))
  (interval_append test26240 80 112 160
  (interval_append test26240 80 96 112
  test26240_block_5
  test26240_block_6)
  (interval_append test26240 112 128 160
  test26240_block_7
  (interval_append test26240 128 144 160
  test26240_block_8
  test26240_block_9))))
  (interval_append test26240 160 240 320
  (interval_append test26240 160 192 240
  (interval_append test26240 160 176 192
  test26240_block_10
  test26240_block_11)
  (interval_append test26240 192 208 240
  test26240_block_12
  (interval_append test26240 208 224 240
  test26240_block_13
  test26240_block_14)))
  (interval_append test26240 240 272 320
  (interval_append test26240 240 256 272
  test26240_block_15
  test26240_block_16)
  (interval_append test26240 272 288 320
  test26240_block_17
  (interval_append test26240 288 304 320
  test26240_block_18
  test26240_block_19)))))
  (interval_append test26240 320 480 640
  (interval_append test26240 320 400 480
  (interval_append test26240 320 352 400
  (interval_append test26240 320 336 352
  test26240_block_20
  test26240_block_21)
  (interval_append test26240 352 368 400
  test26240_block_22
  (interval_append test26240 368 384 400
  test26240_block_23
  test26240_block_24)))
  (interval_append test26240 400 432 480
  (interval_append test26240 400 416 432
  test26240_block_25
  test26240_block_26)
  (interval_append test26240 432 448 480
  test26240_block_27
  (interval_append test26240 448 464 480
  test26240_block_28
  test26240_block_29))))
  (interval_append test26240 480 560 640
  (interval_append test26240 480 512 560
  (interval_append test26240 480 496 512
  test26240_block_30
  test26240_block_31)
  (interval_append test26240 512 528 560
  test26240_block_32
  (interval_append test26240 528 544 560
  test26240_block_33
  test26240_block_34)))
  (interval_append test26240 560 592 640
  (interval_append test26240 560 576 592
  test26240_block_35
  test26240_block_36)
  (interval_append test26240 592 608 640
  test26240_block_37
  (interval_append test26240 608 624 640
  test26240_block_38
  test26240_block_39))))))
cert_nodeInterval_3 26240 26880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 26880
cert_test_block_3 26880 0 0 16 16
cert_test_block_3 26880 1 16 32 16
cert_test_block_3 26880 2 32 48 16
cert_test_block_3 26880 3 48 64 16
cert_test_block_3 26880 4 64 80 16
cert_test_block_3 26880 5 80 96 16
cert_test_block_3 26880 6 96 112 16
cert_test_block_3 26880 7 112 128 16
cert_test_block_3 26880 8 128 144 16
cert_test_block_3 26880 9 144 160 16
cert_test_block_3 26880 10 160 176 16
cert_test_block_3 26880 11 176 192 16
cert_test_block_3 26880 12 192 208 16
cert_test_block_3 26880 13 208 224 16
cert_test_block_3 26880 14 224 240 16
cert_test_block_3 26880 15 240 256 16
cert_test_block_3 26880 16 256 272 16
cert_test_block_3 26880 17 272 288 16
cert_test_block_3 26880 18 288 304 16
cert_test_block_3 26880 19 304 320 16
cert_test_block_3 26880 20 320 336 16
cert_test_block_3 26880 21 336 352 16
cert_test_block_3 26880 22 352 368 16
cert_test_block_3 26880 23 368 384 16
cert_test_block_3 26880 24 384 400 16
cert_test_block_3 26880 25 400 416 16
cert_test_block_3 26880 26 416 432 16
cert_test_block_3 26880 27 432 448 16
cert_test_block_3 26880 28 448 464 16
cert_test_block_3 26880 29 464 480 16
cert_test_block_3 26880 30 480 496 16
cert_test_block_3 26880 31 496 512 16
cert_test_block_3 26880 32 512 528 16
cert_test_block_3 26880 33 528 544 16
cert_test_block_3 26880 34 544 560 16
cert_test_block_3 26880 35 560 576 16
cert_test_block_3 26880 36 576 592 16
cert_test_block_3 26880 37 592 608 16
cert_test_block_3 26880 38 608 624 16
cert_test_block_3 26880 39 624 640 16
theorem test26880_complete : Interval test26880 0 640 :=
  (interval_append test26880 0 320 640
  (interval_append test26880 0 160 320
  (interval_append test26880 0 80 160
  (interval_append test26880 0 32 80
  (interval_append test26880 0 16 32
  test26880_block_0
  test26880_block_1)
  (interval_append test26880 32 48 80
  test26880_block_2
  (interval_append test26880 48 64 80
  test26880_block_3
  test26880_block_4)))
  (interval_append test26880 80 112 160
  (interval_append test26880 80 96 112
  test26880_block_5
  test26880_block_6)
  (interval_append test26880 112 128 160
  test26880_block_7
  (interval_append test26880 128 144 160
  test26880_block_8
  test26880_block_9))))
  (interval_append test26880 160 240 320
  (interval_append test26880 160 192 240
  (interval_append test26880 160 176 192
  test26880_block_10
  test26880_block_11)
  (interval_append test26880 192 208 240
  test26880_block_12
  (interval_append test26880 208 224 240
  test26880_block_13
  test26880_block_14)))
  (interval_append test26880 240 272 320
  (interval_append test26880 240 256 272
  test26880_block_15
  test26880_block_16)
  (interval_append test26880 272 288 320
  test26880_block_17
  (interval_append test26880 288 304 320
  test26880_block_18
  test26880_block_19)))))
  (interval_append test26880 320 480 640
  (interval_append test26880 320 400 480
  (interval_append test26880 320 352 400
  (interval_append test26880 320 336 352
  test26880_block_20
  test26880_block_21)
  (interval_append test26880 352 368 400
  test26880_block_22
  (interval_append test26880 368 384 400
  test26880_block_23
  test26880_block_24)))
  (interval_append test26880 400 432 480
  (interval_append test26880 400 416 432
  test26880_block_25
  test26880_block_26)
  (interval_append test26880 432 448 480
  test26880_block_27
  (interval_append test26880 448 464 480
  test26880_block_28
  test26880_block_29))))
  (interval_append test26880 480 560 640
  (interval_append test26880 480 512 560
  (interval_append test26880 480 496 512
  test26880_block_30
  test26880_block_31)
  (interval_append test26880 512 528 560
  test26880_block_32
  (interval_append test26880 528 544 560
  test26880_block_33
  test26880_block_34)))
  (interval_append test26880 560 592 640
  (interval_append test26880 560 576 592
  test26880_block_35
  test26880_block_36)
  (interval_append test26880 592 608 640
  test26880_block_37
  (interval_append test26880 608 624 640
  test26880_block_38
  test26880_block_39))))))
cert_nodeInterval_3 26880 27520
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 27520
cert_test_block_3 27520 0 0 16 16
cert_test_block_3 27520 1 16 32 16
cert_test_block_3 27520 2 32 48 16
cert_test_block_3 27520 3 48 64 16
cert_test_block_3 27520 4 64 80 16
cert_test_block_3 27520 5 80 96 16
cert_test_block_3 27520 6 96 112 16
cert_test_block_3 27520 7 112 128 16
cert_test_block_3 27520 8 128 144 16
cert_test_block_3 27520 9 144 160 16
cert_test_block_3 27520 10 160 176 16
cert_test_block_3 27520 11 176 192 16
cert_test_block_3 27520 12 192 208 16
cert_test_block_3 27520 13 208 224 16
cert_test_block_3 27520 14 224 240 16
cert_test_block_3 27520 15 240 256 16
cert_test_block_3 27520 16 256 272 16
cert_test_block_3 27520 17 272 288 16
cert_test_block_3 27520 18 288 304 16
cert_test_block_3 27520 19 304 320 16
cert_test_block_3 27520 20 320 336 16
cert_test_block_3 27520 21 336 352 16
cert_test_block_3 27520 22 352 368 16
cert_test_block_3 27520 23 368 384 16
cert_test_block_3 27520 24 384 400 16
cert_test_block_3 27520 25 400 416 16
cert_test_block_3 27520 26 416 432 16
cert_test_block_3 27520 27 432 448 16
cert_test_block_3 27520 28 448 464 16
cert_test_block_3 27520 29 464 480 16
cert_test_block_3 27520 30 480 496 16
cert_test_block_3 27520 31 496 512 16
cert_test_block_3 27520 32 512 528 16
cert_test_block_3 27520 33 528 544 16
cert_test_block_3 27520 34 544 560 16
cert_test_block_3 27520 35 560 576 16
cert_test_block_3 27520 36 576 592 16
cert_test_block_3 27520 37 592 608 16
cert_test_block_3 27520 38 608 624 16
cert_test_block_3 27520 39 624 640 16
theorem test27520_complete : Interval test27520 0 640 :=
  (interval_append test27520 0 320 640
  (interval_append test27520 0 160 320
  (interval_append test27520 0 80 160
  (interval_append test27520 0 32 80
  (interval_append test27520 0 16 32
  test27520_block_0
  test27520_block_1)
  (interval_append test27520 32 48 80
  test27520_block_2
  (interval_append test27520 48 64 80
  test27520_block_3
  test27520_block_4)))
  (interval_append test27520 80 112 160
  (interval_append test27520 80 96 112
  test27520_block_5
  test27520_block_6)
  (interval_append test27520 112 128 160
  test27520_block_7
  (interval_append test27520 128 144 160
  test27520_block_8
  test27520_block_9))))
  (interval_append test27520 160 240 320
  (interval_append test27520 160 192 240
  (interval_append test27520 160 176 192
  test27520_block_10
  test27520_block_11)
  (interval_append test27520 192 208 240
  test27520_block_12
  (interval_append test27520 208 224 240
  test27520_block_13
  test27520_block_14)))
  (interval_append test27520 240 272 320
  (interval_append test27520 240 256 272
  test27520_block_15
  test27520_block_16)
  (interval_append test27520 272 288 320
  test27520_block_17
  (interval_append test27520 288 304 320
  test27520_block_18
  test27520_block_19)))))
  (interval_append test27520 320 480 640
  (interval_append test27520 320 400 480
  (interval_append test27520 320 352 400
  (interval_append test27520 320 336 352
  test27520_block_20
  test27520_block_21)
  (interval_append test27520 352 368 400
  test27520_block_22
  (interval_append test27520 368 384 400
  test27520_block_23
  test27520_block_24)))
  (interval_append test27520 400 432 480
  (interval_append test27520 400 416 432
  test27520_block_25
  test27520_block_26)
  (interval_append test27520 432 448 480
  test27520_block_27
  (interval_append test27520 448 464 480
  test27520_block_28
  test27520_block_29))))
  (interval_append test27520 480 560 640
  (interval_append test27520 480 512 560
  (interval_append test27520 480 496 512
  test27520_block_30
  test27520_block_31)
  (interval_append test27520 512 528 560
  test27520_block_32
  (interval_append test27520 528 544 560
  test27520_block_33
  test27520_block_34)))
  (interval_append test27520 560 592 640
  (interval_append test27520 560 576 592
  test27520_block_35
  test27520_block_36)
  (interval_append test27520 592 608 640
  test27520_block_37
  (interval_append test27520 608 624 640
  test27520_block_38
  test27520_block_39))))))
cert_nodeInterval_3 27520 28160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 28160
cert_test_block_3 28160 0 0 16 16
cert_test_block_3 28160 1 16 32 16
cert_test_block_3 28160 2 32 48 16
cert_test_block_3 28160 3 48 64 16
cert_test_block_3 28160 4 64 80 16
cert_test_block_3 28160 5 80 96 16
cert_test_block_3 28160 6 96 112 16
cert_test_block_3 28160 7 112 128 16
cert_test_block_3 28160 8 128 144 16
cert_test_block_3 28160 9 144 160 16
cert_test_block_3 28160 10 160 176 16
cert_test_block_3 28160 11 176 192 16
cert_test_block_3 28160 12 192 208 16
cert_test_block_3 28160 13 208 224 16
cert_test_block_3 28160 14 224 240 16
cert_test_block_3 28160 15 240 256 16
cert_test_block_3 28160 16 256 272 16
cert_test_block_3 28160 17 272 288 16
cert_test_block_3 28160 18 288 304 16
cert_test_block_3 28160 19 304 320 16
cert_test_block_3 28160 20 320 336 16
cert_test_block_3 28160 21 336 352 16
cert_test_block_3 28160 22 352 368 16
cert_test_block_3 28160 23 368 384 16
cert_test_block_3 28160 24 384 400 16
cert_test_block_3 28160 25 400 416 16
cert_test_block_3 28160 26 416 432 16
cert_test_block_3 28160 27 432 448 16
cert_test_block_3 28160 28 448 464 16
cert_test_block_3 28160 29 464 480 16
cert_test_block_3 28160 30 480 496 16
cert_test_block_3 28160 31 496 512 16
cert_test_block_3 28160 32 512 528 16
cert_test_block_3 28160 33 528 544 16
cert_test_block_3 28160 34 544 560 16
cert_test_block_3 28160 35 560 576 16
cert_test_block_3 28160 36 576 592 16
cert_test_block_3 28160 37 592 608 16
cert_test_block_3 28160 38 608 624 16
cert_test_block_3 28160 39 624 640 16
theorem test28160_complete : Interval test28160 0 640 :=
  (interval_append test28160 0 320 640
  (interval_append test28160 0 160 320
  (interval_append test28160 0 80 160
  (interval_append test28160 0 32 80
  (interval_append test28160 0 16 32
  test28160_block_0
  test28160_block_1)
  (interval_append test28160 32 48 80
  test28160_block_2
  (interval_append test28160 48 64 80
  test28160_block_3
  test28160_block_4)))
  (interval_append test28160 80 112 160
  (interval_append test28160 80 96 112
  test28160_block_5
  test28160_block_6)
  (interval_append test28160 112 128 160
  test28160_block_7
  (interval_append test28160 128 144 160
  test28160_block_8
  test28160_block_9))))
  (interval_append test28160 160 240 320
  (interval_append test28160 160 192 240
  (interval_append test28160 160 176 192
  test28160_block_10
  test28160_block_11)
  (interval_append test28160 192 208 240
  test28160_block_12
  (interval_append test28160 208 224 240
  test28160_block_13
  test28160_block_14)))
  (interval_append test28160 240 272 320
  (interval_append test28160 240 256 272
  test28160_block_15
  test28160_block_16)
  (interval_append test28160 272 288 320
  test28160_block_17
  (interval_append test28160 288 304 320
  test28160_block_18
  test28160_block_19)))))
  (interval_append test28160 320 480 640
  (interval_append test28160 320 400 480
  (interval_append test28160 320 352 400
  (interval_append test28160 320 336 352
  test28160_block_20
  test28160_block_21)
  (interval_append test28160 352 368 400
  test28160_block_22
  (interval_append test28160 368 384 400
  test28160_block_23
  test28160_block_24)))
  (interval_append test28160 400 432 480
  (interval_append test28160 400 416 432
  test28160_block_25
  test28160_block_26)
  (interval_append test28160 432 448 480
  test28160_block_27
  (interval_append test28160 448 464 480
  test28160_block_28
  test28160_block_29))))
  (interval_append test28160 480 560 640
  (interval_append test28160 480 512 560
  (interval_append test28160 480 496 512
  test28160_block_30
  test28160_block_31)
  (interval_append test28160 512 528 560
  test28160_block_32
  (interval_append test28160 528 544 560
  test28160_block_33
  test28160_block_34)))
  (interval_append test28160 560 592 640
  (interval_append test28160 560 576 592
  test28160_block_35
  test28160_block_36)
  (interval_append test28160 592 608 640
  test28160_block_37
  (interval_append test28160 608 624 640
  test28160_block_38
  test28160_block_39))))))
cert_nodeInterval_3 28160 28800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 28800
cert_test_block_3 28800 0 0 16 16
cert_test_block_3 28800 1 16 32 16
cert_test_block_3 28800 2 32 48 16
cert_test_block_3 28800 3 48 64 16
cert_test_block_3 28800 4 64 80 16
cert_test_block_3 28800 5 80 96 16
cert_test_block_3 28800 6 96 112 16
cert_test_block_3 28800 7 112 128 16
cert_test_block_3 28800 8 128 144 16
cert_test_block_3 28800 9 144 160 16
cert_test_block_3 28800 10 160 176 16
cert_test_block_3 28800 11 176 192 16
cert_test_block_3 28800 12 192 208 16
cert_test_block_3 28800 13 208 224 16
cert_test_block_3 28800 14 224 240 16
cert_test_block_3 28800 15 240 256 16
cert_test_block_3 28800 16 256 272 16
cert_test_block_3 28800 17 272 288 16
cert_test_block_3 28800 18 288 304 16
cert_test_block_3 28800 19 304 320 16
cert_test_block_3 28800 20 320 336 16
cert_test_block_3 28800 21 336 352 16
cert_test_block_3 28800 22 352 368 16
cert_test_block_3 28800 23 368 384 16
cert_test_block_3 28800 24 384 400 16
cert_test_block_3 28800 25 400 416 16
cert_test_block_3 28800 26 416 432 16
cert_test_block_3 28800 27 432 448 16
cert_test_block_3 28800 28 448 464 16
cert_test_block_3 28800 29 464 480 16
cert_test_block_3 28800 30 480 496 16
cert_test_block_3 28800 31 496 512 16
cert_test_block_3 28800 32 512 528 16
cert_test_block_3 28800 33 528 544 16
cert_test_block_3 28800 34 544 560 16
cert_test_block_3 28800 35 560 576 16
cert_test_block_3 28800 36 576 592 16
cert_test_block_3 28800 37 592 608 16
cert_test_block_3 28800 38 608 624 16
cert_test_block_3 28800 39 624 640 16
theorem test28800_complete : Interval test28800 0 640 :=
  (interval_append test28800 0 320 640
  (interval_append test28800 0 160 320
  (interval_append test28800 0 80 160
  (interval_append test28800 0 32 80
  (interval_append test28800 0 16 32
  test28800_block_0
  test28800_block_1)
  (interval_append test28800 32 48 80
  test28800_block_2
  (interval_append test28800 48 64 80
  test28800_block_3
  test28800_block_4)))
  (interval_append test28800 80 112 160
  (interval_append test28800 80 96 112
  test28800_block_5
  test28800_block_6)
  (interval_append test28800 112 128 160
  test28800_block_7
  (interval_append test28800 128 144 160
  test28800_block_8
  test28800_block_9))))
  (interval_append test28800 160 240 320
  (interval_append test28800 160 192 240
  (interval_append test28800 160 176 192
  test28800_block_10
  test28800_block_11)
  (interval_append test28800 192 208 240
  test28800_block_12
  (interval_append test28800 208 224 240
  test28800_block_13
  test28800_block_14)))
  (interval_append test28800 240 272 320
  (interval_append test28800 240 256 272
  test28800_block_15
  test28800_block_16)
  (interval_append test28800 272 288 320
  test28800_block_17
  (interval_append test28800 288 304 320
  test28800_block_18
  test28800_block_19)))))
  (interval_append test28800 320 480 640
  (interval_append test28800 320 400 480
  (interval_append test28800 320 352 400
  (interval_append test28800 320 336 352
  test28800_block_20
  test28800_block_21)
  (interval_append test28800 352 368 400
  test28800_block_22
  (interval_append test28800 368 384 400
  test28800_block_23
  test28800_block_24)))
  (interval_append test28800 400 432 480
  (interval_append test28800 400 416 432
  test28800_block_25
  test28800_block_26)
  (interval_append test28800 432 448 480
  test28800_block_27
  (interval_append test28800 448 464 480
  test28800_block_28
  test28800_block_29))))
  (interval_append test28800 480 560 640
  (interval_append test28800 480 512 560
  (interval_append test28800 480 496 512
  test28800_block_30
  test28800_block_31)
  (interval_append test28800 512 528 560
  test28800_block_32
  (interval_append test28800 528 544 560
  test28800_block_33
  test28800_block_34)))
  (interval_append test28800 560 592 640
  (interval_append test28800 560 576 592
  test28800_block_35
  test28800_block_36)
  (interval_append test28800 592 608 640
  test28800_block_37
  (interval_append test28800 608 624 640
  test28800_block_38
  test28800_block_39))))))
cert_nodeInterval_3 28800 29440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 29440
cert_test_block_3 29440 0 0 16 16
cert_test_block_3 29440 1 16 32 16
cert_test_block_3 29440 2 32 48 16
cert_test_block_3 29440 3 48 64 16
cert_test_block_3 29440 4 64 80 16
cert_test_block_3 29440 5 80 96 16
cert_test_block_3 29440 6 96 112 16
cert_test_block_3 29440 7 112 128 16
cert_test_block_3 29440 8 128 144 16
cert_test_block_3 29440 9 144 160 16
cert_test_block_3 29440 10 160 176 16
cert_test_block_3 29440 11 176 192 16
cert_test_block_3 29440 12 192 208 16
cert_test_block_3 29440 13 208 224 16
cert_test_block_3 29440 14 224 240 16
cert_test_block_3 29440 15 240 256 16
cert_test_block_3 29440 16 256 272 16
cert_test_block_3 29440 17 272 288 16
cert_test_block_3 29440 18 288 304 16
cert_test_block_3 29440 19 304 320 16
cert_test_block_3 29440 20 320 336 16
cert_test_block_3 29440 21 336 352 16
cert_test_block_3 29440 22 352 368 16
cert_test_block_3 29440 23 368 384 16
cert_test_block_3 29440 24 384 400 16
cert_test_block_3 29440 25 400 416 16
cert_test_block_3 29440 26 416 432 16
cert_test_block_3 29440 27 432 448 16
cert_test_block_3 29440 28 448 464 16
cert_test_block_3 29440 29 464 480 16
cert_test_block_3 29440 30 480 496 16
cert_test_block_3 29440 31 496 512 16
cert_test_block_3 29440 32 512 528 16
cert_test_block_3 29440 33 528 544 16
cert_test_block_3 29440 34 544 560 16
cert_test_block_3 29440 35 560 576 16
cert_test_block_3 29440 36 576 592 16
cert_test_block_3 29440 37 592 608 16
cert_test_block_3 29440 38 608 624 16
cert_test_block_3 29440 39 624 640 16
theorem test29440_complete : Interval test29440 0 640 :=
  (interval_append test29440 0 320 640
  (interval_append test29440 0 160 320
  (interval_append test29440 0 80 160
  (interval_append test29440 0 32 80
  (interval_append test29440 0 16 32
  test29440_block_0
  test29440_block_1)
  (interval_append test29440 32 48 80
  test29440_block_2
  (interval_append test29440 48 64 80
  test29440_block_3
  test29440_block_4)))
  (interval_append test29440 80 112 160
  (interval_append test29440 80 96 112
  test29440_block_5
  test29440_block_6)
  (interval_append test29440 112 128 160
  test29440_block_7
  (interval_append test29440 128 144 160
  test29440_block_8
  test29440_block_9))))
  (interval_append test29440 160 240 320
  (interval_append test29440 160 192 240
  (interval_append test29440 160 176 192
  test29440_block_10
  test29440_block_11)
  (interval_append test29440 192 208 240
  test29440_block_12
  (interval_append test29440 208 224 240
  test29440_block_13
  test29440_block_14)))
  (interval_append test29440 240 272 320
  (interval_append test29440 240 256 272
  test29440_block_15
  test29440_block_16)
  (interval_append test29440 272 288 320
  test29440_block_17
  (interval_append test29440 288 304 320
  test29440_block_18
  test29440_block_19)))))
  (interval_append test29440 320 480 640
  (interval_append test29440 320 400 480
  (interval_append test29440 320 352 400
  (interval_append test29440 320 336 352
  test29440_block_20
  test29440_block_21)
  (interval_append test29440 352 368 400
  test29440_block_22
  (interval_append test29440 368 384 400
  test29440_block_23
  test29440_block_24)))
  (interval_append test29440 400 432 480
  (interval_append test29440 400 416 432
  test29440_block_25
  test29440_block_26)
  (interval_append test29440 432 448 480
  test29440_block_27
  (interval_append test29440 448 464 480
  test29440_block_28
  test29440_block_29))))
  (interval_append test29440 480 560 640
  (interval_append test29440 480 512 560
  (interval_append test29440 480 496 512
  test29440_block_30
  test29440_block_31)
  (interval_append test29440 512 528 560
  test29440_block_32
  (interval_append test29440 528 544 560
  test29440_block_33
  test29440_block_34)))
  (interval_append test29440 560 592 640
  (interval_append test29440 560 576 592
  test29440_block_35
  test29440_block_36)
  (interval_append test29440 592 608 640
  test29440_block_37
  (interval_append test29440 608 624 640
  test29440_block_38
  test29440_block_39))))))
cert_nodeInterval_3 29440 30080
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 30080
cert_test_block_3 30080 0 0 16 16
cert_test_block_3 30080 1 16 32 16
cert_test_block_3 30080 2 32 48 16
cert_test_block_3 30080 3 48 64 16
cert_test_block_3 30080 4 64 80 16
cert_test_block_3 30080 5 80 96 16
cert_test_block_3 30080 6 96 112 16
cert_test_block_3 30080 7 112 128 16
cert_test_block_3 30080 8 128 144 16
cert_test_block_3 30080 9 144 160 16
cert_test_block_3 30080 10 160 176 16
cert_test_block_3 30080 11 176 192 16
cert_test_block_3 30080 12 192 208 16
cert_test_block_3 30080 13 208 224 16
cert_test_block_3 30080 14 224 240 16
cert_test_block_3 30080 15 240 256 16
cert_test_block_3 30080 16 256 272 16
cert_test_block_3 30080 17 272 288 16
cert_test_block_3 30080 18 288 304 16
cert_test_block_3 30080 19 304 320 16
cert_test_block_3 30080 20 320 336 16
cert_test_block_3 30080 21 336 352 16
cert_test_block_3 30080 22 352 368 16
cert_test_block_3 30080 23 368 384 16
cert_test_block_3 30080 24 384 400 16
cert_test_block_3 30080 25 400 416 16
cert_test_block_3 30080 26 416 432 16
cert_test_block_3 30080 27 432 448 16
cert_test_block_3 30080 28 448 464 16
cert_test_block_3 30080 29 464 480 16
cert_test_block_3 30080 30 480 496 16
cert_test_block_3 30080 31 496 512 16
cert_test_block_3 30080 32 512 528 16
cert_test_block_3 30080 33 528 544 16
cert_test_block_3 30080 34 544 560 16
cert_test_block_3 30080 35 560 576 16
cert_test_block_3 30080 36 576 592 16
cert_test_block_3 30080 37 592 608 16
cert_test_block_3 30080 38 608 624 16
cert_test_block_3 30080 39 624 640 16
theorem test30080_complete : Interval test30080 0 640 :=
  (interval_append test30080 0 320 640
  (interval_append test30080 0 160 320
  (interval_append test30080 0 80 160
  (interval_append test30080 0 32 80
  (interval_append test30080 0 16 32
  test30080_block_0
  test30080_block_1)
  (interval_append test30080 32 48 80
  test30080_block_2
  (interval_append test30080 48 64 80
  test30080_block_3
  test30080_block_4)))
  (interval_append test30080 80 112 160
  (interval_append test30080 80 96 112
  test30080_block_5
  test30080_block_6)
  (interval_append test30080 112 128 160
  test30080_block_7
  (interval_append test30080 128 144 160
  test30080_block_8
  test30080_block_9))))
  (interval_append test30080 160 240 320
  (interval_append test30080 160 192 240
  (interval_append test30080 160 176 192
  test30080_block_10
  test30080_block_11)
  (interval_append test30080 192 208 240
  test30080_block_12
  (interval_append test30080 208 224 240
  test30080_block_13
  test30080_block_14)))
  (interval_append test30080 240 272 320
  (interval_append test30080 240 256 272
  test30080_block_15
  test30080_block_16)
  (interval_append test30080 272 288 320
  test30080_block_17
  (interval_append test30080 288 304 320
  test30080_block_18
  test30080_block_19)))))
  (interval_append test30080 320 480 640
  (interval_append test30080 320 400 480
  (interval_append test30080 320 352 400
  (interval_append test30080 320 336 352
  test30080_block_20
  test30080_block_21)
  (interval_append test30080 352 368 400
  test30080_block_22
  (interval_append test30080 368 384 400
  test30080_block_23
  test30080_block_24)))
  (interval_append test30080 400 432 480
  (interval_append test30080 400 416 432
  test30080_block_25
  test30080_block_26)
  (interval_append test30080 432 448 480
  test30080_block_27
  (interval_append test30080 448 464 480
  test30080_block_28
  test30080_block_29))))
  (interval_append test30080 480 560 640
  (interval_append test30080 480 512 560
  (interval_append test30080 480 496 512
  test30080_block_30
  test30080_block_31)
  (interval_append test30080 512 528 560
  test30080_block_32
  (interval_append test30080 528 544 560
  test30080_block_33
  test30080_block_34)))
  (interval_append test30080 560 592 640
  (interval_append test30080 560 576 592
  test30080_block_35
  test30080_block_36)
  (interval_append test30080 592 608 640
  test30080_block_37
  (interval_append test30080 608 624 640
  test30080_block_38
  test30080_block_39))))))
cert_nodeInterval_3 30080 30720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 30720
cert_test_block_3 30720 0 0 16 16
cert_test_block_3 30720 1 16 32 16
cert_test_block_3 30720 2 32 48 16
cert_test_block_3 30720 3 48 64 16
cert_test_block_3 30720 4 64 80 16
cert_test_block_3 30720 5 80 96 16
cert_test_block_3 30720 6 96 112 16
cert_test_block_3 30720 7 112 128 16
cert_test_block_3 30720 8 128 144 16
cert_test_block_3 30720 9 144 160 16
cert_test_block_3 30720 10 160 176 16
cert_test_block_3 30720 11 176 192 16
cert_test_block_3 30720 12 192 208 16
cert_test_block_3 30720 13 208 224 16
cert_test_block_3 30720 14 224 240 16
cert_test_block_3 30720 15 240 256 16
cert_test_block_3 30720 16 256 272 16
cert_test_block_3 30720 17 272 288 16
cert_test_block_3 30720 18 288 304 16
cert_test_block_3 30720 19 304 320 16
cert_test_block_3 30720 20 320 336 16
cert_test_block_3 30720 21 336 352 16
cert_test_block_3 30720 22 352 368 16
cert_test_block_3 30720 23 368 384 16
cert_test_block_3 30720 24 384 400 16
cert_test_block_3 30720 25 400 416 16
cert_test_block_3 30720 26 416 432 16
cert_test_block_3 30720 27 432 448 16
cert_test_block_3 30720 28 448 464 16
cert_test_block_3 30720 29 464 480 16
cert_test_block_3 30720 30 480 496 16
cert_test_block_3 30720 31 496 512 16
cert_test_block_3 30720 32 512 528 16
cert_test_block_3 30720 33 528 544 16
cert_test_block_3 30720 34 544 560 16
cert_test_block_3 30720 35 560 576 16
cert_test_block_3 30720 36 576 592 16
cert_test_block_3 30720 37 592 608 16
cert_test_block_3 30720 38 608 624 16
cert_test_block_3 30720 39 624 640 16
theorem test30720_complete : Interval test30720 0 640 :=
  (interval_append test30720 0 320 640
  (interval_append test30720 0 160 320
  (interval_append test30720 0 80 160
  (interval_append test30720 0 32 80
  (interval_append test30720 0 16 32
  test30720_block_0
  test30720_block_1)
  (interval_append test30720 32 48 80
  test30720_block_2
  (interval_append test30720 48 64 80
  test30720_block_3
  test30720_block_4)))
  (interval_append test30720 80 112 160
  (interval_append test30720 80 96 112
  test30720_block_5
  test30720_block_6)
  (interval_append test30720 112 128 160
  test30720_block_7
  (interval_append test30720 128 144 160
  test30720_block_8
  test30720_block_9))))
  (interval_append test30720 160 240 320
  (interval_append test30720 160 192 240
  (interval_append test30720 160 176 192
  test30720_block_10
  test30720_block_11)
  (interval_append test30720 192 208 240
  test30720_block_12
  (interval_append test30720 208 224 240
  test30720_block_13
  test30720_block_14)))
  (interval_append test30720 240 272 320
  (interval_append test30720 240 256 272
  test30720_block_15
  test30720_block_16)
  (interval_append test30720 272 288 320
  test30720_block_17
  (interval_append test30720 288 304 320
  test30720_block_18
  test30720_block_19)))))
  (interval_append test30720 320 480 640
  (interval_append test30720 320 400 480
  (interval_append test30720 320 352 400
  (interval_append test30720 320 336 352
  test30720_block_20
  test30720_block_21)
  (interval_append test30720 352 368 400
  test30720_block_22
  (interval_append test30720 368 384 400
  test30720_block_23
  test30720_block_24)))
  (interval_append test30720 400 432 480
  (interval_append test30720 400 416 432
  test30720_block_25
  test30720_block_26)
  (interval_append test30720 432 448 480
  test30720_block_27
  (interval_append test30720 448 464 480
  test30720_block_28
  test30720_block_29))))
  (interval_append test30720 480 560 640
  (interval_append test30720 480 512 560
  (interval_append test30720 480 496 512
  test30720_block_30
  test30720_block_31)
  (interval_append test30720 512 528 560
  test30720_block_32
  (interval_append test30720 528 544 560
  test30720_block_33
  test30720_block_34)))
  (interval_append test30720 560 592 640
  (interval_append test30720 560 576 592
  test30720_block_35
  test30720_block_36)
  (interval_append test30720 592 608 640
  test30720_block_37
  (interval_append test30720 608 624 640
  test30720_block_38
  test30720_block_39))))))
cert_nodeInterval_3 30720 31360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 31360
cert_test_block_3 31360 0 0 16 16
cert_test_block_3 31360 1 16 32 16
cert_test_block_3 31360 2 32 48 16
cert_test_block_3 31360 3 48 64 16
cert_test_block_3 31360 4 64 80 16
cert_test_block_3 31360 5 80 96 16
cert_test_block_3 31360 6 96 112 16
cert_test_block_3 31360 7 112 128 16
cert_test_block_3 31360 8 128 144 16
cert_test_block_3 31360 9 144 160 16
cert_test_block_3 31360 10 160 176 16
cert_test_block_3 31360 11 176 192 16
cert_test_block_3 31360 12 192 208 16
cert_test_block_3 31360 13 208 224 16
cert_test_block_3 31360 14 224 240 16
cert_test_block_3 31360 15 240 256 16
cert_test_block_3 31360 16 256 272 16
cert_test_block_3 31360 17 272 288 16
cert_test_block_3 31360 18 288 304 16
cert_test_block_3 31360 19 304 320 16
cert_test_block_3 31360 20 320 336 16
cert_test_block_3 31360 21 336 352 16
cert_test_block_3 31360 22 352 368 16
cert_test_block_3 31360 23 368 384 16
cert_test_block_3 31360 24 384 400 16
cert_test_block_3 31360 25 400 416 16
cert_test_block_3 31360 26 416 432 16
cert_test_block_3 31360 27 432 448 16
cert_test_block_3 31360 28 448 464 16
cert_test_block_3 31360 29 464 480 16
cert_test_block_3 31360 30 480 496 16
cert_test_block_3 31360 31 496 512 16
cert_test_block_3 31360 32 512 528 16
cert_test_block_3 31360 33 528 544 16
cert_test_block_3 31360 34 544 560 16
cert_test_block_3 31360 35 560 576 16
cert_test_block_3 31360 36 576 592 16
cert_test_block_3 31360 37 592 608 16
cert_test_block_3 31360 38 608 624 16
cert_test_block_3 31360 39 624 640 16
theorem test31360_complete : Interval test31360 0 640 :=
  (interval_append test31360 0 320 640
  (interval_append test31360 0 160 320
  (interval_append test31360 0 80 160
  (interval_append test31360 0 32 80
  (interval_append test31360 0 16 32
  test31360_block_0
  test31360_block_1)
  (interval_append test31360 32 48 80
  test31360_block_2
  (interval_append test31360 48 64 80
  test31360_block_3
  test31360_block_4)))
  (interval_append test31360 80 112 160
  (interval_append test31360 80 96 112
  test31360_block_5
  test31360_block_6)
  (interval_append test31360 112 128 160
  test31360_block_7
  (interval_append test31360 128 144 160
  test31360_block_8
  test31360_block_9))))
  (interval_append test31360 160 240 320
  (interval_append test31360 160 192 240
  (interval_append test31360 160 176 192
  test31360_block_10
  test31360_block_11)
  (interval_append test31360 192 208 240
  test31360_block_12
  (interval_append test31360 208 224 240
  test31360_block_13
  test31360_block_14)))
  (interval_append test31360 240 272 320
  (interval_append test31360 240 256 272
  test31360_block_15
  test31360_block_16)
  (interval_append test31360 272 288 320
  test31360_block_17
  (interval_append test31360 288 304 320
  test31360_block_18
  test31360_block_19)))))
  (interval_append test31360 320 480 640
  (interval_append test31360 320 400 480
  (interval_append test31360 320 352 400
  (interval_append test31360 320 336 352
  test31360_block_20
  test31360_block_21)
  (interval_append test31360 352 368 400
  test31360_block_22
  (interval_append test31360 368 384 400
  test31360_block_23
  test31360_block_24)))
  (interval_append test31360 400 432 480
  (interval_append test31360 400 416 432
  test31360_block_25
  test31360_block_26)
  (interval_append test31360 432 448 480
  test31360_block_27
  (interval_append test31360 448 464 480
  test31360_block_28
  test31360_block_29))))
  (interval_append test31360 480 560 640
  (interval_append test31360 480 512 560
  (interval_append test31360 480 496 512
  test31360_block_30
  test31360_block_31)
  (interval_append test31360 512 528 560
  test31360_block_32
  (interval_append test31360 528 544 560
  test31360_block_33
  test31360_block_34)))
  (interval_append test31360 560 592 640
  (interval_append test31360 560 576 592
  test31360_block_35
  test31360_block_36)
  (interval_append test31360 592 608 640
  test31360_block_37
  (interval_append test31360 608 624 640
  test31360_block_38
  test31360_block_39))))))
cert_nodeInterval_3 31360 32000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 32000
cert_test_block_3 32000 0 0 16 16
cert_test_block_3 32000 1 16 32 16
cert_test_block_3 32000 2 32 48 16
cert_test_block_3 32000 3 48 64 16
cert_test_block_3 32000 4 64 80 16
cert_test_block_3 32000 5 80 96 16
cert_test_block_3 32000 6 96 112 16
cert_test_block_3 32000 7 112 128 16
cert_test_block_3 32000 8 128 144 16
cert_test_block_3 32000 9 144 160 16
cert_test_block_3 32000 10 160 176 16
cert_test_block_3 32000 11 176 192 16
cert_test_block_3 32000 12 192 208 16
cert_test_block_3 32000 13 208 224 16
cert_test_block_3 32000 14 224 240 16
cert_test_block_3 32000 15 240 256 16
cert_test_block_3 32000 16 256 272 16
cert_test_block_3 32000 17 272 288 16
cert_test_block_3 32000 18 288 304 16
cert_test_block_3 32000 19 304 320 16
cert_test_block_3 32000 20 320 336 16
cert_test_block_3 32000 21 336 352 16
cert_test_block_3 32000 22 352 368 16
cert_test_block_3 32000 23 368 384 16
cert_test_block_3 32000 24 384 400 16
cert_test_block_3 32000 25 400 416 16
cert_test_block_3 32000 26 416 432 16
cert_test_block_3 32000 27 432 448 16
cert_test_block_3 32000 28 448 464 16
cert_test_block_3 32000 29 464 480 16
cert_test_block_3 32000 30 480 496 16
cert_test_block_3 32000 31 496 512 16
cert_test_block_3 32000 32 512 528 16
cert_test_block_3 32000 33 528 544 16
cert_test_block_3 32000 34 544 560 16
cert_test_block_3 32000 35 560 576 16
cert_test_block_3 32000 36 576 592 16
cert_test_block_3 32000 37 592 608 16
cert_test_block_3 32000 38 608 624 16
cert_test_block_3 32000 39 624 640 16
theorem test32000_complete : Interval test32000 0 640 :=
  (interval_append test32000 0 320 640
  (interval_append test32000 0 160 320
  (interval_append test32000 0 80 160
  (interval_append test32000 0 32 80
  (interval_append test32000 0 16 32
  test32000_block_0
  test32000_block_1)
  (interval_append test32000 32 48 80
  test32000_block_2
  (interval_append test32000 48 64 80
  test32000_block_3
  test32000_block_4)))
  (interval_append test32000 80 112 160
  (interval_append test32000 80 96 112
  test32000_block_5
  test32000_block_6)
  (interval_append test32000 112 128 160
  test32000_block_7
  (interval_append test32000 128 144 160
  test32000_block_8
  test32000_block_9))))
  (interval_append test32000 160 240 320
  (interval_append test32000 160 192 240
  (interval_append test32000 160 176 192
  test32000_block_10
  test32000_block_11)
  (interval_append test32000 192 208 240
  test32000_block_12
  (interval_append test32000 208 224 240
  test32000_block_13
  test32000_block_14)))
  (interval_append test32000 240 272 320
  (interval_append test32000 240 256 272
  test32000_block_15
  test32000_block_16)
  (interval_append test32000 272 288 320
  test32000_block_17
  (interval_append test32000 288 304 320
  test32000_block_18
  test32000_block_19)))))
  (interval_append test32000 320 480 640
  (interval_append test32000 320 400 480
  (interval_append test32000 320 352 400
  (interval_append test32000 320 336 352
  test32000_block_20
  test32000_block_21)
  (interval_append test32000 352 368 400
  test32000_block_22
  (interval_append test32000 368 384 400
  test32000_block_23
  test32000_block_24)))
  (interval_append test32000 400 432 480
  (interval_append test32000 400 416 432
  test32000_block_25
  test32000_block_26)
  (interval_append test32000 432 448 480
  test32000_block_27
  (interval_append test32000 448 464 480
  test32000_block_28
  test32000_block_29))))
  (interval_append test32000 480 560 640
  (interval_append test32000 480 512 560
  (interval_append test32000 480 496 512
  test32000_block_30
  test32000_block_31)
  (interval_append test32000 512 528 560
  test32000_block_32
  (interval_append test32000 528 544 560
  test32000_block_33
  test32000_block_34)))
  (interval_append test32000 560 592 640
  (interval_append test32000 560 576 592
  test32000_block_35
  test32000_block_36)
  (interval_append test32000 592 608 640
  test32000_block_37
  (interval_append test32000 608 624 640
  test32000_block_38
  test32000_block_39))))))
cert_nodeInterval_3 32000 32640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 32640
cert_test_block_3 32640 0 0 16 16
cert_test_block_3 32640 1 16 32 16
cert_test_block_3 32640 2 32 48 16
cert_test_block_3 32640 3 48 64 16
cert_test_block_3 32640 4 64 80 16
cert_test_block_3 32640 5 80 96 16
cert_test_block_3 32640 6 96 112 16
cert_test_block_3 32640 7 112 128 16
cert_test_block_3 32640 8 128 144 16
cert_test_block_3 32640 9 144 160 16
cert_test_block_3 32640 10 160 176 16
cert_test_block_3 32640 11 176 192 16
cert_test_block_3 32640 12 192 208 16
cert_test_block_3 32640 13 208 224 16
cert_test_block_3 32640 14 224 240 16
cert_test_block_3 32640 15 240 256 16
cert_test_block_3 32640 16 256 272 16
cert_test_block_3 32640 17 272 288 16
cert_test_block_3 32640 18 288 304 16
cert_test_block_3 32640 19 304 320 16
cert_test_block_3 32640 20 320 336 16
cert_test_block_3 32640 21 336 352 16
cert_test_block_3 32640 22 352 368 16
cert_test_block_3 32640 23 368 384 16
cert_test_block_3 32640 24 384 400 16
cert_test_block_3 32640 25 400 416 16
cert_test_block_3 32640 26 416 432 16
cert_test_block_3 32640 27 432 448 16
cert_test_block_3 32640 28 448 464 16
cert_test_block_3 32640 29 464 480 16
cert_test_block_3 32640 30 480 496 16
cert_test_block_3 32640 31 496 512 16
cert_test_block_3 32640 32 512 528 16
cert_test_block_3 32640 33 528 544 16
cert_test_block_3 32640 34 544 560 16
cert_test_block_3 32640 35 560 576 16
cert_test_block_3 32640 36 576 592 16
cert_test_block_3 32640 37 592 608 16
cert_test_block_3 32640 38 608 624 16
cert_test_block_3 32640 39 624 640 16
theorem test32640_complete : Interval test32640 0 640 :=
  (interval_append test32640 0 320 640
  (interval_append test32640 0 160 320
  (interval_append test32640 0 80 160
  (interval_append test32640 0 32 80
  (interval_append test32640 0 16 32
  test32640_block_0
  test32640_block_1)
  (interval_append test32640 32 48 80
  test32640_block_2
  (interval_append test32640 48 64 80
  test32640_block_3
  test32640_block_4)))
  (interval_append test32640 80 112 160
  (interval_append test32640 80 96 112
  test32640_block_5
  test32640_block_6)
  (interval_append test32640 112 128 160
  test32640_block_7
  (interval_append test32640 128 144 160
  test32640_block_8
  test32640_block_9))))
  (interval_append test32640 160 240 320
  (interval_append test32640 160 192 240
  (interval_append test32640 160 176 192
  test32640_block_10
  test32640_block_11)
  (interval_append test32640 192 208 240
  test32640_block_12
  (interval_append test32640 208 224 240
  test32640_block_13
  test32640_block_14)))
  (interval_append test32640 240 272 320
  (interval_append test32640 240 256 272
  test32640_block_15
  test32640_block_16)
  (interval_append test32640 272 288 320
  test32640_block_17
  (interval_append test32640 288 304 320
  test32640_block_18
  test32640_block_19)))))
  (interval_append test32640 320 480 640
  (interval_append test32640 320 400 480
  (interval_append test32640 320 352 400
  (interval_append test32640 320 336 352
  test32640_block_20
  test32640_block_21)
  (interval_append test32640 352 368 400
  test32640_block_22
  (interval_append test32640 368 384 400
  test32640_block_23
  test32640_block_24)))
  (interval_append test32640 400 432 480
  (interval_append test32640 400 416 432
  test32640_block_25
  test32640_block_26)
  (interval_append test32640 432 448 480
  test32640_block_27
  (interval_append test32640 448 464 480
  test32640_block_28
  test32640_block_29))))
  (interval_append test32640 480 560 640
  (interval_append test32640 480 512 560
  (interval_append test32640 480 496 512
  test32640_block_30
  test32640_block_31)
  (interval_append test32640 512 528 560
  test32640_block_32
  (interval_append test32640 528 544 560
  test32640_block_33
  test32640_block_34)))
  (interval_append test32640 560 592 640
  (interval_append test32640 560 576 592
  test32640_block_35
  test32640_block_36)
  (interval_append test32640 592 608 640
  test32640_block_37
  (interval_append test32640 608 624 640
  test32640_block_38
  test32640_block_39))))))
cert_nodeInterval_3 32640 33280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
