module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0319Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 35200
cert_test_block_3 35200 0 0 16 16
cert_test_block_3 35200 1 16 32 16
cert_test_block_3 35200 2 32 48 16
cert_test_block_3 35200 3 48 64 16
cert_test_block_3 35200 4 64 80 16
cert_test_block_3 35200 5 80 96 16
cert_test_block_3 35200 6 96 112 16
cert_test_block_3 35200 7 112 128 16
cert_test_block_3 35200 8 128 144 16
cert_test_block_3 35200 9 144 160 16
cert_test_block_3 35200 10 160 176 16
cert_test_block_3 35200 11 176 192 16
cert_test_block_3 35200 12 192 208 16
cert_test_block_3 35200 13 208 224 16
cert_test_block_3 35200 14 224 240 16
cert_test_block_3 35200 15 240 256 16
cert_test_block_3 35200 16 256 272 16
cert_test_block_3 35200 17 272 288 16
cert_test_block_3 35200 18 288 304 16
cert_test_block_3 35200 19 304 320 16
cert_test_block_3 35200 20 320 336 16
cert_test_block_3 35200 21 336 352 16
cert_test_block_3 35200 22 352 368 16
cert_test_block_3 35200 23 368 384 16
cert_test_block_3 35200 24 384 400 16
cert_test_block_3 35200 25 400 416 16
cert_test_block_3 35200 26 416 432 16
cert_test_block_3 35200 27 432 448 16
cert_test_block_3 35200 28 448 464 16
cert_test_block_3 35200 29 464 480 16
cert_test_block_3 35200 30 480 496 16
cert_test_block_3 35200 31 496 512 16
cert_test_block_3 35200 32 512 528 16
cert_test_block_3 35200 33 528 544 16
cert_test_block_3 35200 34 544 560 16
cert_test_block_3 35200 35 560 576 16
cert_test_block_3 35200 36 576 592 16
cert_test_block_3 35200 37 592 608 16
cert_test_block_3 35200 38 608 624 16
cert_test_block_3 35200 39 624 640 16
theorem test35200_complete : Interval test35200 0 640 :=
  (interval_append test35200 0 320 640
  (interval_append test35200 0 160 320
  (interval_append test35200 0 80 160
  (interval_append test35200 0 32 80
  (interval_append test35200 0 16 32
  test35200_block_0
  test35200_block_1)
  (interval_append test35200 32 48 80
  test35200_block_2
  (interval_append test35200 48 64 80
  test35200_block_3
  test35200_block_4)))
  (interval_append test35200 80 112 160
  (interval_append test35200 80 96 112
  test35200_block_5
  test35200_block_6)
  (interval_append test35200 112 128 160
  test35200_block_7
  (interval_append test35200 128 144 160
  test35200_block_8
  test35200_block_9))))
  (interval_append test35200 160 240 320
  (interval_append test35200 160 192 240
  (interval_append test35200 160 176 192
  test35200_block_10
  test35200_block_11)
  (interval_append test35200 192 208 240
  test35200_block_12
  (interval_append test35200 208 224 240
  test35200_block_13
  test35200_block_14)))
  (interval_append test35200 240 272 320
  (interval_append test35200 240 256 272
  test35200_block_15
  test35200_block_16)
  (interval_append test35200 272 288 320
  test35200_block_17
  (interval_append test35200 288 304 320
  test35200_block_18
  test35200_block_19)))))
  (interval_append test35200 320 480 640
  (interval_append test35200 320 400 480
  (interval_append test35200 320 352 400
  (interval_append test35200 320 336 352
  test35200_block_20
  test35200_block_21)
  (interval_append test35200 352 368 400
  test35200_block_22
  (interval_append test35200 368 384 400
  test35200_block_23
  test35200_block_24)))
  (interval_append test35200 400 432 480
  (interval_append test35200 400 416 432
  test35200_block_25
  test35200_block_26)
  (interval_append test35200 432 448 480
  test35200_block_27
  (interval_append test35200 448 464 480
  test35200_block_28
  test35200_block_29))))
  (interval_append test35200 480 560 640
  (interval_append test35200 480 512 560
  (interval_append test35200 480 496 512
  test35200_block_30
  test35200_block_31)
  (interval_append test35200 512 528 560
  test35200_block_32
  (interval_append test35200 528 544 560
  test35200_block_33
  test35200_block_34)))
  (interval_append test35200 560 592 640
  (interval_append test35200 560 576 592
  test35200_block_35
  test35200_block_36)
  (interval_append test35200 592 608 640
  test35200_block_37
  (interval_append test35200 608 624 640
  test35200_block_38
  test35200_block_39))))))
cert_nodeInterval_3 35200 35840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 35840
cert_test_block_3 35840 0 0 16 16
cert_test_block_3 35840 1 16 32 16
cert_test_block_3 35840 2 32 48 16
cert_test_block_3 35840 3 48 64 16
cert_test_block_3 35840 4 64 80 16
cert_test_block_3 35840 5 80 96 16
cert_test_block_3 35840 6 96 112 16
cert_test_block_3 35840 7 112 128 16
cert_test_block_3 35840 8 128 144 16
cert_test_block_3 35840 9 144 160 16
cert_test_block_3 35840 10 160 176 16
cert_test_block_3 35840 11 176 192 16
cert_test_block_3 35840 12 192 208 16
cert_test_block_3 35840 13 208 224 16
cert_test_block_3 35840 14 224 240 16
cert_test_block_3 35840 15 240 256 16
cert_test_block_3 35840 16 256 272 16
cert_test_block_3 35840 17 272 288 16
cert_test_block_3 35840 18 288 304 16
cert_test_block_3 35840 19 304 320 16
cert_test_block_3 35840 20 320 336 16
cert_test_block_3 35840 21 336 352 16
cert_test_block_3 35840 22 352 368 16
cert_test_block_3 35840 23 368 384 16
cert_test_block_3 35840 24 384 400 16
cert_test_block_3 35840 25 400 416 16
cert_test_block_3 35840 26 416 432 16
cert_test_block_3 35840 27 432 448 16
cert_test_block_3 35840 28 448 464 16
cert_test_block_3 35840 29 464 480 16
cert_test_block_3 35840 30 480 496 16
cert_test_block_3 35840 31 496 512 16
cert_test_block_3 35840 32 512 528 16
cert_test_block_3 35840 33 528 544 16
cert_test_block_3 35840 34 544 560 16
cert_test_block_3 35840 35 560 576 16
cert_test_block_3 35840 36 576 592 16
cert_test_block_3 35840 37 592 608 16
cert_test_block_3 35840 38 608 624 16
cert_test_block_3 35840 39 624 640 16
theorem test35840_complete : Interval test35840 0 640 :=
  (interval_append test35840 0 320 640
  (interval_append test35840 0 160 320
  (interval_append test35840 0 80 160
  (interval_append test35840 0 32 80
  (interval_append test35840 0 16 32
  test35840_block_0
  test35840_block_1)
  (interval_append test35840 32 48 80
  test35840_block_2
  (interval_append test35840 48 64 80
  test35840_block_3
  test35840_block_4)))
  (interval_append test35840 80 112 160
  (interval_append test35840 80 96 112
  test35840_block_5
  test35840_block_6)
  (interval_append test35840 112 128 160
  test35840_block_7
  (interval_append test35840 128 144 160
  test35840_block_8
  test35840_block_9))))
  (interval_append test35840 160 240 320
  (interval_append test35840 160 192 240
  (interval_append test35840 160 176 192
  test35840_block_10
  test35840_block_11)
  (interval_append test35840 192 208 240
  test35840_block_12
  (interval_append test35840 208 224 240
  test35840_block_13
  test35840_block_14)))
  (interval_append test35840 240 272 320
  (interval_append test35840 240 256 272
  test35840_block_15
  test35840_block_16)
  (interval_append test35840 272 288 320
  test35840_block_17
  (interval_append test35840 288 304 320
  test35840_block_18
  test35840_block_19)))))
  (interval_append test35840 320 480 640
  (interval_append test35840 320 400 480
  (interval_append test35840 320 352 400
  (interval_append test35840 320 336 352
  test35840_block_20
  test35840_block_21)
  (interval_append test35840 352 368 400
  test35840_block_22
  (interval_append test35840 368 384 400
  test35840_block_23
  test35840_block_24)))
  (interval_append test35840 400 432 480
  (interval_append test35840 400 416 432
  test35840_block_25
  test35840_block_26)
  (interval_append test35840 432 448 480
  test35840_block_27
  (interval_append test35840 448 464 480
  test35840_block_28
  test35840_block_29))))
  (interval_append test35840 480 560 640
  (interval_append test35840 480 512 560
  (interval_append test35840 480 496 512
  test35840_block_30
  test35840_block_31)
  (interval_append test35840 512 528 560
  test35840_block_32
  (interval_append test35840 528 544 560
  test35840_block_33
  test35840_block_34)))
  (interval_append test35840 560 592 640
  (interval_append test35840 560 576 592
  test35840_block_35
  test35840_block_36)
  (interval_append test35840 592 608 640
  test35840_block_37
  (interval_append test35840 608 624 640
  test35840_block_38
  test35840_block_39))))))
cert_nodeInterval_3 35840 36480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 36480
cert_test_block_3 36480 0 0 16 16
cert_test_block_3 36480 1 16 32 16
cert_test_block_3 36480 2 32 48 16
cert_test_block_3 36480 3 48 64 16
cert_test_block_3 36480 4 64 80 16
cert_test_block_3 36480 5 80 96 16
cert_test_block_3 36480 6 96 112 16
cert_test_block_3 36480 7 112 128 16
cert_test_block_3 36480 8 128 144 16
cert_test_block_3 36480 9 144 160 16
cert_test_block_3 36480 10 160 176 16
cert_test_block_3 36480 11 176 192 16
cert_test_block_3 36480 12 192 208 16
cert_test_block_3 36480 13 208 224 16
cert_test_block_3 36480 14 224 240 16
cert_test_block_3 36480 15 240 256 16
cert_test_block_3 36480 16 256 272 16
cert_test_block_3 36480 17 272 288 16
cert_test_block_3 36480 18 288 304 16
cert_test_block_3 36480 19 304 320 16
cert_test_block_3 36480 20 320 336 16
cert_test_block_3 36480 21 336 352 16
cert_test_block_3 36480 22 352 368 16
cert_test_block_3 36480 23 368 384 16
cert_test_block_3 36480 24 384 400 16
cert_test_block_3 36480 25 400 416 16
cert_test_block_3 36480 26 416 432 16
cert_test_block_3 36480 27 432 448 16
cert_test_block_3 36480 28 448 464 16
cert_test_block_3 36480 29 464 480 16
cert_test_block_3 36480 30 480 496 16
cert_test_block_3 36480 31 496 512 16
cert_test_block_3 36480 32 512 528 16
cert_test_block_3 36480 33 528 544 16
cert_test_block_3 36480 34 544 560 16
cert_test_block_3 36480 35 560 576 16
cert_test_block_3 36480 36 576 592 16
cert_test_block_3 36480 37 592 608 16
cert_test_block_3 36480 38 608 624 16
cert_test_block_3 36480 39 624 640 16
theorem test36480_complete : Interval test36480 0 640 :=
  (interval_append test36480 0 320 640
  (interval_append test36480 0 160 320
  (interval_append test36480 0 80 160
  (interval_append test36480 0 32 80
  (interval_append test36480 0 16 32
  test36480_block_0
  test36480_block_1)
  (interval_append test36480 32 48 80
  test36480_block_2
  (interval_append test36480 48 64 80
  test36480_block_3
  test36480_block_4)))
  (interval_append test36480 80 112 160
  (interval_append test36480 80 96 112
  test36480_block_5
  test36480_block_6)
  (interval_append test36480 112 128 160
  test36480_block_7
  (interval_append test36480 128 144 160
  test36480_block_8
  test36480_block_9))))
  (interval_append test36480 160 240 320
  (interval_append test36480 160 192 240
  (interval_append test36480 160 176 192
  test36480_block_10
  test36480_block_11)
  (interval_append test36480 192 208 240
  test36480_block_12
  (interval_append test36480 208 224 240
  test36480_block_13
  test36480_block_14)))
  (interval_append test36480 240 272 320
  (interval_append test36480 240 256 272
  test36480_block_15
  test36480_block_16)
  (interval_append test36480 272 288 320
  test36480_block_17
  (interval_append test36480 288 304 320
  test36480_block_18
  test36480_block_19)))))
  (interval_append test36480 320 480 640
  (interval_append test36480 320 400 480
  (interval_append test36480 320 352 400
  (interval_append test36480 320 336 352
  test36480_block_20
  test36480_block_21)
  (interval_append test36480 352 368 400
  test36480_block_22
  (interval_append test36480 368 384 400
  test36480_block_23
  test36480_block_24)))
  (interval_append test36480 400 432 480
  (interval_append test36480 400 416 432
  test36480_block_25
  test36480_block_26)
  (interval_append test36480 432 448 480
  test36480_block_27
  (interval_append test36480 448 464 480
  test36480_block_28
  test36480_block_29))))
  (interval_append test36480 480 560 640
  (interval_append test36480 480 512 560
  (interval_append test36480 480 496 512
  test36480_block_30
  test36480_block_31)
  (interval_append test36480 512 528 560
  test36480_block_32
  (interval_append test36480 528 544 560
  test36480_block_33
  test36480_block_34)))
  (interval_append test36480 560 592 640
  (interval_append test36480 560 576 592
  test36480_block_35
  test36480_block_36)
  (interval_append test36480 592 608 640
  test36480_block_37
  (interval_append test36480 608 624 640
  test36480_block_38
  test36480_block_39))))))
cert_nodeInterval_3 36480 37120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 37120
cert_test_block_3 37120 0 0 16 16
cert_test_block_3 37120 1 16 32 16
cert_test_block_3 37120 2 32 48 16
cert_test_block_3 37120 3 48 64 16
cert_test_block_3 37120 4 64 80 16
cert_test_block_3 37120 5 80 96 16
cert_test_block_3 37120 6 96 112 16
cert_test_block_3 37120 7 112 128 16
cert_test_block_3 37120 8 128 144 16
cert_test_block_3 37120 9 144 160 16
cert_test_block_3 37120 10 160 176 16
cert_test_block_3 37120 11 176 192 16
cert_test_block_3 37120 12 192 208 16
cert_test_block_3 37120 13 208 224 16
cert_test_block_3 37120 14 224 240 16
cert_test_block_3 37120 15 240 256 16
cert_test_block_3 37120 16 256 272 16
cert_test_block_3 37120 17 272 288 16
cert_test_block_3 37120 18 288 304 16
cert_test_block_3 37120 19 304 320 16
cert_test_block_3 37120 20 320 336 16
cert_test_block_3 37120 21 336 352 16
cert_test_block_3 37120 22 352 368 16
cert_test_block_3 37120 23 368 384 16
cert_test_block_3 37120 24 384 400 16
cert_test_block_3 37120 25 400 416 16
cert_test_block_3 37120 26 416 432 16
cert_test_block_3 37120 27 432 448 16
cert_test_block_3 37120 28 448 464 16
cert_test_block_3 37120 29 464 480 16
cert_test_block_3 37120 30 480 496 16
cert_test_block_3 37120 31 496 512 16
cert_test_block_3 37120 32 512 528 16
cert_test_block_3 37120 33 528 544 16
cert_test_block_3 37120 34 544 560 16
cert_test_block_3 37120 35 560 576 16
cert_test_block_3 37120 36 576 592 16
cert_test_block_3 37120 37 592 608 16
cert_test_block_3 37120 38 608 624 16
cert_test_block_3 37120 39 624 640 16
theorem test37120_complete : Interval test37120 0 640 :=
  (interval_append test37120 0 320 640
  (interval_append test37120 0 160 320
  (interval_append test37120 0 80 160
  (interval_append test37120 0 32 80
  (interval_append test37120 0 16 32
  test37120_block_0
  test37120_block_1)
  (interval_append test37120 32 48 80
  test37120_block_2
  (interval_append test37120 48 64 80
  test37120_block_3
  test37120_block_4)))
  (interval_append test37120 80 112 160
  (interval_append test37120 80 96 112
  test37120_block_5
  test37120_block_6)
  (interval_append test37120 112 128 160
  test37120_block_7
  (interval_append test37120 128 144 160
  test37120_block_8
  test37120_block_9))))
  (interval_append test37120 160 240 320
  (interval_append test37120 160 192 240
  (interval_append test37120 160 176 192
  test37120_block_10
  test37120_block_11)
  (interval_append test37120 192 208 240
  test37120_block_12
  (interval_append test37120 208 224 240
  test37120_block_13
  test37120_block_14)))
  (interval_append test37120 240 272 320
  (interval_append test37120 240 256 272
  test37120_block_15
  test37120_block_16)
  (interval_append test37120 272 288 320
  test37120_block_17
  (interval_append test37120 288 304 320
  test37120_block_18
  test37120_block_19)))))
  (interval_append test37120 320 480 640
  (interval_append test37120 320 400 480
  (interval_append test37120 320 352 400
  (interval_append test37120 320 336 352
  test37120_block_20
  test37120_block_21)
  (interval_append test37120 352 368 400
  test37120_block_22
  (interval_append test37120 368 384 400
  test37120_block_23
  test37120_block_24)))
  (interval_append test37120 400 432 480
  (interval_append test37120 400 416 432
  test37120_block_25
  test37120_block_26)
  (interval_append test37120 432 448 480
  test37120_block_27
  (interval_append test37120 448 464 480
  test37120_block_28
  test37120_block_29))))
  (interval_append test37120 480 560 640
  (interval_append test37120 480 512 560
  (interval_append test37120 480 496 512
  test37120_block_30
  test37120_block_31)
  (interval_append test37120 512 528 560
  test37120_block_32
  (interval_append test37120 528 544 560
  test37120_block_33
  test37120_block_34)))
  (interval_append test37120 560 592 640
  (interval_append test37120 560 576 592
  test37120_block_35
  test37120_block_36)
  (interval_append test37120 592 608 640
  test37120_block_37
  (interval_append test37120 608 624 640
  test37120_block_38
  test37120_block_39))))))
cert_nodeInterval_3 37120 37760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 37760
cert_test_block_3 37760 0 0 16 16
cert_test_block_3 37760 1 16 32 16
cert_test_block_3 37760 2 32 48 16
cert_test_block_3 37760 3 48 64 16
cert_test_block_3 37760 4 64 80 16
cert_test_block_3 37760 5 80 96 16
cert_test_block_3 37760 6 96 112 16
cert_test_block_3 37760 7 112 128 16
cert_test_block_3 37760 8 128 144 16
cert_test_block_3 37760 9 144 160 16
cert_test_block_3 37760 10 160 176 16
cert_test_block_3 37760 11 176 192 16
cert_test_block_3 37760 12 192 208 16
cert_test_block_3 37760 13 208 224 16
cert_test_block_3 37760 14 224 240 16
cert_test_block_3 37760 15 240 256 16
cert_test_block_3 37760 16 256 272 16
cert_test_block_3 37760 17 272 288 16
cert_test_block_3 37760 18 288 304 16
cert_test_block_3 37760 19 304 320 16
cert_test_block_3 37760 20 320 336 16
cert_test_block_3 37760 21 336 352 16
cert_test_block_3 37760 22 352 368 16
cert_test_block_3 37760 23 368 384 16
cert_test_block_3 37760 24 384 400 16
cert_test_block_3 37760 25 400 416 16
cert_test_block_3 37760 26 416 432 16
cert_test_block_3 37760 27 432 448 16
cert_test_block_3 37760 28 448 464 16
cert_test_block_3 37760 29 464 480 16
cert_test_block_3 37760 30 480 496 16
cert_test_block_3 37760 31 496 512 16
cert_test_block_3 37760 32 512 528 16
cert_test_block_3 37760 33 528 544 16
cert_test_block_3 37760 34 544 560 16
cert_test_block_3 37760 35 560 576 16
cert_test_block_3 37760 36 576 592 16
cert_test_block_3 37760 37 592 608 16
cert_test_block_3 37760 38 608 624 16
cert_test_block_3 37760 39 624 640 16
theorem test37760_complete : Interval test37760 0 640 :=
  (interval_append test37760 0 320 640
  (interval_append test37760 0 160 320
  (interval_append test37760 0 80 160
  (interval_append test37760 0 32 80
  (interval_append test37760 0 16 32
  test37760_block_0
  test37760_block_1)
  (interval_append test37760 32 48 80
  test37760_block_2
  (interval_append test37760 48 64 80
  test37760_block_3
  test37760_block_4)))
  (interval_append test37760 80 112 160
  (interval_append test37760 80 96 112
  test37760_block_5
  test37760_block_6)
  (interval_append test37760 112 128 160
  test37760_block_7
  (interval_append test37760 128 144 160
  test37760_block_8
  test37760_block_9))))
  (interval_append test37760 160 240 320
  (interval_append test37760 160 192 240
  (interval_append test37760 160 176 192
  test37760_block_10
  test37760_block_11)
  (interval_append test37760 192 208 240
  test37760_block_12
  (interval_append test37760 208 224 240
  test37760_block_13
  test37760_block_14)))
  (interval_append test37760 240 272 320
  (interval_append test37760 240 256 272
  test37760_block_15
  test37760_block_16)
  (interval_append test37760 272 288 320
  test37760_block_17
  (interval_append test37760 288 304 320
  test37760_block_18
  test37760_block_19)))))
  (interval_append test37760 320 480 640
  (interval_append test37760 320 400 480
  (interval_append test37760 320 352 400
  (interval_append test37760 320 336 352
  test37760_block_20
  test37760_block_21)
  (interval_append test37760 352 368 400
  test37760_block_22
  (interval_append test37760 368 384 400
  test37760_block_23
  test37760_block_24)))
  (interval_append test37760 400 432 480
  (interval_append test37760 400 416 432
  test37760_block_25
  test37760_block_26)
  (interval_append test37760 432 448 480
  test37760_block_27
  (interval_append test37760 448 464 480
  test37760_block_28
  test37760_block_29))))
  (interval_append test37760 480 560 640
  (interval_append test37760 480 512 560
  (interval_append test37760 480 496 512
  test37760_block_30
  test37760_block_31)
  (interval_append test37760 512 528 560
  test37760_block_32
  (interval_append test37760 528 544 560
  test37760_block_33
  test37760_block_34)))
  (interval_append test37760 560 592 640
  (interval_append test37760 560 576 592
  test37760_block_35
  test37760_block_36)
  (interval_append test37760 592 608 640
  test37760_block_37
  (interval_append test37760 608 624 640
  test37760_block_38
  test37760_block_39))))))
cert_nodeInterval_3 37760 38400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 38400
cert_test_block_3 38400 0 0 16 16
cert_test_block_3 38400 1 16 32 16
cert_test_block_3 38400 2 32 48 16
cert_test_block_3 38400 3 48 64 16
cert_test_block_3 38400 4 64 80 16
cert_test_block_3 38400 5 80 96 16
cert_test_block_3 38400 6 96 112 16
cert_test_block_3 38400 7 112 128 16
cert_test_block_3 38400 8 128 144 16
cert_test_block_3 38400 9 144 160 16
cert_test_block_3 38400 10 160 176 16
cert_test_block_3 38400 11 176 192 16
cert_test_block_3 38400 12 192 208 16
cert_test_block_3 38400 13 208 224 16
cert_test_block_3 38400 14 224 240 16
cert_test_block_3 38400 15 240 256 16
cert_test_block_3 38400 16 256 272 16
cert_test_block_3 38400 17 272 288 16
cert_test_block_3 38400 18 288 304 16
cert_test_block_3 38400 19 304 320 16
cert_test_block_3 38400 20 320 336 16
cert_test_block_3 38400 21 336 352 16
cert_test_block_3 38400 22 352 368 16
cert_test_block_3 38400 23 368 384 16
cert_test_block_3 38400 24 384 400 16
cert_test_block_3 38400 25 400 416 16
cert_test_block_3 38400 26 416 432 16
cert_test_block_3 38400 27 432 448 16
cert_test_block_3 38400 28 448 464 16
cert_test_block_3 38400 29 464 480 16
cert_test_block_3 38400 30 480 496 16
cert_test_block_3 38400 31 496 512 16
cert_test_block_3 38400 32 512 528 16
cert_test_block_3 38400 33 528 544 16
cert_test_block_3 38400 34 544 560 16
cert_test_block_3 38400 35 560 576 16
cert_test_block_3 38400 36 576 592 16
cert_test_block_3 38400 37 592 608 16
cert_test_block_3 38400 38 608 624 16
cert_test_block_3 38400 39 624 640 16
theorem test38400_complete : Interval test38400 0 640 :=
  (interval_append test38400 0 320 640
  (interval_append test38400 0 160 320
  (interval_append test38400 0 80 160
  (interval_append test38400 0 32 80
  (interval_append test38400 0 16 32
  test38400_block_0
  test38400_block_1)
  (interval_append test38400 32 48 80
  test38400_block_2
  (interval_append test38400 48 64 80
  test38400_block_3
  test38400_block_4)))
  (interval_append test38400 80 112 160
  (interval_append test38400 80 96 112
  test38400_block_5
  test38400_block_6)
  (interval_append test38400 112 128 160
  test38400_block_7
  (interval_append test38400 128 144 160
  test38400_block_8
  test38400_block_9))))
  (interval_append test38400 160 240 320
  (interval_append test38400 160 192 240
  (interval_append test38400 160 176 192
  test38400_block_10
  test38400_block_11)
  (interval_append test38400 192 208 240
  test38400_block_12
  (interval_append test38400 208 224 240
  test38400_block_13
  test38400_block_14)))
  (interval_append test38400 240 272 320
  (interval_append test38400 240 256 272
  test38400_block_15
  test38400_block_16)
  (interval_append test38400 272 288 320
  test38400_block_17
  (interval_append test38400 288 304 320
  test38400_block_18
  test38400_block_19)))))
  (interval_append test38400 320 480 640
  (interval_append test38400 320 400 480
  (interval_append test38400 320 352 400
  (interval_append test38400 320 336 352
  test38400_block_20
  test38400_block_21)
  (interval_append test38400 352 368 400
  test38400_block_22
  (interval_append test38400 368 384 400
  test38400_block_23
  test38400_block_24)))
  (interval_append test38400 400 432 480
  (interval_append test38400 400 416 432
  test38400_block_25
  test38400_block_26)
  (interval_append test38400 432 448 480
  test38400_block_27
  (interval_append test38400 448 464 480
  test38400_block_28
  test38400_block_29))))
  (interval_append test38400 480 560 640
  (interval_append test38400 480 512 560
  (interval_append test38400 480 496 512
  test38400_block_30
  test38400_block_31)
  (interval_append test38400 512 528 560
  test38400_block_32
  (interval_append test38400 528 544 560
  test38400_block_33
  test38400_block_34)))
  (interval_append test38400 560 592 640
  (interval_append test38400 560 576 592
  test38400_block_35
  test38400_block_36)
  (interval_append test38400 592 608 640
  test38400_block_37
  (interval_append test38400 608 624 640
  test38400_block_38
  test38400_block_39))))))
cert_nodeInterval_3 38400 39040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 39040
cert_test_block_3 39040 0 0 16 16
cert_test_block_3 39040 1 16 32 16
cert_test_block_3 39040 2 32 48 16
cert_test_block_3 39040 3 48 64 16
cert_test_block_3 39040 4 64 80 16
cert_test_block_3 39040 5 80 96 16
cert_test_block_3 39040 6 96 112 16
cert_test_block_3 39040 7 112 128 16
cert_test_block_3 39040 8 128 144 16
cert_test_block_3 39040 9 144 160 16
cert_test_block_3 39040 10 160 176 16
cert_test_block_3 39040 11 176 192 16
cert_test_block_3 39040 12 192 208 16
cert_test_block_3 39040 13 208 224 16
cert_test_block_3 39040 14 224 240 16
cert_test_block_3 39040 15 240 256 16
cert_test_block_3 39040 16 256 272 16
cert_test_block_3 39040 17 272 288 16
cert_test_block_3 39040 18 288 304 16
cert_test_block_3 39040 19 304 320 16
cert_test_block_3 39040 20 320 336 16
cert_test_block_3 39040 21 336 352 16
cert_test_block_3 39040 22 352 368 16
cert_test_block_3 39040 23 368 384 16
cert_test_block_3 39040 24 384 400 16
cert_test_block_3 39040 25 400 416 16
cert_test_block_3 39040 26 416 432 16
cert_test_block_3 39040 27 432 448 16
cert_test_block_3 39040 28 448 464 16
cert_test_block_3 39040 29 464 480 16
cert_test_block_3 39040 30 480 496 16
cert_test_block_3 39040 31 496 512 16
cert_test_block_3 39040 32 512 528 16
cert_test_block_3 39040 33 528 544 16
cert_test_block_3 39040 34 544 560 16
cert_test_block_3 39040 35 560 576 16
cert_test_block_3 39040 36 576 592 16
cert_test_block_3 39040 37 592 608 16
cert_test_block_3 39040 38 608 624 16
cert_test_block_3 39040 39 624 640 16
theorem test39040_complete : Interval test39040 0 640 :=
  (interval_append test39040 0 320 640
  (interval_append test39040 0 160 320
  (interval_append test39040 0 80 160
  (interval_append test39040 0 32 80
  (interval_append test39040 0 16 32
  test39040_block_0
  test39040_block_1)
  (interval_append test39040 32 48 80
  test39040_block_2
  (interval_append test39040 48 64 80
  test39040_block_3
  test39040_block_4)))
  (interval_append test39040 80 112 160
  (interval_append test39040 80 96 112
  test39040_block_5
  test39040_block_6)
  (interval_append test39040 112 128 160
  test39040_block_7
  (interval_append test39040 128 144 160
  test39040_block_8
  test39040_block_9))))
  (interval_append test39040 160 240 320
  (interval_append test39040 160 192 240
  (interval_append test39040 160 176 192
  test39040_block_10
  test39040_block_11)
  (interval_append test39040 192 208 240
  test39040_block_12
  (interval_append test39040 208 224 240
  test39040_block_13
  test39040_block_14)))
  (interval_append test39040 240 272 320
  (interval_append test39040 240 256 272
  test39040_block_15
  test39040_block_16)
  (interval_append test39040 272 288 320
  test39040_block_17
  (interval_append test39040 288 304 320
  test39040_block_18
  test39040_block_19)))))
  (interval_append test39040 320 480 640
  (interval_append test39040 320 400 480
  (interval_append test39040 320 352 400
  (interval_append test39040 320 336 352
  test39040_block_20
  test39040_block_21)
  (interval_append test39040 352 368 400
  test39040_block_22
  (interval_append test39040 368 384 400
  test39040_block_23
  test39040_block_24)))
  (interval_append test39040 400 432 480
  (interval_append test39040 400 416 432
  test39040_block_25
  test39040_block_26)
  (interval_append test39040 432 448 480
  test39040_block_27
  (interval_append test39040 448 464 480
  test39040_block_28
  test39040_block_29))))
  (interval_append test39040 480 560 640
  (interval_append test39040 480 512 560
  (interval_append test39040 480 496 512
  test39040_block_30
  test39040_block_31)
  (interval_append test39040 512 528 560
  test39040_block_32
  (interval_append test39040 528 544 560
  test39040_block_33
  test39040_block_34)))
  (interval_append test39040 560 592 640
  (interval_append test39040 560 576 592
  test39040_block_35
  test39040_block_36)
  (interval_append test39040 592 608 640
  test39040_block_37
  (interval_append test39040 608 624 640
  test39040_block_38
  test39040_block_39))))))
cert_nodeInterval_3 39040 39680
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 39680
cert_test_block_3 39680 0 0 16 16
cert_test_block_3 39680 1 16 32 16
cert_test_block_3 39680 2 32 48 16
cert_test_block_3 39680 3 48 64 16
cert_test_block_3 39680 4 64 80 16
cert_test_block_3 39680 5 80 96 16
cert_test_block_3 39680 6 96 112 16
cert_test_block_3 39680 7 112 128 16
cert_test_block_3 39680 8 128 144 16
cert_test_block_3 39680 9 144 160 16
cert_test_block_3 39680 10 160 176 16
cert_test_block_3 39680 11 176 192 16
cert_test_block_3 39680 12 192 208 16
cert_test_block_3 39680 13 208 224 16
cert_test_block_3 39680 14 224 240 16
cert_test_block_3 39680 15 240 256 16
cert_test_block_3 39680 16 256 272 16
cert_test_block_3 39680 17 272 288 16
cert_test_block_3 39680 18 288 304 16
cert_test_block_3 39680 19 304 320 16
cert_test_block_3 39680 20 320 336 16
cert_test_block_3 39680 21 336 352 16
cert_test_block_3 39680 22 352 368 16
cert_test_block_3 39680 23 368 384 16
cert_test_block_3 39680 24 384 400 16
cert_test_block_3 39680 25 400 416 16
cert_test_block_3 39680 26 416 432 16
cert_test_block_3 39680 27 432 448 16
cert_test_block_3 39680 28 448 464 16
cert_test_block_3 39680 29 464 480 16
cert_test_block_3 39680 30 480 496 16
cert_test_block_3 39680 31 496 512 16
cert_test_block_3 39680 32 512 528 16
cert_test_block_3 39680 33 528 544 16
cert_test_block_3 39680 34 544 560 16
cert_test_block_3 39680 35 560 576 16
cert_test_block_3 39680 36 576 592 16
cert_test_block_3 39680 37 592 608 16
cert_test_block_3 39680 38 608 624 16
cert_test_block_3 39680 39 624 640 16
theorem test39680_complete : Interval test39680 0 640 :=
  (interval_append test39680 0 320 640
  (interval_append test39680 0 160 320
  (interval_append test39680 0 80 160
  (interval_append test39680 0 32 80
  (interval_append test39680 0 16 32
  test39680_block_0
  test39680_block_1)
  (interval_append test39680 32 48 80
  test39680_block_2
  (interval_append test39680 48 64 80
  test39680_block_3
  test39680_block_4)))
  (interval_append test39680 80 112 160
  (interval_append test39680 80 96 112
  test39680_block_5
  test39680_block_6)
  (interval_append test39680 112 128 160
  test39680_block_7
  (interval_append test39680 128 144 160
  test39680_block_8
  test39680_block_9))))
  (interval_append test39680 160 240 320
  (interval_append test39680 160 192 240
  (interval_append test39680 160 176 192
  test39680_block_10
  test39680_block_11)
  (interval_append test39680 192 208 240
  test39680_block_12
  (interval_append test39680 208 224 240
  test39680_block_13
  test39680_block_14)))
  (interval_append test39680 240 272 320
  (interval_append test39680 240 256 272
  test39680_block_15
  test39680_block_16)
  (interval_append test39680 272 288 320
  test39680_block_17
  (interval_append test39680 288 304 320
  test39680_block_18
  test39680_block_19)))))
  (interval_append test39680 320 480 640
  (interval_append test39680 320 400 480
  (interval_append test39680 320 352 400
  (interval_append test39680 320 336 352
  test39680_block_20
  test39680_block_21)
  (interval_append test39680 352 368 400
  test39680_block_22
  (interval_append test39680 368 384 400
  test39680_block_23
  test39680_block_24)))
  (interval_append test39680 400 432 480
  (interval_append test39680 400 416 432
  test39680_block_25
  test39680_block_26)
  (interval_append test39680 432 448 480
  test39680_block_27
  (interval_append test39680 448 464 480
  test39680_block_28
  test39680_block_29))))
  (interval_append test39680 480 560 640
  (interval_append test39680 480 512 560
  (interval_append test39680 480 496 512
  test39680_block_30
  test39680_block_31)
  (interval_append test39680 512 528 560
  test39680_block_32
  (interval_append test39680 528 544 560
  test39680_block_33
  test39680_block_34)))
  (interval_append test39680 560 592 640
  (interval_append test39680 560 576 592
  test39680_block_35
  test39680_block_36)
  (interval_append test39680 592 608 640
  test39680_block_37
  (interval_append test39680 608 624 640
  test39680_block_38
  test39680_block_39))))))
cert_nodeInterval_3 39680 40320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 40320
cert_test_block_3 40320 0 0 16 16
cert_test_block_3 40320 1 16 32 16
cert_test_block_3 40320 2 32 48 16
cert_test_block_3 40320 3 48 64 16
cert_test_block_3 40320 4 64 80 16
cert_test_block_3 40320 5 80 96 16
cert_test_block_3 40320 6 96 112 16
cert_test_block_3 40320 7 112 128 16
cert_test_block_3 40320 8 128 144 16
cert_test_block_3 40320 9 144 160 16
cert_test_block_3 40320 10 160 176 16
cert_test_block_3 40320 11 176 192 16
cert_test_block_3 40320 12 192 208 16
cert_test_block_3 40320 13 208 224 16
cert_test_block_3 40320 14 224 240 16
cert_test_block_3 40320 15 240 256 16
cert_test_block_3 40320 16 256 272 16
cert_test_block_3 40320 17 272 288 16
cert_test_block_3 40320 18 288 304 16
cert_test_block_3 40320 19 304 320 16
cert_test_block_3 40320 20 320 336 16
cert_test_block_3 40320 21 336 352 16
cert_test_block_3 40320 22 352 368 16
cert_test_block_3 40320 23 368 384 16
cert_test_block_3 40320 24 384 400 16
cert_test_block_3 40320 25 400 416 16
cert_test_block_3 40320 26 416 432 16
cert_test_block_3 40320 27 432 448 16
cert_test_block_3 40320 28 448 464 16
cert_test_block_3 40320 29 464 480 16
cert_test_block_3 40320 30 480 496 16
cert_test_block_3 40320 31 496 512 16
cert_test_block_3 40320 32 512 528 16
cert_test_block_3 40320 33 528 544 16
cert_test_block_3 40320 34 544 560 16
cert_test_block_3 40320 35 560 576 16
cert_test_block_3 40320 36 576 592 16
cert_test_block_3 40320 37 592 608 16
cert_test_block_3 40320 38 608 624 16
cert_test_block_3 40320 39 624 640 16
theorem test40320_complete : Interval test40320 0 640 :=
  (interval_append test40320 0 320 640
  (interval_append test40320 0 160 320
  (interval_append test40320 0 80 160
  (interval_append test40320 0 32 80
  (interval_append test40320 0 16 32
  test40320_block_0
  test40320_block_1)
  (interval_append test40320 32 48 80
  test40320_block_2
  (interval_append test40320 48 64 80
  test40320_block_3
  test40320_block_4)))
  (interval_append test40320 80 112 160
  (interval_append test40320 80 96 112
  test40320_block_5
  test40320_block_6)
  (interval_append test40320 112 128 160
  test40320_block_7
  (interval_append test40320 128 144 160
  test40320_block_8
  test40320_block_9))))
  (interval_append test40320 160 240 320
  (interval_append test40320 160 192 240
  (interval_append test40320 160 176 192
  test40320_block_10
  test40320_block_11)
  (interval_append test40320 192 208 240
  test40320_block_12
  (interval_append test40320 208 224 240
  test40320_block_13
  test40320_block_14)))
  (interval_append test40320 240 272 320
  (interval_append test40320 240 256 272
  test40320_block_15
  test40320_block_16)
  (interval_append test40320 272 288 320
  test40320_block_17
  (interval_append test40320 288 304 320
  test40320_block_18
  test40320_block_19)))))
  (interval_append test40320 320 480 640
  (interval_append test40320 320 400 480
  (interval_append test40320 320 352 400
  (interval_append test40320 320 336 352
  test40320_block_20
  test40320_block_21)
  (interval_append test40320 352 368 400
  test40320_block_22
  (interval_append test40320 368 384 400
  test40320_block_23
  test40320_block_24)))
  (interval_append test40320 400 432 480
  (interval_append test40320 400 416 432
  test40320_block_25
  test40320_block_26)
  (interval_append test40320 432 448 480
  test40320_block_27
  (interval_append test40320 448 464 480
  test40320_block_28
  test40320_block_29))))
  (interval_append test40320 480 560 640
  (interval_append test40320 480 512 560
  (interval_append test40320 480 496 512
  test40320_block_30
  test40320_block_31)
  (interval_append test40320 512 528 560
  test40320_block_32
  (interval_append test40320 528 544 560
  test40320_block_33
  test40320_block_34)))
  (interval_append test40320 560 592 640
  (interval_append test40320 560 576 592
  test40320_block_35
  test40320_block_36)
  (interval_append test40320 592 608 640
  test40320_block_37
  (interval_append test40320 608 624 640
  test40320_block_38
  test40320_block_39))))))
cert_nodeInterval_3 40320 40960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 40960
cert_test_block_3 40960 0 0 16 16
cert_test_block_3 40960 1 16 32 16
cert_test_block_3 40960 2 32 48 16
cert_test_block_3 40960 3 48 64 16
cert_test_block_3 40960 4 64 80 16
cert_test_block_3 40960 5 80 96 16
cert_test_block_3 40960 6 96 112 16
cert_test_block_3 40960 7 112 128 16
cert_test_block_3 40960 8 128 144 16
cert_test_block_3 40960 9 144 160 16
cert_test_block_3 40960 10 160 176 16
cert_test_block_3 40960 11 176 192 16
cert_test_block_3 40960 12 192 208 16
cert_test_block_3 40960 13 208 224 16
cert_test_block_3 40960 14 224 240 16
cert_test_block_3 40960 15 240 256 16
cert_test_block_3 40960 16 256 272 16
cert_test_block_3 40960 17 272 288 16
cert_test_block_3 40960 18 288 304 16
cert_test_block_3 40960 19 304 320 16
cert_test_block_3 40960 20 320 336 16
cert_test_block_3 40960 21 336 352 16
cert_test_block_3 40960 22 352 368 16
cert_test_block_3 40960 23 368 384 16
cert_test_block_3 40960 24 384 400 16
cert_test_block_3 40960 25 400 416 16
cert_test_block_3 40960 26 416 432 16
cert_test_block_3 40960 27 432 448 16
cert_test_block_3 40960 28 448 464 16
cert_test_block_3 40960 29 464 480 16
cert_test_block_3 40960 30 480 496 16
cert_test_block_3 40960 31 496 512 16
cert_test_block_3 40960 32 512 528 16
cert_test_block_3 40960 33 528 544 16
cert_test_block_3 40960 34 544 560 16
cert_test_block_3 40960 35 560 576 16
cert_test_block_3 40960 36 576 592 16
cert_test_block_3 40960 37 592 608 16
cert_test_block_3 40960 38 608 624 16
cert_test_block_3 40960 39 624 640 16
theorem test40960_complete : Interval test40960 0 640 :=
  (interval_append test40960 0 320 640
  (interval_append test40960 0 160 320
  (interval_append test40960 0 80 160
  (interval_append test40960 0 32 80
  (interval_append test40960 0 16 32
  test40960_block_0
  test40960_block_1)
  (interval_append test40960 32 48 80
  test40960_block_2
  (interval_append test40960 48 64 80
  test40960_block_3
  test40960_block_4)))
  (interval_append test40960 80 112 160
  (interval_append test40960 80 96 112
  test40960_block_5
  test40960_block_6)
  (interval_append test40960 112 128 160
  test40960_block_7
  (interval_append test40960 128 144 160
  test40960_block_8
  test40960_block_9))))
  (interval_append test40960 160 240 320
  (interval_append test40960 160 192 240
  (interval_append test40960 160 176 192
  test40960_block_10
  test40960_block_11)
  (interval_append test40960 192 208 240
  test40960_block_12
  (interval_append test40960 208 224 240
  test40960_block_13
  test40960_block_14)))
  (interval_append test40960 240 272 320
  (interval_append test40960 240 256 272
  test40960_block_15
  test40960_block_16)
  (interval_append test40960 272 288 320
  test40960_block_17
  (interval_append test40960 288 304 320
  test40960_block_18
  test40960_block_19)))))
  (interval_append test40960 320 480 640
  (interval_append test40960 320 400 480
  (interval_append test40960 320 352 400
  (interval_append test40960 320 336 352
  test40960_block_20
  test40960_block_21)
  (interval_append test40960 352 368 400
  test40960_block_22
  (interval_append test40960 368 384 400
  test40960_block_23
  test40960_block_24)))
  (interval_append test40960 400 432 480
  (interval_append test40960 400 416 432
  test40960_block_25
  test40960_block_26)
  (interval_append test40960 432 448 480
  test40960_block_27
  (interval_append test40960 448 464 480
  test40960_block_28
  test40960_block_29))))
  (interval_append test40960 480 560 640
  (interval_append test40960 480 512 560
  (interval_append test40960 480 496 512
  test40960_block_30
  test40960_block_31)
  (interval_append test40960 512 528 560
  test40960_block_32
  (interval_append test40960 528 544 560
  test40960_block_33
  test40960_block_34)))
  (interval_append test40960 560 592 640
  (interval_append test40960 560 576 592
  test40960_block_35
  test40960_block_36)
  (interval_append test40960 592 608 640
  test40960_block_37
  (interval_append test40960 608 624 640
  test40960_block_38
  test40960_block_39))))))
cert_nodeInterval_3 40960 41600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 41600
cert_test_block_3 41600 0 0 16 16
cert_test_block_3 41600 1 16 32 16
cert_test_block_3 41600 2 32 48 16
cert_test_block_3 41600 3 48 64 16
cert_test_block_3 41600 4 64 80 16
cert_test_block_3 41600 5 80 96 16
cert_test_block_3 41600 6 96 112 16
cert_test_block_3 41600 7 112 128 16
cert_test_block_3 41600 8 128 144 16
cert_test_block_3 41600 9 144 160 16
cert_test_block_3 41600 10 160 176 16
cert_test_block_3 41600 11 176 192 16
cert_test_block_3 41600 12 192 208 16
cert_test_block_3 41600 13 208 224 16
cert_test_block_3 41600 14 224 240 16
cert_test_block_3 41600 15 240 256 16
cert_test_block_3 41600 16 256 272 16
cert_test_block_3 41600 17 272 288 16
cert_test_block_3 41600 18 288 304 16
cert_test_block_3 41600 19 304 320 16
cert_test_block_3 41600 20 320 336 16
cert_test_block_3 41600 21 336 352 16
cert_test_block_3 41600 22 352 368 16
cert_test_block_3 41600 23 368 384 16
cert_test_block_3 41600 24 384 400 16
cert_test_block_3 41600 25 400 416 16
cert_test_block_3 41600 26 416 432 16
cert_test_block_3 41600 27 432 448 16
cert_test_block_3 41600 28 448 464 16
cert_test_block_3 41600 29 464 480 16
cert_test_block_3 41600 30 480 496 16
cert_test_block_3 41600 31 496 512 16
cert_test_block_3 41600 32 512 528 16
cert_test_block_3 41600 33 528 544 16
cert_test_block_3 41600 34 544 560 16
cert_test_block_3 41600 35 560 576 16
cert_test_block_3 41600 36 576 592 16
cert_test_block_3 41600 37 592 608 16
cert_test_block_3 41600 38 608 624 16
cert_test_block_3 41600 39 624 640 16
theorem test41600_complete : Interval test41600 0 640 :=
  (interval_append test41600 0 320 640
  (interval_append test41600 0 160 320
  (interval_append test41600 0 80 160
  (interval_append test41600 0 32 80
  (interval_append test41600 0 16 32
  test41600_block_0
  test41600_block_1)
  (interval_append test41600 32 48 80
  test41600_block_2
  (interval_append test41600 48 64 80
  test41600_block_3
  test41600_block_4)))
  (interval_append test41600 80 112 160
  (interval_append test41600 80 96 112
  test41600_block_5
  test41600_block_6)
  (interval_append test41600 112 128 160
  test41600_block_7
  (interval_append test41600 128 144 160
  test41600_block_8
  test41600_block_9))))
  (interval_append test41600 160 240 320
  (interval_append test41600 160 192 240
  (interval_append test41600 160 176 192
  test41600_block_10
  test41600_block_11)
  (interval_append test41600 192 208 240
  test41600_block_12
  (interval_append test41600 208 224 240
  test41600_block_13
  test41600_block_14)))
  (interval_append test41600 240 272 320
  (interval_append test41600 240 256 272
  test41600_block_15
  test41600_block_16)
  (interval_append test41600 272 288 320
  test41600_block_17
  (interval_append test41600 288 304 320
  test41600_block_18
  test41600_block_19)))))
  (interval_append test41600 320 480 640
  (interval_append test41600 320 400 480
  (interval_append test41600 320 352 400
  (interval_append test41600 320 336 352
  test41600_block_20
  test41600_block_21)
  (interval_append test41600 352 368 400
  test41600_block_22
  (interval_append test41600 368 384 400
  test41600_block_23
  test41600_block_24)))
  (interval_append test41600 400 432 480
  (interval_append test41600 400 416 432
  test41600_block_25
  test41600_block_26)
  (interval_append test41600 432 448 480
  test41600_block_27
  (interval_append test41600 448 464 480
  test41600_block_28
  test41600_block_29))))
  (interval_append test41600 480 560 640
  (interval_append test41600 480 512 560
  (interval_append test41600 480 496 512
  test41600_block_30
  test41600_block_31)
  (interval_append test41600 512 528 560
  test41600_block_32
  (interval_append test41600 528 544 560
  test41600_block_33
  test41600_block_34)))
  (interval_append test41600 560 592 640
  (interval_append test41600 560 576 592
  test41600_block_35
  test41600_block_36)
  (interval_append test41600 592 608 640
  test41600_block_37
  (interval_append test41600 608 624 640
  test41600_block_38
  test41600_block_39))))))
cert_nodeInterval_3 41600 42240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end
