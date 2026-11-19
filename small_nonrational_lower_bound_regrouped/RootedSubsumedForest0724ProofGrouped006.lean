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
cert_test_11 53760
cert_test_block_3 53760 0 0 16 16
cert_test_block_3 53760 1 16 32 16
cert_test_block_3 53760 2 32 48 16
cert_test_block_3 53760 3 48 64 16
cert_test_block_3 53760 4 64 80 16
cert_test_block_3 53760 5 80 96 16
cert_test_block_3 53760 6 96 112 16
cert_test_block_3 53760 7 112 128 16
cert_test_block_3 53760 8 128 144 16
cert_test_block_3 53760 9 144 160 16
cert_test_block_3 53760 10 160 176 16
cert_test_block_3 53760 11 176 192 16
cert_test_block_3 53760 12 192 208 16
cert_test_block_3 53760 13 208 224 16
cert_test_block_3 53760 14 224 240 16
cert_test_block_3 53760 15 240 256 16
cert_test_block_3 53760 16 256 272 16
cert_test_block_3 53760 17 272 288 16
cert_test_block_3 53760 18 288 304 16
cert_test_block_3 53760 19 304 320 16
cert_test_block_3 53760 20 320 336 16
cert_test_block_3 53760 21 336 352 16
cert_test_block_3 53760 22 352 368 16
cert_test_block_3 53760 23 368 384 16
cert_test_block_3 53760 24 384 400 16
cert_test_block_3 53760 25 400 416 16
cert_test_block_3 53760 26 416 432 16
cert_test_block_3 53760 27 432 448 16
cert_test_block_3 53760 28 448 464 16
cert_test_block_3 53760 29 464 480 16
cert_test_block_3 53760 30 480 496 16
cert_test_block_3 53760 31 496 512 16
cert_test_block_3 53760 32 512 528 16
cert_test_block_3 53760 33 528 544 16
cert_test_block_3 53760 34 544 560 16
cert_test_block_3 53760 35 560 576 16
cert_test_block_3 53760 36 576 592 16
cert_test_block_3 53760 37 592 608 16
cert_test_block_3 53760 38 608 624 16
cert_test_block_3 53760 39 624 640 16
theorem test53760_complete : Interval test53760 0 640 :=
  (interval_append test53760 0 320 640
  (interval_append test53760 0 160 320
  (interval_append test53760 0 80 160
  (interval_append test53760 0 32 80
  (interval_append test53760 0 16 32
  test53760_block_0
  test53760_block_1)
  (interval_append test53760 32 48 80
  test53760_block_2
  (interval_append test53760 48 64 80
  test53760_block_3
  test53760_block_4)))
  (interval_append test53760 80 112 160
  (interval_append test53760 80 96 112
  test53760_block_5
  test53760_block_6)
  (interval_append test53760 112 128 160
  test53760_block_7
  (interval_append test53760 128 144 160
  test53760_block_8
  test53760_block_9))))
  (interval_append test53760 160 240 320
  (interval_append test53760 160 192 240
  (interval_append test53760 160 176 192
  test53760_block_10
  test53760_block_11)
  (interval_append test53760 192 208 240
  test53760_block_12
  (interval_append test53760 208 224 240
  test53760_block_13
  test53760_block_14)))
  (interval_append test53760 240 272 320
  (interval_append test53760 240 256 272
  test53760_block_15
  test53760_block_16)
  (interval_append test53760 272 288 320
  test53760_block_17
  (interval_append test53760 288 304 320
  test53760_block_18
  test53760_block_19)))))
  (interval_append test53760 320 480 640
  (interval_append test53760 320 400 480
  (interval_append test53760 320 352 400
  (interval_append test53760 320 336 352
  test53760_block_20
  test53760_block_21)
  (interval_append test53760 352 368 400
  test53760_block_22
  (interval_append test53760 368 384 400
  test53760_block_23
  test53760_block_24)))
  (interval_append test53760 400 432 480
  (interval_append test53760 400 416 432
  test53760_block_25
  test53760_block_26)
  (interval_append test53760 432 448 480
  test53760_block_27
  (interval_append test53760 448 464 480
  test53760_block_28
  test53760_block_29))))
  (interval_append test53760 480 560 640
  (interval_append test53760 480 512 560
  (interval_append test53760 480 496 512
  test53760_block_30
  test53760_block_31)
  (interval_append test53760 512 528 560
  test53760_block_32
  (interval_append test53760 528 544 560
  test53760_block_33
  test53760_block_34)))
  (interval_append test53760 560 592 640
  (interval_append test53760 560 576 592
  test53760_block_35
  test53760_block_36)
  (interval_append test53760 592 608 640
  test53760_block_37
  (interval_append test53760 608 624 640
  test53760_block_38
  test53760_block_39))))))
cert_nodeInterval_3 53760 54400
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
cert_test_11 54400
cert_test_block_3 54400 0 0 16 16
cert_test_block_3 54400 1 16 32 16
cert_test_block_3 54400 2 32 48 16
cert_test_block_3 54400 3 48 64 16
cert_test_block_3 54400 4 64 80 16
cert_test_block_3 54400 5 80 96 16
cert_test_block_3 54400 6 96 112 16
cert_test_block_3 54400 7 112 128 16
cert_test_block_3 54400 8 128 144 16
cert_test_block_3 54400 9 144 160 16
cert_test_block_3 54400 10 160 176 16
cert_test_block_3 54400 11 176 192 16
cert_test_block_3 54400 12 192 208 16
cert_test_block_3 54400 13 208 224 16
cert_test_block_3 54400 14 224 240 16
cert_test_block_3 54400 15 240 256 16
cert_test_block_3 54400 16 256 272 16
cert_test_block_3 54400 17 272 288 16
cert_test_block_3 54400 18 288 304 16
cert_test_block_3 54400 19 304 320 16
cert_test_block_3 54400 20 320 336 16
cert_test_block_3 54400 21 336 352 16
cert_test_block_3 54400 22 352 368 16
cert_test_block_3 54400 23 368 384 16
cert_test_block_3 54400 24 384 400 16
cert_test_block_3 54400 25 400 416 16
cert_test_block_3 54400 26 416 432 16
cert_test_block_3 54400 27 432 448 16
cert_test_block_3 54400 28 448 464 16
cert_test_block_3 54400 29 464 480 16
cert_test_block_3 54400 30 480 496 16
cert_test_block_3 54400 31 496 512 16
cert_test_block_3 54400 32 512 528 16
cert_test_block_3 54400 33 528 544 16
cert_test_block_3 54400 34 544 560 16
cert_test_block_3 54400 35 560 576 16
cert_test_block_3 54400 36 576 592 16
cert_test_block_3 54400 37 592 608 16
cert_test_block_3 54400 38 608 624 16
cert_test_block_3 54400 39 624 640 16
theorem test54400_complete : Interval test54400 0 640 :=
  (interval_append test54400 0 320 640
  (interval_append test54400 0 160 320
  (interval_append test54400 0 80 160
  (interval_append test54400 0 32 80
  (interval_append test54400 0 16 32
  test54400_block_0
  test54400_block_1)
  (interval_append test54400 32 48 80
  test54400_block_2
  (interval_append test54400 48 64 80
  test54400_block_3
  test54400_block_4)))
  (interval_append test54400 80 112 160
  (interval_append test54400 80 96 112
  test54400_block_5
  test54400_block_6)
  (interval_append test54400 112 128 160
  test54400_block_7
  (interval_append test54400 128 144 160
  test54400_block_8
  test54400_block_9))))
  (interval_append test54400 160 240 320
  (interval_append test54400 160 192 240
  (interval_append test54400 160 176 192
  test54400_block_10
  test54400_block_11)
  (interval_append test54400 192 208 240
  test54400_block_12
  (interval_append test54400 208 224 240
  test54400_block_13
  test54400_block_14)))
  (interval_append test54400 240 272 320
  (interval_append test54400 240 256 272
  test54400_block_15
  test54400_block_16)
  (interval_append test54400 272 288 320
  test54400_block_17
  (interval_append test54400 288 304 320
  test54400_block_18
  test54400_block_19)))))
  (interval_append test54400 320 480 640
  (interval_append test54400 320 400 480
  (interval_append test54400 320 352 400
  (interval_append test54400 320 336 352
  test54400_block_20
  test54400_block_21)
  (interval_append test54400 352 368 400
  test54400_block_22
  (interval_append test54400 368 384 400
  test54400_block_23
  test54400_block_24)))
  (interval_append test54400 400 432 480
  (interval_append test54400 400 416 432
  test54400_block_25
  test54400_block_26)
  (interval_append test54400 432 448 480
  test54400_block_27
  (interval_append test54400 448 464 480
  test54400_block_28
  test54400_block_29))))
  (interval_append test54400 480 560 640
  (interval_append test54400 480 512 560
  (interval_append test54400 480 496 512
  test54400_block_30
  test54400_block_31)
  (interval_append test54400 512 528 560
  test54400_block_32
  (interval_append test54400 528 544 560
  test54400_block_33
  test54400_block_34)))
  (interval_append test54400 560 592 640
  (interval_append test54400 560 576 592
  test54400_block_35
  test54400_block_36)
  (interval_append test54400 592 608 640
  test54400_block_37
  (interval_append test54400 608 624 640
  test54400_block_38
  test54400_block_39))))))
cert_nodeInterval_3 54400 55040
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
cert_test_11 55040
cert_test_block_3 55040 0 0 16 16
cert_test_block_3 55040 1 16 32 16
cert_test_block_3 55040 2 32 48 16
cert_test_block_3 55040 3 48 64 16
cert_test_block_3 55040 4 64 80 16
cert_test_block_3 55040 5 80 96 16
cert_test_block_3 55040 6 96 112 16
cert_test_block_3 55040 7 112 128 16
cert_test_block_3 55040 8 128 144 16
cert_test_block_3 55040 9 144 160 16
cert_test_block_3 55040 10 160 176 16
cert_test_block_3 55040 11 176 192 16
cert_test_block_3 55040 12 192 208 16
cert_test_block_3 55040 13 208 224 16
cert_test_block_3 55040 14 224 240 16
cert_test_block_3 55040 15 240 256 16
cert_test_block_3 55040 16 256 272 16
cert_test_block_3 55040 17 272 288 16
cert_test_block_3 55040 18 288 304 16
cert_test_block_3 55040 19 304 320 16
cert_test_block_3 55040 20 320 336 16
cert_test_block_3 55040 21 336 352 16
cert_test_block_3 55040 22 352 368 16
cert_test_block_3 55040 23 368 384 16
cert_test_block_3 55040 24 384 400 16
cert_test_block_3 55040 25 400 416 16
cert_test_block_3 55040 26 416 432 16
cert_test_block_3 55040 27 432 448 16
cert_test_block_3 55040 28 448 464 16
cert_test_block_3 55040 29 464 480 16
cert_test_block_3 55040 30 480 496 16
cert_test_block_3 55040 31 496 512 16
cert_test_block_3 55040 32 512 528 16
cert_test_block_3 55040 33 528 544 16
cert_test_block_3 55040 34 544 560 16
cert_test_block_3 55040 35 560 576 16
cert_test_block_3 55040 36 576 592 16
cert_test_block_3 55040 37 592 608 16
cert_test_block_3 55040 38 608 624 16
cert_test_block_3 55040 39 624 640 16
theorem test55040_complete : Interval test55040 0 640 :=
  (interval_append test55040 0 320 640
  (interval_append test55040 0 160 320
  (interval_append test55040 0 80 160
  (interval_append test55040 0 32 80
  (interval_append test55040 0 16 32
  test55040_block_0
  test55040_block_1)
  (interval_append test55040 32 48 80
  test55040_block_2
  (interval_append test55040 48 64 80
  test55040_block_3
  test55040_block_4)))
  (interval_append test55040 80 112 160
  (interval_append test55040 80 96 112
  test55040_block_5
  test55040_block_6)
  (interval_append test55040 112 128 160
  test55040_block_7
  (interval_append test55040 128 144 160
  test55040_block_8
  test55040_block_9))))
  (interval_append test55040 160 240 320
  (interval_append test55040 160 192 240
  (interval_append test55040 160 176 192
  test55040_block_10
  test55040_block_11)
  (interval_append test55040 192 208 240
  test55040_block_12
  (interval_append test55040 208 224 240
  test55040_block_13
  test55040_block_14)))
  (interval_append test55040 240 272 320
  (interval_append test55040 240 256 272
  test55040_block_15
  test55040_block_16)
  (interval_append test55040 272 288 320
  test55040_block_17
  (interval_append test55040 288 304 320
  test55040_block_18
  test55040_block_19)))))
  (interval_append test55040 320 480 640
  (interval_append test55040 320 400 480
  (interval_append test55040 320 352 400
  (interval_append test55040 320 336 352
  test55040_block_20
  test55040_block_21)
  (interval_append test55040 352 368 400
  test55040_block_22
  (interval_append test55040 368 384 400
  test55040_block_23
  test55040_block_24)))
  (interval_append test55040 400 432 480
  (interval_append test55040 400 416 432
  test55040_block_25
  test55040_block_26)
  (interval_append test55040 432 448 480
  test55040_block_27
  (interval_append test55040 448 464 480
  test55040_block_28
  test55040_block_29))))
  (interval_append test55040 480 560 640
  (interval_append test55040 480 512 560
  (interval_append test55040 480 496 512
  test55040_block_30
  test55040_block_31)
  (interval_append test55040 512 528 560
  test55040_block_32
  (interval_append test55040 528 544 560
  test55040_block_33
  test55040_block_34)))
  (interval_append test55040 560 592 640
  (interval_append test55040 560 576 592
  test55040_block_35
  test55040_block_36)
  (interval_append test55040 592 608 640
  test55040_block_37
  (interval_append test55040 608 624 640
  test55040_block_38
  test55040_block_39))))))
cert_nodeInterval_3 55040 55680
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
cert_test_11 55680
cert_test_block_3 55680 0 0 16 16
cert_test_block_3 55680 1 16 32 16
cert_test_block_3 55680 2 32 48 16
cert_test_block_3 55680 3 48 64 16
cert_test_block_3 55680 4 64 80 16
cert_test_block_3 55680 5 80 96 16
cert_test_block_3 55680 6 96 112 16
cert_test_block_3 55680 7 112 128 16
cert_test_block_3 55680 8 128 144 16
cert_test_block_3 55680 9 144 160 16
cert_test_block_3 55680 10 160 176 16
cert_test_block_3 55680 11 176 192 16
cert_test_block_3 55680 12 192 208 16
cert_test_block_3 55680 13 208 224 16
cert_test_block_3 55680 14 224 240 16
cert_test_block_3 55680 15 240 256 16
cert_test_block_3 55680 16 256 272 16
cert_test_block_3 55680 17 272 288 16
cert_test_block_3 55680 18 288 304 16
cert_test_block_3 55680 19 304 320 16
cert_test_block_3 55680 20 320 336 16
cert_test_block_3 55680 21 336 352 16
cert_test_block_3 55680 22 352 368 16
cert_test_block_3 55680 23 368 384 16
cert_test_block_3 55680 24 384 400 16
cert_test_block_3 55680 25 400 416 16
cert_test_block_3 55680 26 416 432 16
cert_test_block_3 55680 27 432 448 16
cert_test_block_3 55680 28 448 464 16
cert_test_block_3 55680 29 464 480 16
cert_test_block_3 55680 30 480 496 16
cert_test_block_3 55680 31 496 512 16
cert_test_block_3 55680 32 512 528 16
cert_test_block_3 55680 33 528 544 16
cert_test_block_3 55680 34 544 560 16
cert_test_block_3 55680 35 560 576 16
cert_test_block_3 55680 36 576 592 16
cert_test_block_3 55680 37 592 608 16
cert_test_block_3 55680 38 608 624 16
cert_test_block_3 55680 39 624 640 16
theorem test55680_complete : Interval test55680 0 640 :=
  (interval_append test55680 0 320 640
  (interval_append test55680 0 160 320
  (interval_append test55680 0 80 160
  (interval_append test55680 0 32 80
  (interval_append test55680 0 16 32
  test55680_block_0
  test55680_block_1)
  (interval_append test55680 32 48 80
  test55680_block_2
  (interval_append test55680 48 64 80
  test55680_block_3
  test55680_block_4)))
  (interval_append test55680 80 112 160
  (interval_append test55680 80 96 112
  test55680_block_5
  test55680_block_6)
  (interval_append test55680 112 128 160
  test55680_block_7
  (interval_append test55680 128 144 160
  test55680_block_8
  test55680_block_9))))
  (interval_append test55680 160 240 320
  (interval_append test55680 160 192 240
  (interval_append test55680 160 176 192
  test55680_block_10
  test55680_block_11)
  (interval_append test55680 192 208 240
  test55680_block_12
  (interval_append test55680 208 224 240
  test55680_block_13
  test55680_block_14)))
  (interval_append test55680 240 272 320
  (interval_append test55680 240 256 272
  test55680_block_15
  test55680_block_16)
  (interval_append test55680 272 288 320
  test55680_block_17
  (interval_append test55680 288 304 320
  test55680_block_18
  test55680_block_19)))))
  (interval_append test55680 320 480 640
  (interval_append test55680 320 400 480
  (interval_append test55680 320 352 400
  (interval_append test55680 320 336 352
  test55680_block_20
  test55680_block_21)
  (interval_append test55680 352 368 400
  test55680_block_22
  (interval_append test55680 368 384 400
  test55680_block_23
  test55680_block_24)))
  (interval_append test55680 400 432 480
  (interval_append test55680 400 416 432
  test55680_block_25
  test55680_block_26)
  (interval_append test55680 432 448 480
  test55680_block_27
  (interval_append test55680 448 464 480
  test55680_block_28
  test55680_block_29))))
  (interval_append test55680 480 560 640
  (interval_append test55680 480 512 560
  (interval_append test55680 480 496 512
  test55680_block_30
  test55680_block_31)
  (interval_append test55680 512 528 560
  test55680_block_32
  (interval_append test55680 528 544 560
  test55680_block_33
  test55680_block_34)))
  (interval_append test55680 560 592 640
  (interval_append test55680 560 576 592
  test55680_block_35
  test55680_block_36)
  (interval_append test55680 592 608 640
  test55680_block_37
  (interval_append test55680 608 624 640
  test55680_block_38
  test55680_block_39))))))
cert_nodeInterval_3 55680 56320
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
cert_test_11 56320
cert_test_block_3 56320 0 0 16 16
cert_test_block_3 56320 1 16 32 16
cert_test_block_3 56320 2 32 48 16
cert_test_block_3 56320 3 48 64 16
cert_test_block_3 56320 4 64 80 16
cert_test_block_3 56320 5 80 96 16
cert_test_block_3 56320 6 96 112 16
cert_test_block_3 56320 7 112 128 16
cert_test_block_3 56320 8 128 144 16
cert_test_block_3 56320 9 144 160 16
cert_test_block_3 56320 10 160 176 16
cert_test_block_3 56320 11 176 192 16
cert_test_block_3 56320 12 192 208 16
cert_test_block_3 56320 13 208 224 16
cert_test_block_3 56320 14 224 240 16
cert_test_block_3 56320 15 240 256 16
cert_test_block_3 56320 16 256 272 16
cert_test_block_3 56320 17 272 288 16
cert_test_block_3 56320 18 288 304 16
cert_test_block_3 56320 19 304 320 16
cert_test_block_3 56320 20 320 336 16
cert_test_block_3 56320 21 336 352 16
cert_test_block_3 56320 22 352 368 16
cert_test_block_3 56320 23 368 384 16
cert_test_block_3 56320 24 384 400 16
cert_test_block_3 56320 25 400 416 16
cert_test_block_3 56320 26 416 432 16
cert_test_block_3 56320 27 432 448 16
cert_test_block_3 56320 28 448 464 16
cert_test_block_3 56320 29 464 480 16
cert_test_block_3 56320 30 480 496 16
cert_test_block_3 56320 31 496 512 16
cert_test_block_3 56320 32 512 528 16
cert_test_block_3 56320 33 528 544 16
cert_test_block_3 56320 34 544 560 16
cert_test_block_3 56320 35 560 576 16
cert_test_block_3 56320 36 576 592 16
cert_test_block_3 56320 37 592 608 16
cert_test_block_3 56320 38 608 624 16
cert_test_block_3 56320 39 624 640 16
theorem test56320_complete : Interval test56320 0 640 :=
  (interval_append test56320 0 320 640
  (interval_append test56320 0 160 320
  (interval_append test56320 0 80 160
  (interval_append test56320 0 32 80
  (interval_append test56320 0 16 32
  test56320_block_0
  test56320_block_1)
  (interval_append test56320 32 48 80
  test56320_block_2
  (interval_append test56320 48 64 80
  test56320_block_3
  test56320_block_4)))
  (interval_append test56320 80 112 160
  (interval_append test56320 80 96 112
  test56320_block_5
  test56320_block_6)
  (interval_append test56320 112 128 160
  test56320_block_7
  (interval_append test56320 128 144 160
  test56320_block_8
  test56320_block_9))))
  (interval_append test56320 160 240 320
  (interval_append test56320 160 192 240
  (interval_append test56320 160 176 192
  test56320_block_10
  test56320_block_11)
  (interval_append test56320 192 208 240
  test56320_block_12
  (interval_append test56320 208 224 240
  test56320_block_13
  test56320_block_14)))
  (interval_append test56320 240 272 320
  (interval_append test56320 240 256 272
  test56320_block_15
  test56320_block_16)
  (interval_append test56320 272 288 320
  test56320_block_17
  (interval_append test56320 288 304 320
  test56320_block_18
  test56320_block_19)))))
  (interval_append test56320 320 480 640
  (interval_append test56320 320 400 480
  (interval_append test56320 320 352 400
  (interval_append test56320 320 336 352
  test56320_block_20
  test56320_block_21)
  (interval_append test56320 352 368 400
  test56320_block_22
  (interval_append test56320 368 384 400
  test56320_block_23
  test56320_block_24)))
  (interval_append test56320 400 432 480
  (interval_append test56320 400 416 432
  test56320_block_25
  test56320_block_26)
  (interval_append test56320 432 448 480
  test56320_block_27
  (interval_append test56320 448 464 480
  test56320_block_28
  test56320_block_29))))
  (interval_append test56320 480 560 640
  (interval_append test56320 480 512 560
  (interval_append test56320 480 496 512
  test56320_block_30
  test56320_block_31)
  (interval_append test56320 512 528 560
  test56320_block_32
  (interval_append test56320 528 544 560
  test56320_block_33
  test56320_block_34)))
  (interval_append test56320 560 592 640
  (interval_append test56320 560 576 592
  test56320_block_35
  test56320_block_36)
  (interval_append test56320 592 608 640
  test56320_block_37
  (interval_append test56320 608 624 640
  test56320_block_38
  test56320_block_39))))))
cert_nodeInterval_3 56320 56960
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
cert_test_11 56960
cert_test_block_3 56960 0 0 16 16
cert_test_block_3 56960 1 16 32 16
cert_test_block_3 56960 2 32 48 16
cert_test_block_3 56960 3 48 64 16
cert_test_block_3 56960 4 64 80 16
cert_test_block_3 56960 5 80 96 16
cert_test_block_3 56960 6 96 112 16
cert_test_block_3 56960 7 112 128 16
cert_test_block_3 56960 8 128 144 16
cert_test_block_3 56960 9 144 160 16
cert_test_block_3 56960 10 160 176 16
cert_test_block_3 56960 11 176 192 16
cert_test_block_3 56960 12 192 208 16
cert_test_block_3 56960 13 208 224 16
cert_test_block_3 56960 14 224 240 16
cert_test_block_3 56960 15 240 256 16
cert_test_block_3 56960 16 256 272 16
cert_test_block_3 56960 17 272 288 16
cert_test_block_3 56960 18 288 304 16
cert_test_block_3 56960 19 304 320 16
cert_test_block_3 56960 20 320 336 16
cert_test_block_3 56960 21 336 352 16
cert_test_block_3 56960 22 352 368 16
cert_test_block_3 56960 23 368 384 16
cert_test_block_3 56960 24 384 400 16
cert_test_block_3 56960 25 400 416 16
cert_test_block_3 56960 26 416 432 16
cert_test_block_3 56960 27 432 448 16
cert_test_block_3 56960 28 448 464 16
cert_test_block_3 56960 29 464 480 16
cert_test_block_3 56960 30 480 496 16
cert_test_block_3 56960 31 496 512 16
cert_test_block_3 56960 32 512 528 16
cert_test_block_3 56960 33 528 544 16
cert_test_block_3 56960 34 544 560 16
cert_test_block_3 56960 35 560 576 16
cert_test_block_3 56960 36 576 592 16
cert_test_block_3 56960 37 592 608 16
cert_test_block_3 56960 38 608 624 16
cert_test_block_3 56960 39 624 640 16
theorem test56960_complete : Interval test56960 0 640 :=
  (interval_append test56960 0 320 640
  (interval_append test56960 0 160 320
  (interval_append test56960 0 80 160
  (interval_append test56960 0 32 80
  (interval_append test56960 0 16 32
  test56960_block_0
  test56960_block_1)
  (interval_append test56960 32 48 80
  test56960_block_2
  (interval_append test56960 48 64 80
  test56960_block_3
  test56960_block_4)))
  (interval_append test56960 80 112 160
  (interval_append test56960 80 96 112
  test56960_block_5
  test56960_block_6)
  (interval_append test56960 112 128 160
  test56960_block_7
  (interval_append test56960 128 144 160
  test56960_block_8
  test56960_block_9))))
  (interval_append test56960 160 240 320
  (interval_append test56960 160 192 240
  (interval_append test56960 160 176 192
  test56960_block_10
  test56960_block_11)
  (interval_append test56960 192 208 240
  test56960_block_12
  (interval_append test56960 208 224 240
  test56960_block_13
  test56960_block_14)))
  (interval_append test56960 240 272 320
  (interval_append test56960 240 256 272
  test56960_block_15
  test56960_block_16)
  (interval_append test56960 272 288 320
  test56960_block_17
  (interval_append test56960 288 304 320
  test56960_block_18
  test56960_block_19)))))
  (interval_append test56960 320 480 640
  (interval_append test56960 320 400 480
  (interval_append test56960 320 352 400
  (interval_append test56960 320 336 352
  test56960_block_20
  test56960_block_21)
  (interval_append test56960 352 368 400
  test56960_block_22
  (interval_append test56960 368 384 400
  test56960_block_23
  test56960_block_24)))
  (interval_append test56960 400 432 480
  (interval_append test56960 400 416 432
  test56960_block_25
  test56960_block_26)
  (interval_append test56960 432 448 480
  test56960_block_27
  (interval_append test56960 448 464 480
  test56960_block_28
  test56960_block_29))))
  (interval_append test56960 480 560 640
  (interval_append test56960 480 512 560
  (interval_append test56960 480 496 512
  test56960_block_30
  test56960_block_31)
  (interval_append test56960 512 528 560
  test56960_block_32
  (interval_append test56960 528 544 560
  test56960_block_33
  test56960_block_34)))
  (interval_append test56960 560 592 640
  (interval_append test56960 560 576 592
  test56960_block_35
  test56960_block_36)
  (interval_append test56960 592 608 640
  test56960_block_37
  (interval_append test56960 608 624 640
  test56960_block_38
  test56960_block_39))))))
cert_nodeInterval_3 56960 57600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
