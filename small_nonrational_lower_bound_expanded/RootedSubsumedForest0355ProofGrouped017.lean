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
cert_test_11 129280
cert_test_block_3 129280 0 0 16 16
cert_test_block_3 129280 1 16 32 16
cert_test_block_3 129280 2 32 48 16
cert_test_block_3 129280 3 48 64 16
cert_test_block_3 129280 4 64 80 16
cert_test_block_3 129280 5 80 96 16
cert_test_block_3 129280 6 96 112 16
cert_test_block_3 129280 7 112 128 16
cert_test_block_3 129280 8 128 144 16
cert_test_block_3 129280 9 144 160 16
cert_test_block_3 129280 10 160 176 16
cert_test_block_3 129280 11 176 192 16
cert_test_block_3 129280 12 192 208 16
cert_test_block_3 129280 13 208 224 16
cert_test_block_3 129280 14 224 240 16
cert_test_block_3 129280 15 240 256 16
cert_test_block_3 129280 16 256 272 16
cert_test_block_3 129280 17 272 288 16
cert_test_block_3 129280 18 288 304 16
cert_test_block_3 129280 19 304 320 16
cert_test_block_3 129280 20 320 336 16
cert_test_block_3 129280 21 336 352 16
cert_test_block_3 129280 22 352 368 16
cert_test_block_3 129280 23 368 384 16
cert_test_block_3 129280 24 384 400 16
cert_test_block_3 129280 25 400 416 16
cert_test_block_3 129280 26 416 432 16
cert_test_block_3 129280 27 432 448 16
cert_test_block_3 129280 28 448 464 16
cert_test_block_3 129280 29 464 480 16
cert_test_block_3 129280 30 480 496 16
cert_test_block_3 129280 31 496 512 16
cert_test_block_3 129280 32 512 528 16
cert_test_block_3 129280 33 528 544 16
cert_test_block_3 129280 34 544 560 16
cert_test_block_3 129280 35 560 576 16
cert_test_block_3 129280 36 576 592 16
cert_test_block_3 129280 37 592 608 16
cert_test_block_3 129280 38 608 624 16
cert_test_block_3 129280 39 624 640 16
theorem test129280_complete : Interval test129280 0 640 :=
  (interval_append test129280 0 320 640
  (interval_append test129280 0 160 320
  (interval_append test129280 0 80 160
  (interval_append test129280 0 32 80
  (interval_append test129280 0 16 32
  test129280_block_0
  test129280_block_1)
  (interval_append test129280 32 48 80
  test129280_block_2
  (interval_append test129280 48 64 80
  test129280_block_3
  test129280_block_4)))
  (interval_append test129280 80 112 160
  (interval_append test129280 80 96 112
  test129280_block_5
  test129280_block_6)
  (interval_append test129280 112 128 160
  test129280_block_7
  (interval_append test129280 128 144 160
  test129280_block_8
  test129280_block_9))))
  (interval_append test129280 160 240 320
  (interval_append test129280 160 192 240
  (interval_append test129280 160 176 192
  test129280_block_10
  test129280_block_11)
  (interval_append test129280 192 208 240
  test129280_block_12
  (interval_append test129280 208 224 240
  test129280_block_13
  test129280_block_14)))
  (interval_append test129280 240 272 320
  (interval_append test129280 240 256 272
  test129280_block_15
  test129280_block_16)
  (interval_append test129280 272 288 320
  test129280_block_17
  (interval_append test129280 288 304 320
  test129280_block_18
  test129280_block_19)))))
  (interval_append test129280 320 480 640
  (interval_append test129280 320 400 480
  (interval_append test129280 320 352 400
  (interval_append test129280 320 336 352
  test129280_block_20
  test129280_block_21)
  (interval_append test129280 352 368 400
  test129280_block_22
  (interval_append test129280 368 384 400
  test129280_block_23
  test129280_block_24)))
  (interval_append test129280 400 432 480
  (interval_append test129280 400 416 432
  test129280_block_25
  test129280_block_26)
  (interval_append test129280 432 448 480
  test129280_block_27
  (interval_append test129280 448 464 480
  test129280_block_28
  test129280_block_29))))
  (interval_append test129280 480 560 640
  (interval_append test129280 480 512 560
  (interval_append test129280 480 496 512
  test129280_block_30
  test129280_block_31)
  (interval_append test129280 512 528 560
  test129280_block_32
  (interval_append test129280 528 544 560
  test129280_block_33
  test129280_block_34)))
  (interval_append test129280 560 592 640
  (interval_append test129280 560 576 592
  test129280_block_35
  test129280_block_36)
  (interval_append test129280 592 608 640
  test129280_block_37
  (interval_append test129280 608 624 640
  test129280_block_38
  test129280_block_39))))))
cert_nodeInterval_3 129280 129920
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
cert_test_11 129920
cert_test_block_3 129920 0 0 16 16
cert_test_block_3 129920 1 16 32 16
cert_test_block_3 129920 2 32 48 16
cert_test_block_3 129920 3 48 64 16
cert_test_block_3 129920 4 64 80 16
cert_test_block_3 129920 5 80 96 16
cert_test_block_3 129920 6 96 112 16
cert_test_block_3 129920 7 112 128 16
cert_test_block_3 129920 8 128 144 16
cert_test_block_3 129920 9 144 160 16
cert_test_block_3 129920 10 160 176 16
cert_test_block_3 129920 11 176 192 16
cert_test_block_3 129920 12 192 208 16
cert_test_block_3 129920 13 208 224 16
cert_test_block_3 129920 14 224 240 16
cert_test_block_3 129920 15 240 256 16
cert_test_block_3 129920 16 256 272 16
cert_test_block_3 129920 17 272 288 16
cert_test_block_3 129920 18 288 304 16
cert_test_block_3 129920 19 304 320 16
cert_test_block_3 129920 20 320 336 16
cert_test_block_3 129920 21 336 352 16
cert_test_block_3 129920 22 352 368 16
cert_test_block_3 129920 23 368 384 16
cert_test_block_3 129920 24 384 400 16
cert_test_block_3 129920 25 400 416 16
cert_test_block_3 129920 26 416 432 16
cert_test_block_3 129920 27 432 448 16
cert_test_block_3 129920 28 448 464 16
cert_test_block_3 129920 29 464 480 16
cert_test_block_3 129920 30 480 496 16
cert_test_block_3 129920 31 496 512 16
cert_test_block_3 129920 32 512 528 16
cert_test_block_3 129920 33 528 544 16
cert_test_block_3 129920 34 544 560 16
cert_test_block_3 129920 35 560 576 16
cert_test_block_3 129920 36 576 592 16
cert_test_block_3 129920 37 592 608 16
cert_test_block_3 129920 38 608 624 16
cert_test_block_3 129920 39 624 640 16
theorem test129920_complete : Interval test129920 0 640 :=
  (interval_append test129920 0 320 640
  (interval_append test129920 0 160 320
  (interval_append test129920 0 80 160
  (interval_append test129920 0 32 80
  (interval_append test129920 0 16 32
  test129920_block_0
  test129920_block_1)
  (interval_append test129920 32 48 80
  test129920_block_2
  (interval_append test129920 48 64 80
  test129920_block_3
  test129920_block_4)))
  (interval_append test129920 80 112 160
  (interval_append test129920 80 96 112
  test129920_block_5
  test129920_block_6)
  (interval_append test129920 112 128 160
  test129920_block_7
  (interval_append test129920 128 144 160
  test129920_block_8
  test129920_block_9))))
  (interval_append test129920 160 240 320
  (interval_append test129920 160 192 240
  (interval_append test129920 160 176 192
  test129920_block_10
  test129920_block_11)
  (interval_append test129920 192 208 240
  test129920_block_12
  (interval_append test129920 208 224 240
  test129920_block_13
  test129920_block_14)))
  (interval_append test129920 240 272 320
  (interval_append test129920 240 256 272
  test129920_block_15
  test129920_block_16)
  (interval_append test129920 272 288 320
  test129920_block_17
  (interval_append test129920 288 304 320
  test129920_block_18
  test129920_block_19)))))
  (interval_append test129920 320 480 640
  (interval_append test129920 320 400 480
  (interval_append test129920 320 352 400
  (interval_append test129920 320 336 352
  test129920_block_20
  test129920_block_21)
  (interval_append test129920 352 368 400
  test129920_block_22
  (interval_append test129920 368 384 400
  test129920_block_23
  test129920_block_24)))
  (interval_append test129920 400 432 480
  (interval_append test129920 400 416 432
  test129920_block_25
  test129920_block_26)
  (interval_append test129920 432 448 480
  test129920_block_27
  (interval_append test129920 448 464 480
  test129920_block_28
  test129920_block_29))))
  (interval_append test129920 480 560 640
  (interval_append test129920 480 512 560
  (interval_append test129920 480 496 512
  test129920_block_30
  test129920_block_31)
  (interval_append test129920 512 528 560
  test129920_block_32
  (interval_append test129920 528 544 560
  test129920_block_33
  test129920_block_34)))
  (interval_append test129920 560 592 640
  (interval_append test129920 560 576 592
  test129920_block_35
  test129920_block_36)
  (interval_append test129920 592 608 640
  test129920_block_37
  (interval_append test129920 608 624 640
  test129920_block_38
  test129920_block_39))))))
cert_nodeInterval_3 129920 130560
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
cert_test_11 130560
cert_test_block_3 130560 0 0 16 16
cert_test_block_3 130560 1 16 32 16
cert_test_block_3 130560 2 32 48 16
cert_test_block_3 130560 3 48 64 16
cert_test_block_3 130560 4 64 80 16
cert_test_block_3 130560 5 80 96 16
cert_test_block_3 130560 6 96 112 16
cert_test_block_3 130560 7 112 128 16
cert_test_block_3 130560 8 128 144 16
cert_test_block_3 130560 9 144 160 16
cert_test_block_3 130560 10 160 176 16
cert_test_block_3 130560 11 176 192 16
cert_test_block_3 130560 12 192 208 16
cert_test_block_3 130560 13 208 224 16
cert_test_block_3 130560 14 224 240 16
cert_test_block_3 130560 15 240 256 16
cert_test_block_3 130560 16 256 272 16
cert_test_block_3 130560 17 272 288 16
cert_test_block_3 130560 18 288 304 16
cert_test_block_3 130560 19 304 320 16
cert_test_block_3 130560 20 320 336 16
cert_test_block_3 130560 21 336 352 16
cert_test_block_3 130560 22 352 368 16
cert_test_block_3 130560 23 368 384 16
cert_test_block_3 130560 24 384 400 16
cert_test_block_3 130560 25 400 416 16
cert_test_block_3 130560 26 416 432 16
cert_test_block_3 130560 27 432 448 16
cert_test_block_3 130560 28 448 464 16
cert_test_block_3 130560 29 464 480 16
cert_test_block_3 130560 30 480 496 16
cert_test_block_3 130560 31 496 512 16
cert_test_block_3 130560 32 512 528 16
cert_test_block_3 130560 33 528 544 16
cert_test_block_3 130560 34 544 560 16
cert_test_block_3 130560 35 560 576 16
cert_test_block_3 130560 36 576 592 16
cert_test_block_3 130560 37 592 608 16
cert_test_block_3 130560 38 608 624 16
cert_test_block_3 130560 39 624 640 16
theorem test130560_complete : Interval test130560 0 640 :=
  (interval_append test130560 0 320 640
  (interval_append test130560 0 160 320
  (interval_append test130560 0 80 160
  (interval_append test130560 0 32 80
  (interval_append test130560 0 16 32
  test130560_block_0
  test130560_block_1)
  (interval_append test130560 32 48 80
  test130560_block_2
  (interval_append test130560 48 64 80
  test130560_block_3
  test130560_block_4)))
  (interval_append test130560 80 112 160
  (interval_append test130560 80 96 112
  test130560_block_5
  test130560_block_6)
  (interval_append test130560 112 128 160
  test130560_block_7
  (interval_append test130560 128 144 160
  test130560_block_8
  test130560_block_9))))
  (interval_append test130560 160 240 320
  (interval_append test130560 160 192 240
  (interval_append test130560 160 176 192
  test130560_block_10
  test130560_block_11)
  (interval_append test130560 192 208 240
  test130560_block_12
  (interval_append test130560 208 224 240
  test130560_block_13
  test130560_block_14)))
  (interval_append test130560 240 272 320
  (interval_append test130560 240 256 272
  test130560_block_15
  test130560_block_16)
  (interval_append test130560 272 288 320
  test130560_block_17
  (interval_append test130560 288 304 320
  test130560_block_18
  test130560_block_19)))))
  (interval_append test130560 320 480 640
  (interval_append test130560 320 400 480
  (interval_append test130560 320 352 400
  (interval_append test130560 320 336 352
  test130560_block_20
  test130560_block_21)
  (interval_append test130560 352 368 400
  test130560_block_22
  (interval_append test130560 368 384 400
  test130560_block_23
  test130560_block_24)))
  (interval_append test130560 400 432 480
  (interval_append test130560 400 416 432
  test130560_block_25
  test130560_block_26)
  (interval_append test130560 432 448 480
  test130560_block_27
  (interval_append test130560 448 464 480
  test130560_block_28
  test130560_block_29))))
  (interval_append test130560 480 560 640
  (interval_append test130560 480 512 560
  (interval_append test130560 480 496 512
  test130560_block_30
  test130560_block_31)
  (interval_append test130560 512 528 560
  test130560_block_32
  (interval_append test130560 528 544 560
  test130560_block_33
  test130560_block_34)))
  (interval_append test130560 560 592 640
  (interval_append test130560 560 576 592
  test130560_block_35
  test130560_block_36)
  (interval_append test130560 592 608 640
  test130560_block_37
  (interval_append test130560 608 624 640
  test130560_block_38
  test130560_block_39))))))
cert_nodeInterval_3 130560 131200
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
cert_test_11 131200
cert_test_block_3 131200 0 0 16 16
cert_test_block_3 131200 1 16 32 16
cert_test_block_3 131200 2 32 48 16
cert_test_block_3 131200 3 48 64 16
cert_test_block_3 131200 4 64 80 16
cert_test_block_3 131200 5 80 96 16
cert_test_block_3 131200 6 96 112 16
cert_test_block_3 131200 7 112 128 16
cert_test_block_3 131200 8 128 144 16
cert_test_block_3 131200 9 144 160 16
cert_test_block_3 131200 10 160 176 16
cert_test_block_3 131200 11 176 192 16
cert_test_block_3 131200 12 192 208 16
cert_test_block_3 131200 13 208 224 16
cert_test_block_3 131200 14 224 240 16
cert_test_block_3 131200 15 240 256 16
cert_test_block_3 131200 16 256 272 16
cert_test_block_3 131200 17 272 288 16
cert_test_block_3 131200 18 288 304 16
cert_test_block_3 131200 19 304 320 16
cert_test_block_3 131200 20 320 336 16
cert_test_block_3 131200 21 336 352 16
cert_test_block_3 131200 22 352 368 16
cert_test_block_3 131200 23 368 384 16
cert_test_block_3 131200 24 384 400 16
cert_test_block_3 131200 25 400 416 16
cert_test_block_3 131200 26 416 432 16
cert_test_block_3 131200 27 432 448 16
cert_test_block_3 131200 28 448 464 16
cert_test_block_3 131200 29 464 480 16
cert_test_block_3 131200 30 480 496 16
cert_test_block_3 131200 31 496 512 16
cert_test_block_3 131200 32 512 528 16
cert_test_block_3 131200 33 528 544 16
cert_test_block_3 131200 34 544 560 16
cert_test_block_3 131200 35 560 576 16
cert_test_block_3 131200 36 576 592 16
cert_test_block_3 131200 37 592 608 16
cert_test_block_3 131200 38 608 624 16
cert_test_block_3 131200 39 624 640 16
theorem test131200_complete : Interval test131200 0 640 :=
  (interval_append test131200 0 320 640
  (interval_append test131200 0 160 320
  (interval_append test131200 0 80 160
  (interval_append test131200 0 32 80
  (interval_append test131200 0 16 32
  test131200_block_0
  test131200_block_1)
  (interval_append test131200 32 48 80
  test131200_block_2
  (interval_append test131200 48 64 80
  test131200_block_3
  test131200_block_4)))
  (interval_append test131200 80 112 160
  (interval_append test131200 80 96 112
  test131200_block_5
  test131200_block_6)
  (interval_append test131200 112 128 160
  test131200_block_7
  (interval_append test131200 128 144 160
  test131200_block_8
  test131200_block_9))))
  (interval_append test131200 160 240 320
  (interval_append test131200 160 192 240
  (interval_append test131200 160 176 192
  test131200_block_10
  test131200_block_11)
  (interval_append test131200 192 208 240
  test131200_block_12
  (interval_append test131200 208 224 240
  test131200_block_13
  test131200_block_14)))
  (interval_append test131200 240 272 320
  (interval_append test131200 240 256 272
  test131200_block_15
  test131200_block_16)
  (interval_append test131200 272 288 320
  test131200_block_17
  (interval_append test131200 288 304 320
  test131200_block_18
  test131200_block_19)))))
  (interval_append test131200 320 480 640
  (interval_append test131200 320 400 480
  (interval_append test131200 320 352 400
  (interval_append test131200 320 336 352
  test131200_block_20
  test131200_block_21)
  (interval_append test131200 352 368 400
  test131200_block_22
  (interval_append test131200 368 384 400
  test131200_block_23
  test131200_block_24)))
  (interval_append test131200 400 432 480
  (interval_append test131200 400 416 432
  test131200_block_25
  test131200_block_26)
  (interval_append test131200 432 448 480
  test131200_block_27
  (interval_append test131200 448 464 480
  test131200_block_28
  test131200_block_29))))
  (interval_append test131200 480 560 640
  (interval_append test131200 480 512 560
  (interval_append test131200 480 496 512
  test131200_block_30
  test131200_block_31)
  (interval_append test131200 512 528 560
  test131200_block_32
  (interval_append test131200 528 544 560
  test131200_block_33
  test131200_block_34)))
  (interval_append test131200 560 592 640
  (interval_append test131200 560 576 592
  test131200_block_35
  test131200_block_36)
  (interval_append test131200 592 608 640
  test131200_block_37
  (interval_append test131200 608 624 640
  test131200_block_38
  test131200_block_39))))))
cert_nodeInterval_3 131200 131840
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
cert_test_11 131840
cert_test_block_3 131840 0 0 16 16
cert_test_block_3 131840 1 16 32 16
cert_test_block_3 131840 2 32 48 16
cert_test_block_3 131840 3 48 64 16
cert_test_block_3 131840 4 64 80 16
cert_test_block_3 131840 5 80 96 16
cert_test_block_3 131840 6 96 112 16
cert_test_block_3 131840 7 112 128 16
cert_test_block_3 131840 8 128 144 16
cert_test_block_3 131840 9 144 160 16
cert_test_block_3 131840 10 160 176 16
cert_test_block_3 131840 11 176 192 16
cert_test_block_3 131840 12 192 208 16
cert_test_block_3 131840 13 208 224 16
cert_test_block_3 131840 14 224 240 16
cert_test_block_3 131840 15 240 256 16
cert_test_block_3 131840 16 256 272 16
cert_test_block_3 131840 17 272 288 16
cert_test_block_3 131840 18 288 304 16
cert_test_block_3 131840 19 304 320 16
cert_test_block_3 131840 20 320 336 16
cert_test_block_3 131840 21 336 352 16
cert_test_block_3 131840 22 352 368 16
cert_test_block_3 131840 23 368 384 16
cert_test_block_3 131840 24 384 400 16
cert_test_block_3 131840 25 400 416 16
cert_test_block_3 131840 26 416 432 16
cert_test_block_3 131840 27 432 448 16
cert_test_block_3 131840 28 448 464 16
cert_test_block_3 131840 29 464 480 16
cert_test_block_3 131840 30 480 496 16
cert_test_block_3 131840 31 496 512 16
cert_test_block_3 131840 32 512 528 16
cert_test_block_3 131840 33 528 544 16
cert_test_block_3 131840 34 544 560 16
cert_test_block_3 131840 35 560 576 16
cert_test_block_3 131840 36 576 592 16
cert_test_block_3 131840 37 592 608 16
cert_test_block_3 131840 38 608 624 16
cert_test_block_3 131840 39 624 640 16
theorem test131840_complete : Interval test131840 0 640 :=
  (interval_append test131840 0 320 640
  (interval_append test131840 0 160 320
  (interval_append test131840 0 80 160
  (interval_append test131840 0 32 80
  (interval_append test131840 0 16 32
  test131840_block_0
  test131840_block_1)
  (interval_append test131840 32 48 80
  test131840_block_2
  (interval_append test131840 48 64 80
  test131840_block_3
  test131840_block_4)))
  (interval_append test131840 80 112 160
  (interval_append test131840 80 96 112
  test131840_block_5
  test131840_block_6)
  (interval_append test131840 112 128 160
  test131840_block_7
  (interval_append test131840 128 144 160
  test131840_block_8
  test131840_block_9))))
  (interval_append test131840 160 240 320
  (interval_append test131840 160 192 240
  (interval_append test131840 160 176 192
  test131840_block_10
  test131840_block_11)
  (interval_append test131840 192 208 240
  test131840_block_12
  (interval_append test131840 208 224 240
  test131840_block_13
  test131840_block_14)))
  (interval_append test131840 240 272 320
  (interval_append test131840 240 256 272
  test131840_block_15
  test131840_block_16)
  (interval_append test131840 272 288 320
  test131840_block_17
  (interval_append test131840 288 304 320
  test131840_block_18
  test131840_block_19)))))
  (interval_append test131840 320 480 640
  (interval_append test131840 320 400 480
  (interval_append test131840 320 352 400
  (interval_append test131840 320 336 352
  test131840_block_20
  test131840_block_21)
  (interval_append test131840 352 368 400
  test131840_block_22
  (interval_append test131840 368 384 400
  test131840_block_23
  test131840_block_24)))
  (interval_append test131840 400 432 480
  (interval_append test131840 400 416 432
  test131840_block_25
  test131840_block_26)
  (interval_append test131840 432 448 480
  test131840_block_27
  (interval_append test131840 448 464 480
  test131840_block_28
  test131840_block_29))))
  (interval_append test131840 480 560 640
  (interval_append test131840 480 512 560
  (interval_append test131840 480 496 512
  test131840_block_30
  test131840_block_31)
  (interval_append test131840 512 528 560
  test131840_block_32
  (interval_append test131840 528 544 560
  test131840_block_33
  test131840_block_34)))
  (interval_append test131840 560 592 640
  (interval_append test131840 560 576 592
  test131840_block_35
  test131840_block_36)
  (interval_append test131840 592 608 640
  test131840_block_37
  (interval_append test131840 608 624 640
  test131840_block_38
  test131840_block_39))))))
cert_nodeInterval_3 131840 132480
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
cert_test_11 132480
cert_test_block_3 132480 0 0 16 16
cert_test_block_3 132480 1 16 32 16
cert_test_block_3 132480 2 32 48 16
cert_test_block_3 132480 3 48 64 16
cert_test_block_3 132480 4 64 80 16
cert_test_block_3 132480 5 80 96 16
cert_test_block_3 132480 6 96 112 16
cert_test_block_3 132480 7 112 128 16
cert_test_block_3 132480 8 128 144 16
cert_test_block_3 132480 9 144 160 16
cert_test_block_3 132480 10 160 176 16
cert_test_block_3 132480 11 176 192 16
cert_test_block_3 132480 12 192 208 16
cert_test_block_3 132480 13 208 224 16
cert_test_block_3 132480 14 224 240 16
cert_test_block_3 132480 15 240 256 16
cert_test_block_3 132480 16 256 272 16
cert_test_block_3 132480 17 272 288 16
cert_test_block_3 132480 18 288 304 16
cert_test_block_3 132480 19 304 320 16
cert_test_block_3 132480 20 320 336 16
cert_test_block_3 132480 21 336 352 16
cert_test_block_3 132480 22 352 368 16
cert_test_block_3 132480 23 368 384 16
cert_test_block_3 132480 24 384 400 16
cert_test_block_3 132480 25 400 416 16
cert_test_block_3 132480 26 416 432 16
cert_test_block_3 132480 27 432 448 16
cert_test_block_3 132480 28 448 464 16
cert_test_block_3 132480 29 464 480 16
cert_test_block_3 132480 30 480 496 16
cert_test_block_3 132480 31 496 512 16
cert_test_block_3 132480 32 512 528 16
cert_test_block_3 132480 33 528 544 16
cert_test_block_3 132480 34 544 560 16
cert_test_block_3 132480 35 560 576 16
cert_test_block_3 132480 36 576 592 16
cert_test_block_3 132480 37 592 608 16
cert_test_block_3 132480 38 608 624 16
cert_test_block_3 132480 39 624 640 16
theorem test132480_complete : Interval test132480 0 640 :=
  (interval_append test132480 0 320 640
  (interval_append test132480 0 160 320
  (interval_append test132480 0 80 160
  (interval_append test132480 0 32 80
  (interval_append test132480 0 16 32
  test132480_block_0
  test132480_block_1)
  (interval_append test132480 32 48 80
  test132480_block_2
  (interval_append test132480 48 64 80
  test132480_block_3
  test132480_block_4)))
  (interval_append test132480 80 112 160
  (interval_append test132480 80 96 112
  test132480_block_5
  test132480_block_6)
  (interval_append test132480 112 128 160
  test132480_block_7
  (interval_append test132480 128 144 160
  test132480_block_8
  test132480_block_9))))
  (interval_append test132480 160 240 320
  (interval_append test132480 160 192 240
  (interval_append test132480 160 176 192
  test132480_block_10
  test132480_block_11)
  (interval_append test132480 192 208 240
  test132480_block_12
  (interval_append test132480 208 224 240
  test132480_block_13
  test132480_block_14)))
  (interval_append test132480 240 272 320
  (interval_append test132480 240 256 272
  test132480_block_15
  test132480_block_16)
  (interval_append test132480 272 288 320
  test132480_block_17
  (interval_append test132480 288 304 320
  test132480_block_18
  test132480_block_19)))))
  (interval_append test132480 320 480 640
  (interval_append test132480 320 400 480
  (interval_append test132480 320 352 400
  (interval_append test132480 320 336 352
  test132480_block_20
  test132480_block_21)
  (interval_append test132480 352 368 400
  test132480_block_22
  (interval_append test132480 368 384 400
  test132480_block_23
  test132480_block_24)))
  (interval_append test132480 400 432 480
  (interval_append test132480 400 416 432
  test132480_block_25
  test132480_block_26)
  (interval_append test132480 432 448 480
  test132480_block_27
  (interval_append test132480 448 464 480
  test132480_block_28
  test132480_block_29))))
  (interval_append test132480 480 560 640
  (interval_append test132480 480 512 560
  (interval_append test132480 480 496 512
  test132480_block_30
  test132480_block_31)
  (interval_append test132480 512 528 560
  test132480_block_32
  (interval_append test132480 528 544 560
  test132480_block_33
  test132480_block_34)))
  (interval_append test132480 560 592 640
  (interval_append test132480 560 576 592
  test132480_block_35
  test132480_block_36)
  (interval_append test132480 592 608 640
  test132480_block_37
  (interval_append test132480 608 624 640
  test132480_block_38
  test132480_block_39))))))
cert_nodeInterval_3 132480 133120
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
cert_test_11 133120
cert_test_block_3 133120 0 0 16 16
cert_test_block_3 133120 1 16 32 16
cert_test_block_3 133120 2 32 48 16
cert_test_block_3 133120 3 48 64 16
cert_test_block_3 133120 4 64 80 16
cert_test_block_3 133120 5 80 96 16
cert_test_block_3 133120 6 96 112 16
cert_test_block_3 133120 7 112 128 16
cert_test_block_3 133120 8 128 144 16
cert_test_block_3 133120 9 144 160 16
cert_test_block_3 133120 10 160 176 16
cert_test_block_3 133120 11 176 192 16
cert_test_block_3 133120 12 192 208 16
cert_test_block_3 133120 13 208 224 16
cert_test_block_3 133120 14 224 240 16
cert_test_block_3 133120 15 240 256 16
cert_test_block_3 133120 16 256 272 16
cert_test_block_3 133120 17 272 288 16
cert_test_block_3 133120 18 288 304 16
cert_test_block_3 133120 19 304 320 16
cert_test_block_3 133120 20 320 336 16
cert_test_block_3 133120 21 336 352 16
cert_test_block_3 133120 22 352 368 16
cert_test_block_3 133120 23 368 384 16
cert_test_block_3 133120 24 384 400 16
cert_test_block_3 133120 25 400 416 16
cert_test_block_3 133120 26 416 432 16
cert_test_block_3 133120 27 432 448 16
cert_test_block_3 133120 28 448 464 16
cert_test_block_3 133120 29 464 480 16
cert_test_block_3 133120 30 480 496 16
cert_test_block_3 133120 31 496 512 16
cert_test_block_3 133120 32 512 528 16
cert_test_block_3 133120 33 528 544 16
cert_test_block_3 133120 34 544 560 16
cert_test_block_3 133120 35 560 576 16
cert_test_block_3 133120 36 576 592 16
cert_test_block_3 133120 37 592 608 16
cert_test_block_3 133120 38 608 624 16
cert_test_block_3 133120 39 624 640 16
theorem test133120_complete : Interval test133120 0 640 :=
  (interval_append test133120 0 320 640
  (interval_append test133120 0 160 320
  (interval_append test133120 0 80 160
  (interval_append test133120 0 32 80
  (interval_append test133120 0 16 32
  test133120_block_0
  test133120_block_1)
  (interval_append test133120 32 48 80
  test133120_block_2
  (interval_append test133120 48 64 80
  test133120_block_3
  test133120_block_4)))
  (interval_append test133120 80 112 160
  (interval_append test133120 80 96 112
  test133120_block_5
  test133120_block_6)
  (interval_append test133120 112 128 160
  test133120_block_7
  (interval_append test133120 128 144 160
  test133120_block_8
  test133120_block_9))))
  (interval_append test133120 160 240 320
  (interval_append test133120 160 192 240
  (interval_append test133120 160 176 192
  test133120_block_10
  test133120_block_11)
  (interval_append test133120 192 208 240
  test133120_block_12
  (interval_append test133120 208 224 240
  test133120_block_13
  test133120_block_14)))
  (interval_append test133120 240 272 320
  (interval_append test133120 240 256 272
  test133120_block_15
  test133120_block_16)
  (interval_append test133120 272 288 320
  test133120_block_17
  (interval_append test133120 288 304 320
  test133120_block_18
  test133120_block_19)))))
  (interval_append test133120 320 480 640
  (interval_append test133120 320 400 480
  (interval_append test133120 320 352 400
  (interval_append test133120 320 336 352
  test133120_block_20
  test133120_block_21)
  (interval_append test133120 352 368 400
  test133120_block_22
  (interval_append test133120 368 384 400
  test133120_block_23
  test133120_block_24)))
  (interval_append test133120 400 432 480
  (interval_append test133120 400 416 432
  test133120_block_25
  test133120_block_26)
  (interval_append test133120 432 448 480
  test133120_block_27
  (interval_append test133120 448 464 480
  test133120_block_28
  test133120_block_29))))
  (interval_append test133120 480 560 640
  (interval_append test133120 480 512 560
  (interval_append test133120 480 496 512
  test133120_block_30
  test133120_block_31)
  (interval_append test133120 512 528 560
  test133120_block_32
  (interval_append test133120 528 544 560
  test133120_block_33
  test133120_block_34)))
  (interval_append test133120 560 592 640
  (interval_append test133120 560 576 592
  test133120_block_35
  test133120_block_36)
  (interval_append test133120 592 608 640
  test133120_block_37
  (interval_append test133120 608 624 640
  test133120_block_38
  test133120_block_39))))))
cert_nodeInterval_3 133120 133760
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
cert_test_11 133760
cert_test_block_3 133760 0 0 16 16
cert_test_block_3 133760 1 16 32 16
cert_test_block_3 133760 2 32 48 16
cert_test_block_3 133760 3 48 64 16
cert_test_block_3 133760 4 64 80 16
cert_test_block_3 133760 5 80 96 16
cert_test_block_3 133760 6 96 112 16
cert_test_block_3 133760 7 112 128 16
cert_test_block_3 133760 8 128 144 16
cert_test_block_3 133760 9 144 160 16
cert_test_block_3 133760 10 160 176 16
cert_test_block_3 133760 11 176 192 16
cert_test_block_3 133760 12 192 208 16
cert_test_block_3 133760 13 208 224 16
cert_test_block_3 133760 14 224 240 16
cert_test_block_3 133760 15 240 256 16
cert_test_block_3 133760 16 256 272 16
cert_test_block_3 133760 17 272 288 16
cert_test_block_3 133760 18 288 304 16
cert_test_block_3 133760 19 304 320 16
cert_test_block_3 133760 20 320 336 16
cert_test_block_3 133760 21 336 352 16
cert_test_block_3 133760 22 352 368 16
cert_test_block_3 133760 23 368 384 16
cert_test_block_3 133760 24 384 400 16
cert_test_block_3 133760 25 400 416 16
cert_test_block_3 133760 26 416 432 16
cert_test_block_3 133760 27 432 448 16
cert_test_block_3 133760 28 448 464 16
cert_test_block_3 133760 29 464 480 16
cert_test_block_3 133760 30 480 496 16
cert_test_block_3 133760 31 496 512 16
cert_test_block_3 133760 32 512 528 16
cert_test_block_3 133760 33 528 544 16
cert_test_block_3 133760 34 544 560 16
cert_test_block_3 133760 35 560 576 16
cert_test_block_3 133760 36 576 592 16
cert_test_block_3 133760 37 592 608 16
cert_test_block_3 133760 38 608 624 16
cert_test_block_3 133760 39 624 640 16
theorem test133760_complete : Interval test133760 0 640 :=
  (interval_append test133760 0 320 640
  (interval_append test133760 0 160 320
  (interval_append test133760 0 80 160
  (interval_append test133760 0 32 80
  (interval_append test133760 0 16 32
  test133760_block_0
  test133760_block_1)
  (interval_append test133760 32 48 80
  test133760_block_2
  (interval_append test133760 48 64 80
  test133760_block_3
  test133760_block_4)))
  (interval_append test133760 80 112 160
  (interval_append test133760 80 96 112
  test133760_block_5
  test133760_block_6)
  (interval_append test133760 112 128 160
  test133760_block_7
  (interval_append test133760 128 144 160
  test133760_block_8
  test133760_block_9))))
  (interval_append test133760 160 240 320
  (interval_append test133760 160 192 240
  (interval_append test133760 160 176 192
  test133760_block_10
  test133760_block_11)
  (interval_append test133760 192 208 240
  test133760_block_12
  (interval_append test133760 208 224 240
  test133760_block_13
  test133760_block_14)))
  (interval_append test133760 240 272 320
  (interval_append test133760 240 256 272
  test133760_block_15
  test133760_block_16)
  (interval_append test133760 272 288 320
  test133760_block_17
  (interval_append test133760 288 304 320
  test133760_block_18
  test133760_block_19)))))
  (interval_append test133760 320 480 640
  (interval_append test133760 320 400 480
  (interval_append test133760 320 352 400
  (interval_append test133760 320 336 352
  test133760_block_20
  test133760_block_21)
  (interval_append test133760 352 368 400
  test133760_block_22
  (interval_append test133760 368 384 400
  test133760_block_23
  test133760_block_24)))
  (interval_append test133760 400 432 480
  (interval_append test133760 400 416 432
  test133760_block_25
  test133760_block_26)
  (interval_append test133760 432 448 480
  test133760_block_27
  (interval_append test133760 448 464 480
  test133760_block_28
  test133760_block_29))))
  (interval_append test133760 480 560 640
  (interval_append test133760 480 512 560
  (interval_append test133760 480 496 512
  test133760_block_30
  test133760_block_31)
  (interval_append test133760 512 528 560
  test133760_block_32
  (interval_append test133760 528 544 560
  test133760_block_33
  test133760_block_34)))
  (interval_append test133760 560 592 640
  (interval_append test133760 560 576 592
  test133760_block_35
  test133760_block_36)
  (interval_append test133760 592 608 640
  test133760_block_37
  (interval_append test133760 608 624 640
  test133760_block_38
  test133760_block_39))))))
cert_nodeInterval_3 133760 134400
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
cert_test_11 134400
cert_test_block_3 134400 0 0 16 16
cert_test_block_3 134400 1 16 32 16
cert_test_block_3 134400 2 32 48 16
cert_test_block_3 134400 3 48 64 16
cert_test_block_3 134400 4 64 80 16
cert_test_block_3 134400 5 80 96 16
cert_test_block_3 134400 6 96 112 16
cert_test_block_3 134400 7 112 128 16
cert_test_block_3 134400 8 128 144 16
cert_test_block_3 134400 9 144 160 16
cert_test_block_3 134400 10 160 176 16
cert_test_block_3 134400 11 176 192 16
cert_test_block_3 134400 12 192 208 16
cert_test_block_3 134400 13 208 224 16
cert_test_block_3 134400 14 224 240 16
cert_test_block_3 134400 15 240 256 16
cert_test_block_3 134400 16 256 272 16
cert_test_block_3 134400 17 272 288 16
cert_test_block_3 134400 18 288 304 16
cert_test_block_3 134400 19 304 320 16
cert_test_block_3 134400 20 320 336 16
cert_test_block_3 134400 21 336 352 16
cert_test_block_3 134400 22 352 368 16
cert_test_block_3 134400 23 368 384 16
cert_test_block_3 134400 24 384 400 16
cert_test_block_3 134400 25 400 416 16
cert_test_block_3 134400 26 416 432 16
cert_test_block_3 134400 27 432 448 16
cert_test_block_3 134400 28 448 464 16
cert_test_block_3 134400 29 464 480 16
cert_test_block_3 134400 30 480 496 16
cert_test_block_3 134400 31 496 512 16
cert_test_block_3 134400 32 512 528 16
cert_test_block_3 134400 33 528 544 16
cert_test_block_3 134400 34 544 560 16
cert_test_block_3 134400 35 560 576 16
cert_test_block_3 134400 36 576 592 16
cert_test_block_3 134400 37 592 608 16
cert_test_block_3 134400 38 608 624 16
cert_test_block_3 134400 39 624 640 16
theorem test134400_complete : Interval test134400 0 640 :=
  (interval_append test134400 0 320 640
  (interval_append test134400 0 160 320
  (interval_append test134400 0 80 160
  (interval_append test134400 0 32 80
  (interval_append test134400 0 16 32
  test134400_block_0
  test134400_block_1)
  (interval_append test134400 32 48 80
  test134400_block_2
  (interval_append test134400 48 64 80
  test134400_block_3
  test134400_block_4)))
  (interval_append test134400 80 112 160
  (interval_append test134400 80 96 112
  test134400_block_5
  test134400_block_6)
  (interval_append test134400 112 128 160
  test134400_block_7
  (interval_append test134400 128 144 160
  test134400_block_8
  test134400_block_9))))
  (interval_append test134400 160 240 320
  (interval_append test134400 160 192 240
  (interval_append test134400 160 176 192
  test134400_block_10
  test134400_block_11)
  (interval_append test134400 192 208 240
  test134400_block_12
  (interval_append test134400 208 224 240
  test134400_block_13
  test134400_block_14)))
  (interval_append test134400 240 272 320
  (interval_append test134400 240 256 272
  test134400_block_15
  test134400_block_16)
  (interval_append test134400 272 288 320
  test134400_block_17
  (interval_append test134400 288 304 320
  test134400_block_18
  test134400_block_19)))))
  (interval_append test134400 320 480 640
  (interval_append test134400 320 400 480
  (interval_append test134400 320 352 400
  (interval_append test134400 320 336 352
  test134400_block_20
  test134400_block_21)
  (interval_append test134400 352 368 400
  test134400_block_22
  (interval_append test134400 368 384 400
  test134400_block_23
  test134400_block_24)))
  (interval_append test134400 400 432 480
  (interval_append test134400 400 416 432
  test134400_block_25
  test134400_block_26)
  (interval_append test134400 432 448 480
  test134400_block_27
  (interval_append test134400 448 464 480
  test134400_block_28
  test134400_block_29))))
  (interval_append test134400 480 560 640
  (interval_append test134400 480 512 560
  (interval_append test134400 480 496 512
  test134400_block_30
  test134400_block_31)
  (interval_append test134400 512 528 560
  test134400_block_32
  (interval_append test134400 528 544 560
  test134400_block_33
  test134400_block_34)))
  (interval_append test134400 560 592 640
  (interval_append test134400 560 576 592
  test134400_block_35
  test134400_block_36)
  (interval_append test134400 592 608 640
  test134400_block_37
  (interval_append test134400 608 624 640
  test134400_block_38
  test134400_block_39))))))
cert_nodeInterval_3 134400 135040
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
cert_test_11 135040
cert_test_block_3 135040 0 0 16 16
cert_test_block_3 135040 1 16 32 16
cert_test_block_3 135040 2 32 48 16
cert_test_block_3 135040 3 48 64 16
cert_test_block_3 135040 4 64 80 16
cert_test_block_3 135040 5 80 96 16
cert_test_block_3 135040 6 96 112 16
cert_test_block_3 135040 7 112 128 16
cert_test_block_3 135040 8 128 144 16
cert_test_block_3 135040 9 144 160 16
cert_test_block_3 135040 10 160 176 16
cert_test_block_3 135040 11 176 192 16
cert_test_block_3 135040 12 192 208 16
cert_test_block_3 135040 13 208 224 16
cert_test_block_3 135040 14 224 240 16
cert_test_block_3 135040 15 240 256 16
cert_test_block_3 135040 16 256 272 16
cert_test_block_3 135040 17 272 288 16
cert_test_block_3 135040 18 288 304 16
cert_test_block_3 135040 19 304 320 16
cert_test_block_3 135040 20 320 336 16
cert_test_block_3 135040 21 336 352 16
cert_test_block_3 135040 22 352 368 16
cert_test_block_3 135040 23 368 384 16
cert_test_block_3 135040 24 384 400 16
cert_test_block_3 135040 25 400 416 16
cert_test_block_3 135040 26 416 432 16
cert_test_block_3 135040 27 432 448 16
cert_test_block_3 135040 28 448 464 16
cert_test_block_3 135040 29 464 480 16
cert_test_block_3 135040 30 480 496 16
cert_test_block_3 135040 31 496 512 16
cert_test_block_3 135040 32 512 528 16
cert_test_block_3 135040 33 528 544 16
cert_test_block_3 135040 34 544 560 16
cert_test_block_3 135040 35 560 576 16
cert_test_block_3 135040 36 576 592 16
cert_test_block_3 135040 37 592 608 16
cert_test_block_3 135040 38 608 624 16
cert_test_block_3 135040 39 624 640 16
theorem test135040_complete : Interval test135040 0 640 :=
  (interval_append test135040 0 320 640
  (interval_append test135040 0 160 320
  (interval_append test135040 0 80 160
  (interval_append test135040 0 32 80
  (interval_append test135040 0 16 32
  test135040_block_0
  test135040_block_1)
  (interval_append test135040 32 48 80
  test135040_block_2
  (interval_append test135040 48 64 80
  test135040_block_3
  test135040_block_4)))
  (interval_append test135040 80 112 160
  (interval_append test135040 80 96 112
  test135040_block_5
  test135040_block_6)
  (interval_append test135040 112 128 160
  test135040_block_7
  (interval_append test135040 128 144 160
  test135040_block_8
  test135040_block_9))))
  (interval_append test135040 160 240 320
  (interval_append test135040 160 192 240
  (interval_append test135040 160 176 192
  test135040_block_10
  test135040_block_11)
  (interval_append test135040 192 208 240
  test135040_block_12
  (interval_append test135040 208 224 240
  test135040_block_13
  test135040_block_14)))
  (interval_append test135040 240 272 320
  (interval_append test135040 240 256 272
  test135040_block_15
  test135040_block_16)
  (interval_append test135040 272 288 320
  test135040_block_17
  (interval_append test135040 288 304 320
  test135040_block_18
  test135040_block_19)))))
  (interval_append test135040 320 480 640
  (interval_append test135040 320 400 480
  (interval_append test135040 320 352 400
  (interval_append test135040 320 336 352
  test135040_block_20
  test135040_block_21)
  (interval_append test135040 352 368 400
  test135040_block_22
  (interval_append test135040 368 384 400
  test135040_block_23
  test135040_block_24)))
  (interval_append test135040 400 432 480
  (interval_append test135040 400 416 432
  test135040_block_25
  test135040_block_26)
  (interval_append test135040 432 448 480
  test135040_block_27
  (interval_append test135040 448 464 480
  test135040_block_28
  test135040_block_29))))
  (interval_append test135040 480 560 640
  (interval_append test135040 480 512 560
  (interval_append test135040 480 496 512
  test135040_block_30
  test135040_block_31)
  (interval_append test135040 512 528 560
  test135040_block_32
  (interval_append test135040 528 544 560
  test135040_block_33
  test135040_block_34)))
  (interval_append test135040 560 592 640
  (interval_append test135040 560 576 592
  test135040_block_35
  test135040_block_36)
  (interval_append test135040 592 608 640
  test135040_block_37
  (interval_append test135040 608 624 640
  test135040_block_38
  test135040_block_39))))))
cert_nodeInterval_3 135040 135680
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
cert_test_11 135680
cert_test_block_3 135680 0 0 16 16
cert_test_block_3 135680 1 16 32 16
cert_test_block_3 135680 2 32 48 16
cert_test_block_3 135680 3 48 64 16
cert_test_block_3 135680 4 64 80 16
cert_test_block_3 135680 5 80 96 16
cert_test_block_3 135680 6 96 112 16
cert_test_block_3 135680 7 112 128 16
cert_test_block_3 135680 8 128 144 16
cert_test_block_3 135680 9 144 160 16
cert_test_block_3 135680 10 160 176 16
cert_test_block_3 135680 11 176 192 16
cert_test_block_3 135680 12 192 208 16
cert_test_block_3 135680 13 208 224 16
cert_test_block_3 135680 14 224 240 16
cert_test_block_3 135680 15 240 256 16
cert_test_block_3 135680 16 256 272 16
cert_test_block_3 135680 17 272 288 16
cert_test_block_3 135680 18 288 304 16
cert_test_block_3 135680 19 304 320 16
cert_test_block_3 135680 20 320 336 16
cert_test_block_3 135680 21 336 352 16
cert_test_block_3 135680 22 352 368 16
cert_test_block_3 135680 23 368 384 16
cert_test_block_3 135680 24 384 400 16
cert_test_block_3 135680 25 400 416 16
cert_test_block_3 135680 26 416 432 16
cert_test_block_3 135680 27 432 448 16
cert_test_block_3 135680 28 448 464 16
cert_test_block_3 135680 29 464 480 16
cert_test_block_3 135680 30 480 496 16
cert_test_block_3 135680 31 496 512 16
cert_test_block_3 135680 32 512 528 16
cert_test_block_3 135680 33 528 544 16
cert_test_block_3 135680 34 544 560 16
cert_test_block_3 135680 35 560 576 16
cert_test_block_3 135680 36 576 592 16
cert_test_block_3 135680 37 592 608 16
cert_test_block_3 135680 38 608 624 16
cert_test_block_3 135680 39 624 640 16
theorem test135680_complete : Interval test135680 0 640 :=
  (interval_append test135680 0 320 640
  (interval_append test135680 0 160 320
  (interval_append test135680 0 80 160
  (interval_append test135680 0 32 80
  (interval_append test135680 0 16 32
  test135680_block_0
  test135680_block_1)
  (interval_append test135680 32 48 80
  test135680_block_2
  (interval_append test135680 48 64 80
  test135680_block_3
  test135680_block_4)))
  (interval_append test135680 80 112 160
  (interval_append test135680 80 96 112
  test135680_block_5
  test135680_block_6)
  (interval_append test135680 112 128 160
  test135680_block_7
  (interval_append test135680 128 144 160
  test135680_block_8
  test135680_block_9))))
  (interval_append test135680 160 240 320
  (interval_append test135680 160 192 240
  (interval_append test135680 160 176 192
  test135680_block_10
  test135680_block_11)
  (interval_append test135680 192 208 240
  test135680_block_12
  (interval_append test135680 208 224 240
  test135680_block_13
  test135680_block_14)))
  (interval_append test135680 240 272 320
  (interval_append test135680 240 256 272
  test135680_block_15
  test135680_block_16)
  (interval_append test135680 272 288 320
  test135680_block_17
  (interval_append test135680 288 304 320
  test135680_block_18
  test135680_block_19)))))
  (interval_append test135680 320 480 640
  (interval_append test135680 320 400 480
  (interval_append test135680 320 352 400
  (interval_append test135680 320 336 352
  test135680_block_20
  test135680_block_21)
  (interval_append test135680 352 368 400
  test135680_block_22
  (interval_append test135680 368 384 400
  test135680_block_23
  test135680_block_24)))
  (interval_append test135680 400 432 480
  (interval_append test135680 400 416 432
  test135680_block_25
  test135680_block_26)
  (interval_append test135680 432 448 480
  test135680_block_27
  (interval_append test135680 448 464 480
  test135680_block_28
  test135680_block_29))))
  (interval_append test135680 480 560 640
  (interval_append test135680 480 512 560
  (interval_append test135680 480 496 512
  test135680_block_30
  test135680_block_31)
  (interval_append test135680 512 528 560
  test135680_block_32
  (interval_append test135680 528 544 560
  test135680_block_33
  test135680_block_34)))
  (interval_append test135680 560 592 640
  (interval_append test135680 560 576 592
  test135680_block_35
  test135680_block_36)
  (interval_append test135680 592 608 640
  test135680_block_37
  (interval_append test135680 608 624 640
  test135680_block_38
  test135680_block_39))))))
cert_nodeInterval_3 135680 136320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
