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
cert_test_11 113920
cert_test_block_3 113920 0 0 16 16
cert_test_block_3 113920 1 16 32 16
cert_test_block_3 113920 2 32 48 16
cert_test_block_3 113920 3 48 64 16
cert_test_block_3 113920 4 64 80 16
cert_test_block_3 113920 5 80 96 16
cert_test_block_3 113920 6 96 112 16
cert_test_block_3 113920 7 112 128 16
cert_test_block_3 113920 8 128 144 16
cert_test_block_3 113920 9 144 160 16
cert_test_block_3 113920 10 160 176 16
cert_test_block_3 113920 11 176 192 16
cert_test_block_3 113920 12 192 208 16
cert_test_block_3 113920 13 208 224 16
cert_test_block_3 113920 14 224 240 16
cert_test_block_3 113920 15 240 256 16
cert_test_block_3 113920 16 256 272 16
cert_test_block_3 113920 17 272 288 16
cert_test_block_3 113920 18 288 304 16
cert_test_block_3 113920 19 304 320 16
cert_test_block_3 113920 20 320 336 16
cert_test_block_3 113920 21 336 352 16
cert_test_block_3 113920 22 352 368 16
cert_test_block_3 113920 23 368 384 16
cert_test_block_3 113920 24 384 400 16
cert_test_block_3 113920 25 400 416 16
cert_test_block_3 113920 26 416 432 16
cert_test_block_3 113920 27 432 448 16
cert_test_block_3 113920 28 448 464 16
cert_test_block_3 113920 29 464 480 16
cert_test_block_3 113920 30 480 496 16
cert_test_block_3 113920 31 496 512 16
cert_test_block_3 113920 32 512 528 16
cert_test_block_3 113920 33 528 544 16
cert_test_block_3 113920 34 544 560 16
cert_test_block_3 113920 35 560 576 16
cert_test_block_3 113920 36 576 592 16
cert_test_block_3 113920 37 592 608 16
cert_test_block_3 113920 38 608 624 16
cert_test_block_3 113920 39 624 640 16
theorem test113920_complete : Interval test113920 0 640 :=
  (interval_append test113920 0 320 640
  (interval_append test113920 0 160 320
  (interval_append test113920 0 80 160
  (interval_append test113920 0 32 80
  (interval_append test113920 0 16 32
  test113920_block_0
  test113920_block_1)
  (interval_append test113920 32 48 80
  test113920_block_2
  (interval_append test113920 48 64 80
  test113920_block_3
  test113920_block_4)))
  (interval_append test113920 80 112 160
  (interval_append test113920 80 96 112
  test113920_block_5
  test113920_block_6)
  (interval_append test113920 112 128 160
  test113920_block_7
  (interval_append test113920 128 144 160
  test113920_block_8
  test113920_block_9))))
  (interval_append test113920 160 240 320
  (interval_append test113920 160 192 240
  (interval_append test113920 160 176 192
  test113920_block_10
  test113920_block_11)
  (interval_append test113920 192 208 240
  test113920_block_12
  (interval_append test113920 208 224 240
  test113920_block_13
  test113920_block_14)))
  (interval_append test113920 240 272 320
  (interval_append test113920 240 256 272
  test113920_block_15
  test113920_block_16)
  (interval_append test113920 272 288 320
  test113920_block_17
  (interval_append test113920 288 304 320
  test113920_block_18
  test113920_block_19)))))
  (interval_append test113920 320 480 640
  (interval_append test113920 320 400 480
  (interval_append test113920 320 352 400
  (interval_append test113920 320 336 352
  test113920_block_20
  test113920_block_21)
  (interval_append test113920 352 368 400
  test113920_block_22
  (interval_append test113920 368 384 400
  test113920_block_23
  test113920_block_24)))
  (interval_append test113920 400 432 480
  (interval_append test113920 400 416 432
  test113920_block_25
  test113920_block_26)
  (interval_append test113920 432 448 480
  test113920_block_27
  (interval_append test113920 448 464 480
  test113920_block_28
  test113920_block_29))))
  (interval_append test113920 480 560 640
  (interval_append test113920 480 512 560
  (interval_append test113920 480 496 512
  test113920_block_30
  test113920_block_31)
  (interval_append test113920 512 528 560
  test113920_block_32
  (interval_append test113920 528 544 560
  test113920_block_33
  test113920_block_34)))
  (interval_append test113920 560 592 640
  (interval_append test113920 560 576 592
  test113920_block_35
  test113920_block_36)
  (interval_append test113920 592 608 640
  test113920_block_37
  (interval_append test113920 608 624 640
  test113920_block_38
  test113920_block_39))))))
cert_nodeInterval_3 113920 114560
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
cert_test_11 114560
cert_test_block_3 114560 0 0 16 16
cert_test_block_3 114560 1 16 32 16
cert_test_block_3 114560 2 32 48 16
cert_test_block_3 114560 3 48 64 16
cert_test_block_3 114560 4 64 80 16
cert_test_block_3 114560 5 80 96 16
cert_test_block_3 114560 6 96 112 16
cert_test_block_3 114560 7 112 128 16
cert_test_block_3 114560 8 128 144 16
cert_test_block_3 114560 9 144 160 16
cert_test_block_3 114560 10 160 176 16
cert_test_block_3 114560 11 176 192 16
cert_test_block_3 114560 12 192 208 16
cert_test_block_3 114560 13 208 224 16
cert_test_block_3 114560 14 224 240 16
cert_test_block_3 114560 15 240 256 16
cert_test_block_3 114560 16 256 272 16
cert_test_block_3 114560 17 272 288 16
cert_test_block_3 114560 18 288 304 16
cert_test_block_3 114560 19 304 320 16
cert_test_block_3 114560 20 320 336 16
cert_test_block_3 114560 21 336 352 16
cert_test_block_3 114560 22 352 368 16
cert_test_block_3 114560 23 368 384 16
cert_test_block_3 114560 24 384 400 16
cert_test_block_3 114560 25 400 416 16
cert_test_block_3 114560 26 416 432 16
cert_test_block_3 114560 27 432 448 16
cert_test_block_3 114560 28 448 464 16
cert_test_block_3 114560 29 464 480 16
cert_test_block_3 114560 30 480 496 16
cert_test_block_3 114560 31 496 512 16
cert_test_block_3 114560 32 512 528 16
cert_test_block_3 114560 33 528 544 16
cert_test_block_3 114560 34 544 560 16
cert_test_block_3 114560 35 560 576 16
cert_test_block_3 114560 36 576 592 16
cert_test_block_3 114560 37 592 608 16
cert_test_block_3 114560 38 608 624 16
cert_test_block_3 114560 39 624 640 16
theorem test114560_complete : Interval test114560 0 640 :=
  (interval_append test114560 0 320 640
  (interval_append test114560 0 160 320
  (interval_append test114560 0 80 160
  (interval_append test114560 0 32 80
  (interval_append test114560 0 16 32
  test114560_block_0
  test114560_block_1)
  (interval_append test114560 32 48 80
  test114560_block_2
  (interval_append test114560 48 64 80
  test114560_block_3
  test114560_block_4)))
  (interval_append test114560 80 112 160
  (interval_append test114560 80 96 112
  test114560_block_5
  test114560_block_6)
  (interval_append test114560 112 128 160
  test114560_block_7
  (interval_append test114560 128 144 160
  test114560_block_8
  test114560_block_9))))
  (interval_append test114560 160 240 320
  (interval_append test114560 160 192 240
  (interval_append test114560 160 176 192
  test114560_block_10
  test114560_block_11)
  (interval_append test114560 192 208 240
  test114560_block_12
  (interval_append test114560 208 224 240
  test114560_block_13
  test114560_block_14)))
  (interval_append test114560 240 272 320
  (interval_append test114560 240 256 272
  test114560_block_15
  test114560_block_16)
  (interval_append test114560 272 288 320
  test114560_block_17
  (interval_append test114560 288 304 320
  test114560_block_18
  test114560_block_19)))))
  (interval_append test114560 320 480 640
  (interval_append test114560 320 400 480
  (interval_append test114560 320 352 400
  (interval_append test114560 320 336 352
  test114560_block_20
  test114560_block_21)
  (interval_append test114560 352 368 400
  test114560_block_22
  (interval_append test114560 368 384 400
  test114560_block_23
  test114560_block_24)))
  (interval_append test114560 400 432 480
  (interval_append test114560 400 416 432
  test114560_block_25
  test114560_block_26)
  (interval_append test114560 432 448 480
  test114560_block_27
  (interval_append test114560 448 464 480
  test114560_block_28
  test114560_block_29))))
  (interval_append test114560 480 560 640
  (interval_append test114560 480 512 560
  (interval_append test114560 480 496 512
  test114560_block_30
  test114560_block_31)
  (interval_append test114560 512 528 560
  test114560_block_32
  (interval_append test114560 528 544 560
  test114560_block_33
  test114560_block_34)))
  (interval_append test114560 560 592 640
  (interval_append test114560 560 576 592
  test114560_block_35
  test114560_block_36)
  (interval_append test114560 592 608 640
  test114560_block_37
  (interval_append test114560 608 624 640
  test114560_block_38
  test114560_block_39))))))
cert_nodeInterval_3 114560 115200
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
cert_test_11 115200
cert_test_block_3 115200 0 0 16 16
cert_test_block_3 115200 1 16 32 16
cert_test_block_3 115200 2 32 48 16
cert_test_block_3 115200 3 48 64 16
cert_test_block_3 115200 4 64 80 16
cert_test_block_3 115200 5 80 96 16
cert_test_block_3 115200 6 96 112 16
cert_test_block_3 115200 7 112 128 16
cert_test_block_3 115200 8 128 144 16
cert_test_block_3 115200 9 144 160 16
cert_test_block_3 115200 10 160 176 16
cert_test_block_3 115200 11 176 192 16
cert_test_block_3 115200 12 192 208 16
cert_test_block_3 115200 13 208 224 16
cert_test_block_3 115200 14 224 240 16
cert_test_block_3 115200 15 240 256 16
cert_test_block_3 115200 16 256 272 16
cert_test_block_3 115200 17 272 288 16
cert_test_block_3 115200 18 288 304 16
cert_test_block_3 115200 19 304 320 16
cert_test_block_3 115200 20 320 336 16
cert_test_block_3 115200 21 336 352 16
cert_test_block_3 115200 22 352 368 16
cert_test_block_3 115200 23 368 384 16
cert_test_block_3 115200 24 384 400 16
cert_test_block_3 115200 25 400 416 16
cert_test_block_3 115200 26 416 432 16
cert_test_block_3 115200 27 432 448 16
cert_test_block_3 115200 28 448 464 16
cert_test_block_3 115200 29 464 480 16
cert_test_block_3 115200 30 480 496 16
cert_test_block_3 115200 31 496 512 16
cert_test_block_3 115200 32 512 528 16
cert_test_block_3 115200 33 528 544 16
cert_test_block_3 115200 34 544 560 16
cert_test_block_3 115200 35 560 576 16
cert_test_block_3 115200 36 576 592 16
cert_test_block_3 115200 37 592 608 16
cert_test_block_3 115200 38 608 624 16
cert_test_block_3 115200 39 624 640 16
theorem test115200_complete : Interval test115200 0 640 :=
  (interval_append test115200 0 320 640
  (interval_append test115200 0 160 320
  (interval_append test115200 0 80 160
  (interval_append test115200 0 32 80
  (interval_append test115200 0 16 32
  test115200_block_0
  test115200_block_1)
  (interval_append test115200 32 48 80
  test115200_block_2
  (interval_append test115200 48 64 80
  test115200_block_3
  test115200_block_4)))
  (interval_append test115200 80 112 160
  (interval_append test115200 80 96 112
  test115200_block_5
  test115200_block_6)
  (interval_append test115200 112 128 160
  test115200_block_7
  (interval_append test115200 128 144 160
  test115200_block_8
  test115200_block_9))))
  (interval_append test115200 160 240 320
  (interval_append test115200 160 192 240
  (interval_append test115200 160 176 192
  test115200_block_10
  test115200_block_11)
  (interval_append test115200 192 208 240
  test115200_block_12
  (interval_append test115200 208 224 240
  test115200_block_13
  test115200_block_14)))
  (interval_append test115200 240 272 320
  (interval_append test115200 240 256 272
  test115200_block_15
  test115200_block_16)
  (interval_append test115200 272 288 320
  test115200_block_17
  (interval_append test115200 288 304 320
  test115200_block_18
  test115200_block_19)))))
  (interval_append test115200 320 480 640
  (interval_append test115200 320 400 480
  (interval_append test115200 320 352 400
  (interval_append test115200 320 336 352
  test115200_block_20
  test115200_block_21)
  (interval_append test115200 352 368 400
  test115200_block_22
  (interval_append test115200 368 384 400
  test115200_block_23
  test115200_block_24)))
  (interval_append test115200 400 432 480
  (interval_append test115200 400 416 432
  test115200_block_25
  test115200_block_26)
  (interval_append test115200 432 448 480
  test115200_block_27
  (interval_append test115200 448 464 480
  test115200_block_28
  test115200_block_29))))
  (interval_append test115200 480 560 640
  (interval_append test115200 480 512 560
  (interval_append test115200 480 496 512
  test115200_block_30
  test115200_block_31)
  (interval_append test115200 512 528 560
  test115200_block_32
  (interval_append test115200 528 544 560
  test115200_block_33
  test115200_block_34)))
  (interval_append test115200 560 592 640
  (interval_append test115200 560 576 592
  test115200_block_35
  test115200_block_36)
  (interval_append test115200 592 608 640
  test115200_block_37
  (interval_append test115200 608 624 640
  test115200_block_38
  test115200_block_39))))))
cert_nodeInterval_3 115200 115840
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
cert_test_11 115840
cert_test_block_3 115840 0 0 16 16
cert_test_block_3 115840 1 16 32 16
cert_test_block_3 115840 2 32 48 16
cert_test_block_3 115840 3 48 64 16
cert_test_block_3 115840 4 64 80 16
cert_test_block_3 115840 5 80 96 16
cert_test_block_3 115840 6 96 112 16
cert_test_block_3 115840 7 112 128 16
cert_test_block_3 115840 8 128 144 16
cert_test_block_3 115840 9 144 160 16
cert_test_block_3 115840 10 160 176 16
cert_test_block_3 115840 11 176 192 16
cert_test_block_3 115840 12 192 208 16
cert_test_block_3 115840 13 208 224 16
cert_test_block_3 115840 14 224 240 16
cert_test_block_3 115840 15 240 256 16
cert_test_block_3 115840 16 256 272 16
cert_test_block_3 115840 17 272 288 16
cert_test_block_3 115840 18 288 304 16
cert_test_block_3 115840 19 304 320 16
cert_test_block_3 115840 20 320 336 16
cert_test_block_3 115840 21 336 352 16
cert_test_block_3 115840 22 352 368 16
cert_test_block_3 115840 23 368 384 16
cert_test_block_3 115840 24 384 400 16
cert_test_block_3 115840 25 400 416 16
cert_test_block_3 115840 26 416 432 16
cert_test_block_3 115840 27 432 448 16
cert_test_block_3 115840 28 448 464 16
cert_test_block_3 115840 29 464 480 16
cert_test_block_3 115840 30 480 496 16
cert_test_block_3 115840 31 496 512 16
cert_test_block_3 115840 32 512 528 16
cert_test_block_3 115840 33 528 544 16
cert_test_block_3 115840 34 544 560 16
cert_test_block_3 115840 35 560 576 16
cert_test_block_3 115840 36 576 592 16
cert_test_block_3 115840 37 592 608 16
cert_test_block_3 115840 38 608 624 16
cert_test_block_3 115840 39 624 640 16
theorem test115840_complete : Interval test115840 0 640 :=
  (interval_append test115840 0 320 640
  (interval_append test115840 0 160 320
  (interval_append test115840 0 80 160
  (interval_append test115840 0 32 80
  (interval_append test115840 0 16 32
  test115840_block_0
  test115840_block_1)
  (interval_append test115840 32 48 80
  test115840_block_2
  (interval_append test115840 48 64 80
  test115840_block_3
  test115840_block_4)))
  (interval_append test115840 80 112 160
  (interval_append test115840 80 96 112
  test115840_block_5
  test115840_block_6)
  (interval_append test115840 112 128 160
  test115840_block_7
  (interval_append test115840 128 144 160
  test115840_block_8
  test115840_block_9))))
  (interval_append test115840 160 240 320
  (interval_append test115840 160 192 240
  (interval_append test115840 160 176 192
  test115840_block_10
  test115840_block_11)
  (interval_append test115840 192 208 240
  test115840_block_12
  (interval_append test115840 208 224 240
  test115840_block_13
  test115840_block_14)))
  (interval_append test115840 240 272 320
  (interval_append test115840 240 256 272
  test115840_block_15
  test115840_block_16)
  (interval_append test115840 272 288 320
  test115840_block_17
  (interval_append test115840 288 304 320
  test115840_block_18
  test115840_block_19)))))
  (interval_append test115840 320 480 640
  (interval_append test115840 320 400 480
  (interval_append test115840 320 352 400
  (interval_append test115840 320 336 352
  test115840_block_20
  test115840_block_21)
  (interval_append test115840 352 368 400
  test115840_block_22
  (interval_append test115840 368 384 400
  test115840_block_23
  test115840_block_24)))
  (interval_append test115840 400 432 480
  (interval_append test115840 400 416 432
  test115840_block_25
  test115840_block_26)
  (interval_append test115840 432 448 480
  test115840_block_27
  (interval_append test115840 448 464 480
  test115840_block_28
  test115840_block_29))))
  (interval_append test115840 480 560 640
  (interval_append test115840 480 512 560
  (interval_append test115840 480 496 512
  test115840_block_30
  test115840_block_31)
  (interval_append test115840 512 528 560
  test115840_block_32
  (interval_append test115840 528 544 560
  test115840_block_33
  test115840_block_34)))
  (interval_append test115840 560 592 640
  (interval_append test115840 560 576 592
  test115840_block_35
  test115840_block_36)
  (interval_append test115840 592 608 640
  test115840_block_37
  (interval_append test115840 608 624 640
  test115840_block_38
  test115840_block_39))))))
cert_nodeInterval_3 115840 116480
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
cert_test_11 116480
cert_test_block_3 116480 0 0 16 16
cert_test_block_3 116480 1 16 32 16
cert_test_block_3 116480 2 32 48 16
cert_test_block_3 116480 3 48 64 16
cert_test_block_3 116480 4 64 80 16
cert_test_block_3 116480 5 80 96 16
cert_test_block_3 116480 6 96 112 16
cert_test_block_3 116480 7 112 128 16
cert_test_block_3 116480 8 128 144 16
cert_test_block_3 116480 9 144 160 16
cert_test_block_3 116480 10 160 176 16
cert_test_block_3 116480 11 176 192 16
cert_test_block_3 116480 12 192 208 16
cert_test_block_3 116480 13 208 224 16
cert_test_block_3 116480 14 224 240 16
cert_test_block_3 116480 15 240 256 16
cert_test_block_3 116480 16 256 272 16
cert_test_block_3 116480 17 272 288 16
cert_test_block_3 116480 18 288 304 16
cert_test_block_3 116480 19 304 320 16
cert_test_block_3 116480 20 320 336 16
cert_test_block_3 116480 21 336 352 16
cert_test_block_3 116480 22 352 368 16
cert_test_block_3 116480 23 368 384 16
cert_test_block_3 116480 24 384 400 16
cert_test_block_3 116480 25 400 416 16
cert_test_block_3 116480 26 416 432 16
cert_test_block_3 116480 27 432 448 16
cert_test_block_3 116480 28 448 464 16
cert_test_block_3 116480 29 464 480 16
cert_test_block_3 116480 30 480 496 16
cert_test_block_3 116480 31 496 512 16
cert_test_block_3 116480 32 512 528 16
cert_test_block_3 116480 33 528 544 16
cert_test_block_3 116480 34 544 560 16
cert_test_block_3 116480 35 560 576 16
cert_test_block_3 116480 36 576 592 16
cert_test_block_3 116480 37 592 608 16
cert_test_block_3 116480 38 608 624 16
cert_test_block_3 116480 39 624 640 16
theorem test116480_complete : Interval test116480 0 640 :=
  (interval_append test116480 0 320 640
  (interval_append test116480 0 160 320
  (interval_append test116480 0 80 160
  (interval_append test116480 0 32 80
  (interval_append test116480 0 16 32
  test116480_block_0
  test116480_block_1)
  (interval_append test116480 32 48 80
  test116480_block_2
  (interval_append test116480 48 64 80
  test116480_block_3
  test116480_block_4)))
  (interval_append test116480 80 112 160
  (interval_append test116480 80 96 112
  test116480_block_5
  test116480_block_6)
  (interval_append test116480 112 128 160
  test116480_block_7
  (interval_append test116480 128 144 160
  test116480_block_8
  test116480_block_9))))
  (interval_append test116480 160 240 320
  (interval_append test116480 160 192 240
  (interval_append test116480 160 176 192
  test116480_block_10
  test116480_block_11)
  (interval_append test116480 192 208 240
  test116480_block_12
  (interval_append test116480 208 224 240
  test116480_block_13
  test116480_block_14)))
  (interval_append test116480 240 272 320
  (interval_append test116480 240 256 272
  test116480_block_15
  test116480_block_16)
  (interval_append test116480 272 288 320
  test116480_block_17
  (interval_append test116480 288 304 320
  test116480_block_18
  test116480_block_19)))))
  (interval_append test116480 320 480 640
  (interval_append test116480 320 400 480
  (interval_append test116480 320 352 400
  (interval_append test116480 320 336 352
  test116480_block_20
  test116480_block_21)
  (interval_append test116480 352 368 400
  test116480_block_22
  (interval_append test116480 368 384 400
  test116480_block_23
  test116480_block_24)))
  (interval_append test116480 400 432 480
  (interval_append test116480 400 416 432
  test116480_block_25
  test116480_block_26)
  (interval_append test116480 432 448 480
  test116480_block_27
  (interval_append test116480 448 464 480
  test116480_block_28
  test116480_block_29))))
  (interval_append test116480 480 560 640
  (interval_append test116480 480 512 560
  (interval_append test116480 480 496 512
  test116480_block_30
  test116480_block_31)
  (interval_append test116480 512 528 560
  test116480_block_32
  (interval_append test116480 528 544 560
  test116480_block_33
  test116480_block_34)))
  (interval_append test116480 560 592 640
  (interval_append test116480 560 576 592
  test116480_block_35
  test116480_block_36)
  (interval_append test116480 592 608 640
  test116480_block_37
  (interval_append test116480 608 624 640
  test116480_block_38
  test116480_block_39))))))
cert_nodeInterval_3 116480 117120
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
cert_test_11 117120
cert_test_block_3 117120 0 0 16 16
cert_test_block_3 117120 1 16 32 16
cert_test_block_3 117120 2 32 48 16
cert_test_block_3 117120 3 48 64 16
cert_test_block_3 117120 4 64 80 16
cert_test_block_3 117120 5 80 96 16
cert_test_block_3 117120 6 96 112 16
cert_test_block_3 117120 7 112 128 16
cert_test_block_3 117120 8 128 144 16
cert_test_block_3 117120 9 144 160 16
cert_test_block_3 117120 10 160 176 16
cert_test_block_3 117120 11 176 192 16
cert_test_block_3 117120 12 192 208 16
cert_test_block_3 117120 13 208 224 16
cert_test_block_3 117120 14 224 240 16
cert_test_block_3 117120 15 240 256 16
cert_test_block_3 117120 16 256 272 16
cert_test_block_3 117120 17 272 288 16
cert_test_block_3 117120 18 288 304 16
cert_test_block_3 117120 19 304 320 16
cert_test_block_3 117120 20 320 336 16
cert_test_block_3 117120 21 336 352 16
cert_test_block_3 117120 22 352 368 16
cert_test_block_3 117120 23 368 384 16
cert_test_block_3 117120 24 384 400 16
cert_test_block_3 117120 25 400 416 16
cert_test_block_3 117120 26 416 432 16
cert_test_block_3 117120 27 432 448 16
cert_test_block_3 117120 28 448 464 16
cert_test_block_3 117120 29 464 480 16
cert_test_block_3 117120 30 480 496 16
cert_test_block_3 117120 31 496 512 16
cert_test_block_3 117120 32 512 528 16
cert_test_block_3 117120 33 528 544 16
cert_test_block_3 117120 34 544 560 16
cert_test_block_3 117120 35 560 576 16
cert_test_block_3 117120 36 576 592 16
cert_test_block_3 117120 37 592 608 16
cert_test_block_3 117120 38 608 624 16
cert_test_block_3 117120 39 624 640 16
theorem test117120_complete : Interval test117120 0 640 :=
  (interval_append test117120 0 320 640
  (interval_append test117120 0 160 320
  (interval_append test117120 0 80 160
  (interval_append test117120 0 32 80
  (interval_append test117120 0 16 32
  test117120_block_0
  test117120_block_1)
  (interval_append test117120 32 48 80
  test117120_block_2
  (interval_append test117120 48 64 80
  test117120_block_3
  test117120_block_4)))
  (interval_append test117120 80 112 160
  (interval_append test117120 80 96 112
  test117120_block_5
  test117120_block_6)
  (interval_append test117120 112 128 160
  test117120_block_7
  (interval_append test117120 128 144 160
  test117120_block_8
  test117120_block_9))))
  (interval_append test117120 160 240 320
  (interval_append test117120 160 192 240
  (interval_append test117120 160 176 192
  test117120_block_10
  test117120_block_11)
  (interval_append test117120 192 208 240
  test117120_block_12
  (interval_append test117120 208 224 240
  test117120_block_13
  test117120_block_14)))
  (interval_append test117120 240 272 320
  (interval_append test117120 240 256 272
  test117120_block_15
  test117120_block_16)
  (interval_append test117120 272 288 320
  test117120_block_17
  (interval_append test117120 288 304 320
  test117120_block_18
  test117120_block_19)))))
  (interval_append test117120 320 480 640
  (interval_append test117120 320 400 480
  (interval_append test117120 320 352 400
  (interval_append test117120 320 336 352
  test117120_block_20
  test117120_block_21)
  (interval_append test117120 352 368 400
  test117120_block_22
  (interval_append test117120 368 384 400
  test117120_block_23
  test117120_block_24)))
  (interval_append test117120 400 432 480
  (interval_append test117120 400 416 432
  test117120_block_25
  test117120_block_26)
  (interval_append test117120 432 448 480
  test117120_block_27
  (interval_append test117120 448 464 480
  test117120_block_28
  test117120_block_29))))
  (interval_append test117120 480 560 640
  (interval_append test117120 480 512 560
  (interval_append test117120 480 496 512
  test117120_block_30
  test117120_block_31)
  (interval_append test117120 512 528 560
  test117120_block_32
  (interval_append test117120 528 544 560
  test117120_block_33
  test117120_block_34)))
  (interval_append test117120 560 592 640
  (interval_append test117120 560 576 592
  test117120_block_35
  test117120_block_36)
  (interval_append test117120 592 608 640
  test117120_block_37
  (interval_append test117120 608 624 640
  test117120_block_38
  test117120_block_39))))))
cert_nodeInterval_3 117120 117760
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
cert_test_11 117760
cert_test_block_3 117760 0 0 16 16
cert_test_block_3 117760 1 16 32 16
cert_test_block_3 117760 2 32 48 16
cert_test_block_3 117760 3 48 64 16
cert_test_block_3 117760 4 64 80 16
cert_test_block_3 117760 5 80 96 16
cert_test_block_3 117760 6 96 112 16
cert_test_block_3 117760 7 112 128 16
cert_test_block_3 117760 8 128 144 16
cert_test_block_3 117760 9 144 160 16
cert_test_block_3 117760 10 160 176 16
cert_test_block_3 117760 11 176 192 16
cert_test_block_3 117760 12 192 208 16
cert_test_block_3 117760 13 208 224 16
cert_test_block_3 117760 14 224 240 16
cert_test_block_3 117760 15 240 256 16
cert_test_block_3 117760 16 256 272 16
cert_test_block_3 117760 17 272 288 16
cert_test_block_3 117760 18 288 304 16
cert_test_block_3 117760 19 304 320 16
cert_test_block_3 117760 20 320 336 16
cert_test_block_3 117760 21 336 352 16
cert_test_block_3 117760 22 352 368 16
cert_test_block_3 117760 23 368 384 16
cert_test_block_3 117760 24 384 400 16
cert_test_block_3 117760 25 400 416 16
cert_test_block_3 117760 26 416 432 16
cert_test_block_3 117760 27 432 448 16
cert_test_block_3 117760 28 448 464 16
cert_test_block_3 117760 29 464 480 16
cert_test_block_3 117760 30 480 496 16
cert_test_block_3 117760 31 496 512 16
cert_test_block_3 117760 32 512 528 16
cert_test_block_3 117760 33 528 544 16
cert_test_block_3 117760 34 544 560 16
cert_test_block_3 117760 35 560 576 16
cert_test_block_3 117760 36 576 592 16
cert_test_block_3 117760 37 592 608 16
cert_test_block_3 117760 38 608 624 16
cert_test_block_3 117760 39 624 640 16
theorem test117760_complete : Interval test117760 0 640 :=
  (interval_append test117760 0 320 640
  (interval_append test117760 0 160 320
  (interval_append test117760 0 80 160
  (interval_append test117760 0 32 80
  (interval_append test117760 0 16 32
  test117760_block_0
  test117760_block_1)
  (interval_append test117760 32 48 80
  test117760_block_2
  (interval_append test117760 48 64 80
  test117760_block_3
  test117760_block_4)))
  (interval_append test117760 80 112 160
  (interval_append test117760 80 96 112
  test117760_block_5
  test117760_block_6)
  (interval_append test117760 112 128 160
  test117760_block_7
  (interval_append test117760 128 144 160
  test117760_block_8
  test117760_block_9))))
  (interval_append test117760 160 240 320
  (interval_append test117760 160 192 240
  (interval_append test117760 160 176 192
  test117760_block_10
  test117760_block_11)
  (interval_append test117760 192 208 240
  test117760_block_12
  (interval_append test117760 208 224 240
  test117760_block_13
  test117760_block_14)))
  (interval_append test117760 240 272 320
  (interval_append test117760 240 256 272
  test117760_block_15
  test117760_block_16)
  (interval_append test117760 272 288 320
  test117760_block_17
  (interval_append test117760 288 304 320
  test117760_block_18
  test117760_block_19)))))
  (interval_append test117760 320 480 640
  (interval_append test117760 320 400 480
  (interval_append test117760 320 352 400
  (interval_append test117760 320 336 352
  test117760_block_20
  test117760_block_21)
  (interval_append test117760 352 368 400
  test117760_block_22
  (interval_append test117760 368 384 400
  test117760_block_23
  test117760_block_24)))
  (interval_append test117760 400 432 480
  (interval_append test117760 400 416 432
  test117760_block_25
  test117760_block_26)
  (interval_append test117760 432 448 480
  test117760_block_27
  (interval_append test117760 448 464 480
  test117760_block_28
  test117760_block_29))))
  (interval_append test117760 480 560 640
  (interval_append test117760 480 512 560
  (interval_append test117760 480 496 512
  test117760_block_30
  test117760_block_31)
  (interval_append test117760 512 528 560
  test117760_block_32
  (interval_append test117760 528 544 560
  test117760_block_33
  test117760_block_34)))
  (interval_append test117760 560 592 640
  (interval_append test117760 560 576 592
  test117760_block_35
  test117760_block_36)
  (interval_append test117760 592 608 640
  test117760_block_37
  (interval_append test117760 608 624 640
  test117760_block_38
  test117760_block_39))))))
cert_nodeInterval_3 117760 118400
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
cert_test_11 118400
cert_test_block_3 118400 0 0 16 16
cert_test_block_3 118400 1 16 32 16
cert_test_block_3 118400 2 32 48 16
cert_test_block_3 118400 3 48 64 16
cert_test_block_3 118400 4 64 80 16
cert_test_block_3 118400 5 80 96 16
cert_test_block_3 118400 6 96 112 16
cert_test_block_3 118400 7 112 128 16
cert_test_block_3 118400 8 128 144 16
cert_test_block_3 118400 9 144 160 16
cert_test_block_3 118400 10 160 176 16
cert_test_block_3 118400 11 176 192 16
cert_test_block_3 118400 12 192 208 16
cert_test_block_3 118400 13 208 224 16
cert_test_block_3 118400 14 224 240 16
cert_test_block_3 118400 15 240 256 16
cert_test_block_3 118400 16 256 272 16
cert_test_block_3 118400 17 272 288 16
cert_test_block_3 118400 18 288 304 16
cert_test_block_3 118400 19 304 320 16
cert_test_block_3 118400 20 320 336 16
cert_test_block_3 118400 21 336 352 16
cert_test_block_3 118400 22 352 368 16
cert_test_block_3 118400 23 368 384 16
cert_test_block_3 118400 24 384 400 16
cert_test_block_3 118400 25 400 416 16
cert_test_block_3 118400 26 416 432 16
cert_test_block_3 118400 27 432 448 16
cert_test_block_3 118400 28 448 464 16
cert_test_block_3 118400 29 464 480 16
cert_test_block_3 118400 30 480 496 16
cert_test_block_3 118400 31 496 512 16
cert_test_block_3 118400 32 512 528 16
cert_test_block_3 118400 33 528 544 16
cert_test_block_3 118400 34 544 560 16
cert_test_block_3 118400 35 560 576 16
cert_test_block_3 118400 36 576 592 16
cert_test_block_3 118400 37 592 608 16
cert_test_block_3 118400 38 608 624 16
cert_test_block_3 118400 39 624 640 16
theorem test118400_complete : Interval test118400 0 640 :=
  (interval_append test118400 0 320 640
  (interval_append test118400 0 160 320
  (interval_append test118400 0 80 160
  (interval_append test118400 0 32 80
  (interval_append test118400 0 16 32
  test118400_block_0
  test118400_block_1)
  (interval_append test118400 32 48 80
  test118400_block_2
  (interval_append test118400 48 64 80
  test118400_block_3
  test118400_block_4)))
  (interval_append test118400 80 112 160
  (interval_append test118400 80 96 112
  test118400_block_5
  test118400_block_6)
  (interval_append test118400 112 128 160
  test118400_block_7
  (interval_append test118400 128 144 160
  test118400_block_8
  test118400_block_9))))
  (interval_append test118400 160 240 320
  (interval_append test118400 160 192 240
  (interval_append test118400 160 176 192
  test118400_block_10
  test118400_block_11)
  (interval_append test118400 192 208 240
  test118400_block_12
  (interval_append test118400 208 224 240
  test118400_block_13
  test118400_block_14)))
  (interval_append test118400 240 272 320
  (interval_append test118400 240 256 272
  test118400_block_15
  test118400_block_16)
  (interval_append test118400 272 288 320
  test118400_block_17
  (interval_append test118400 288 304 320
  test118400_block_18
  test118400_block_19)))))
  (interval_append test118400 320 480 640
  (interval_append test118400 320 400 480
  (interval_append test118400 320 352 400
  (interval_append test118400 320 336 352
  test118400_block_20
  test118400_block_21)
  (interval_append test118400 352 368 400
  test118400_block_22
  (interval_append test118400 368 384 400
  test118400_block_23
  test118400_block_24)))
  (interval_append test118400 400 432 480
  (interval_append test118400 400 416 432
  test118400_block_25
  test118400_block_26)
  (interval_append test118400 432 448 480
  test118400_block_27
  (interval_append test118400 448 464 480
  test118400_block_28
  test118400_block_29))))
  (interval_append test118400 480 560 640
  (interval_append test118400 480 512 560
  (interval_append test118400 480 496 512
  test118400_block_30
  test118400_block_31)
  (interval_append test118400 512 528 560
  test118400_block_32
  (interval_append test118400 528 544 560
  test118400_block_33
  test118400_block_34)))
  (interval_append test118400 560 592 640
  (interval_append test118400 560 576 592
  test118400_block_35
  test118400_block_36)
  (interval_append test118400 592 608 640
  test118400_block_37
  (interval_append test118400 608 624 640
  test118400_block_38
  test118400_block_39))))))
cert_nodeInterval_3 118400 119040
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
cert_test_11 119040
cert_test_block_3 119040 0 0 16 16
cert_test_block_3 119040 1 16 32 16
cert_test_block_3 119040 2 32 48 16
cert_test_block_3 119040 3 48 64 16
cert_test_block_3 119040 4 64 80 16
cert_test_block_3 119040 5 80 96 16
cert_test_block_3 119040 6 96 112 16
cert_test_block_3 119040 7 112 128 16
cert_test_block_3 119040 8 128 144 16
cert_test_block_3 119040 9 144 160 16
cert_test_block_3 119040 10 160 176 16
cert_test_block_3 119040 11 176 192 16
cert_test_block_3 119040 12 192 208 16
cert_test_block_3 119040 13 208 224 16
cert_test_block_3 119040 14 224 240 16
cert_test_block_3 119040 15 240 256 16
cert_test_block_3 119040 16 256 272 16
cert_test_block_3 119040 17 272 288 16
cert_test_block_3 119040 18 288 304 16
cert_test_block_3 119040 19 304 320 16
cert_test_block_3 119040 20 320 336 16
cert_test_block_3 119040 21 336 352 16
cert_test_block_3 119040 22 352 368 16
cert_test_block_3 119040 23 368 384 16
cert_test_block_3 119040 24 384 400 16
cert_test_block_3 119040 25 400 416 16
cert_test_block_3 119040 26 416 432 16
cert_test_block_3 119040 27 432 448 16
cert_test_block_3 119040 28 448 464 16
cert_test_block_3 119040 29 464 480 16
cert_test_block_3 119040 30 480 496 16
cert_test_block_3 119040 31 496 512 16
cert_test_block_3 119040 32 512 528 16
cert_test_block_3 119040 33 528 544 16
cert_test_block_3 119040 34 544 560 16
cert_test_block_3 119040 35 560 576 16
cert_test_block_3 119040 36 576 592 16
cert_test_block_3 119040 37 592 608 16
cert_test_block_3 119040 38 608 624 16
cert_test_block_3 119040 39 624 640 16
theorem test119040_complete : Interval test119040 0 640 :=
  (interval_append test119040 0 320 640
  (interval_append test119040 0 160 320
  (interval_append test119040 0 80 160
  (interval_append test119040 0 32 80
  (interval_append test119040 0 16 32
  test119040_block_0
  test119040_block_1)
  (interval_append test119040 32 48 80
  test119040_block_2
  (interval_append test119040 48 64 80
  test119040_block_3
  test119040_block_4)))
  (interval_append test119040 80 112 160
  (interval_append test119040 80 96 112
  test119040_block_5
  test119040_block_6)
  (interval_append test119040 112 128 160
  test119040_block_7
  (interval_append test119040 128 144 160
  test119040_block_8
  test119040_block_9))))
  (interval_append test119040 160 240 320
  (interval_append test119040 160 192 240
  (interval_append test119040 160 176 192
  test119040_block_10
  test119040_block_11)
  (interval_append test119040 192 208 240
  test119040_block_12
  (interval_append test119040 208 224 240
  test119040_block_13
  test119040_block_14)))
  (interval_append test119040 240 272 320
  (interval_append test119040 240 256 272
  test119040_block_15
  test119040_block_16)
  (interval_append test119040 272 288 320
  test119040_block_17
  (interval_append test119040 288 304 320
  test119040_block_18
  test119040_block_19)))))
  (interval_append test119040 320 480 640
  (interval_append test119040 320 400 480
  (interval_append test119040 320 352 400
  (interval_append test119040 320 336 352
  test119040_block_20
  test119040_block_21)
  (interval_append test119040 352 368 400
  test119040_block_22
  (interval_append test119040 368 384 400
  test119040_block_23
  test119040_block_24)))
  (interval_append test119040 400 432 480
  (interval_append test119040 400 416 432
  test119040_block_25
  test119040_block_26)
  (interval_append test119040 432 448 480
  test119040_block_27
  (interval_append test119040 448 464 480
  test119040_block_28
  test119040_block_29))))
  (interval_append test119040 480 560 640
  (interval_append test119040 480 512 560
  (interval_append test119040 480 496 512
  test119040_block_30
  test119040_block_31)
  (interval_append test119040 512 528 560
  test119040_block_32
  (interval_append test119040 528 544 560
  test119040_block_33
  test119040_block_34)))
  (interval_append test119040 560 592 640
  (interval_append test119040 560 576 592
  test119040_block_35
  test119040_block_36)
  (interval_append test119040 592 608 640
  test119040_block_37
  (interval_append test119040 608 624 640
  test119040_block_38
  test119040_block_39))))))
cert_nodeInterval_3 119040 119680
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
cert_test_11 119680
cert_test_block_3 119680 0 0 16 16
cert_test_block_3 119680 1 16 32 16
cert_test_block_3 119680 2 32 48 16
cert_test_block_3 119680 3 48 64 16
cert_test_block_3 119680 4 64 80 16
cert_test_block_3 119680 5 80 96 16
cert_test_block_3 119680 6 96 112 16
cert_test_block_3 119680 7 112 128 16
cert_test_block_3 119680 8 128 144 16
cert_test_block_3 119680 9 144 160 16
cert_test_block_3 119680 10 160 176 16
cert_test_block_3 119680 11 176 192 16
cert_test_block_3 119680 12 192 208 16
cert_test_block_3 119680 13 208 224 16
cert_test_block_3 119680 14 224 240 16
cert_test_block_3 119680 15 240 256 16
cert_test_block_3 119680 16 256 272 16
cert_test_block_3 119680 17 272 288 16
cert_test_block_3 119680 18 288 304 16
cert_test_block_3 119680 19 304 320 16
cert_test_block_3 119680 20 320 336 16
cert_test_block_3 119680 21 336 352 16
cert_test_block_3 119680 22 352 368 16
cert_test_block_3 119680 23 368 384 16
cert_test_block_3 119680 24 384 400 16
cert_test_block_3 119680 25 400 416 16
cert_test_block_3 119680 26 416 432 16
cert_test_block_3 119680 27 432 448 16
cert_test_block_3 119680 28 448 464 16
cert_test_block_3 119680 29 464 480 16
cert_test_block_3 119680 30 480 496 16
cert_test_block_3 119680 31 496 512 16
cert_test_block_3 119680 32 512 528 16
cert_test_block_3 119680 33 528 544 16
cert_test_block_3 119680 34 544 560 16
cert_test_block_3 119680 35 560 576 16
cert_test_block_3 119680 36 576 592 16
cert_test_block_3 119680 37 592 608 16
cert_test_block_3 119680 38 608 624 16
cert_test_block_3 119680 39 624 640 16
theorem test119680_complete : Interval test119680 0 640 :=
  (interval_append test119680 0 320 640
  (interval_append test119680 0 160 320
  (interval_append test119680 0 80 160
  (interval_append test119680 0 32 80
  (interval_append test119680 0 16 32
  test119680_block_0
  test119680_block_1)
  (interval_append test119680 32 48 80
  test119680_block_2
  (interval_append test119680 48 64 80
  test119680_block_3
  test119680_block_4)))
  (interval_append test119680 80 112 160
  (interval_append test119680 80 96 112
  test119680_block_5
  test119680_block_6)
  (interval_append test119680 112 128 160
  test119680_block_7
  (interval_append test119680 128 144 160
  test119680_block_8
  test119680_block_9))))
  (interval_append test119680 160 240 320
  (interval_append test119680 160 192 240
  (interval_append test119680 160 176 192
  test119680_block_10
  test119680_block_11)
  (interval_append test119680 192 208 240
  test119680_block_12
  (interval_append test119680 208 224 240
  test119680_block_13
  test119680_block_14)))
  (interval_append test119680 240 272 320
  (interval_append test119680 240 256 272
  test119680_block_15
  test119680_block_16)
  (interval_append test119680 272 288 320
  test119680_block_17
  (interval_append test119680 288 304 320
  test119680_block_18
  test119680_block_19)))))
  (interval_append test119680 320 480 640
  (interval_append test119680 320 400 480
  (interval_append test119680 320 352 400
  (interval_append test119680 320 336 352
  test119680_block_20
  test119680_block_21)
  (interval_append test119680 352 368 400
  test119680_block_22
  (interval_append test119680 368 384 400
  test119680_block_23
  test119680_block_24)))
  (interval_append test119680 400 432 480
  (interval_append test119680 400 416 432
  test119680_block_25
  test119680_block_26)
  (interval_append test119680 432 448 480
  test119680_block_27
  (interval_append test119680 448 464 480
  test119680_block_28
  test119680_block_29))))
  (interval_append test119680 480 560 640
  (interval_append test119680 480 512 560
  (interval_append test119680 480 496 512
  test119680_block_30
  test119680_block_31)
  (interval_append test119680 512 528 560
  test119680_block_32
  (interval_append test119680 528 544 560
  test119680_block_33
  test119680_block_34)))
  (interval_append test119680 560 592 640
  (interval_append test119680 560 576 592
  test119680_block_35
  test119680_block_36)
  (interval_append test119680 592 608 640
  test119680_block_37
  (interval_append test119680 608 624 640
  test119680_block_38
  test119680_block_39))))))
cert_nodeInterval_3 119680 120320
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
cert_test_11 120320
cert_test_block_3 120320 0 0 16 16
cert_test_block_3 120320 1 16 32 16
cert_test_block_3 120320 2 32 48 16
cert_test_block_3 120320 3 48 64 16
cert_test_block_3 120320 4 64 80 16
cert_test_block_3 120320 5 80 96 16
cert_test_block_3 120320 6 96 112 16
cert_test_block_3 120320 7 112 128 16
cert_test_block_3 120320 8 128 144 16
cert_test_block_3 120320 9 144 160 16
cert_test_block_3 120320 10 160 176 16
cert_test_block_3 120320 11 176 192 16
cert_test_block_3 120320 12 192 208 16
cert_test_block_3 120320 13 208 224 16
cert_test_block_3 120320 14 224 240 16
cert_test_block_3 120320 15 240 256 16
cert_test_block_3 120320 16 256 272 16
cert_test_block_3 120320 17 272 288 16
cert_test_block_3 120320 18 288 304 16
cert_test_block_3 120320 19 304 320 16
cert_test_block_3 120320 20 320 336 16
cert_test_block_3 120320 21 336 352 16
cert_test_block_3 120320 22 352 368 16
cert_test_block_3 120320 23 368 384 16
cert_test_block_3 120320 24 384 400 16
cert_test_block_3 120320 25 400 416 16
cert_test_block_3 120320 26 416 432 16
cert_test_block_3 120320 27 432 448 16
cert_test_block_3 120320 28 448 464 16
cert_test_block_3 120320 29 464 480 16
cert_test_block_3 120320 30 480 496 16
cert_test_block_3 120320 31 496 512 16
cert_test_block_3 120320 32 512 528 16
cert_test_block_3 120320 33 528 544 16
cert_test_block_3 120320 34 544 560 16
cert_test_block_3 120320 35 560 576 16
cert_test_block_3 120320 36 576 592 16
cert_test_block_3 120320 37 592 608 16
cert_test_block_3 120320 38 608 624 16
cert_test_block_3 120320 39 624 640 16
theorem test120320_complete : Interval test120320 0 640 :=
  (interval_append test120320 0 320 640
  (interval_append test120320 0 160 320
  (interval_append test120320 0 80 160
  (interval_append test120320 0 32 80
  (interval_append test120320 0 16 32
  test120320_block_0
  test120320_block_1)
  (interval_append test120320 32 48 80
  test120320_block_2
  (interval_append test120320 48 64 80
  test120320_block_3
  test120320_block_4)))
  (interval_append test120320 80 112 160
  (interval_append test120320 80 96 112
  test120320_block_5
  test120320_block_6)
  (interval_append test120320 112 128 160
  test120320_block_7
  (interval_append test120320 128 144 160
  test120320_block_8
  test120320_block_9))))
  (interval_append test120320 160 240 320
  (interval_append test120320 160 192 240
  (interval_append test120320 160 176 192
  test120320_block_10
  test120320_block_11)
  (interval_append test120320 192 208 240
  test120320_block_12
  (interval_append test120320 208 224 240
  test120320_block_13
  test120320_block_14)))
  (interval_append test120320 240 272 320
  (interval_append test120320 240 256 272
  test120320_block_15
  test120320_block_16)
  (interval_append test120320 272 288 320
  test120320_block_17
  (interval_append test120320 288 304 320
  test120320_block_18
  test120320_block_19)))))
  (interval_append test120320 320 480 640
  (interval_append test120320 320 400 480
  (interval_append test120320 320 352 400
  (interval_append test120320 320 336 352
  test120320_block_20
  test120320_block_21)
  (interval_append test120320 352 368 400
  test120320_block_22
  (interval_append test120320 368 384 400
  test120320_block_23
  test120320_block_24)))
  (interval_append test120320 400 432 480
  (interval_append test120320 400 416 432
  test120320_block_25
  test120320_block_26)
  (interval_append test120320 432 448 480
  test120320_block_27
  (interval_append test120320 448 464 480
  test120320_block_28
  test120320_block_29))))
  (interval_append test120320 480 560 640
  (interval_append test120320 480 512 560
  (interval_append test120320 480 496 512
  test120320_block_30
  test120320_block_31)
  (interval_append test120320 512 528 560
  test120320_block_32
  (interval_append test120320 528 544 560
  test120320_block_33
  test120320_block_34)))
  (interval_append test120320 560 592 640
  (interval_append test120320 560 576 592
  test120320_block_35
  test120320_block_36)
  (interval_append test120320 592 608 640
  test120320_block_37
  (interval_append test120320 608 624 640
  test120320_block_38
  test120320_block_39))))))
cert_nodeInterval_3 120320 120960
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
cert_test_11 120960
cert_test_block_3 120960 0 0 16 16
cert_test_block_3 120960 1 16 32 16
cert_test_block_3 120960 2 32 48 16
cert_test_block_3 120960 3 48 64 16
cert_test_block_3 120960 4 64 80 16
cert_test_block_3 120960 5 80 96 16
cert_test_block_3 120960 6 96 112 16
cert_test_block_3 120960 7 112 128 16
cert_test_block_3 120960 8 128 144 16
cert_test_block_3 120960 9 144 160 16
cert_test_block_3 120960 10 160 176 16
cert_test_block_3 120960 11 176 192 16
cert_test_block_3 120960 12 192 208 16
cert_test_block_3 120960 13 208 224 16
cert_test_block_3 120960 14 224 240 16
cert_test_block_3 120960 15 240 256 16
cert_test_block_3 120960 16 256 272 16
cert_test_block_3 120960 17 272 288 16
cert_test_block_3 120960 18 288 304 16
cert_test_block_3 120960 19 304 320 16
cert_test_block_3 120960 20 320 336 16
cert_test_block_3 120960 21 336 352 16
cert_test_block_3 120960 22 352 368 16
cert_test_block_3 120960 23 368 384 16
cert_test_block_3 120960 24 384 400 16
cert_test_block_3 120960 25 400 416 16
cert_test_block_3 120960 26 416 432 16
cert_test_block_3 120960 27 432 448 16
cert_test_block_3 120960 28 448 464 16
cert_test_block_3 120960 29 464 480 16
cert_test_block_3 120960 30 480 496 16
cert_test_block_3 120960 31 496 512 16
cert_test_block_3 120960 32 512 528 16
cert_test_block_3 120960 33 528 544 16
cert_test_block_3 120960 34 544 560 16
cert_test_block_3 120960 35 560 576 16
cert_test_block_3 120960 36 576 592 16
cert_test_block_3 120960 37 592 608 16
cert_test_block_3 120960 38 608 624 16
cert_test_block_3 120960 39 624 640 16
theorem test120960_complete : Interval test120960 0 640 :=
  (interval_append test120960 0 320 640
  (interval_append test120960 0 160 320
  (interval_append test120960 0 80 160
  (interval_append test120960 0 32 80
  (interval_append test120960 0 16 32
  test120960_block_0
  test120960_block_1)
  (interval_append test120960 32 48 80
  test120960_block_2
  (interval_append test120960 48 64 80
  test120960_block_3
  test120960_block_4)))
  (interval_append test120960 80 112 160
  (interval_append test120960 80 96 112
  test120960_block_5
  test120960_block_6)
  (interval_append test120960 112 128 160
  test120960_block_7
  (interval_append test120960 128 144 160
  test120960_block_8
  test120960_block_9))))
  (interval_append test120960 160 240 320
  (interval_append test120960 160 192 240
  (interval_append test120960 160 176 192
  test120960_block_10
  test120960_block_11)
  (interval_append test120960 192 208 240
  test120960_block_12
  (interval_append test120960 208 224 240
  test120960_block_13
  test120960_block_14)))
  (interval_append test120960 240 272 320
  (interval_append test120960 240 256 272
  test120960_block_15
  test120960_block_16)
  (interval_append test120960 272 288 320
  test120960_block_17
  (interval_append test120960 288 304 320
  test120960_block_18
  test120960_block_19)))))
  (interval_append test120960 320 480 640
  (interval_append test120960 320 400 480
  (interval_append test120960 320 352 400
  (interval_append test120960 320 336 352
  test120960_block_20
  test120960_block_21)
  (interval_append test120960 352 368 400
  test120960_block_22
  (interval_append test120960 368 384 400
  test120960_block_23
  test120960_block_24)))
  (interval_append test120960 400 432 480
  (interval_append test120960 400 416 432
  test120960_block_25
  test120960_block_26)
  (interval_append test120960 432 448 480
  test120960_block_27
  (interval_append test120960 448 464 480
  test120960_block_28
  test120960_block_29))))
  (interval_append test120960 480 560 640
  (interval_append test120960 480 512 560
  (interval_append test120960 480 496 512
  test120960_block_30
  test120960_block_31)
  (interval_append test120960 512 528 560
  test120960_block_32
  (interval_append test120960 528 544 560
  test120960_block_33
  test120960_block_34)))
  (interval_append test120960 560 592 640
  (interval_append test120960 560 576 592
  test120960_block_35
  test120960_block_36)
  (interval_append test120960 592 608 640
  test120960_block_37
  (interval_append test120960 608 624 640
  test120960_block_38
  test120960_block_39))))))
cert_nodeInterval_3 120960 121600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
