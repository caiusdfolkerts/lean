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
cert_test_11 69120
cert_test_block_3 69120 0 0 16 16
cert_test_block_3 69120 1 16 32 16
cert_test_block_3 69120 2 32 48 16
cert_test_block_3 69120 3 48 64 16
cert_test_block_3 69120 4 64 80 16
cert_test_block_3 69120 5 80 96 16
cert_test_block_3 69120 6 96 112 16
cert_test_block_3 69120 7 112 128 16
cert_test_block_3 69120 8 128 144 16
cert_test_block_3 69120 9 144 160 16
cert_test_block_3 69120 10 160 176 16
cert_test_block_3 69120 11 176 192 16
cert_test_block_3 69120 12 192 208 16
cert_test_block_3 69120 13 208 224 16
cert_test_block_3 69120 14 224 240 16
cert_test_block_3 69120 15 240 256 16
cert_test_block_3 69120 16 256 272 16
cert_test_block_3 69120 17 272 288 16
cert_test_block_3 69120 18 288 304 16
cert_test_block_3 69120 19 304 320 16
cert_test_block_3 69120 20 320 336 16
cert_test_block_3 69120 21 336 352 16
cert_test_block_3 69120 22 352 368 16
cert_test_block_3 69120 23 368 384 16
cert_test_block_3 69120 24 384 400 16
cert_test_block_3 69120 25 400 416 16
cert_test_block_3 69120 26 416 432 16
cert_test_block_3 69120 27 432 448 16
cert_test_block_3 69120 28 448 464 16
cert_test_block_3 69120 29 464 480 16
cert_test_block_3 69120 30 480 496 16
cert_test_block_3 69120 31 496 512 16
cert_test_block_3 69120 32 512 528 16
cert_test_block_3 69120 33 528 544 16
cert_test_block_3 69120 34 544 560 16
cert_test_block_3 69120 35 560 576 16
cert_test_block_3 69120 36 576 592 16
cert_test_block_3 69120 37 592 608 16
cert_test_block_3 69120 38 608 624 16
cert_test_block_3 69120 39 624 640 16
theorem test69120_complete : Interval test69120 0 640 :=
  (interval_append test69120 0 320 640
  (interval_append test69120 0 160 320
  (interval_append test69120 0 80 160
  (interval_append test69120 0 32 80
  (interval_append test69120 0 16 32
  test69120_block_0
  test69120_block_1)
  (interval_append test69120 32 48 80
  test69120_block_2
  (interval_append test69120 48 64 80
  test69120_block_3
  test69120_block_4)))
  (interval_append test69120 80 112 160
  (interval_append test69120 80 96 112
  test69120_block_5
  test69120_block_6)
  (interval_append test69120 112 128 160
  test69120_block_7
  (interval_append test69120 128 144 160
  test69120_block_8
  test69120_block_9))))
  (interval_append test69120 160 240 320
  (interval_append test69120 160 192 240
  (interval_append test69120 160 176 192
  test69120_block_10
  test69120_block_11)
  (interval_append test69120 192 208 240
  test69120_block_12
  (interval_append test69120 208 224 240
  test69120_block_13
  test69120_block_14)))
  (interval_append test69120 240 272 320
  (interval_append test69120 240 256 272
  test69120_block_15
  test69120_block_16)
  (interval_append test69120 272 288 320
  test69120_block_17
  (interval_append test69120 288 304 320
  test69120_block_18
  test69120_block_19)))))
  (interval_append test69120 320 480 640
  (interval_append test69120 320 400 480
  (interval_append test69120 320 352 400
  (interval_append test69120 320 336 352
  test69120_block_20
  test69120_block_21)
  (interval_append test69120 352 368 400
  test69120_block_22
  (interval_append test69120 368 384 400
  test69120_block_23
  test69120_block_24)))
  (interval_append test69120 400 432 480
  (interval_append test69120 400 416 432
  test69120_block_25
  test69120_block_26)
  (interval_append test69120 432 448 480
  test69120_block_27
  (interval_append test69120 448 464 480
  test69120_block_28
  test69120_block_29))))
  (interval_append test69120 480 560 640
  (interval_append test69120 480 512 560
  (interval_append test69120 480 496 512
  test69120_block_30
  test69120_block_31)
  (interval_append test69120 512 528 560
  test69120_block_32
  (interval_append test69120 528 544 560
  test69120_block_33
  test69120_block_34)))
  (interval_append test69120 560 592 640
  (interval_append test69120 560 576 592
  test69120_block_35
  test69120_block_36)
  (interval_append test69120 592 608 640
  test69120_block_37
  (interval_append test69120 608 624 640
  test69120_block_38
  test69120_block_39))))))
cert_nodeInterval_3 69120 69760
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
cert_test_11 69760
cert_test_block_3 69760 0 0 16 16
cert_test_block_3 69760 1 16 32 16
cert_test_block_3 69760 2 32 48 16
cert_test_block_3 69760 3 48 64 16
cert_test_block_3 69760 4 64 80 16
cert_test_block_3 69760 5 80 96 16
cert_test_block_3 69760 6 96 112 16
cert_test_block_3 69760 7 112 128 16
cert_test_block_3 69760 8 128 144 16
cert_test_block_3 69760 9 144 160 16
cert_test_block_3 69760 10 160 176 16
cert_test_block_3 69760 11 176 192 16
cert_test_block_3 69760 12 192 208 16
cert_test_block_3 69760 13 208 224 16
cert_test_block_3 69760 14 224 240 16
cert_test_block_3 69760 15 240 256 16
cert_test_block_3 69760 16 256 272 16
cert_test_block_3 69760 17 272 288 16
cert_test_block_3 69760 18 288 304 16
cert_test_block_3 69760 19 304 320 16
cert_test_block_3 69760 20 320 336 16
cert_test_block_3 69760 21 336 352 16
cert_test_block_3 69760 22 352 368 16
cert_test_block_3 69760 23 368 384 16
cert_test_block_3 69760 24 384 400 16
cert_test_block_3 69760 25 400 416 16
cert_test_block_3 69760 26 416 432 16
cert_test_block_3 69760 27 432 448 16
cert_test_block_3 69760 28 448 464 16
cert_test_block_3 69760 29 464 480 16
cert_test_block_3 69760 30 480 496 16
cert_test_block_3 69760 31 496 512 16
cert_test_block_3 69760 32 512 528 16
cert_test_block_3 69760 33 528 544 16
cert_test_block_3 69760 34 544 560 16
cert_test_block_3 69760 35 560 576 16
cert_test_block_3 69760 36 576 592 16
cert_test_block_3 69760 37 592 608 16
cert_test_block_3 69760 38 608 624 16
cert_test_block_3 69760 39 624 640 16
theorem test69760_complete : Interval test69760 0 640 :=
  (interval_append test69760 0 320 640
  (interval_append test69760 0 160 320
  (interval_append test69760 0 80 160
  (interval_append test69760 0 32 80
  (interval_append test69760 0 16 32
  test69760_block_0
  test69760_block_1)
  (interval_append test69760 32 48 80
  test69760_block_2
  (interval_append test69760 48 64 80
  test69760_block_3
  test69760_block_4)))
  (interval_append test69760 80 112 160
  (interval_append test69760 80 96 112
  test69760_block_5
  test69760_block_6)
  (interval_append test69760 112 128 160
  test69760_block_7
  (interval_append test69760 128 144 160
  test69760_block_8
  test69760_block_9))))
  (interval_append test69760 160 240 320
  (interval_append test69760 160 192 240
  (interval_append test69760 160 176 192
  test69760_block_10
  test69760_block_11)
  (interval_append test69760 192 208 240
  test69760_block_12
  (interval_append test69760 208 224 240
  test69760_block_13
  test69760_block_14)))
  (interval_append test69760 240 272 320
  (interval_append test69760 240 256 272
  test69760_block_15
  test69760_block_16)
  (interval_append test69760 272 288 320
  test69760_block_17
  (interval_append test69760 288 304 320
  test69760_block_18
  test69760_block_19)))))
  (interval_append test69760 320 480 640
  (interval_append test69760 320 400 480
  (interval_append test69760 320 352 400
  (interval_append test69760 320 336 352
  test69760_block_20
  test69760_block_21)
  (interval_append test69760 352 368 400
  test69760_block_22
  (interval_append test69760 368 384 400
  test69760_block_23
  test69760_block_24)))
  (interval_append test69760 400 432 480
  (interval_append test69760 400 416 432
  test69760_block_25
  test69760_block_26)
  (interval_append test69760 432 448 480
  test69760_block_27
  (interval_append test69760 448 464 480
  test69760_block_28
  test69760_block_29))))
  (interval_append test69760 480 560 640
  (interval_append test69760 480 512 560
  (interval_append test69760 480 496 512
  test69760_block_30
  test69760_block_31)
  (interval_append test69760 512 528 560
  test69760_block_32
  (interval_append test69760 528 544 560
  test69760_block_33
  test69760_block_34)))
  (interval_append test69760 560 592 640
  (interval_append test69760 560 576 592
  test69760_block_35
  test69760_block_36)
  (interval_append test69760 592 608 640
  test69760_block_37
  (interval_append test69760 608 624 640
  test69760_block_38
  test69760_block_39))))))
cert_nodeInterval_3 69760 70400
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
cert_test_11 70400
cert_test_block_3 70400 0 0 16 16
cert_test_block_3 70400 1 16 32 16
cert_test_block_3 70400 2 32 48 16
cert_test_block_3 70400 3 48 64 16
cert_test_block_3 70400 4 64 80 16
cert_test_block_3 70400 5 80 96 16
cert_test_block_3 70400 6 96 112 16
cert_test_block_3 70400 7 112 128 16
cert_test_block_3 70400 8 128 144 16
cert_test_block_3 70400 9 144 160 16
cert_test_block_3 70400 10 160 176 16
cert_test_block_3 70400 11 176 192 16
cert_test_block_3 70400 12 192 208 16
cert_test_block_3 70400 13 208 224 16
cert_test_block_3 70400 14 224 240 16
cert_test_block_3 70400 15 240 256 16
cert_test_block_3 70400 16 256 272 16
cert_test_block_3 70400 17 272 288 16
cert_test_block_3 70400 18 288 304 16
cert_test_block_3 70400 19 304 320 16
cert_test_block_3 70400 20 320 336 16
cert_test_block_3 70400 21 336 352 16
cert_test_block_3 70400 22 352 368 16
cert_test_block_3 70400 23 368 384 16
cert_test_block_3 70400 24 384 400 16
cert_test_block_3 70400 25 400 416 16
cert_test_block_3 70400 26 416 432 16
cert_test_block_3 70400 27 432 448 16
cert_test_block_3 70400 28 448 464 16
cert_test_block_3 70400 29 464 480 16
cert_test_block_3 70400 30 480 496 16
cert_test_block_3 70400 31 496 512 16
cert_test_block_3 70400 32 512 528 16
cert_test_block_3 70400 33 528 544 16
cert_test_block_3 70400 34 544 560 16
cert_test_block_3 70400 35 560 576 16
cert_test_block_3 70400 36 576 592 16
cert_test_block_3 70400 37 592 608 16
cert_test_block_3 70400 38 608 624 16
cert_test_block_3 70400 39 624 640 16
theorem test70400_complete : Interval test70400 0 640 :=
  (interval_append test70400 0 320 640
  (interval_append test70400 0 160 320
  (interval_append test70400 0 80 160
  (interval_append test70400 0 32 80
  (interval_append test70400 0 16 32
  test70400_block_0
  test70400_block_1)
  (interval_append test70400 32 48 80
  test70400_block_2
  (interval_append test70400 48 64 80
  test70400_block_3
  test70400_block_4)))
  (interval_append test70400 80 112 160
  (interval_append test70400 80 96 112
  test70400_block_5
  test70400_block_6)
  (interval_append test70400 112 128 160
  test70400_block_7
  (interval_append test70400 128 144 160
  test70400_block_8
  test70400_block_9))))
  (interval_append test70400 160 240 320
  (interval_append test70400 160 192 240
  (interval_append test70400 160 176 192
  test70400_block_10
  test70400_block_11)
  (interval_append test70400 192 208 240
  test70400_block_12
  (interval_append test70400 208 224 240
  test70400_block_13
  test70400_block_14)))
  (interval_append test70400 240 272 320
  (interval_append test70400 240 256 272
  test70400_block_15
  test70400_block_16)
  (interval_append test70400 272 288 320
  test70400_block_17
  (interval_append test70400 288 304 320
  test70400_block_18
  test70400_block_19)))))
  (interval_append test70400 320 480 640
  (interval_append test70400 320 400 480
  (interval_append test70400 320 352 400
  (interval_append test70400 320 336 352
  test70400_block_20
  test70400_block_21)
  (interval_append test70400 352 368 400
  test70400_block_22
  (interval_append test70400 368 384 400
  test70400_block_23
  test70400_block_24)))
  (interval_append test70400 400 432 480
  (interval_append test70400 400 416 432
  test70400_block_25
  test70400_block_26)
  (interval_append test70400 432 448 480
  test70400_block_27
  (interval_append test70400 448 464 480
  test70400_block_28
  test70400_block_29))))
  (interval_append test70400 480 560 640
  (interval_append test70400 480 512 560
  (interval_append test70400 480 496 512
  test70400_block_30
  test70400_block_31)
  (interval_append test70400 512 528 560
  test70400_block_32
  (interval_append test70400 528 544 560
  test70400_block_33
  test70400_block_34)))
  (interval_append test70400 560 592 640
  (interval_append test70400 560 576 592
  test70400_block_35
  test70400_block_36)
  (interval_append test70400 592 608 640
  test70400_block_37
  (interval_append test70400 608 624 640
  test70400_block_38
  test70400_block_39))))))
cert_nodeInterval_3 70400 71040
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
cert_test_11 71040
cert_test_block_3 71040 0 0 16 16
cert_test_block_3 71040 1 16 32 16
cert_test_block_3 71040 2 32 48 16
cert_test_block_3 71040 3 48 64 16
cert_test_block_3 71040 4 64 80 16
cert_test_block_3 71040 5 80 96 16
cert_test_block_3 71040 6 96 112 16
cert_test_block_3 71040 7 112 128 16
cert_test_block_3 71040 8 128 144 16
cert_test_block_3 71040 9 144 160 16
cert_test_block_3 71040 10 160 176 16
cert_test_block_3 71040 11 176 192 16
cert_test_block_3 71040 12 192 208 16
cert_test_block_3 71040 13 208 224 16
cert_test_block_3 71040 14 224 240 16
cert_test_block_3 71040 15 240 256 16
cert_test_block_3 71040 16 256 272 16
cert_test_block_3 71040 17 272 288 16
cert_test_block_3 71040 18 288 304 16
cert_test_block_3 71040 19 304 320 16
cert_test_block_3 71040 20 320 336 16
cert_test_block_3 71040 21 336 352 16
cert_test_block_3 71040 22 352 368 16
cert_test_block_3 71040 23 368 384 16
cert_test_block_3 71040 24 384 400 16
cert_test_block_3 71040 25 400 416 16
cert_test_block_3 71040 26 416 432 16
cert_test_block_3 71040 27 432 448 16
cert_test_block_3 71040 28 448 464 16
cert_test_block_3 71040 29 464 480 16
cert_test_block_3 71040 30 480 496 16
cert_test_block_3 71040 31 496 512 16
cert_test_block_3 71040 32 512 528 16
cert_test_block_3 71040 33 528 544 16
cert_test_block_3 71040 34 544 560 16
cert_test_block_3 71040 35 560 576 16
cert_test_block_3 71040 36 576 592 16
cert_test_block_3 71040 37 592 608 16
cert_test_block_3 71040 38 608 624 16
cert_test_block_3 71040 39 624 640 16
theorem test71040_complete : Interval test71040 0 640 :=
  (interval_append test71040 0 320 640
  (interval_append test71040 0 160 320
  (interval_append test71040 0 80 160
  (interval_append test71040 0 32 80
  (interval_append test71040 0 16 32
  test71040_block_0
  test71040_block_1)
  (interval_append test71040 32 48 80
  test71040_block_2
  (interval_append test71040 48 64 80
  test71040_block_3
  test71040_block_4)))
  (interval_append test71040 80 112 160
  (interval_append test71040 80 96 112
  test71040_block_5
  test71040_block_6)
  (interval_append test71040 112 128 160
  test71040_block_7
  (interval_append test71040 128 144 160
  test71040_block_8
  test71040_block_9))))
  (interval_append test71040 160 240 320
  (interval_append test71040 160 192 240
  (interval_append test71040 160 176 192
  test71040_block_10
  test71040_block_11)
  (interval_append test71040 192 208 240
  test71040_block_12
  (interval_append test71040 208 224 240
  test71040_block_13
  test71040_block_14)))
  (interval_append test71040 240 272 320
  (interval_append test71040 240 256 272
  test71040_block_15
  test71040_block_16)
  (interval_append test71040 272 288 320
  test71040_block_17
  (interval_append test71040 288 304 320
  test71040_block_18
  test71040_block_19)))))
  (interval_append test71040 320 480 640
  (interval_append test71040 320 400 480
  (interval_append test71040 320 352 400
  (interval_append test71040 320 336 352
  test71040_block_20
  test71040_block_21)
  (interval_append test71040 352 368 400
  test71040_block_22
  (interval_append test71040 368 384 400
  test71040_block_23
  test71040_block_24)))
  (interval_append test71040 400 432 480
  (interval_append test71040 400 416 432
  test71040_block_25
  test71040_block_26)
  (interval_append test71040 432 448 480
  test71040_block_27
  (interval_append test71040 448 464 480
  test71040_block_28
  test71040_block_29))))
  (interval_append test71040 480 560 640
  (interval_append test71040 480 512 560
  (interval_append test71040 480 496 512
  test71040_block_30
  test71040_block_31)
  (interval_append test71040 512 528 560
  test71040_block_32
  (interval_append test71040 528 544 560
  test71040_block_33
  test71040_block_34)))
  (interval_append test71040 560 592 640
  (interval_append test71040 560 576 592
  test71040_block_35
  test71040_block_36)
  (interval_append test71040 592 608 640
  test71040_block_37
  (interval_append test71040 608 624 640
  test71040_block_38
  test71040_block_39))))))
cert_nodeInterval_3 71040 71680
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
cert_test_11 71680
cert_test_block_3 71680 0 0 16 16
cert_test_block_3 71680 1 16 32 16
cert_test_block_3 71680 2 32 48 16
cert_test_block_3 71680 3 48 64 16
cert_test_block_3 71680 4 64 80 16
cert_test_block_3 71680 5 80 96 16
cert_test_block_3 71680 6 96 112 16
cert_test_block_3 71680 7 112 128 16
cert_test_block_3 71680 8 128 144 16
cert_test_block_3 71680 9 144 160 16
cert_test_block_3 71680 10 160 176 16
cert_test_block_3 71680 11 176 192 16
cert_test_block_3 71680 12 192 208 16
cert_test_block_3 71680 13 208 224 16
cert_test_block_3 71680 14 224 240 16
cert_test_block_3 71680 15 240 256 16
cert_test_block_3 71680 16 256 272 16
cert_test_block_3 71680 17 272 288 16
cert_test_block_3 71680 18 288 304 16
cert_test_block_3 71680 19 304 320 16
cert_test_block_3 71680 20 320 336 16
cert_test_block_3 71680 21 336 352 16
cert_test_block_3 71680 22 352 368 16
cert_test_block_3 71680 23 368 384 16
cert_test_block_3 71680 24 384 400 16
cert_test_block_3 71680 25 400 416 16
cert_test_block_3 71680 26 416 432 16
cert_test_block_3 71680 27 432 448 16
cert_test_block_3 71680 28 448 464 16
cert_test_block_3 71680 29 464 480 16
cert_test_block_3 71680 30 480 496 16
cert_test_block_3 71680 31 496 512 16
cert_test_block_3 71680 32 512 528 16
cert_test_block_3 71680 33 528 544 16
cert_test_block_3 71680 34 544 560 16
cert_test_block_3 71680 35 560 576 16
cert_test_block_3 71680 36 576 592 16
cert_test_block_3 71680 37 592 608 16
cert_test_block_3 71680 38 608 624 16
cert_test_block_3 71680 39 624 640 16
theorem test71680_complete : Interval test71680 0 640 :=
  (interval_append test71680 0 320 640
  (interval_append test71680 0 160 320
  (interval_append test71680 0 80 160
  (interval_append test71680 0 32 80
  (interval_append test71680 0 16 32
  test71680_block_0
  test71680_block_1)
  (interval_append test71680 32 48 80
  test71680_block_2
  (interval_append test71680 48 64 80
  test71680_block_3
  test71680_block_4)))
  (interval_append test71680 80 112 160
  (interval_append test71680 80 96 112
  test71680_block_5
  test71680_block_6)
  (interval_append test71680 112 128 160
  test71680_block_7
  (interval_append test71680 128 144 160
  test71680_block_8
  test71680_block_9))))
  (interval_append test71680 160 240 320
  (interval_append test71680 160 192 240
  (interval_append test71680 160 176 192
  test71680_block_10
  test71680_block_11)
  (interval_append test71680 192 208 240
  test71680_block_12
  (interval_append test71680 208 224 240
  test71680_block_13
  test71680_block_14)))
  (interval_append test71680 240 272 320
  (interval_append test71680 240 256 272
  test71680_block_15
  test71680_block_16)
  (interval_append test71680 272 288 320
  test71680_block_17
  (interval_append test71680 288 304 320
  test71680_block_18
  test71680_block_19)))))
  (interval_append test71680 320 480 640
  (interval_append test71680 320 400 480
  (interval_append test71680 320 352 400
  (interval_append test71680 320 336 352
  test71680_block_20
  test71680_block_21)
  (interval_append test71680 352 368 400
  test71680_block_22
  (interval_append test71680 368 384 400
  test71680_block_23
  test71680_block_24)))
  (interval_append test71680 400 432 480
  (interval_append test71680 400 416 432
  test71680_block_25
  test71680_block_26)
  (interval_append test71680 432 448 480
  test71680_block_27
  (interval_append test71680 448 464 480
  test71680_block_28
  test71680_block_29))))
  (interval_append test71680 480 560 640
  (interval_append test71680 480 512 560
  (interval_append test71680 480 496 512
  test71680_block_30
  test71680_block_31)
  (interval_append test71680 512 528 560
  test71680_block_32
  (interval_append test71680 528 544 560
  test71680_block_33
  test71680_block_34)))
  (interval_append test71680 560 592 640
  (interval_append test71680 560 576 592
  test71680_block_35
  test71680_block_36)
  (interval_append test71680 592 608 640
  test71680_block_37
  (interval_append test71680 608 624 640
  test71680_block_38
  test71680_block_39))))))
cert_nodeInterval_3 71680 72320
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
cert_test_11 72320
cert_test_block_3 72320 0 0 16 16
cert_test_block_3 72320 1 16 32 16
cert_test_block_3 72320 2 32 48 16
cert_test_block_3 72320 3 48 64 16
cert_test_block_3 72320 4 64 80 16
cert_test_block_3 72320 5 80 96 16
cert_test_block_3 72320 6 96 112 16
cert_test_block_3 72320 7 112 128 16
cert_test_block_3 72320 8 128 144 16
cert_test_block_3 72320 9 144 160 16
cert_test_block_3 72320 10 160 176 16
cert_test_block_3 72320 11 176 192 16
cert_test_block_3 72320 12 192 208 16
cert_test_block_3 72320 13 208 224 16
cert_test_block_3 72320 14 224 240 16
cert_test_block_3 72320 15 240 256 16
cert_test_block_3 72320 16 256 272 16
cert_test_block_3 72320 17 272 288 16
cert_test_block_3 72320 18 288 304 16
cert_test_block_3 72320 19 304 320 16
cert_test_block_3 72320 20 320 336 16
cert_test_block_3 72320 21 336 352 16
cert_test_block_3 72320 22 352 368 16
cert_test_block_3 72320 23 368 384 16
cert_test_block_3 72320 24 384 400 16
cert_test_block_3 72320 25 400 416 16
cert_test_block_3 72320 26 416 432 16
cert_test_block_3 72320 27 432 448 16
cert_test_block_3 72320 28 448 464 16
cert_test_block_3 72320 29 464 480 16
cert_test_block_3 72320 30 480 496 16
cert_test_block_3 72320 31 496 512 16
cert_test_block_3 72320 32 512 528 16
cert_test_block_3 72320 33 528 544 16
cert_test_block_3 72320 34 544 560 16
cert_test_block_3 72320 35 560 576 16
cert_test_block_3 72320 36 576 592 16
cert_test_block_3 72320 37 592 608 16
cert_test_block_3 72320 38 608 624 16
cert_test_block_3 72320 39 624 640 16
theorem test72320_complete : Interval test72320 0 640 :=
  (interval_append test72320 0 320 640
  (interval_append test72320 0 160 320
  (interval_append test72320 0 80 160
  (interval_append test72320 0 32 80
  (interval_append test72320 0 16 32
  test72320_block_0
  test72320_block_1)
  (interval_append test72320 32 48 80
  test72320_block_2
  (interval_append test72320 48 64 80
  test72320_block_3
  test72320_block_4)))
  (interval_append test72320 80 112 160
  (interval_append test72320 80 96 112
  test72320_block_5
  test72320_block_6)
  (interval_append test72320 112 128 160
  test72320_block_7
  (interval_append test72320 128 144 160
  test72320_block_8
  test72320_block_9))))
  (interval_append test72320 160 240 320
  (interval_append test72320 160 192 240
  (interval_append test72320 160 176 192
  test72320_block_10
  test72320_block_11)
  (interval_append test72320 192 208 240
  test72320_block_12
  (interval_append test72320 208 224 240
  test72320_block_13
  test72320_block_14)))
  (interval_append test72320 240 272 320
  (interval_append test72320 240 256 272
  test72320_block_15
  test72320_block_16)
  (interval_append test72320 272 288 320
  test72320_block_17
  (interval_append test72320 288 304 320
  test72320_block_18
  test72320_block_19)))))
  (interval_append test72320 320 480 640
  (interval_append test72320 320 400 480
  (interval_append test72320 320 352 400
  (interval_append test72320 320 336 352
  test72320_block_20
  test72320_block_21)
  (interval_append test72320 352 368 400
  test72320_block_22
  (interval_append test72320 368 384 400
  test72320_block_23
  test72320_block_24)))
  (interval_append test72320 400 432 480
  (interval_append test72320 400 416 432
  test72320_block_25
  test72320_block_26)
  (interval_append test72320 432 448 480
  test72320_block_27
  (interval_append test72320 448 464 480
  test72320_block_28
  test72320_block_29))))
  (interval_append test72320 480 560 640
  (interval_append test72320 480 512 560
  (interval_append test72320 480 496 512
  test72320_block_30
  test72320_block_31)
  (interval_append test72320 512 528 560
  test72320_block_32
  (interval_append test72320 528 544 560
  test72320_block_33
  test72320_block_34)))
  (interval_append test72320 560 592 640
  (interval_append test72320 560 576 592
  test72320_block_35
  test72320_block_36)
  (interval_append test72320 592 608 640
  test72320_block_37
  (interval_append test72320 608 624 640
  test72320_block_38
  test72320_block_39))))))
cert_nodeInterval_3 72320 72960
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
cert_test_11 72960
cert_test_block_3 72960 0 0 16 16
cert_test_block_3 72960 1 16 32 16
cert_test_block_3 72960 2 32 48 16
cert_test_block_3 72960 3 48 64 16
cert_test_block_3 72960 4 64 80 16
cert_test_block_3 72960 5 80 96 16
cert_test_block_3 72960 6 96 112 16
cert_test_block_3 72960 7 112 128 16
cert_test_block_3 72960 8 128 144 16
cert_test_block_3 72960 9 144 160 16
cert_test_block_3 72960 10 160 176 16
cert_test_block_3 72960 11 176 192 16
cert_test_block_3 72960 12 192 208 16
cert_test_block_3 72960 13 208 224 16
cert_test_block_3 72960 14 224 240 16
cert_test_block_3 72960 15 240 256 16
cert_test_block_3 72960 16 256 272 16
cert_test_block_3 72960 17 272 288 16
cert_test_block_3 72960 18 288 304 16
cert_test_block_3 72960 19 304 320 16
cert_test_block_3 72960 20 320 336 16
cert_test_block_3 72960 21 336 352 16
cert_test_block_3 72960 22 352 368 16
cert_test_block_3 72960 23 368 384 16
cert_test_block_3 72960 24 384 400 16
cert_test_block_3 72960 25 400 416 16
cert_test_block_3 72960 26 416 432 16
cert_test_block_3 72960 27 432 448 16
cert_test_block_3 72960 28 448 464 16
cert_test_block_3 72960 29 464 480 16
cert_test_block_3 72960 30 480 496 16
cert_test_block_3 72960 31 496 512 16
cert_test_block_3 72960 32 512 528 16
cert_test_block_3 72960 33 528 544 16
cert_test_block_3 72960 34 544 560 16
cert_test_block_3 72960 35 560 576 16
cert_test_block_3 72960 36 576 592 16
cert_test_block_3 72960 37 592 608 16
cert_test_block_3 72960 38 608 624 16
cert_test_block_3 72960 39 624 640 16
theorem test72960_complete : Interval test72960 0 640 :=
  (interval_append test72960 0 320 640
  (interval_append test72960 0 160 320
  (interval_append test72960 0 80 160
  (interval_append test72960 0 32 80
  (interval_append test72960 0 16 32
  test72960_block_0
  test72960_block_1)
  (interval_append test72960 32 48 80
  test72960_block_2
  (interval_append test72960 48 64 80
  test72960_block_3
  test72960_block_4)))
  (interval_append test72960 80 112 160
  (interval_append test72960 80 96 112
  test72960_block_5
  test72960_block_6)
  (interval_append test72960 112 128 160
  test72960_block_7
  (interval_append test72960 128 144 160
  test72960_block_8
  test72960_block_9))))
  (interval_append test72960 160 240 320
  (interval_append test72960 160 192 240
  (interval_append test72960 160 176 192
  test72960_block_10
  test72960_block_11)
  (interval_append test72960 192 208 240
  test72960_block_12
  (interval_append test72960 208 224 240
  test72960_block_13
  test72960_block_14)))
  (interval_append test72960 240 272 320
  (interval_append test72960 240 256 272
  test72960_block_15
  test72960_block_16)
  (interval_append test72960 272 288 320
  test72960_block_17
  (interval_append test72960 288 304 320
  test72960_block_18
  test72960_block_19)))))
  (interval_append test72960 320 480 640
  (interval_append test72960 320 400 480
  (interval_append test72960 320 352 400
  (interval_append test72960 320 336 352
  test72960_block_20
  test72960_block_21)
  (interval_append test72960 352 368 400
  test72960_block_22
  (interval_append test72960 368 384 400
  test72960_block_23
  test72960_block_24)))
  (interval_append test72960 400 432 480
  (interval_append test72960 400 416 432
  test72960_block_25
  test72960_block_26)
  (interval_append test72960 432 448 480
  test72960_block_27
  (interval_append test72960 448 464 480
  test72960_block_28
  test72960_block_29))))
  (interval_append test72960 480 560 640
  (interval_append test72960 480 512 560
  (interval_append test72960 480 496 512
  test72960_block_30
  test72960_block_31)
  (interval_append test72960 512 528 560
  test72960_block_32
  (interval_append test72960 528 544 560
  test72960_block_33
  test72960_block_34)))
  (interval_append test72960 560 592 640
  (interval_append test72960 560 576 592
  test72960_block_35
  test72960_block_36)
  (interval_append test72960 592 608 640
  test72960_block_37
  (interval_append test72960 608 624 640
  test72960_block_38
  test72960_block_39))))))
cert_nodeInterval_3 72960 73600
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
cert_test_11 73600
cert_test_block_3 73600 0 0 16 16
cert_test_block_3 73600 1 16 32 16
cert_test_block_3 73600 2 32 48 16
cert_test_block_3 73600 3 48 64 16
cert_test_block_3 73600 4 64 80 16
cert_test_block_3 73600 5 80 96 16
cert_test_block_3 73600 6 96 112 16
cert_test_block_3 73600 7 112 128 16
cert_test_block_3 73600 8 128 144 16
cert_test_block_3 73600 9 144 160 16
cert_test_block_3 73600 10 160 176 16
cert_test_block_3 73600 11 176 192 16
cert_test_block_3 73600 12 192 208 16
cert_test_block_3 73600 13 208 224 16
cert_test_block_3 73600 14 224 240 16
cert_test_block_3 73600 15 240 256 16
cert_test_block_3 73600 16 256 272 16
cert_test_block_3 73600 17 272 288 16
cert_test_block_3 73600 18 288 304 16
cert_test_block_3 73600 19 304 320 16
cert_test_block_3 73600 20 320 336 16
cert_test_block_3 73600 21 336 352 16
cert_test_block_3 73600 22 352 368 16
cert_test_block_3 73600 23 368 384 16
cert_test_block_3 73600 24 384 400 16
cert_test_block_3 73600 25 400 416 16
cert_test_block_3 73600 26 416 432 16
cert_test_block_3 73600 27 432 448 16
cert_test_block_3 73600 28 448 464 16
cert_test_block_3 73600 29 464 480 16
cert_test_block_3 73600 30 480 496 16
cert_test_block_3 73600 31 496 512 16
cert_test_block_3 73600 32 512 528 16
cert_test_block_3 73600 33 528 544 16
cert_test_block_3 73600 34 544 560 16
cert_test_block_3 73600 35 560 576 16
cert_test_block_3 73600 36 576 592 16
cert_test_block_3 73600 37 592 608 16
cert_test_block_3 73600 38 608 624 16
cert_test_block_3 73600 39 624 640 16
theorem test73600_complete : Interval test73600 0 640 :=
  (interval_append test73600 0 320 640
  (interval_append test73600 0 160 320
  (interval_append test73600 0 80 160
  (interval_append test73600 0 32 80
  (interval_append test73600 0 16 32
  test73600_block_0
  test73600_block_1)
  (interval_append test73600 32 48 80
  test73600_block_2
  (interval_append test73600 48 64 80
  test73600_block_3
  test73600_block_4)))
  (interval_append test73600 80 112 160
  (interval_append test73600 80 96 112
  test73600_block_5
  test73600_block_6)
  (interval_append test73600 112 128 160
  test73600_block_7
  (interval_append test73600 128 144 160
  test73600_block_8
  test73600_block_9))))
  (interval_append test73600 160 240 320
  (interval_append test73600 160 192 240
  (interval_append test73600 160 176 192
  test73600_block_10
  test73600_block_11)
  (interval_append test73600 192 208 240
  test73600_block_12
  (interval_append test73600 208 224 240
  test73600_block_13
  test73600_block_14)))
  (interval_append test73600 240 272 320
  (interval_append test73600 240 256 272
  test73600_block_15
  test73600_block_16)
  (interval_append test73600 272 288 320
  test73600_block_17
  (interval_append test73600 288 304 320
  test73600_block_18
  test73600_block_19)))))
  (interval_append test73600 320 480 640
  (interval_append test73600 320 400 480
  (interval_append test73600 320 352 400
  (interval_append test73600 320 336 352
  test73600_block_20
  test73600_block_21)
  (interval_append test73600 352 368 400
  test73600_block_22
  (interval_append test73600 368 384 400
  test73600_block_23
  test73600_block_24)))
  (interval_append test73600 400 432 480
  (interval_append test73600 400 416 432
  test73600_block_25
  test73600_block_26)
  (interval_append test73600 432 448 480
  test73600_block_27
  (interval_append test73600 448 464 480
  test73600_block_28
  test73600_block_29))))
  (interval_append test73600 480 560 640
  (interval_append test73600 480 512 560
  (interval_append test73600 480 496 512
  test73600_block_30
  test73600_block_31)
  (interval_append test73600 512 528 560
  test73600_block_32
  (interval_append test73600 528 544 560
  test73600_block_33
  test73600_block_34)))
  (interval_append test73600 560 592 640
  (interval_append test73600 560 576 592
  test73600_block_35
  test73600_block_36)
  (interval_append test73600 592 608 640
  test73600_block_37
  (interval_append test73600 608 624 640
  test73600_block_38
  test73600_block_39))))))
cert_nodeInterval_3 73600 74240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
