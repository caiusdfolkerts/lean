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
cert_test_11 84480
cert_test_block_3 84480 0 0 16 16
cert_test_block_3 84480 1 16 32 16
cert_test_block_3 84480 2 32 48 16
cert_test_block_3 84480 3 48 64 16
cert_test_block_3 84480 4 64 80 16
cert_test_block_3 84480 5 80 96 16
cert_test_block_3 84480 6 96 112 16
cert_test_block_3 84480 7 112 128 16
cert_test_block_3 84480 8 128 144 16
cert_test_block_3 84480 9 144 160 16
cert_test_block_3 84480 10 160 176 16
cert_test_block_3 84480 11 176 192 16
cert_test_block_3 84480 12 192 208 16
cert_test_block_3 84480 13 208 224 16
cert_test_block_3 84480 14 224 240 16
cert_test_block_3 84480 15 240 256 16
cert_test_block_3 84480 16 256 272 16
cert_test_block_3 84480 17 272 288 16
cert_test_block_3 84480 18 288 304 16
cert_test_block_3 84480 19 304 320 16
cert_test_block_3 84480 20 320 336 16
cert_test_block_3 84480 21 336 352 16
cert_test_block_3 84480 22 352 368 16
cert_test_block_3 84480 23 368 384 16
cert_test_block_3 84480 24 384 400 16
cert_test_block_3 84480 25 400 416 16
cert_test_block_3 84480 26 416 432 16
cert_test_block_3 84480 27 432 448 16
cert_test_block_3 84480 28 448 464 16
cert_test_block_3 84480 29 464 480 16
cert_test_block_3 84480 30 480 496 16
cert_test_block_3 84480 31 496 512 16
cert_test_block_3 84480 32 512 528 16
cert_test_block_3 84480 33 528 544 16
cert_test_block_3 84480 34 544 560 16
cert_test_block_3 84480 35 560 576 16
cert_test_block_3 84480 36 576 592 16
cert_test_block_3 84480 37 592 608 16
cert_test_block_3 84480 38 608 624 16
cert_test_block_3 84480 39 624 640 16
theorem test84480_complete : Interval test84480 0 640 :=
  (interval_append test84480 0 320 640
  (interval_append test84480 0 160 320
  (interval_append test84480 0 80 160
  (interval_append test84480 0 32 80
  (interval_append test84480 0 16 32
  test84480_block_0
  test84480_block_1)
  (interval_append test84480 32 48 80
  test84480_block_2
  (interval_append test84480 48 64 80
  test84480_block_3
  test84480_block_4)))
  (interval_append test84480 80 112 160
  (interval_append test84480 80 96 112
  test84480_block_5
  test84480_block_6)
  (interval_append test84480 112 128 160
  test84480_block_7
  (interval_append test84480 128 144 160
  test84480_block_8
  test84480_block_9))))
  (interval_append test84480 160 240 320
  (interval_append test84480 160 192 240
  (interval_append test84480 160 176 192
  test84480_block_10
  test84480_block_11)
  (interval_append test84480 192 208 240
  test84480_block_12
  (interval_append test84480 208 224 240
  test84480_block_13
  test84480_block_14)))
  (interval_append test84480 240 272 320
  (interval_append test84480 240 256 272
  test84480_block_15
  test84480_block_16)
  (interval_append test84480 272 288 320
  test84480_block_17
  (interval_append test84480 288 304 320
  test84480_block_18
  test84480_block_19)))))
  (interval_append test84480 320 480 640
  (interval_append test84480 320 400 480
  (interval_append test84480 320 352 400
  (interval_append test84480 320 336 352
  test84480_block_20
  test84480_block_21)
  (interval_append test84480 352 368 400
  test84480_block_22
  (interval_append test84480 368 384 400
  test84480_block_23
  test84480_block_24)))
  (interval_append test84480 400 432 480
  (interval_append test84480 400 416 432
  test84480_block_25
  test84480_block_26)
  (interval_append test84480 432 448 480
  test84480_block_27
  (interval_append test84480 448 464 480
  test84480_block_28
  test84480_block_29))))
  (interval_append test84480 480 560 640
  (interval_append test84480 480 512 560
  (interval_append test84480 480 496 512
  test84480_block_30
  test84480_block_31)
  (interval_append test84480 512 528 560
  test84480_block_32
  (interval_append test84480 528 544 560
  test84480_block_33
  test84480_block_34)))
  (interval_append test84480 560 592 640
  (interval_append test84480 560 576 592
  test84480_block_35
  test84480_block_36)
  (interval_append test84480 592 608 640
  test84480_block_37
  (interval_append test84480 608 624 640
  test84480_block_38
  test84480_block_39))))))
cert_nodeInterval_3 84480 85120
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
cert_test_11 85120
cert_test_block_3 85120 0 0 16 16
cert_test_block_3 85120 1 16 32 16
cert_test_block_3 85120 2 32 48 16
cert_test_block_3 85120 3 48 64 16
cert_test_block_3 85120 4 64 80 16
cert_test_block_3 85120 5 80 96 16
cert_test_block_3 85120 6 96 112 16
cert_test_block_3 85120 7 112 128 16
cert_test_block_3 85120 8 128 144 16
cert_test_block_3 85120 9 144 160 16
cert_test_block_3 85120 10 160 176 16
cert_test_block_3 85120 11 176 192 16
cert_test_block_3 85120 12 192 208 16
cert_test_block_3 85120 13 208 224 16
cert_test_block_3 85120 14 224 240 16
cert_test_block_3 85120 15 240 256 16
cert_test_block_3 85120 16 256 272 16
cert_test_block_3 85120 17 272 288 16
cert_test_block_3 85120 18 288 304 16
cert_test_block_3 85120 19 304 320 16
cert_test_block_3 85120 20 320 336 16
cert_test_block_3 85120 21 336 352 16
cert_test_block_3 85120 22 352 368 16
cert_test_block_3 85120 23 368 384 16
cert_test_block_3 85120 24 384 400 16
cert_test_block_3 85120 25 400 416 16
cert_test_block_3 85120 26 416 432 16
cert_test_block_3 85120 27 432 448 16
cert_test_block_3 85120 28 448 464 16
cert_test_block_3 85120 29 464 480 16
cert_test_block_3 85120 30 480 496 16
cert_test_block_3 85120 31 496 512 16
cert_test_block_3 85120 32 512 528 16
cert_test_block_3 85120 33 528 544 16
cert_test_block_3 85120 34 544 560 16
cert_test_block_3 85120 35 560 576 16
cert_test_block_3 85120 36 576 592 16
cert_test_block_3 85120 37 592 608 16
cert_test_block_3 85120 38 608 624 16
cert_test_block_3 85120 39 624 640 16
theorem test85120_complete : Interval test85120 0 640 :=
  (interval_append test85120 0 320 640
  (interval_append test85120 0 160 320
  (interval_append test85120 0 80 160
  (interval_append test85120 0 32 80
  (interval_append test85120 0 16 32
  test85120_block_0
  test85120_block_1)
  (interval_append test85120 32 48 80
  test85120_block_2
  (interval_append test85120 48 64 80
  test85120_block_3
  test85120_block_4)))
  (interval_append test85120 80 112 160
  (interval_append test85120 80 96 112
  test85120_block_5
  test85120_block_6)
  (interval_append test85120 112 128 160
  test85120_block_7
  (interval_append test85120 128 144 160
  test85120_block_8
  test85120_block_9))))
  (interval_append test85120 160 240 320
  (interval_append test85120 160 192 240
  (interval_append test85120 160 176 192
  test85120_block_10
  test85120_block_11)
  (interval_append test85120 192 208 240
  test85120_block_12
  (interval_append test85120 208 224 240
  test85120_block_13
  test85120_block_14)))
  (interval_append test85120 240 272 320
  (interval_append test85120 240 256 272
  test85120_block_15
  test85120_block_16)
  (interval_append test85120 272 288 320
  test85120_block_17
  (interval_append test85120 288 304 320
  test85120_block_18
  test85120_block_19)))))
  (interval_append test85120 320 480 640
  (interval_append test85120 320 400 480
  (interval_append test85120 320 352 400
  (interval_append test85120 320 336 352
  test85120_block_20
  test85120_block_21)
  (interval_append test85120 352 368 400
  test85120_block_22
  (interval_append test85120 368 384 400
  test85120_block_23
  test85120_block_24)))
  (interval_append test85120 400 432 480
  (interval_append test85120 400 416 432
  test85120_block_25
  test85120_block_26)
  (interval_append test85120 432 448 480
  test85120_block_27
  (interval_append test85120 448 464 480
  test85120_block_28
  test85120_block_29))))
  (interval_append test85120 480 560 640
  (interval_append test85120 480 512 560
  (interval_append test85120 480 496 512
  test85120_block_30
  test85120_block_31)
  (interval_append test85120 512 528 560
  test85120_block_32
  (interval_append test85120 528 544 560
  test85120_block_33
  test85120_block_34)))
  (interval_append test85120 560 592 640
  (interval_append test85120 560 576 592
  test85120_block_35
  test85120_block_36)
  (interval_append test85120 592 608 640
  test85120_block_37
  (interval_append test85120 608 624 640
  test85120_block_38
  test85120_block_39))))))
cert_nodeInterval_3 85120 85760
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
cert_test_11 85760
cert_test_block_3 85760 0 0 16 16
cert_test_block_3 85760 1 16 32 16
cert_test_block_3 85760 2 32 48 16
cert_test_block_3 85760 3 48 64 16
cert_test_block_3 85760 4 64 80 16
cert_test_block_3 85760 5 80 96 16
cert_test_block_3 85760 6 96 112 16
cert_test_block_3 85760 7 112 128 16
cert_test_block_3 85760 8 128 144 16
cert_test_block_3 85760 9 144 160 16
cert_test_block_3 85760 10 160 176 16
cert_test_block_3 85760 11 176 192 16
cert_test_block_3 85760 12 192 208 16
cert_test_block_3 85760 13 208 224 16
cert_test_block_3 85760 14 224 240 16
cert_test_block_3 85760 15 240 256 16
cert_test_block_3 85760 16 256 272 16
cert_test_block_3 85760 17 272 288 16
cert_test_block_3 85760 18 288 304 16
cert_test_block_3 85760 19 304 320 16
cert_test_block_3 85760 20 320 336 16
cert_test_block_3 85760 21 336 352 16
cert_test_block_3 85760 22 352 368 16
cert_test_block_3 85760 23 368 384 16
cert_test_block_3 85760 24 384 400 16
cert_test_block_3 85760 25 400 416 16
cert_test_block_3 85760 26 416 432 16
cert_test_block_3 85760 27 432 448 16
cert_test_block_3 85760 28 448 464 16
cert_test_block_3 85760 29 464 480 16
cert_test_block_3 85760 30 480 496 16
cert_test_block_3 85760 31 496 512 16
cert_test_block_3 85760 32 512 528 16
cert_test_block_3 85760 33 528 544 16
cert_test_block_3 85760 34 544 560 16
cert_test_block_3 85760 35 560 576 16
cert_test_block_3 85760 36 576 592 16
cert_test_block_3 85760 37 592 608 16
cert_test_block_3 85760 38 608 624 16
cert_test_block_3 85760 39 624 640 16
theorem test85760_complete : Interval test85760 0 640 :=
  (interval_append test85760 0 320 640
  (interval_append test85760 0 160 320
  (interval_append test85760 0 80 160
  (interval_append test85760 0 32 80
  (interval_append test85760 0 16 32
  test85760_block_0
  test85760_block_1)
  (interval_append test85760 32 48 80
  test85760_block_2
  (interval_append test85760 48 64 80
  test85760_block_3
  test85760_block_4)))
  (interval_append test85760 80 112 160
  (interval_append test85760 80 96 112
  test85760_block_5
  test85760_block_6)
  (interval_append test85760 112 128 160
  test85760_block_7
  (interval_append test85760 128 144 160
  test85760_block_8
  test85760_block_9))))
  (interval_append test85760 160 240 320
  (interval_append test85760 160 192 240
  (interval_append test85760 160 176 192
  test85760_block_10
  test85760_block_11)
  (interval_append test85760 192 208 240
  test85760_block_12
  (interval_append test85760 208 224 240
  test85760_block_13
  test85760_block_14)))
  (interval_append test85760 240 272 320
  (interval_append test85760 240 256 272
  test85760_block_15
  test85760_block_16)
  (interval_append test85760 272 288 320
  test85760_block_17
  (interval_append test85760 288 304 320
  test85760_block_18
  test85760_block_19)))))
  (interval_append test85760 320 480 640
  (interval_append test85760 320 400 480
  (interval_append test85760 320 352 400
  (interval_append test85760 320 336 352
  test85760_block_20
  test85760_block_21)
  (interval_append test85760 352 368 400
  test85760_block_22
  (interval_append test85760 368 384 400
  test85760_block_23
  test85760_block_24)))
  (interval_append test85760 400 432 480
  (interval_append test85760 400 416 432
  test85760_block_25
  test85760_block_26)
  (interval_append test85760 432 448 480
  test85760_block_27
  (interval_append test85760 448 464 480
  test85760_block_28
  test85760_block_29))))
  (interval_append test85760 480 560 640
  (interval_append test85760 480 512 560
  (interval_append test85760 480 496 512
  test85760_block_30
  test85760_block_31)
  (interval_append test85760 512 528 560
  test85760_block_32
  (interval_append test85760 528 544 560
  test85760_block_33
  test85760_block_34)))
  (interval_append test85760 560 592 640
  (interval_append test85760 560 576 592
  test85760_block_35
  test85760_block_36)
  (interval_append test85760 592 608 640
  test85760_block_37
  (interval_append test85760 608 624 640
  test85760_block_38
  test85760_block_39))))))
cert_nodeInterval_3 85760 86400
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
cert_test_11 86400
cert_test_block_3 86400 0 0 16 16
cert_test_block_3 86400 1 16 32 16
cert_test_block_3 86400 2 32 48 16
cert_test_block_3 86400 3 48 64 16
cert_test_block_3 86400 4 64 80 16
cert_test_block_3 86400 5 80 96 16
cert_test_block_3 86400 6 96 112 16
cert_test_block_3 86400 7 112 128 16
cert_test_block_3 86400 8 128 144 16
cert_test_block_3 86400 9 144 160 16
cert_test_block_3 86400 10 160 176 16
cert_test_block_3 86400 11 176 192 16
cert_test_block_3 86400 12 192 208 16
cert_test_block_3 86400 13 208 224 16
cert_test_block_3 86400 14 224 240 16
cert_test_block_3 86400 15 240 256 16
cert_test_block_3 86400 16 256 272 16
cert_test_block_3 86400 17 272 288 16
cert_test_block_3 86400 18 288 304 16
cert_test_block_3 86400 19 304 320 16
cert_test_block_3 86400 20 320 336 16
cert_test_block_3 86400 21 336 352 16
cert_test_block_3 86400 22 352 368 16
cert_test_block_3 86400 23 368 384 16
cert_test_block_3 86400 24 384 400 16
cert_test_block_3 86400 25 400 416 16
cert_test_block_3 86400 26 416 432 16
cert_test_block_3 86400 27 432 448 16
cert_test_block_3 86400 28 448 464 16
cert_test_block_3 86400 29 464 480 16
cert_test_block_3 86400 30 480 496 16
cert_test_block_3 86400 31 496 512 16
cert_test_block_3 86400 32 512 528 16
cert_test_block_3 86400 33 528 544 16
cert_test_block_3 86400 34 544 560 16
cert_test_block_3 86400 35 560 576 16
cert_test_block_3 86400 36 576 592 16
cert_test_block_3 86400 37 592 608 16
cert_test_block_3 86400 38 608 624 16
cert_test_block_3 86400 39 624 640 16
theorem test86400_complete : Interval test86400 0 640 :=
  (interval_append test86400 0 320 640
  (interval_append test86400 0 160 320
  (interval_append test86400 0 80 160
  (interval_append test86400 0 32 80
  (interval_append test86400 0 16 32
  test86400_block_0
  test86400_block_1)
  (interval_append test86400 32 48 80
  test86400_block_2
  (interval_append test86400 48 64 80
  test86400_block_3
  test86400_block_4)))
  (interval_append test86400 80 112 160
  (interval_append test86400 80 96 112
  test86400_block_5
  test86400_block_6)
  (interval_append test86400 112 128 160
  test86400_block_7
  (interval_append test86400 128 144 160
  test86400_block_8
  test86400_block_9))))
  (interval_append test86400 160 240 320
  (interval_append test86400 160 192 240
  (interval_append test86400 160 176 192
  test86400_block_10
  test86400_block_11)
  (interval_append test86400 192 208 240
  test86400_block_12
  (interval_append test86400 208 224 240
  test86400_block_13
  test86400_block_14)))
  (interval_append test86400 240 272 320
  (interval_append test86400 240 256 272
  test86400_block_15
  test86400_block_16)
  (interval_append test86400 272 288 320
  test86400_block_17
  (interval_append test86400 288 304 320
  test86400_block_18
  test86400_block_19)))))
  (interval_append test86400 320 480 640
  (interval_append test86400 320 400 480
  (interval_append test86400 320 352 400
  (interval_append test86400 320 336 352
  test86400_block_20
  test86400_block_21)
  (interval_append test86400 352 368 400
  test86400_block_22
  (interval_append test86400 368 384 400
  test86400_block_23
  test86400_block_24)))
  (interval_append test86400 400 432 480
  (interval_append test86400 400 416 432
  test86400_block_25
  test86400_block_26)
  (interval_append test86400 432 448 480
  test86400_block_27
  (interval_append test86400 448 464 480
  test86400_block_28
  test86400_block_29))))
  (interval_append test86400 480 560 640
  (interval_append test86400 480 512 560
  (interval_append test86400 480 496 512
  test86400_block_30
  test86400_block_31)
  (interval_append test86400 512 528 560
  test86400_block_32
  (interval_append test86400 528 544 560
  test86400_block_33
  test86400_block_34)))
  (interval_append test86400 560 592 640
  (interval_append test86400 560 576 592
  test86400_block_35
  test86400_block_36)
  (interval_append test86400 592 608 640
  test86400_block_37
  (interval_append test86400 608 624 640
  test86400_block_38
  test86400_block_39))))))
cert_nodeInterval_3 86400 87040
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
cert_test_11 87040
cert_test_block_3 87040 0 0 16 16
cert_test_block_3 87040 1 16 32 16
cert_test_block_3 87040 2 32 48 16
cert_test_block_3 87040 3 48 64 16
cert_test_block_3 87040 4 64 80 16
cert_test_block_3 87040 5 80 96 16
cert_test_block_3 87040 6 96 112 16
cert_test_block_3 87040 7 112 128 16
cert_test_block_3 87040 8 128 144 16
cert_test_block_3 87040 9 144 160 16
cert_test_block_3 87040 10 160 176 16
cert_test_block_3 87040 11 176 192 16
cert_test_block_3 87040 12 192 208 16
cert_test_block_3 87040 13 208 224 16
cert_test_block_3 87040 14 224 240 16
cert_test_block_3 87040 15 240 256 16
cert_test_block_3 87040 16 256 272 16
cert_test_block_3 87040 17 272 288 16
cert_test_block_3 87040 18 288 304 16
cert_test_block_3 87040 19 304 320 16
cert_test_block_3 87040 20 320 336 16
cert_test_block_3 87040 21 336 352 16
cert_test_block_3 87040 22 352 368 16
cert_test_block_3 87040 23 368 384 16
cert_test_block_3 87040 24 384 400 16
cert_test_block_3 87040 25 400 416 16
cert_test_block_3 87040 26 416 432 16
cert_test_block_3 87040 27 432 448 16
cert_test_block_3 87040 28 448 464 16
cert_test_block_3 87040 29 464 480 16
cert_test_block_3 87040 30 480 496 16
cert_test_block_3 87040 31 496 512 16
cert_test_block_3 87040 32 512 528 16
cert_test_block_3 87040 33 528 544 16
cert_test_block_3 87040 34 544 560 16
cert_test_block_3 87040 35 560 576 16
cert_test_block_3 87040 36 576 592 16
cert_test_block_3 87040 37 592 608 16
cert_test_block_3 87040 38 608 624 16
cert_test_block_3 87040 39 624 640 16
theorem test87040_complete : Interval test87040 0 640 :=
  (interval_append test87040 0 320 640
  (interval_append test87040 0 160 320
  (interval_append test87040 0 80 160
  (interval_append test87040 0 32 80
  (interval_append test87040 0 16 32
  test87040_block_0
  test87040_block_1)
  (interval_append test87040 32 48 80
  test87040_block_2
  (interval_append test87040 48 64 80
  test87040_block_3
  test87040_block_4)))
  (interval_append test87040 80 112 160
  (interval_append test87040 80 96 112
  test87040_block_5
  test87040_block_6)
  (interval_append test87040 112 128 160
  test87040_block_7
  (interval_append test87040 128 144 160
  test87040_block_8
  test87040_block_9))))
  (interval_append test87040 160 240 320
  (interval_append test87040 160 192 240
  (interval_append test87040 160 176 192
  test87040_block_10
  test87040_block_11)
  (interval_append test87040 192 208 240
  test87040_block_12
  (interval_append test87040 208 224 240
  test87040_block_13
  test87040_block_14)))
  (interval_append test87040 240 272 320
  (interval_append test87040 240 256 272
  test87040_block_15
  test87040_block_16)
  (interval_append test87040 272 288 320
  test87040_block_17
  (interval_append test87040 288 304 320
  test87040_block_18
  test87040_block_19)))))
  (interval_append test87040 320 480 640
  (interval_append test87040 320 400 480
  (interval_append test87040 320 352 400
  (interval_append test87040 320 336 352
  test87040_block_20
  test87040_block_21)
  (interval_append test87040 352 368 400
  test87040_block_22
  (interval_append test87040 368 384 400
  test87040_block_23
  test87040_block_24)))
  (interval_append test87040 400 432 480
  (interval_append test87040 400 416 432
  test87040_block_25
  test87040_block_26)
  (interval_append test87040 432 448 480
  test87040_block_27
  (interval_append test87040 448 464 480
  test87040_block_28
  test87040_block_29))))
  (interval_append test87040 480 560 640
  (interval_append test87040 480 512 560
  (interval_append test87040 480 496 512
  test87040_block_30
  test87040_block_31)
  (interval_append test87040 512 528 560
  test87040_block_32
  (interval_append test87040 528 544 560
  test87040_block_33
  test87040_block_34)))
  (interval_append test87040 560 592 640
  (interval_append test87040 560 576 592
  test87040_block_35
  test87040_block_36)
  (interval_append test87040 592 608 640
  test87040_block_37
  (interval_append test87040 608 624 640
  test87040_block_38
  test87040_block_39))))))
cert_nodeInterval_3 87040 87680
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
cert_test_11 87680
cert_test_block_3 87680 0 0 16 16
cert_test_block_3 87680 1 16 32 16
cert_test_block_3 87680 2 32 48 16
cert_test_block_3 87680 3 48 64 16
cert_test_block_3 87680 4 64 80 16
cert_test_block_3 87680 5 80 96 16
cert_test_block_3 87680 6 96 112 16
cert_test_block_3 87680 7 112 128 16
cert_test_block_3 87680 8 128 144 16
cert_test_block_3 87680 9 144 160 16
cert_test_block_3 87680 10 160 176 16
cert_test_block_3 87680 11 176 192 16
cert_test_block_3 87680 12 192 208 16
cert_test_block_3 87680 13 208 224 16
cert_test_block_3 87680 14 224 240 16
cert_test_block_3 87680 15 240 256 16
cert_test_block_3 87680 16 256 272 16
cert_test_block_3 87680 17 272 288 16
cert_test_block_3 87680 18 288 304 16
cert_test_block_3 87680 19 304 320 16
cert_test_block_3 87680 20 320 336 16
cert_test_block_3 87680 21 336 352 16
cert_test_block_3 87680 22 352 368 16
cert_test_block_3 87680 23 368 384 16
cert_test_block_3 87680 24 384 400 16
cert_test_block_3 87680 25 400 416 16
cert_test_block_3 87680 26 416 432 16
cert_test_block_3 87680 27 432 448 16
cert_test_block_3 87680 28 448 464 16
cert_test_block_3 87680 29 464 480 16
cert_test_block_3 87680 30 480 496 16
cert_test_block_3 87680 31 496 512 16
cert_test_block_3 87680 32 512 528 16
cert_test_block_3 87680 33 528 544 16
cert_test_block_3 87680 34 544 560 16
cert_test_block_3 87680 35 560 576 16
cert_test_block_3 87680 36 576 592 16
cert_test_block_3 87680 37 592 608 16
cert_test_block_3 87680 38 608 624 16
cert_test_block_3 87680 39 624 640 16
theorem test87680_complete : Interval test87680 0 640 :=
  (interval_append test87680 0 320 640
  (interval_append test87680 0 160 320
  (interval_append test87680 0 80 160
  (interval_append test87680 0 32 80
  (interval_append test87680 0 16 32
  test87680_block_0
  test87680_block_1)
  (interval_append test87680 32 48 80
  test87680_block_2
  (interval_append test87680 48 64 80
  test87680_block_3
  test87680_block_4)))
  (interval_append test87680 80 112 160
  (interval_append test87680 80 96 112
  test87680_block_5
  test87680_block_6)
  (interval_append test87680 112 128 160
  test87680_block_7
  (interval_append test87680 128 144 160
  test87680_block_8
  test87680_block_9))))
  (interval_append test87680 160 240 320
  (interval_append test87680 160 192 240
  (interval_append test87680 160 176 192
  test87680_block_10
  test87680_block_11)
  (interval_append test87680 192 208 240
  test87680_block_12
  (interval_append test87680 208 224 240
  test87680_block_13
  test87680_block_14)))
  (interval_append test87680 240 272 320
  (interval_append test87680 240 256 272
  test87680_block_15
  test87680_block_16)
  (interval_append test87680 272 288 320
  test87680_block_17
  (interval_append test87680 288 304 320
  test87680_block_18
  test87680_block_19)))))
  (interval_append test87680 320 480 640
  (interval_append test87680 320 400 480
  (interval_append test87680 320 352 400
  (interval_append test87680 320 336 352
  test87680_block_20
  test87680_block_21)
  (interval_append test87680 352 368 400
  test87680_block_22
  (interval_append test87680 368 384 400
  test87680_block_23
  test87680_block_24)))
  (interval_append test87680 400 432 480
  (interval_append test87680 400 416 432
  test87680_block_25
  test87680_block_26)
  (interval_append test87680 432 448 480
  test87680_block_27
  (interval_append test87680 448 464 480
  test87680_block_28
  test87680_block_29))))
  (interval_append test87680 480 560 640
  (interval_append test87680 480 512 560
  (interval_append test87680 480 496 512
  test87680_block_30
  test87680_block_31)
  (interval_append test87680 512 528 560
  test87680_block_32
  (interval_append test87680 528 544 560
  test87680_block_33
  test87680_block_34)))
  (interval_append test87680 560 592 640
  (interval_append test87680 560 576 592
  test87680_block_35
  test87680_block_36)
  (interval_append test87680 592 608 640
  test87680_block_37
  (interval_append test87680 608 624 640
  test87680_block_38
  test87680_block_39))))))
cert_nodeInterval_3 87680 88320
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
cert_test_11 88320
cert_test_block_3 88320 0 0 16 16
cert_test_block_3 88320 1 16 32 16
cert_test_block_3 88320 2 32 48 16
cert_test_block_3 88320 3 48 64 16
cert_test_block_3 88320 4 64 80 16
cert_test_block_3 88320 5 80 96 16
cert_test_block_3 88320 6 96 112 16
cert_test_block_3 88320 7 112 128 16
cert_test_block_3 88320 8 128 144 16
cert_test_block_3 88320 9 144 160 16
cert_test_block_3 88320 10 160 176 16
cert_test_block_3 88320 11 176 192 16
cert_test_block_3 88320 12 192 208 16
cert_test_block_3 88320 13 208 224 16
cert_test_block_3 88320 14 224 240 16
cert_test_block_3 88320 15 240 256 16
cert_test_block_3 88320 16 256 272 16
cert_test_block_3 88320 17 272 288 16
cert_test_block_3 88320 18 288 304 16
cert_test_block_3 88320 19 304 320 16
cert_test_block_3 88320 20 320 336 16
cert_test_block_3 88320 21 336 352 16
cert_test_block_3 88320 22 352 368 16
cert_test_block_3 88320 23 368 384 16
cert_test_block_3 88320 24 384 400 16
cert_test_block_3 88320 25 400 416 16
cert_test_block_3 88320 26 416 432 16
cert_test_block_3 88320 27 432 448 16
cert_test_block_3 88320 28 448 464 16
cert_test_block_3 88320 29 464 480 16
cert_test_block_3 88320 30 480 496 16
cert_test_block_3 88320 31 496 512 16
cert_test_block_3 88320 32 512 528 16
cert_test_block_3 88320 33 528 544 16
cert_test_block_3 88320 34 544 560 16
cert_test_block_3 88320 35 560 576 16
cert_test_block_3 88320 36 576 592 16
cert_test_block_3 88320 37 592 608 16
cert_test_block_3 88320 38 608 624 16
cert_test_block_3 88320 39 624 640 16
theorem test88320_complete : Interval test88320 0 640 :=
  (interval_append test88320 0 320 640
  (interval_append test88320 0 160 320
  (interval_append test88320 0 80 160
  (interval_append test88320 0 32 80
  (interval_append test88320 0 16 32
  test88320_block_0
  test88320_block_1)
  (interval_append test88320 32 48 80
  test88320_block_2
  (interval_append test88320 48 64 80
  test88320_block_3
  test88320_block_4)))
  (interval_append test88320 80 112 160
  (interval_append test88320 80 96 112
  test88320_block_5
  test88320_block_6)
  (interval_append test88320 112 128 160
  test88320_block_7
  (interval_append test88320 128 144 160
  test88320_block_8
  test88320_block_9))))
  (interval_append test88320 160 240 320
  (interval_append test88320 160 192 240
  (interval_append test88320 160 176 192
  test88320_block_10
  test88320_block_11)
  (interval_append test88320 192 208 240
  test88320_block_12
  (interval_append test88320 208 224 240
  test88320_block_13
  test88320_block_14)))
  (interval_append test88320 240 272 320
  (interval_append test88320 240 256 272
  test88320_block_15
  test88320_block_16)
  (interval_append test88320 272 288 320
  test88320_block_17
  (interval_append test88320 288 304 320
  test88320_block_18
  test88320_block_19)))))
  (interval_append test88320 320 480 640
  (interval_append test88320 320 400 480
  (interval_append test88320 320 352 400
  (interval_append test88320 320 336 352
  test88320_block_20
  test88320_block_21)
  (interval_append test88320 352 368 400
  test88320_block_22
  (interval_append test88320 368 384 400
  test88320_block_23
  test88320_block_24)))
  (interval_append test88320 400 432 480
  (interval_append test88320 400 416 432
  test88320_block_25
  test88320_block_26)
  (interval_append test88320 432 448 480
  test88320_block_27
  (interval_append test88320 448 464 480
  test88320_block_28
  test88320_block_29))))
  (interval_append test88320 480 560 640
  (interval_append test88320 480 512 560
  (interval_append test88320 480 496 512
  test88320_block_30
  test88320_block_31)
  (interval_append test88320 512 528 560
  test88320_block_32
  (interval_append test88320 528 544 560
  test88320_block_33
  test88320_block_34)))
  (interval_append test88320 560 592 640
  (interval_append test88320 560 576 592
  test88320_block_35
  test88320_block_36)
  (interval_append test88320 592 608 640
  test88320_block_37
  (interval_append test88320 608 624 640
  test88320_block_38
  test88320_block_39))))))
cert_nodeInterval_3 88320 88960
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
cert_test_11 88960
cert_test_block_3 88960 0 0 16 16
cert_test_block_3 88960 1 16 32 16
cert_test_block_3 88960 2 32 48 16
cert_test_block_3 88960 3 48 64 16
cert_test_block_3 88960 4 64 80 16
cert_test_block_3 88960 5 80 96 16
cert_test_block_3 88960 6 96 112 16
cert_test_block_3 88960 7 112 128 16
cert_test_block_3 88960 8 128 144 16
cert_test_block_3 88960 9 144 160 16
cert_test_block_3 88960 10 160 176 16
cert_test_block_3 88960 11 176 192 16
cert_test_block_3 88960 12 192 208 16
cert_test_block_3 88960 13 208 224 16
cert_test_block_3 88960 14 224 240 16
cert_test_block_3 88960 15 240 256 16
cert_test_block_3 88960 16 256 272 16
cert_test_block_3 88960 17 272 288 16
cert_test_block_3 88960 18 288 304 16
cert_test_block_3 88960 19 304 320 16
cert_test_block_3 88960 20 320 336 16
cert_test_block_3 88960 21 336 352 16
cert_test_block_3 88960 22 352 368 16
cert_test_block_3 88960 23 368 384 16
cert_test_block_3 88960 24 384 400 16
cert_test_block_3 88960 25 400 416 16
cert_test_block_3 88960 26 416 432 16
cert_test_block_3 88960 27 432 448 16
cert_test_block_3 88960 28 448 464 16
cert_test_block_3 88960 29 464 480 16
cert_test_block_3 88960 30 480 496 16
cert_test_block_3 88960 31 496 512 16
cert_test_block_3 88960 32 512 528 16
cert_test_block_3 88960 33 528 544 16
cert_test_block_3 88960 34 544 560 16
cert_test_block_3 88960 35 560 576 16
cert_test_block_3 88960 36 576 592 16
cert_test_block_3 88960 37 592 608 16
cert_test_block_3 88960 38 608 624 16
cert_test_block_3 88960 39 624 640 16
theorem test88960_complete : Interval test88960 0 640 :=
  (interval_append test88960 0 320 640
  (interval_append test88960 0 160 320
  (interval_append test88960 0 80 160
  (interval_append test88960 0 32 80
  (interval_append test88960 0 16 32
  test88960_block_0
  test88960_block_1)
  (interval_append test88960 32 48 80
  test88960_block_2
  (interval_append test88960 48 64 80
  test88960_block_3
  test88960_block_4)))
  (interval_append test88960 80 112 160
  (interval_append test88960 80 96 112
  test88960_block_5
  test88960_block_6)
  (interval_append test88960 112 128 160
  test88960_block_7
  (interval_append test88960 128 144 160
  test88960_block_8
  test88960_block_9))))
  (interval_append test88960 160 240 320
  (interval_append test88960 160 192 240
  (interval_append test88960 160 176 192
  test88960_block_10
  test88960_block_11)
  (interval_append test88960 192 208 240
  test88960_block_12
  (interval_append test88960 208 224 240
  test88960_block_13
  test88960_block_14)))
  (interval_append test88960 240 272 320
  (interval_append test88960 240 256 272
  test88960_block_15
  test88960_block_16)
  (interval_append test88960 272 288 320
  test88960_block_17
  (interval_append test88960 288 304 320
  test88960_block_18
  test88960_block_19)))))
  (interval_append test88960 320 480 640
  (interval_append test88960 320 400 480
  (interval_append test88960 320 352 400
  (interval_append test88960 320 336 352
  test88960_block_20
  test88960_block_21)
  (interval_append test88960 352 368 400
  test88960_block_22
  (interval_append test88960 368 384 400
  test88960_block_23
  test88960_block_24)))
  (interval_append test88960 400 432 480
  (interval_append test88960 400 416 432
  test88960_block_25
  test88960_block_26)
  (interval_append test88960 432 448 480
  test88960_block_27
  (interval_append test88960 448 464 480
  test88960_block_28
  test88960_block_29))))
  (interval_append test88960 480 560 640
  (interval_append test88960 480 512 560
  (interval_append test88960 480 496 512
  test88960_block_30
  test88960_block_31)
  (interval_append test88960 512 528 560
  test88960_block_32
  (interval_append test88960 528 544 560
  test88960_block_33
  test88960_block_34)))
  (interval_append test88960 560 592 640
  (interval_append test88960 560 576 592
  test88960_block_35
  test88960_block_36)
  (interval_append test88960 592 608 640
  test88960_block_37
  (interval_append test88960 608 624 640
  test88960_block_38
  test88960_block_39))))))
cert_nodeInterval_3 88960 89600
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
cert_test_11 89600
cert_test_block_3 89600 0 0 16 16
cert_test_block_3 89600 1 16 32 16
cert_test_block_3 89600 2 32 48 16
cert_test_block_3 89600 3 48 64 16
cert_test_block_3 89600 4 64 80 16
cert_test_block_3 89600 5 80 96 16
cert_test_block_3 89600 6 96 112 16
cert_test_block_3 89600 7 112 128 16
cert_test_block_3 89600 8 128 144 16
cert_test_block_3 89600 9 144 160 16
cert_test_block_3 89600 10 160 176 16
cert_test_block_3 89600 11 176 192 16
cert_test_block_3 89600 12 192 208 16
cert_test_block_3 89600 13 208 224 16
cert_test_block_3 89600 14 224 240 16
cert_test_block_3 89600 15 240 256 16
cert_test_block_3 89600 16 256 272 16
cert_test_block_3 89600 17 272 288 16
cert_test_block_3 89600 18 288 304 16
cert_test_block_3 89600 19 304 320 16
cert_test_block_3 89600 20 320 336 16
cert_test_block_3 89600 21 336 352 16
cert_test_block_3 89600 22 352 368 16
cert_test_block_3 89600 23 368 384 16
cert_test_block_3 89600 24 384 400 16
cert_test_block_3 89600 25 400 416 16
cert_test_block_3 89600 26 416 432 16
cert_test_block_3 89600 27 432 448 16
cert_test_block_3 89600 28 448 464 16
cert_test_block_3 89600 29 464 480 16
cert_test_block_3 89600 30 480 496 16
cert_test_block_3 89600 31 496 512 16
cert_test_block_3 89600 32 512 528 16
cert_test_block_3 89600 33 528 544 16
cert_test_block_3 89600 34 544 560 16
cert_test_block_3 89600 35 560 576 16
cert_test_block_3 89600 36 576 592 16
cert_test_block_3 89600 37 592 608 16
cert_test_block_3 89600 38 608 624 16
cert_test_block_3 89600 39 624 640 16
theorem test89600_complete : Interval test89600 0 640 :=
  (interval_append test89600 0 320 640
  (interval_append test89600 0 160 320
  (interval_append test89600 0 80 160
  (interval_append test89600 0 32 80
  (interval_append test89600 0 16 32
  test89600_block_0
  test89600_block_1)
  (interval_append test89600 32 48 80
  test89600_block_2
  (interval_append test89600 48 64 80
  test89600_block_3
  test89600_block_4)))
  (interval_append test89600 80 112 160
  (interval_append test89600 80 96 112
  test89600_block_5
  test89600_block_6)
  (interval_append test89600 112 128 160
  test89600_block_7
  (interval_append test89600 128 144 160
  test89600_block_8
  test89600_block_9))))
  (interval_append test89600 160 240 320
  (interval_append test89600 160 192 240
  (interval_append test89600 160 176 192
  test89600_block_10
  test89600_block_11)
  (interval_append test89600 192 208 240
  test89600_block_12
  (interval_append test89600 208 224 240
  test89600_block_13
  test89600_block_14)))
  (interval_append test89600 240 272 320
  (interval_append test89600 240 256 272
  test89600_block_15
  test89600_block_16)
  (interval_append test89600 272 288 320
  test89600_block_17
  (interval_append test89600 288 304 320
  test89600_block_18
  test89600_block_19)))))
  (interval_append test89600 320 480 640
  (interval_append test89600 320 400 480
  (interval_append test89600 320 352 400
  (interval_append test89600 320 336 352
  test89600_block_20
  test89600_block_21)
  (interval_append test89600 352 368 400
  test89600_block_22
  (interval_append test89600 368 384 400
  test89600_block_23
  test89600_block_24)))
  (interval_append test89600 400 432 480
  (interval_append test89600 400 416 432
  test89600_block_25
  test89600_block_26)
  (interval_append test89600 432 448 480
  test89600_block_27
  (interval_append test89600 448 464 480
  test89600_block_28
  test89600_block_29))))
  (interval_append test89600 480 560 640
  (interval_append test89600 480 512 560
  (interval_append test89600 480 496 512
  test89600_block_30
  test89600_block_31)
  (interval_append test89600 512 528 560
  test89600_block_32
  (interval_append test89600 528 544 560
  test89600_block_33
  test89600_block_34)))
  (interval_append test89600 560 592 640
  (interval_append test89600 560 576 592
  test89600_block_35
  test89600_block_36)
  (interval_append test89600 592 608 640
  test89600_block_37
  (interval_append test89600 608 624 640
  test89600_block_38
  test89600_block_39))))))
cert_nodeInterval_3 89600 90240
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
cert_test_11 90240
cert_test_block_3 90240 0 0 16 16
cert_test_block_3 90240 1 16 32 16
cert_test_block_3 90240 2 32 48 16
cert_test_block_3 90240 3 48 64 16
cert_test_block_3 90240 4 64 80 16
cert_test_block_3 90240 5 80 96 16
cert_test_block_3 90240 6 96 112 16
cert_test_block_3 90240 7 112 128 16
cert_test_block_3 90240 8 128 144 16
cert_test_block_3 90240 9 144 160 16
cert_test_block_3 90240 10 160 176 16
cert_test_block_3 90240 11 176 192 16
cert_test_block_3 90240 12 192 208 16
cert_test_block_3 90240 13 208 224 16
cert_test_block_3 90240 14 224 240 16
cert_test_block_3 90240 15 240 256 16
cert_test_block_3 90240 16 256 272 16
cert_test_block_3 90240 17 272 288 16
cert_test_block_3 90240 18 288 304 16
cert_test_block_3 90240 19 304 320 16
cert_test_block_3 90240 20 320 336 16
cert_test_block_3 90240 21 336 352 16
cert_test_block_3 90240 22 352 368 16
cert_test_block_3 90240 23 368 384 16
cert_test_block_3 90240 24 384 400 16
cert_test_block_3 90240 25 400 416 16
cert_test_block_3 90240 26 416 432 16
cert_test_block_3 90240 27 432 448 16
cert_test_block_3 90240 28 448 464 16
cert_test_block_3 90240 29 464 480 16
cert_test_block_3 90240 30 480 496 16
cert_test_block_3 90240 31 496 512 16
cert_test_block_3 90240 32 512 528 16
cert_test_block_3 90240 33 528 544 16
cert_test_block_3 90240 34 544 560 16
cert_test_block_3 90240 35 560 576 16
cert_test_block_3 90240 36 576 592 16
cert_test_block_3 90240 37 592 608 16
cert_test_block_3 90240 38 608 624 16
cert_test_block_3 90240 39 624 640 16
theorem test90240_complete : Interval test90240 0 640 :=
  (interval_append test90240 0 320 640
  (interval_append test90240 0 160 320
  (interval_append test90240 0 80 160
  (interval_append test90240 0 32 80
  (interval_append test90240 0 16 32
  test90240_block_0
  test90240_block_1)
  (interval_append test90240 32 48 80
  test90240_block_2
  (interval_append test90240 48 64 80
  test90240_block_3
  test90240_block_4)))
  (interval_append test90240 80 112 160
  (interval_append test90240 80 96 112
  test90240_block_5
  test90240_block_6)
  (interval_append test90240 112 128 160
  test90240_block_7
  (interval_append test90240 128 144 160
  test90240_block_8
  test90240_block_9))))
  (interval_append test90240 160 240 320
  (interval_append test90240 160 192 240
  (interval_append test90240 160 176 192
  test90240_block_10
  test90240_block_11)
  (interval_append test90240 192 208 240
  test90240_block_12
  (interval_append test90240 208 224 240
  test90240_block_13
  test90240_block_14)))
  (interval_append test90240 240 272 320
  (interval_append test90240 240 256 272
  test90240_block_15
  test90240_block_16)
  (interval_append test90240 272 288 320
  test90240_block_17
  (interval_append test90240 288 304 320
  test90240_block_18
  test90240_block_19)))))
  (interval_append test90240 320 480 640
  (interval_append test90240 320 400 480
  (interval_append test90240 320 352 400
  (interval_append test90240 320 336 352
  test90240_block_20
  test90240_block_21)
  (interval_append test90240 352 368 400
  test90240_block_22
  (interval_append test90240 368 384 400
  test90240_block_23
  test90240_block_24)))
  (interval_append test90240 400 432 480
  (interval_append test90240 400 416 432
  test90240_block_25
  test90240_block_26)
  (interval_append test90240 432 448 480
  test90240_block_27
  (interval_append test90240 448 464 480
  test90240_block_28
  test90240_block_29))))
  (interval_append test90240 480 560 640
  (interval_append test90240 480 512 560
  (interval_append test90240 480 496 512
  test90240_block_30
  test90240_block_31)
  (interval_append test90240 512 528 560
  test90240_block_32
  (interval_append test90240 528 544 560
  test90240_block_33
  test90240_block_34)))
  (interval_append test90240 560 592 640
  (interval_append test90240 560 576 592
  test90240_block_35
  test90240_block_36)
  (interval_append test90240 592 608 640
  test90240_block_37
  (interval_append test90240 608 624 640
  test90240_block_38
  test90240_block_39))))))
cert_nodeInterval_3 90240 90880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
