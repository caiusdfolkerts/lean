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
cert_test_11 99200
cert_test_block_3 99200 0 0 16 16
cert_test_block_3 99200 1 16 32 16
cert_test_block_3 99200 2 32 48 16
cert_test_block_3 99200 3 48 64 16
cert_test_block_3 99200 4 64 80 16
cert_test_block_3 99200 5 80 96 16
cert_test_block_3 99200 6 96 112 16
cert_test_block_3 99200 7 112 128 16
cert_test_block_3 99200 8 128 144 16
cert_test_block_3 99200 9 144 160 16
cert_test_block_3 99200 10 160 176 16
cert_test_block_3 99200 11 176 192 16
cert_test_block_3 99200 12 192 208 16
cert_test_block_3 99200 13 208 224 16
cert_test_block_3 99200 14 224 240 16
cert_test_block_3 99200 15 240 256 16
cert_test_block_3 99200 16 256 272 16
cert_test_block_3 99200 17 272 288 16
cert_test_block_3 99200 18 288 304 16
cert_test_block_3 99200 19 304 320 16
cert_test_block_3 99200 20 320 336 16
cert_test_block_3 99200 21 336 352 16
cert_test_block_3 99200 22 352 368 16
cert_test_block_3 99200 23 368 384 16
cert_test_block_3 99200 24 384 400 16
cert_test_block_3 99200 25 400 416 16
cert_test_block_3 99200 26 416 432 16
cert_test_block_3 99200 27 432 448 16
cert_test_block_3 99200 28 448 464 16
cert_test_block_3 99200 29 464 480 16
cert_test_block_3 99200 30 480 496 16
cert_test_block_3 99200 31 496 512 16
cert_test_block_3 99200 32 512 528 16
cert_test_block_3 99200 33 528 544 16
cert_test_block_3 99200 34 544 560 16
cert_test_block_3 99200 35 560 576 16
cert_test_block_3 99200 36 576 592 16
cert_test_block_3 99200 37 592 608 16
cert_test_block_3 99200 38 608 624 16
cert_test_block_3 99200 39 624 640 16
theorem test99200_complete : Interval test99200 0 640 :=
  (interval_append test99200 0 320 640
  (interval_append test99200 0 160 320
  (interval_append test99200 0 80 160
  (interval_append test99200 0 32 80
  (interval_append test99200 0 16 32
  test99200_block_0
  test99200_block_1)
  (interval_append test99200 32 48 80
  test99200_block_2
  (interval_append test99200 48 64 80
  test99200_block_3
  test99200_block_4)))
  (interval_append test99200 80 112 160
  (interval_append test99200 80 96 112
  test99200_block_5
  test99200_block_6)
  (interval_append test99200 112 128 160
  test99200_block_7
  (interval_append test99200 128 144 160
  test99200_block_8
  test99200_block_9))))
  (interval_append test99200 160 240 320
  (interval_append test99200 160 192 240
  (interval_append test99200 160 176 192
  test99200_block_10
  test99200_block_11)
  (interval_append test99200 192 208 240
  test99200_block_12
  (interval_append test99200 208 224 240
  test99200_block_13
  test99200_block_14)))
  (interval_append test99200 240 272 320
  (interval_append test99200 240 256 272
  test99200_block_15
  test99200_block_16)
  (interval_append test99200 272 288 320
  test99200_block_17
  (interval_append test99200 288 304 320
  test99200_block_18
  test99200_block_19)))))
  (interval_append test99200 320 480 640
  (interval_append test99200 320 400 480
  (interval_append test99200 320 352 400
  (interval_append test99200 320 336 352
  test99200_block_20
  test99200_block_21)
  (interval_append test99200 352 368 400
  test99200_block_22
  (interval_append test99200 368 384 400
  test99200_block_23
  test99200_block_24)))
  (interval_append test99200 400 432 480
  (interval_append test99200 400 416 432
  test99200_block_25
  test99200_block_26)
  (interval_append test99200 432 448 480
  test99200_block_27
  (interval_append test99200 448 464 480
  test99200_block_28
  test99200_block_29))))
  (interval_append test99200 480 560 640
  (interval_append test99200 480 512 560
  (interval_append test99200 480 496 512
  test99200_block_30
  test99200_block_31)
  (interval_append test99200 512 528 560
  test99200_block_32
  (interval_append test99200 528 544 560
  test99200_block_33
  test99200_block_34)))
  (interval_append test99200 560 592 640
  (interval_append test99200 560 576 592
  test99200_block_35
  test99200_block_36)
  (interval_append test99200 592 608 640
  test99200_block_37
  (interval_append test99200 608 624 640
  test99200_block_38
  test99200_block_39))))))
cert_nodeInterval_3 99200 99840
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
cert_test_11 99840
cert_test_block_3 99840 0 0 16 16
cert_test_block_3 99840 1 16 32 16
cert_test_block_3 99840 2 32 48 16
cert_test_block_3 99840 3 48 64 16
cert_test_block_3 99840 4 64 80 16
cert_test_block_3 99840 5 80 96 16
cert_test_block_3 99840 6 96 112 16
cert_test_block_3 99840 7 112 128 16
cert_test_block_3 99840 8 128 144 16
cert_test_block_3 99840 9 144 160 16
cert_test_block_3 99840 10 160 176 16
cert_test_block_3 99840 11 176 192 16
cert_test_block_3 99840 12 192 208 16
cert_test_block_3 99840 13 208 224 16
cert_test_block_3 99840 14 224 240 16
cert_test_block_3 99840 15 240 256 16
cert_test_block_3 99840 16 256 272 16
cert_test_block_3 99840 17 272 288 16
cert_test_block_3 99840 18 288 304 16
cert_test_block_3 99840 19 304 320 16
cert_test_block_3 99840 20 320 336 16
cert_test_block_3 99840 21 336 352 16
cert_test_block_3 99840 22 352 368 16
cert_test_block_3 99840 23 368 384 16
cert_test_block_3 99840 24 384 400 16
cert_test_block_3 99840 25 400 416 16
cert_test_block_3 99840 26 416 432 16
cert_test_block_3 99840 27 432 448 16
cert_test_block_3 99840 28 448 464 16
cert_test_block_3 99840 29 464 480 16
cert_test_block_3 99840 30 480 496 16
cert_test_block_3 99840 31 496 512 16
cert_test_block_3 99840 32 512 528 16
cert_test_block_3 99840 33 528 544 16
cert_test_block_3 99840 34 544 560 16
cert_test_block_3 99840 35 560 576 16
cert_test_block_3 99840 36 576 592 16
cert_test_block_3 99840 37 592 608 16
cert_test_block_3 99840 38 608 624 16
cert_test_block_3 99840 39 624 640 16
theorem test99840_complete : Interval test99840 0 640 :=
  (interval_append test99840 0 320 640
  (interval_append test99840 0 160 320
  (interval_append test99840 0 80 160
  (interval_append test99840 0 32 80
  (interval_append test99840 0 16 32
  test99840_block_0
  test99840_block_1)
  (interval_append test99840 32 48 80
  test99840_block_2
  (interval_append test99840 48 64 80
  test99840_block_3
  test99840_block_4)))
  (interval_append test99840 80 112 160
  (interval_append test99840 80 96 112
  test99840_block_5
  test99840_block_6)
  (interval_append test99840 112 128 160
  test99840_block_7
  (interval_append test99840 128 144 160
  test99840_block_8
  test99840_block_9))))
  (interval_append test99840 160 240 320
  (interval_append test99840 160 192 240
  (interval_append test99840 160 176 192
  test99840_block_10
  test99840_block_11)
  (interval_append test99840 192 208 240
  test99840_block_12
  (interval_append test99840 208 224 240
  test99840_block_13
  test99840_block_14)))
  (interval_append test99840 240 272 320
  (interval_append test99840 240 256 272
  test99840_block_15
  test99840_block_16)
  (interval_append test99840 272 288 320
  test99840_block_17
  (interval_append test99840 288 304 320
  test99840_block_18
  test99840_block_19)))))
  (interval_append test99840 320 480 640
  (interval_append test99840 320 400 480
  (interval_append test99840 320 352 400
  (interval_append test99840 320 336 352
  test99840_block_20
  test99840_block_21)
  (interval_append test99840 352 368 400
  test99840_block_22
  (interval_append test99840 368 384 400
  test99840_block_23
  test99840_block_24)))
  (interval_append test99840 400 432 480
  (interval_append test99840 400 416 432
  test99840_block_25
  test99840_block_26)
  (interval_append test99840 432 448 480
  test99840_block_27
  (interval_append test99840 448 464 480
  test99840_block_28
  test99840_block_29))))
  (interval_append test99840 480 560 640
  (interval_append test99840 480 512 560
  (interval_append test99840 480 496 512
  test99840_block_30
  test99840_block_31)
  (interval_append test99840 512 528 560
  test99840_block_32
  (interval_append test99840 528 544 560
  test99840_block_33
  test99840_block_34)))
  (interval_append test99840 560 592 640
  (interval_append test99840 560 576 592
  test99840_block_35
  test99840_block_36)
  (interval_append test99840 592 608 640
  test99840_block_37
  (interval_append test99840 608 624 640
  test99840_block_38
  test99840_block_39))))))
cert_nodeInterval_3 99840 100480
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
cert_test_11 100480
cert_test_block_3 100480 0 0 16 16
cert_test_block_3 100480 1 16 32 16
cert_test_block_3 100480 2 32 48 16
cert_test_block_3 100480 3 48 64 16
cert_test_block_3 100480 4 64 80 16
cert_test_block_3 100480 5 80 96 16
cert_test_block_3 100480 6 96 112 16
cert_test_block_3 100480 7 112 128 16
cert_test_block_3 100480 8 128 144 16
cert_test_block_3 100480 9 144 160 16
cert_test_block_3 100480 10 160 176 16
cert_test_block_3 100480 11 176 192 16
cert_test_block_3 100480 12 192 208 16
cert_test_block_3 100480 13 208 224 16
cert_test_block_3 100480 14 224 240 16
cert_test_block_3 100480 15 240 256 16
cert_test_block_3 100480 16 256 272 16
cert_test_block_3 100480 17 272 288 16
cert_test_block_3 100480 18 288 304 16
cert_test_block_3 100480 19 304 320 16
cert_test_block_3 100480 20 320 336 16
cert_test_block_3 100480 21 336 352 16
cert_test_block_3 100480 22 352 368 16
cert_test_block_3 100480 23 368 384 16
cert_test_block_3 100480 24 384 400 16
cert_test_block_3 100480 25 400 416 16
cert_test_block_3 100480 26 416 432 16
cert_test_block_3 100480 27 432 448 16
cert_test_block_3 100480 28 448 464 16
cert_test_block_3 100480 29 464 480 16
cert_test_block_3 100480 30 480 496 16
cert_test_block_3 100480 31 496 512 16
cert_test_block_3 100480 32 512 528 16
cert_test_block_3 100480 33 528 544 16
cert_test_block_3 100480 34 544 560 16
cert_test_block_3 100480 35 560 576 16
cert_test_block_3 100480 36 576 592 16
cert_test_block_3 100480 37 592 608 16
cert_test_block_3 100480 38 608 624 16
cert_test_block_3 100480 39 624 640 16
theorem test100480_complete : Interval test100480 0 640 :=
  (interval_append test100480 0 320 640
  (interval_append test100480 0 160 320
  (interval_append test100480 0 80 160
  (interval_append test100480 0 32 80
  (interval_append test100480 0 16 32
  test100480_block_0
  test100480_block_1)
  (interval_append test100480 32 48 80
  test100480_block_2
  (interval_append test100480 48 64 80
  test100480_block_3
  test100480_block_4)))
  (interval_append test100480 80 112 160
  (interval_append test100480 80 96 112
  test100480_block_5
  test100480_block_6)
  (interval_append test100480 112 128 160
  test100480_block_7
  (interval_append test100480 128 144 160
  test100480_block_8
  test100480_block_9))))
  (interval_append test100480 160 240 320
  (interval_append test100480 160 192 240
  (interval_append test100480 160 176 192
  test100480_block_10
  test100480_block_11)
  (interval_append test100480 192 208 240
  test100480_block_12
  (interval_append test100480 208 224 240
  test100480_block_13
  test100480_block_14)))
  (interval_append test100480 240 272 320
  (interval_append test100480 240 256 272
  test100480_block_15
  test100480_block_16)
  (interval_append test100480 272 288 320
  test100480_block_17
  (interval_append test100480 288 304 320
  test100480_block_18
  test100480_block_19)))))
  (interval_append test100480 320 480 640
  (interval_append test100480 320 400 480
  (interval_append test100480 320 352 400
  (interval_append test100480 320 336 352
  test100480_block_20
  test100480_block_21)
  (interval_append test100480 352 368 400
  test100480_block_22
  (interval_append test100480 368 384 400
  test100480_block_23
  test100480_block_24)))
  (interval_append test100480 400 432 480
  (interval_append test100480 400 416 432
  test100480_block_25
  test100480_block_26)
  (interval_append test100480 432 448 480
  test100480_block_27
  (interval_append test100480 448 464 480
  test100480_block_28
  test100480_block_29))))
  (interval_append test100480 480 560 640
  (interval_append test100480 480 512 560
  (interval_append test100480 480 496 512
  test100480_block_30
  test100480_block_31)
  (interval_append test100480 512 528 560
  test100480_block_32
  (interval_append test100480 528 544 560
  test100480_block_33
  test100480_block_34)))
  (interval_append test100480 560 592 640
  (interval_append test100480 560 576 592
  test100480_block_35
  test100480_block_36)
  (interval_append test100480 592 608 640
  test100480_block_37
  (interval_append test100480 608 624 640
  test100480_block_38
  test100480_block_39))))))
cert_nodeInterval_3 100480 101120
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
cert_test_11 101120
cert_test_block_3 101120 0 0 16 16
cert_test_block_3 101120 1 16 32 16
cert_test_block_3 101120 2 32 48 16
cert_test_block_3 101120 3 48 64 16
cert_test_block_3 101120 4 64 80 16
cert_test_block_3 101120 5 80 96 16
cert_test_block_3 101120 6 96 112 16
cert_test_block_3 101120 7 112 128 16
cert_test_block_3 101120 8 128 144 16
cert_test_block_3 101120 9 144 160 16
cert_test_block_3 101120 10 160 176 16
cert_test_block_3 101120 11 176 192 16
cert_test_block_3 101120 12 192 208 16
cert_test_block_3 101120 13 208 224 16
cert_test_block_3 101120 14 224 240 16
cert_test_block_3 101120 15 240 256 16
cert_test_block_3 101120 16 256 272 16
cert_test_block_3 101120 17 272 288 16
cert_test_block_3 101120 18 288 304 16
cert_test_block_3 101120 19 304 320 16
cert_test_block_3 101120 20 320 336 16
cert_test_block_3 101120 21 336 352 16
cert_test_block_3 101120 22 352 368 16
cert_test_block_3 101120 23 368 384 16
cert_test_block_3 101120 24 384 400 16
cert_test_block_3 101120 25 400 416 16
cert_test_block_3 101120 26 416 432 16
cert_test_block_3 101120 27 432 448 16
cert_test_block_3 101120 28 448 464 16
cert_test_block_3 101120 29 464 480 16
cert_test_block_3 101120 30 480 496 16
cert_test_block_3 101120 31 496 512 16
cert_test_block_3 101120 32 512 528 16
cert_test_block_3 101120 33 528 544 16
cert_test_block_3 101120 34 544 560 16
cert_test_block_3 101120 35 560 576 16
cert_test_block_3 101120 36 576 592 16
cert_test_block_3 101120 37 592 608 16
cert_test_block_3 101120 38 608 624 16
cert_test_block_3 101120 39 624 640 16
theorem test101120_complete : Interval test101120 0 640 :=
  (interval_append test101120 0 320 640
  (interval_append test101120 0 160 320
  (interval_append test101120 0 80 160
  (interval_append test101120 0 32 80
  (interval_append test101120 0 16 32
  test101120_block_0
  test101120_block_1)
  (interval_append test101120 32 48 80
  test101120_block_2
  (interval_append test101120 48 64 80
  test101120_block_3
  test101120_block_4)))
  (interval_append test101120 80 112 160
  (interval_append test101120 80 96 112
  test101120_block_5
  test101120_block_6)
  (interval_append test101120 112 128 160
  test101120_block_7
  (interval_append test101120 128 144 160
  test101120_block_8
  test101120_block_9))))
  (interval_append test101120 160 240 320
  (interval_append test101120 160 192 240
  (interval_append test101120 160 176 192
  test101120_block_10
  test101120_block_11)
  (interval_append test101120 192 208 240
  test101120_block_12
  (interval_append test101120 208 224 240
  test101120_block_13
  test101120_block_14)))
  (interval_append test101120 240 272 320
  (interval_append test101120 240 256 272
  test101120_block_15
  test101120_block_16)
  (interval_append test101120 272 288 320
  test101120_block_17
  (interval_append test101120 288 304 320
  test101120_block_18
  test101120_block_19)))))
  (interval_append test101120 320 480 640
  (interval_append test101120 320 400 480
  (interval_append test101120 320 352 400
  (interval_append test101120 320 336 352
  test101120_block_20
  test101120_block_21)
  (interval_append test101120 352 368 400
  test101120_block_22
  (interval_append test101120 368 384 400
  test101120_block_23
  test101120_block_24)))
  (interval_append test101120 400 432 480
  (interval_append test101120 400 416 432
  test101120_block_25
  test101120_block_26)
  (interval_append test101120 432 448 480
  test101120_block_27
  (interval_append test101120 448 464 480
  test101120_block_28
  test101120_block_29))))
  (interval_append test101120 480 560 640
  (interval_append test101120 480 512 560
  (interval_append test101120 480 496 512
  test101120_block_30
  test101120_block_31)
  (interval_append test101120 512 528 560
  test101120_block_32
  (interval_append test101120 528 544 560
  test101120_block_33
  test101120_block_34)))
  (interval_append test101120 560 592 640
  (interval_append test101120 560 576 592
  test101120_block_35
  test101120_block_36)
  (interval_append test101120 592 608 640
  test101120_block_37
  (interval_append test101120 608 624 640
  test101120_block_38
  test101120_block_39))))))
cert_nodeInterval_3 101120 101760
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
cert_test_11 101760
cert_test_block_3 101760 0 0 16 16
cert_test_block_3 101760 1 16 32 16
cert_test_block_3 101760 2 32 48 16
cert_test_block_3 101760 3 48 64 16
cert_test_block_3 101760 4 64 80 16
cert_test_block_3 101760 5 80 96 16
cert_test_block_3 101760 6 96 112 16
cert_test_block_3 101760 7 112 128 16
cert_test_block_3 101760 8 128 144 16
cert_test_block_3 101760 9 144 160 16
cert_test_block_3 101760 10 160 176 16
cert_test_block_3 101760 11 176 192 16
cert_test_block_3 101760 12 192 208 16
cert_test_block_3 101760 13 208 224 16
cert_test_block_3 101760 14 224 240 16
cert_test_block_3 101760 15 240 256 16
cert_test_block_3 101760 16 256 272 16
cert_test_block_3 101760 17 272 288 16
cert_test_block_3 101760 18 288 304 16
cert_test_block_3 101760 19 304 320 16
cert_test_block_3 101760 20 320 336 16
cert_test_block_3 101760 21 336 352 16
cert_test_block_3 101760 22 352 368 16
cert_test_block_3 101760 23 368 384 16
cert_test_block_3 101760 24 384 400 16
cert_test_block_3 101760 25 400 416 16
cert_test_block_3 101760 26 416 432 16
cert_test_block_3 101760 27 432 448 16
cert_test_block_3 101760 28 448 464 16
cert_test_block_3 101760 29 464 480 16
cert_test_block_3 101760 30 480 496 16
cert_test_block_3 101760 31 496 512 16
cert_test_block_3 101760 32 512 528 16
cert_test_block_3 101760 33 528 544 16
cert_test_block_3 101760 34 544 560 16
cert_test_block_3 101760 35 560 576 16
cert_test_block_3 101760 36 576 592 16
cert_test_block_3 101760 37 592 608 16
cert_test_block_3 101760 38 608 624 16
cert_test_block_3 101760 39 624 640 16
theorem test101760_complete : Interval test101760 0 640 :=
  (interval_append test101760 0 320 640
  (interval_append test101760 0 160 320
  (interval_append test101760 0 80 160
  (interval_append test101760 0 32 80
  (interval_append test101760 0 16 32
  test101760_block_0
  test101760_block_1)
  (interval_append test101760 32 48 80
  test101760_block_2
  (interval_append test101760 48 64 80
  test101760_block_3
  test101760_block_4)))
  (interval_append test101760 80 112 160
  (interval_append test101760 80 96 112
  test101760_block_5
  test101760_block_6)
  (interval_append test101760 112 128 160
  test101760_block_7
  (interval_append test101760 128 144 160
  test101760_block_8
  test101760_block_9))))
  (interval_append test101760 160 240 320
  (interval_append test101760 160 192 240
  (interval_append test101760 160 176 192
  test101760_block_10
  test101760_block_11)
  (interval_append test101760 192 208 240
  test101760_block_12
  (interval_append test101760 208 224 240
  test101760_block_13
  test101760_block_14)))
  (interval_append test101760 240 272 320
  (interval_append test101760 240 256 272
  test101760_block_15
  test101760_block_16)
  (interval_append test101760 272 288 320
  test101760_block_17
  (interval_append test101760 288 304 320
  test101760_block_18
  test101760_block_19)))))
  (interval_append test101760 320 480 640
  (interval_append test101760 320 400 480
  (interval_append test101760 320 352 400
  (interval_append test101760 320 336 352
  test101760_block_20
  test101760_block_21)
  (interval_append test101760 352 368 400
  test101760_block_22
  (interval_append test101760 368 384 400
  test101760_block_23
  test101760_block_24)))
  (interval_append test101760 400 432 480
  (interval_append test101760 400 416 432
  test101760_block_25
  test101760_block_26)
  (interval_append test101760 432 448 480
  test101760_block_27
  (interval_append test101760 448 464 480
  test101760_block_28
  test101760_block_29))))
  (interval_append test101760 480 560 640
  (interval_append test101760 480 512 560
  (interval_append test101760 480 496 512
  test101760_block_30
  test101760_block_31)
  (interval_append test101760 512 528 560
  test101760_block_32
  (interval_append test101760 528 544 560
  test101760_block_33
  test101760_block_34)))
  (interval_append test101760 560 592 640
  (interval_append test101760 560 576 592
  test101760_block_35
  test101760_block_36)
  (interval_append test101760 592 608 640
  test101760_block_37
  (interval_append test101760 608 624 640
  test101760_block_38
  test101760_block_39))))))
cert_nodeInterval_3 101760 102400
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
cert_test_11 102400
cert_test_block_3 102400 0 0 16 16
cert_test_block_3 102400 1 16 32 16
cert_test_block_3 102400 2 32 48 16
cert_test_block_3 102400 3 48 64 16
cert_test_block_3 102400 4 64 80 16
cert_test_block_3 102400 5 80 96 16
cert_test_block_3 102400 6 96 112 16
cert_test_block_3 102400 7 112 128 16
cert_test_block_3 102400 8 128 144 16
cert_test_block_3 102400 9 144 160 16
cert_test_block_3 102400 10 160 176 16
cert_test_block_3 102400 11 176 192 16
cert_test_block_3 102400 12 192 208 16
cert_test_block_3 102400 13 208 224 16
cert_test_block_3 102400 14 224 240 16
cert_test_block_3 102400 15 240 256 16
cert_test_block_3 102400 16 256 272 16
cert_test_block_3 102400 17 272 288 16
cert_test_block_3 102400 18 288 304 16
cert_test_block_3 102400 19 304 320 16
cert_test_block_3 102400 20 320 336 16
cert_test_block_3 102400 21 336 352 16
cert_test_block_3 102400 22 352 368 16
cert_test_block_3 102400 23 368 384 16
cert_test_block_3 102400 24 384 400 16
cert_test_block_3 102400 25 400 416 16
cert_test_block_3 102400 26 416 432 16
cert_test_block_3 102400 27 432 448 16
cert_test_block_3 102400 28 448 464 16
cert_test_block_3 102400 29 464 480 16
cert_test_block_3 102400 30 480 496 16
cert_test_block_3 102400 31 496 512 16
cert_test_block_3 102400 32 512 528 16
cert_test_block_3 102400 33 528 544 16
cert_test_block_3 102400 34 544 560 16
cert_test_block_3 102400 35 560 576 16
cert_test_block_3 102400 36 576 592 16
cert_test_block_3 102400 37 592 608 16
cert_test_block_3 102400 38 608 624 16
cert_test_block_3 102400 39 624 640 16
theorem test102400_complete : Interval test102400 0 640 :=
  (interval_append test102400 0 320 640
  (interval_append test102400 0 160 320
  (interval_append test102400 0 80 160
  (interval_append test102400 0 32 80
  (interval_append test102400 0 16 32
  test102400_block_0
  test102400_block_1)
  (interval_append test102400 32 48 80
  test102400_block_2
  (interval_append test102400 48 64 80
  test102400_block_3
  test102400_block_4)))
  (interval_append test102400 80 112 160
  (interval_append test102400 80 96 112
  test102400_block_5
  test102400_block_6)
  (interval_append test102400 112 128 160
  test102400_block_7
  (interval_append test102400 128 144 160
  test102400_block_8
  test102400_block_9))))
  (interval_append test102400 160 240 320
  (interval_append test102400 160 192 240
  (interval_append test102400 160 176 192
  test102400_block_10
  test102400_block_11)
  (interval_append test102400 192 208 240
  test102400_block_12
  (interval_append test102400 208 224 240
  test102400_block_13
  test102400_block_14)))
  (interval_append test102400 240 272 320
  (interval_append test102400 240 256 272
  test102400_block_15
  test102400_block_16)
  (interval_append test102400 272 288 320
  test102400_block_17
  (interval_append test102400 288 304 320
  test102400_block_18
  test102400_block_19)))))
  (interval_append test102400 320 480 640
  (interval_append test102400 320 400 480
  (interval_append test102400 320 352 400
  (interval_append test102400 320 336 352
  test102400_block_20
  test102400_block_21)
  (interval_append test102400 352 368 400
  test102400_block_22
  (interval_append test102400 368 384 400
  test102400_block_23
  test102400_block_24)))
  (interval_append test102400 400 432 480
  (interval_append test102400 400 416 432
  test102400_block_25
  test102400_block_26)
  (interval_append test102400 432 448 480
  test102400_block_27
  (interval_append test102400 448 464 480
  test102400_block_28
  test102400_block_29))))
  (interval_append test102400 480 560 640
  (interval_append test102400 480 512 560
  (interval_append test102400 480 496 512
  test102400_block_30
  test102400_block_31)
  (interval_append test102400 512 528 560
  test102400_block_32
  (interval_append test102400 528 544 560
  test102400_block_33
  test102400_block_34)))
  (interval_append test102400 560 592 640
  (interval_append test102400 560 576 592
  test102400_block_35
  test102400_block_36)
  (interval_append test102400 592 608 640
  test102400_block_37
  (interval_append test102400 608 624 640
  test102400_block_38
  test102400_block_39))))))
cert_nodeInterval_3 102400 103040
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
cert_test_11 103040
cert_test_block_3 103040 0 0 16 16
cert_test_block_3 103040 1 16 32 16
cert_test_block_3 103040 2 32 48 16
cert_test_block_3 103040 3 48 64 16
cert_test_block_3 103040 4 64 80 16
cert_test_block_3 103040 5 80 96 16
cert_test_block_3 103040 6 96 112 16
cert_test_block_3 103040 7 112 128 16
cert_test_block_3 103040 8 128 144 16
cert_test_block_3 103040 9 144 160 16
cert_test_block_3 103040 10 160 176 16
cert_test_block_3 103040 11 176 192 16
cert_test_block_3 103040 12 192 208 16
cert_test_block_3 103040 13 208 224 16
cert_test_block_3 103040 14 224 240 16
cert_test_block_3 103040 15 240 256 16
cert_test_block_3 103040 16 256 272 16
cert_test_block_3 103040 17 272 288 16
cert_test_block_3 103040 18 288 304 16
cert_test_block_3 103040 19 304 320 16
cert_test_block_3 103040 20 320 336 16
cert_test_block_3 103040 21 336 352 16
cert_test_block_3 103040 22 352 368 16
cert_test_block_3 103040 23 368 384 16
cert_test_block_3 103040 24 384 400 16
cert_test_block_3 103040 25 400 416 16
cert_test_block_3 103040 26 416 432 16
cert_test_block_3 103040 27 432 448 16
cert_test_block_3 103040 28 448 464 16
cert_test_block_3 103040 29 464 480 16
cert_test_block_3 103040 30 480 496 16
cert_test_block_3 103040 31 496 512 16
cert_test_block_3 103040 32 512 528 16
cert_test_block_3 103040 33 528 544 16
cert_test_block_3 103040 34 544 560 16
cert_test_block_3 103040 35 560 576 16
cert_test_block_3 103040 36 576 592 16
cert_test_block_3 103040 37 592 608 16
cert_test_block_3 103040 38 608 624 16
cert_test_block_3 103040 39 624 640 16
theorem test103040_complete : Interval test103040 0 640 :=
  (interval_append test103040 0 320 640
  (interval_append test103040 0 160 320
  (interval_append test103040 0 80 160
  (interval_append test103040 0 32 80
  (interval_append test103040 0 16 32
  test103040_block_0
  test103040_block_1)
  (interval_append test103040 32 48 80
  test103040_block_2
  (interval_append test103040 48 64 80
  test103040_block_3
  test103040_block_4)))
  (interval_append test103040 80 112 160
  (interval_append test103040 80 96 112
  test103040_block_5
  test103040_block_6)
  (interval_append test103040 112 128 160
  test103040_block_7
  (interval_append test103040 128 144 160
  test103040_block_8
  test103040_block_9))))
  (interval_append test103040 160 240 320
  (interval_append test103040 160 192 240
  (interval_append test103040 160 176 192
  test103040_block_10
  test103040_block_11)
  (interval_append test103040 192 208 240
  test103040_block_12
  (interval_append test103040 208 224 240
  test103040_block_13
  test103040_block_14)))
  (interval_append test103040 240 272 320
  (interval_append test103040 240 256 272
  test103040_block_15
  test103040_block_16)
  (interval_append test103040 272 288 320
  test103040_block_17
  (interval_append test103040 288 304 320
  test103040_block_18
  test103040_block_19)))))
  (interval_append test103040 320 480 640
  (interval_append test103040 320 400 480
  (interval_append test103040 320 352 400
  (interval_append test103040 320 336 352
  test103040_block_20
  test103040_block_21)
  (interval_append test103040 352 368 400
  test103040_block_22
  (interval_append test103040 368 384 400
  test103040_block_23
  test103040_block_24)))
  (interval_append test103040 400 432 480
  (interval_append test103040 400 416 432
  test103040_block_25
  test103040_block_26)
  (interval_append test103040 432 448 480
  test103040_block_27
  (interval_append test103040 448 464 480
  test103040_block_28
  test103040_block_29))))
  (interval_append test103040 480 560 640
  (interval_append test103040 480 512 560
  (interval_append test103040 480 496 512
  test103040_block_30
  test103040_block_31)
  (interval_append test103040 512 528 560
  test103040_block_32
  (interval_append test103040 528 544 560
  test103040_block_33
  test103040_block_34)))
  (interval_append test103040 560 592 640
  (interval_append test103040 560 576 592
  test103040_block_35
  test103040_block_36)
  (interval_append test103040 592 608 640
  test103040_block_37
  (interval_append test103040 608 624 640
  test103040_block_38
  test103040_block_39))))))
cert_nodeInterval_3 103040 103680
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
cert_test_11 103680
cert_test_block_3 103680 0 0 16 16
cert_test_block_3 103680 1 16 32 16
cert_test_block_3 103680 2 32 48 16
cert_test_block_3 103680 3 48 64 16
cert_test_block_3 103680 4 64 80 16
cert_test_block_3 103680 5 80 96 16
cert_test_block_3 103680 6 96 112 16
cert_test_block_3 103680 7 112 128 16
cert_test_block_3 103680 8 128 144 16
cert_test_block_3 103680 9 144 160 16
cert_test_block_3 103680 10 160 176 16
cert_test_block_3 103680 11 176 192 16
cert_test_block_3 103680 12 192 208 16
cert_test_block_3 103680 13 208 224 16
cert_test_block_3 103680 14 224 240 16
cert_test_block_3 103680 15 240 256 16
cert_test_block_3 103680 16 256 272 16
cert_test_block_3 103680 17 272 288 16
cert_test_block_3 103680 18 288 304 16
cert_test_block_3 103680 19 304 320 16
cert_test_block_3 103680 20 320 336 16
cert_test_block_3 103680 21 336 352 16
cert_test_block_3 103680 22 352 368 16
cert_test_block_3 103680 23 368 384 16
cert_test_block_3 103680 24 384 400 16
cert_test_block_3 103680 25 400 416 16
cert_test_block_3 103680 26 416 432 16
cert_test_block_3 103680 27 432 448 16
cert_test_block_3 103680 28 448 464 16
cert_test_block_3 103680 29 464 480 16
cert_test_block_3 103680 30 480 496 16
cert_test_block_3 103680 31 496 512 16
cert_test_block_3 103680 32 512 528 16
cert_test_block_3 103680 33 528 544 16
cert_test_block_3 103680 34 544 560 16
cert_test_block_3 103680 35 560 576 16
cert_test_block_3 103680 36 576 592 16
cert_test_block_3 103680 37 592 608 16
cert_test_block_3 103680 38 608 624 16
cert_test_block_3 103680 39 624 640 16
theorem test103680_complete : Interval test103680 0 640 :=
  (interval_append test103680 0 320 640
  (interval_append test103680 0 160 320
  (interval_append test103680 0 80 160
  (interval_append test103680 0 32 80
  (interval_append test103680 0 16 32
  test103680_block_0
  test103680_block_1)
  (interval_append test103680 32 48 80
  test103680_block_2
  (interval_append test103680 48 64 80
  test103680_block_3
  test103680_block_4)))
  (interval_append test103680 80 112 160
  (interval_append test103680 80 96 112
  test103680_block_5
  test103680_block_6)
  (interval_append test103680 112 128 160
  test103680_block_7
  (interval_append test103680 128 144 160
  test103680_block_8
  test103680_block_9))))
  (interval_append test103680 160 240 320
  (interval_append test103680 160 192 240
  (interval_append test103680 160 176 192
  test103680_block_10
  test103680_block_11)
  (interval_append test103680 192 208 240
  test103680_block_12
  (interval_append test103680 208 224 240
  test103680_block_13
  test103680_block_14)))
  (interval_append test103680 240 272 320
  (interval_append test103680 240 256 272
  test103680_block_15
  test103680_block_16)
  (interval_append test103680 272 288 320
  test103680_block_17
  (interval_append test103680 288 304 320
  test103680_block_18
  test103680_block_19)))))
  (interval_append test103680 320 480 640
  (interval_append test103680 320 400 480
  (interval_append test103680 320 352 400
  (interval_append test103680 320 336 352
  test103680_block_20
  test103680_block_21)
  (interval_append test103680 352 368 400
  test103680_block_22
  (interval_append test103680 368 384 400
  test103680_block_23
  test103680_block_24)))
  (interval_append test103680 400 432 480
  (interval_append test103680 400 416 432
  test103680_block_25
  test103680_block_26)
  (interval_append test103680 432 448 480
  test103680_block_27
  (interval_append test103680 448 464 480
  test103680_block_28
  test103680_block_29))))
  (interval_append test103680 480 560 640
  (interval_append test103680 480 512 560
  (interval_append test103680 480 496 512
  test103680_block_30
  test103680_block_31)
  (interval_append test103680 512 528 560
  test103680_block_32
  (interval_append test103680 528 544 560
  test103680_block_33
  test103680_block_34)))
  (interval_append test103680 560 592 640
  (interval_append test103680 560 576 592
  test103680_block_35
  test103680_block_36)
  (interval_append test103680 592 608 640
  test103680_block_37
  (interval_append test103680 608 624 640
  test103680_block_38
  test103680_block_39))))))
cert_nodeInterval_3 103680 104320
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
cert_test_11 104320
cert_test_block_3 104320 0 0 16 16
cert_test_block_3 104320 1 16 32 16
cert_test_block_3 104320 2 32 48 16
cert_test_block_3 104320 3 48 64 16
cert_test_block_3 104320 4 64 80 16
cert_test_block_3 104320 5 80 96 16
cert_test_block_3 104320 6 96 112 16
cert_test_block_3 104320 7 112 128 16
cert_test_block_3 104320 8 128 144 16
cert_test_block_3 104320 9 144 160 16
cert_test_block_3 104320 10 160 176 16
cert_test_block_3 104320 11 176 192 16
cert_test_block_3 104320 12 192 208 16
cert_test_block_3 104320 13 208 224 16
cert_test_block_3 104320 14 224 240 16
cert_test_block_3 104320 15 240 256 16
cert_test_block_3 104320 16 256 272 16
cert_test_block_3 104320 17 272 288 16
cert_test_block_3 104320 18 288 304 16
cert_test_block_3 104320 19 304 320 16
cert_test_block_3 104320 20 320 336 16
cert_test_block_3 104320 21 336 352 16
cert_test_block_3 104320 22 352 368 16
cert_test_block_3 104320 23 368 384 16
cert_test_block_3 104320 24 384 400 16
cert_test_block_3 104320 25 400 416 16
cert_test_block_3 104320 26 416 432 16
cert_test_block_3 104320 27 432 448 16
cert_test_block_3 104320 28 448 464 16
cert_test_block_3 104320 29 464 480 16
cert_test_block_3 104320 30 480 496 16
cert_test_block_3 104320 31 496 512 16
cert_test_block_3 104320 32 512 528 16
cert_test_block_3 104320 33 528 544 16
cert_test_block_3 104320 34 544 560 16
cert_test_block_3 104320 35 560 576 16
cert_test_block_3 104320 36 576 592 16
cert_test_block_3 104320 37 592 608 16
cert_test_block_3 104320 38 608 624 16
cert_test_block_3 104320 39 624 640 16
theorem test104320_complete : Interval test104320 0 640 :=
  (interval_append test104320 0 320 640
  (interval_append test104320 0 160 320
  (interval_append test104320 0 80 160
  (interval_append test104320 0 32 80
  (interval_append test104320 0 16 32
  test104320_block_0
  test104320_block_1)
  (interval_append test104320 32 48 80
  test104320_block_2
  (interval_append test104320 48 64 80
  test104320_block_3
  test104320_block_4)))
  (interval_append test104320 80 112 160
  (interval_append test104320 80 96 112
  test104320_block_5
  test104320_block_6)
  (interval_append test104320 112 128 160
  test104320_block_7
  (interval_append test104320 128 144 160
  test104320_block_8
  test104320_block_9))))
  (interval_append test104320 160 240 320
  (interval_append test104320 160 192 240
  (interval_append test104320 160 176 192
  test104320_block_10
  test104320_block_11)
  (interval_append test104320 192 208 240
  test104320_block_12
  (interval_append test104320 208 224 240
  test104320_block_13
  test104320_block_14)))
  (interval_append test104320 240 272 320
  (interval_append test104320 240 256 272
  test104320_block_15
  test104320_block_16)
  (interval_append test104320 272 288 320
  test104320_block_17
  (interval_append test104320 288 304 320
  test104320_block_18
  test104320_block_19)))))
  (interval_append test104320 320 480 640
  (interval_append test104320 320 400 480
  (interval_append test104320 320 352 400
  (interval_append test104320 320 336 352
  test104320_block_20
  test104320_block_21)
  (interval_append test104320 352 368 400
  test104320_block_22
  (interval_append test104320 368 384 400
  test104320_block_23
  test104320_block_24)))
  (interval_append test104320 400 432 480
  (interval_append test104320 400 416 432
  test104320_block_25
  test104320_block_26)
  (interval_append test104320 432 448 480
  test104320_block_27
  (interval_append test104320 448 464 480
  test104320_block_28
  test104320_block_29))))
  (interval_append test104320 480 560 640
  (interval_append test104320 480 512 560
  (interval_append test104320 480 496 512
  test104320_block_30
  test104320_block_31)
  (interval_append test104320 512 528 560
  test104320_block_32
  (interval_append test104320 528 544 560
  test104320_block_33
  test104320_block_34)))
  (interval_append test104320 560 592 640
  (interval_append test104320 560 576 592
  test104320_block_35
  test104320_block_36)
  (interval_append test104320 592 608 640
  test104320_block_37
  (interval_append test104320 608 624 640
  test104320_block_38
  test104320_block_39))))))
cert_nodeInterval_3 104320 104960
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
cert_test_11 104960
cert_test_block_3 104960 0 0 16 16
cert_test_block_3 104960 1 16 32 16
cert_test_block_3 104960 2 32 48 16
cert_test_block_3 104960 3 48 64 16
cert_test_block_3 104960 4 64 80 16
cert_test_block_3 104960 5 80 96 16
cert_test_block_3 104960 6 96 112 16
cert_test_block_3 104960 7 112 128 16
cert_test_block_3 104960 8 128 144 16
cert_test_block_3 104960 9 144 160 16
cert_test_block_3 104960 10 160 176 16
cert_test_block_3 104960 11 176 192 16
cert_test_block_3 104960 12 192 208 16
cert_test_block_3 104960 13 208 224 16
cert_test_block_3 104960 14 224 240 16
cert_test_block_3 104960 15 240 256 16
cert_test_block_3 104960 16 256 272 16
cert_test_block_3 104960 17 272 288 16
cert_test_block_3 104960 18 288 304 16
cert_test_block_3 104960 19 304 320 16
cert_test_block_3 104960 20 320 336 16
cert_test_block_3 104960 21 336 352 16
cert_test_block_3 104960 22 352 368 16
cert_test_block_3 104960 23 368 384 16
cert_test_block_3 104960 24 384 400 16
cert_test_block_3 104960 25 400 416 16
cert_test_block_3 104960 26 416 432 16
cert_test_block_3 104960 27 432 448 16
cert_test_block_3 104960 28 448 464 16
cert_test_block_3 104960 29 464 480 16
cert_test_block_3 104960 30 480 496 16
cert_test_block_3 104960 31 496 512 16
cert_test_block_3 104960 32 512 528 16
cert_test_block_3 104960 33 528 544 16
cert_test_block_3 104960 34 544 560 16
cert_test_block_3 104960 35 560 576 16
cert_test_block_3 104960 36 576 592 16
cert_test_block_3 104960 37 592 608 16
cert_test_block_3 104960 38 608 624 16
cert_test_block_3 104960 39 624 640 16
theorem test104960_complete : Interval test104960 0 640 :=
  (interval_append test104960 0 320 640
  (interval_append test104960 0 160 320
  (interval_append test104960 0 80 160
  (interval_append test104960 0 32 80
  (interval_append test104960 0 16 32
  test104960_block_0
  test104960_block_1)
  (interval_append test104960 32 48 80
  test104960_block_2
  (interval_append test104960 48 64 80
  test104960_block_3
  test104960_block_4)))
  (interval_append test104960 80 112 160
  (interval_append test104960 80 96 112
  test104960_block_5
  test104960_block_6)
  (interval_append test104960 112 128 160
  test104960_block_7
  (interval_append test104960 128 144 160
  test104960_block_8
  test104960_block_9))))
  (interval_append test104960 160 240 320
  (interval_append test104960 160 192 240
  (interval_append test104960 160 176 192
  test104960_block_10
  test104960_block_11)
  (interval_append test104960 192 208 240
  test104960_block_12
  (interval_append test104960 208 224 240
  test104960_block_13
  test104960_block_14)))
  (interval_append test104960 240 272 320
  (interval_append test104960 240 256 272
  test104960_block_15
  test104960_block_16)
  (interval_append test104960 272 288 320
  test104960_block_17
  (interval_append test104960 288 304 320
  test104960_block_18
  test104960_block_19)))))
  (interval_append test104960 320 480 640
  (interval_append test104960 320 400 480
  (interval_append test104960 320 352 400
  (interval_append test104960 320 336 352
  test104960_block_20
  test104960_block_21)
  (interval_append test104960 352 368 400
  test104960_block_22
  (interval_append test104960 368 384 400
  test104960_block_23
  test104960_block_24)))
  (interval_append test104960 400 432 480
  (interval_append test104960 400 416 432
  test104960_block_25
  test104960_block_26)
  (interval_append test104960 432 448 480
  test104960_block_27
  (interval_append test104960 448 464 480
  test104960_block_28
  test104960_block_29))))
  (interval_append test104960 480 560 640
  (interval_append test104960 480 512 560
  (interval_append test104960 480 496 512
  test104960_block_30
  test104960_block_31)
  (interval_append test104960 512 528 560
  test104960_block_32
  (interval_append test104960 528 544 560
  test104960_block_33
  test104960_block_34)))
  (interval_append test104960 560 592 640
  (interval_append test104960 560 576 592
  test104960_block_35
  test104960_block_36)
  (interval_append test104960 592 608 640
  test104960_block_37
  (interval_append test104960 608 624 640
  test104960_block_38
  test104960_block_39))))))
cert_nodeInterval_3 104960 105600
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
cert_test_11 105600
cert_test_block_3 105600 0 0 16 16
cert_test_block_3 105600 1 16 32 16
cert_test_block_3 105600 2 32 48 16
cert_test_block_3 105600 3 48 64 16
cert_test_block_3 105600 4 64 80 16
cert_test_block_3 105600 5 80 96 16
cert_test_block_3 105600 6 96 112 16
cert_test_block_3 105600 7 112 128 16
cert_test_block_3 105600 8 128 144 16
cert_test_block_3 105600 9 144 160 16
cert_test_block_3 105600 10 160 176 16
cert_test_block_3 105600 11 176 192 16
cert_test_block_3 105600 12 192 208 16
cert_test_block_3 105600 13 208 224 16
cert_test_block_3 105600 14 224 240 16
cert_test_block_3 105600 15 240 256 16
cert_test_block_3 105600 16 256 272 16
cert_test_block_3 105600 17 272 288 16
cert_test_block_3 105600 18 288 304 16
cert_test_block_3 105600 19 304 320 16
cert_test_block_3 105600 20 320 336 16
cert_test_block_3 105600 21 336 352 16
cert_test_block_3 105600 22 352 368 16
cert_test_block_3 105600 23 368 384 16
cert_test_block_3 105600 24 384 400 16
cert_test_block_3 105600 25 400 416 16
cert_test_block_3 105600 26 416 432 16
cert_test_block_3 105600 27 432 448 16
cert_test_block_3 105600 28 448 464 16
cert_test_block_3 105600 29 464 480 16
cert_test_block_3 105600 30 480 496 16
cert_test_block_3 105600 31 496 512 16
cert_test_block_3 105600 32 512 528 16
cert_test_block_3 105600 33 528 544 16
cert_test_block_3 105600 34 544 560 16
cert_test_block_3 105600 35 560 576 16
cert_test_block_3 105600 36 576 592 16
cert_test_block_3 105600 37 592 608 16
cert_test_block_3 105600 38 608 624 16
cert_test_block_3 105600 39 624 640 16
theorem test105600_complete : Interval test105600 0 640 :=
  (interval_append test105600 0 320 640
  (interval_append test105600 0 160 320
  (interval_append test105600 0 80 160
  (interval_append test105600 0 32 80
  (interval_append test105600 0 16 32
  test105600_block_0
  test105600_block_1)
  (interval_append test105600 32 48 80
  test105600_block_2
  (interval_append test105600 48 64 80
  test105600_block_3
  test105600_block_4)))
  (interval_append test105600 80 112 160
  (interval_append test105600 80 96 112
  test105600_block_5
  test105600_block_6)
  (interval_append test105600 112 128 160
  test105600_block_7
  (interval_append test105600 128 144 160
  test105600_block_8
  test105600_block_9))))
  (interval_append test105600 160 240 320
  (interval_append test105600 160 192 240
  (interval_append test105600 160 176 192
  test105600_block_10
  test105600_block_11)
  (interval_append test105600 192 208 240
  test105600_block_12
  (interval_append test105600 208 224 240
  test105600_block_13
  test105600_block_14)))
  (interval_append test105600 240 272 320
  (interval_append test105600 240 256 272
  test105600_block_15
  test105600_block_16)
  (interval_append test105600 272 288 320
  test105600_block_17
  (interval_append test105600 288 304 320
  test105600_block_18
  test105600_block_19)))))
  (interval_append test105600 320 480 640
  (interval_append test105600 320 400 480
  (interval_append test105600 320 352 400
  (interval_append test105600 320 336 352
  test105600_block_20
  test105600_block_21)
  (interval_append test105600 352 368 400
  test105600_block_22
  (interval_append test105600 368 384 400
  test105600_block_23
  test105600_block_24)))
  (interval_append test105600 400 432 480
  (interval_append test105600 400 416 432
  test105600_block_25
  test105600_block_26)
  (interval_append test105600 432 448 480
  test105600_block_27
  (interval_append test105600 448 464 480
  test105600_block_28
  test105600_block_29))))
  (interval_append test105600 480 560 640
  (interval_append test105600 480 512 560
  (interval_append test105600 480 496 512
  test105600_block_30
  test105600_block_31)
  (interval_append test105600 512 528 560
  test105600_block_32
  (interval_append test105600 528 544 560
  test105600_block_33
  test105600_block_34)))
  (interval_append test105600 560 592 640
  (interval_append test105600 560 576 592
  test105600_block_35
  test105600_block_36)
  (interval_append test105600 592 608 640
  test105600_block_37
  (interval_append test105600 608 624 640
  test105600_block_38
  test105600_block_39))))))
cert_nodeInterval_3 105600 106240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
