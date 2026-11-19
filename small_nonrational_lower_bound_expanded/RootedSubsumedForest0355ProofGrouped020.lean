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
cert_test_11 150400
cert_test_block_3 150400 0 0 16 16
cert_test_block_3 150400 1 16 32 16
cert_test_block_3 150400 2 32 48 16
cert_test_block_3 150400 3 48 64 16
cert_test_block_3 150400 4 64 80 16
cert_test_block_3 150400 5 80 96 16
cert_test_block_3 150400 6 96 112 16
cert_test_block_3 150400 7 112 128 16
cert_test_block_3 150400 8 128 144 16
cert_test_block_3 150400 9 144 160 16
cert_test_block_3 150400 10 160 176 16
cert_test_block_3 150400 11 176 192 16
cert_test_block_3 150400 12 192 208 16
cert_test_block_3 150400 13 208 224 16
cert_test_block_3 150400 14 224 240 16
cert_test_block_3 150400 15 240 256 16
cert_test_block_3 150400 16 256 272 16
cert_test_block_3 150400 17 272 288 16
cert_test_block_3 150400 18 288 304 16
cert_test_block_3 150400 19 304 320 16
cert_test_block_3 150400 20 320 336 16
cert_test_block_3 150400 21 336 352 16
cert_test_block_3 150400 22 352 368 16
cert_test_block_3 150400 23 368 384 16
cert_test_block_3 150400 24 384 400 16
cert_test_block_3 150400 25 400 416 16
cert_test_block_3 150400 26 416 432 16
cert_test_block_3 150400 27 432 448 16
cert_test_block_3 150400 28 448 464 16
cert_test_block_3 150400 29 464 480 16
cert_test_block_3 150400 30 480 496 16
cert_test_block_3 150400 31 496 512 16
cert_test_block_3 150400 32 512 528 16
cert_test_block_3 150400 33 528 544 16
cert_test_block_3 150400 34 544 560 16
cert_test_block_3 150400 35 560 576 16
cert_test_block_3 150400 36 576 592 16
cert_test_block_3 150400 37 592 608 16
cert_test_block_3 150400 38 608 624 16
cert_test_block_3 150400 39 624 640 16
theorem test150400_complete : Interval test150400 0 640 :=
  (interval_append test150400 0 320 640
  (interval_append test150400 0 160 320
  (interval_append test150400 0 80 160
  (interval_append test150400 0 32 80
  (interval_append test150400 0 16 32
  test150400_block_0
  test150400_block_1)
  (interval_append test150400 32 48 80
  test150400_block_2
  (interval_append test150400 48 64 80
  test150400_block_3
  test150400_block_4)))
  (interval_append test150400 80 112 160
  (interval_append test150400 80 96 112
  test150400_block_5
  test150400_block_6)
  (interval_append test150400 112 128 160
  test150400_block_7
  (interval_append test150400 128 144 160
  test150400_block_8
  test150400_block_9))))
  (interval_append test150400 160 240 320
  (interval_append test150400 160 192 240
  (interval_append test150400 160 176 192
  test150400_block_10
  test150400_block_11)
  (interval_append test150400 192 208 240
  test150400_block_12
  (interval_append test150400 208 224 240
  test150400_block_13
  test150400_block_14)))
  (interval_append test150400 240 272 320
  (interval_append test150400 240 256 272
  test150400_block_15
  test150400_block_16)
  (interval_append test150400 272 288 320
  test150400_block_17
  (interval_append test150400 288 304 320
  test150400_block_18
  test150400_block_19)))))
  (interval_append test150400 320 480 640
  (interval_append test150400 320 400 480
  (interval_append test150400 320 352 400
  (interval_append test150400 320 336 352
  test150400_block_20
  test150400_block_21)
  (interval_append test150400 352 368 400
  test150400_block_22
  (interval_append test150400 368 384 400
  test150400_block_23
  test150400_block_24)))
  (interval_append test150400 400 432 480
  (interval_append test150400 400 416 432
  test150400_block_25
  test150400_block_26)
  (interval_append test150400 432 448 480
  test150400_block_27
  (interval_append test150400 448 464 480
  test150400_block_28
  test150400_block_29))))
  (interval_append test150400 480 560 640
  (interval_append test150400 480 512 560
  (interval_append test150400 480 496 512
  test150400_block_30
  test150400_block_31)
  (interval_append test150400 512 528 560
  test150400_block_32
  (interval_append test150400 528 544 560
  test150400_block_33
  test150400_block_34)))
  (interval_append test150400 560 592 640
  (interval_append test150400 560 576 592
  test150400_block_35
  test150400_block_36)
  (interval_append test150400 592 608 640
  test150400_block_37
  (interval_append test150400 608 624 640
  test150400_block_38
  test150400_block_39))))))
cert_nodeInterval_3 150400 151040
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
cert_test_11 151040
cert_test_block_3 151040 0 0 16 16
cert_test_block_3 151040 1 16 32 16
cert_test_block_3 151040 2 32 48 16
cert_test_block_3 151040 3 48 64 16
cert_test_block_3 151040 4 64 80 16
cert_test_block_3 151040 5 80 96 16
cert_test_block_3 151040 6 96 112 16
cert_test_block_3 151040 7 112 128 16
cert_test_block_3 151040 8 128 144 16
cert_test_block_3 151040 9 144 160 16
cert_test_block_3 151040 10 160 176 16
cert_test_block_3 151040 11 176 192 16
cert_test_block_3 151040 12 192 208 16
cert_test_block_3 151040 13 208 224 16
cert_test_block_3 151040 14 224 240 16
cert_test_block_3 151040 15 240 256 16
cert_test_block_3 151040 16 256 272 16
cert_test_block_3 151040 17 272 288 16
cert_test_block_3 151040 18 288 304 16
cert_test_block_3 151040 19 304 320 16
cert_test_block_3 151040 20 320 336 16
cert_test_block_3 151040 21 336 352 16
cert_test_block_3 151040 22 352 368 16
cert_test_block_3 151040 23 368 384 16
cert_test_block_3 151040 24 384 400 16
cert_test_block_3 151040 25 400 416 16
cert_test_block_3 151040 26 416 432 16
cert_test_block_3 151040 27 432 448 16
cert_test_block_3 151040 28 448 464 16
cert_test_block_3 151040 29 464 480 16
cert_test_block_3 151040 30 480 496 16
cert_test_block_3 151040 31 496 512 16
cert_test_block_3 151040 32 512 528 16
cert_test_block_3 151040 33 528 544 16
cert_test_block_3 151040 34 544 560 16
cert_test_block_3 151040 35 560 576 16
cert_test_block_3 151040 36 576 592 16
cert_test_block_3 151040 37 592 608 16
cert_test_block_3 151040 38 608 624 16
cert_test_block_3 151040 39 624 640 16
theorem test151040_complete : Interval test151040 0 640 :=
  (interval_append test151040 0 320 640
  (interval_append test151040 0 160 320
  (interval_append test151040 0 80 160
  (interval_append test151040 0 32 80
  (interval_append test151040 0 16 32
  test151040_block_0
  test151040_block_1)
  (interval_append test151040 32 48 80
  test151040_block_2
  (interval_append test151040 48 64 80
  test151040_block_3
  test151040_block_4)))
  (interval_append test151040 80 112 160
  (interval_append test151040 80 96 112
  test151040_block_5
  test151040_block_6)
  (interval_append test151040 112 128 160
  test151040_block_7
  (interval_append test151040 128 144 160
  test151040_block_8
  test151040_block_9))))
  (interval_append test151040 160 240 320
  (interval_append test151040 160 192 240
  (interval_append test151040 160 176 192
  test151040_block_10
  test151040_block_11)
  (interval_append test151040 192 208 240
  test151040_block_12
  (interval_append test151040 208 224 240
  test151040_block_13
  test151040_block_14)))
  (interval_append test151040 240 272 320
  (interval_append test151040 240 256 272
  test151040_block_15
  test151040_block_16)
  (interval_append test151040 272 288 320
  test151040_block_17
  (interval_append test151040 288 304 320
  test151040_block_18
  test151040_block_19)))))
  (interval_append test151040 320 480 640
  (interval_append test151040 320 400 480
  (interval_append test151040 320 352 400
  (interval_append test151040 320 336 352
  test151040_block_20
  test151040_block_21)
  (interval_append test151040 352 368 400
  test151040_block_22
  (interval_append test151040 368 384 400
  test151040_block_23
  test151040_block_24)))
  (interval_append test151040 400 432 480
  (interval_append test151040 400 416 432
  test151040_block_25
  test151040_block_26)
  (interval_append test151040 432 448 480
  test151040_block_27
  (interval_append test151040 448 464 480
  test151040_block_28
  test151040_block_29))))
  (interval_append test151040 480 560 640
  (interval_append test151040 480 512 560
  (interval_append test151040 480 496 512
  test151040_block_30
  test151040_block_31)
  (interval_append test151040 512 528 560
  test151040_block_32
  (interval_append test151040 528 544 560
  test151040_block_33
  test151040_block_34)))
  (interval_append test151040 560 592 640
  (interval_append test151040 560 576 592
  test151040_block_35
  test151040_block_36)
  (interval_append test151040 592 608 640
  test151040_block_37
  (interval_append test151040 608 624 640
  test151040_block_38
  test151040_block_39))))))
cert_nodeInterval_3 151040 151680
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
cert_test_11 151680
cert_test_block_3 151680 0 0 16 16
cert_test_block_3 151680 1 16 32 16
cert_test_block_3 151680 2 32 48 16
cert_test_block_3 151680 3 48 64 16
cert_test_block_3 151680 4 64 80 16
cert_test_block_3 151680 5 80 96 16
cert_test_block_3 151680 6 96 112 16
cert_test_block_3 151680 7 112 128 16
cert_test_block_3 151680 8 128 144 16
cert_test_block_3 151680 9 144 160 16
cert_test_block_3 151680 10 160 176 16
cert_test_block_3 151680 11 176 192 16
cert_test_block_3 151680 12 192 208 16
cert_test_block_3 151680 13 208 224 16
cert_test_block_3 151680 14 224 240 16
cert_test_block_3 151680 15 240 256 16
cert_test_block_3 151680 16 256 272 16
cert_test_block_3 151680 17 272 288 16
cert_test_block_3 151680 18 288 304 16
cert_test_block_3 151680 19 304 320 16
cert_test_block_3 151680 20 320 336 16
cert_test_block_3 151680 21 336 352 16
cert_test_block_3 151680 22 352 368 16
cert_test_block_3 151680 23 368 384 16
cert_test_block_3 151680 24 384 400 16
cert_test_block_3 151680 25 400 416 16
cert_test_block_3 151680 26 416 432 16
cert_test_block_3 151680 27 432 448 16
cert_test_block_3 151680 28 448 464 16
cert_test_block_3 151680 29 464 480 16
cert_test_block_3 151680 30 480 496 16
cert_test_block_3 151680 31 496 512 16
cert_test_block_3 151680 32 512 528 16
cert_test_block_3 151680 33 528 544 16
cert_test_block_3 151680 34 544 560 16
cert_test_block_3 151680 35 560 576 16
cert_test_block_3 151680 36 576 592 16
cert_test_block_3 151680 37 592 608 16
cert_test_block_3 151680 38 608 624 16
cert_test_block_3 151680 39 624 640 16
theorem test151680_complete : Interval test151680 0 640 :=
  (interval_append test151680 0 320 640
  (interval_append test151680 0 160 320
  (interval_append test151680 0 80 160
  (interval_append test151680 0 32 80
  (interval_append test151680 0 16 32
  test151680_block_0
  test151680_block_1)
  (interval_append test151680 32 48 80
  test151680_block_2
  (interval_append test151680 48 64 80
  test151680_block_3
  test151680_block_4)))
  (interval_append test151680 80 112 160
  (interval_append test151680 80 96 112
  test151680_block_5
  test151680_block_6)
  (interval_append test151680 112 128 160
  test151680_block_7
  (interval_append test151680 128 144 160
  test151680_block_8
  test151680_block_9))))
  (interval_append test151680 160 240 320
  (interval_append test151680 160 192 240
  (interval_append test151680 160 176 192
  test151680_block_10
  test151680_block_11)
  (interval_append test151680 192 208 240
  test151680_block_12
  (interval_append test151680 208 224 240
  test151680_block_13
  test151680_block_14)))
  (interval_append test151680 240 272 320
  (interval_append test151680 240 256 272
  test151680_block_15
  test151680_block_16)
  (interval_append test151680 272 288 320
  test151680_block_17
  (interval_append test151680 288 304 320
  test151680_block_18
  test151680_block_19)))))
  (interval_append test151680 320 480 640
  (interval_append test151680 320 400 480
  (interval_append test151680 320 352 400
  (interval_append test151680 320 336 352
  test151680_block_20
  test151680_block_21)
  (interval_append test151680 352 368 400
  test151680_block_22
  (interval_append test151680 368 384 400
  test151680_block_23
  test151680_block_24)))
  (interval_append test151680 400 432 480
  (interval_append test151680 400 416 432
  test151680_block_25
  test151680_block_26)
  (interval_append test151680 432 448 480
  test151680_block_27
  (interval_append test151680 448 464 480
  test151680_block_28
  test151680_block_29))))
  (interval_append test151680 480 560 640
  (interval_append test151680 480 512 560
  (interval_append test151680 480 496 512
  test151680_block_30
  test151680_block_31)
  (interval_append test151680 512 528 560
  test151680_block_32
  (interval_append test151680 528 544 560
  test151680_block_33
  test151680_block_34)))
  (interval_append test151680 560 592 640
  (interval_append test151680 560 576 592
  test151680_block_35
  test151680_block_36)
  (interval_append test151680 592 608 640
  test151680_block_37
  (interval_append test151680 608 624 640
  test151680_block_38
  test151680_block_39))))))
cert_nodeInterval_3 151680 152320
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
cert_test_11 152320
cert_test_block_3 152320 0 0 16 16
cert_test_block_3 152320 1 16 32 16
cert_test_block_3 152320 2 32 48 16
cert_test_block_3 152320 3 48 64 16
cert_test_block_3 152320 4 64 80 16
cert_test_block_3 152320 5 80 96 16
cert_test_block_3 152320 6 96 112 16
cert_test_block_3 152320 7 112 128 16
cert_test_block_3 152320 8 128 144 16
cert_test_block_3 152320 9 144 160 16
cert_test_block_3 152320 10 160 176 16
cert_test_block_3 152320 11 176 192 16
cert_test_block_3 152320 12 192 208 16
cert_test_block_3 152320 13 208 224 16
cert_test_block_3 152320 14 224 240 16
cert_test_block_3 152320 15 240 256 16
cert_test_block_3 152320 16 256 272 16
cert_test_block_3 152320 17 272 288 16
cert_test_block_3 152320 18 288 304 16
cert_test_block_3 152320 19 304 320 16
cert_test_block_3 152320 20 320 336 16
cert_test_block_3 152320 21 336 352 16
cert_test_block_3 152320 22 352 368 16
cert_test_block_3 152320 23 368 384 16
cert_test_block_3 152320 24 384 400 16
cert_test_block_3 152320 25 400 416 16
cert_test_block_3 152320 26 416 432 16
cert_test_block_3 152320 27 432 448 16
cert_test_block_3 152320 28 448 464 16
cert_test_block_3 152320 29 464 480 16
cert_test_block_3 152320 30 480 496 16
cert_test_block_3 152320 31 496 512 16
cert_test_block_3 152320 32 512 528 16
cert_test_block_3 152320 33 528 544 16
cert_test_block_3 152320 34 544 560 16
cert_test_block_3 152320 35 560 576 16
cert_test_block_3 152320 36 576 592 16
cert_test_block_3 152320 37 592 608 16
cert_test_block_3 152320 38 608 624 16
cert_test_block_3 152320 39 624 640 16
theorem test152320_complete : Interval test152320 0 640 :=
  (interval_append test152320 0 320 640
  (interval_append test152320 0 160 320
  (interval_append test152320 0 80 160
  (interval_append test152320 0 32 80
  (interval_append test152320 0 16 32
  test152320_block_0
  test152320_block_1)
  (interval_append test152320 32 48 80
  test152320_block_2
  (interval_append test152320 48 64 80
  test152320_block_3
  test152320_block_4)))
  (interval_append test152320 80 112 160
  (interval_append test152320 80 96 112
  test152320_block_5
  test152320_block_6)
  (interval_append test152320 112 128 160
  test152320_block_7
  (interval_append test152320 128 144 160
  test152320_block_8
  test152320_block_9))))
  (interval_append test152320 160 240 320
  (interval_append test152320 160 192 240
  (interval_append test152320 160 176 192
  test152320_block_10
  test152320_block_11)
  (interval_append test152320 192 208 240
  test152320_block_12
  (interval_append test152320 208 224 240
  test152320_block_13
  test152320_block_14)))
  (interval_append test152320 240 272 320
  (interval_append test152320 240 256 272
  test152320_block_15
  test152320_block_16)
  (interval_append test152320 272 288 320
  test152320_block_17
  (interval_append test152320 288 304 320
  test152320_block_18
  test152320_block_19)))))
  (interval_append test152320 320 480 640
  (interval_append test152320 320 400 480
  (interval_append test152320 320 352 400
  (interval_append test152320 320 336 352
  test152320_block_20
  test152320_block_21)
  (interval_append test152320 352 368 400
  test152320_block_22
  (interval_append test152320 368 384 400
  test152320_block_23
  test152320_block_24)))
  (interval_append test152320 400 432 480
  (interval_append test152320 400 416 432
  test152320_block_25
  test152320_block_26)
  (interval_append test152320 432 448 480
  test152320_block_27
  (interval_append test152320 448 464 480
  test152320_block_28
  test152320_block_29))))
  (interval_append test152320 480 560 640
  (interval_append test152320 480 512 560
  (interval_append test152320 480 496 512
  test152320_block_30
  test152320_block_31)
  (interval_append test152320 512 528 560
  test152320_block_32
  (interval_append test152320 528 544 560
  test152320_block_33
  test152320_block_34)))
  (interval_append test152320 560 592 640
  (interval_append test152320 560 576 592
  test152320_block_35
  test152320_block_36)
  (interval_append test152320 592 608 640
  test152320_block_37
  (interval_append test152320 608 624 640
  test152320_block_38
  test152320_block_39))))))
cert_nodeInterval_3 152320 152960
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
cert_test_11 152960
cert_test_block_3 152960 0 0 16 16
cert_test_block_3 152960 1 16 32 16
cert_test_block_3 152960 2 32 48 16
cert_test_block_3 152960 3 48 64 16
cert_test_block_3 152960 4 64 80 16
cert_test_block_3 152960 5 80 96 16
cert_test_block_3 152960 6 96 112 16
cert_test_block_3 152960 7 112 128 16
cert_test_block_3 152960 8 128 144 16
cert_test_block_3 152960 9 144 160 16
cert_test_block_3 152960 10 160 176 16
cert_test_block_3 152960 11 176 192 16
cert_test_block_3 152960 12 192 208 16
cert_test_block_3 152960 13 208 224 16
cert_test_block_3 152960 14 224 240 16
cert_test_block_3 152960 15 240 256 16
cert_test_block_3 152960 16 256 272 16
cert_test_block_3 152960 17 272 288 16
cert_test_block_3 152960 18 288 304 16
cert_test_block_3 152960 19 304 320 16
cert_test_block_3 152960 20 320 336 16
cert_test_block_3 152960 21 336 352 16
cert_test_block_3 152960 22 352 368 16
cert_test_block_3 152960 23 368 384 16
cert_test_block_3 152960 24 384 400 16
cert_test_block_3 152960 25 400 416 16
cert_test_block_3 152960 26 416 432 16
cert_test_block_3 152960 27 432 448 16
cert_test_block_3 152960 28 448 464 16
cert_test_block_3 152960 29 464 480 16
cert_test_block_3 152960 30 480 496 16
cert_test_block_3 152960 31 496 512 16
cert_test_block_3 152960 32 512 528 16
cert_test_block_3 152960 33 528 544 16
cert_test_block_3 152960 34 544 560 16
cert_test_block_3 152960 35 560 576 16
cert_test_block_3 152960 36 576 592 16
cert_test_block_3 152960 37 592 608 16
cert_test_block_3 152960 38 608 624 16
cert_test_block_3 152960 39 624 640 16
theorem test152960_complete : Interval test152960 0 640 :=
  (interval_append test152960 0 320 640
  (interval_append test152960 0 160 320
  (interval_append test152960 0 80 160
  (interval_append test152960 0 32 80
  (interval_append test152960 0 16 32
  test152960_block_0
  test152960_block_1)
  (interval_append test152960 32 48 80
  test152960_block_2
  (interval_append test152960 48 64 80
  test152960_block_3
  test152960_block_4)))
  (interval_append test152960 80 112 160
  (interval_append test152960 80 96 112
  test152960_block_5
  test152960_block_6)
  (interval_append test152960 112 128 160
  test152960_block_7
  (interval_append test152960 128 144 160
  test152960_block_8
  test152960_block_9))))
  (interval_append test152960 160 240 320
  (interval_append test152960 160 192 240
  (interval_append test152960 160 176 192
  test152960_block_10
  test152960_block_11)
  (interval_append test152960 192 208 240
  test152960_block_12
  (interval_append test152960 208 224 240
  test152960_block_13
  test152960_block_14)))
  (interval_append test152960 240 272 320
  (interval_append test152960 240 256 272
  test152960_block_15
  test152960_block_16)
  (interval_append test152960 272 288 320
  test152960_block_17
  (interval_append test152960 288 304 320
  test152960_block_18
  test152960_block_19)))))
  (interval_append test152960 320 480 640
  (interval_append test152960 320 400 480
  (interval_append test152960 320 352 400
  (interval_append test152960 320 336 352
  test152960_block_20
  test152960_block_21)
  (interval_append test152960 352 368 400
  test152960_block_22
  (interval_append test152960 368 384 400
  test152960_block_23
  test152960_block_24)))
  (interval_append test152960 400 432 480
  (interval_append test152960 400 416 432
  test152960_block_25
  test152960_block_26)
  (interval_append test152960 432 448 480
  test152960_block_27
  (interval_append test152960 448 464 480
  test152960_block_28
  test152960_block_29))))
  (interval_append test152960 480 560 640
  (interval_append test152960 480 512 560
  (interval_append test152960 480 496 512
  test152960_block_30
  test152960_block_31)
  (interval_append test152960 512 528 560
  test152960_block_32
  (interval_append test152960 528 544 560
  test152960_block_33
  test152960_block_34)))
  (interval_append test152960 560 592 640
  (interval_append test152960 560 576 592
  test152960_block_35
  test152960_block_36)
  (interval_append test152960 592 608 640
  test152960_block_37
  (interval_append test152960 608 624 640
  test152960_block_38
  test152960_block_39))))))
cert_nodeInterval_3 152960 153600
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
cert_test_11 153600
cert_test_block_3 153600 0 0 16 16
cert_test_block_3 153600 1 16 32 16
cert_test_block_3 153600 2 32 48 16
cert_test_block_3 153600 3 48 64 16
cert_test_block_3 153600 4 64 80 16
cert_test_block_3 153600 5 80 96 16
cert_test_block_3 153600 6 96 112 16
cert_test_block_3 153600 7 112 128 16
cert_test_block_3 153600 8 128 144 16
cert_test_block_3 153600 9 144 160 16
cert_test_block_3 153600 10 160 176 16
cert_test_block_3 153600 11 176 192 16
cert_test_block_3 153600 12 192 208 16
cert_test_block_3 153600 13 208 224 16
cert_test_block_3 153600 14 224 240 16
cert_test_block_3 153600 15 240 256 16
cert_test_block_3 153600 16 256 272 16
cert_test_block_3 153600 17 272 288 16
cert_test_block_3 153600 18 288 304 16
cert_test_block_3 153600 19 304 320 16
cert_test_block_3 153600 20 320 336 16
cert_test_block_3 153600 21 336 352 16
cert_test_block_3 153600 22 352 368 16
cert_test_block_3 153600 23 368 384 16
cert_test_block_3 153600 24 384 400 16
cert_test_block_3 153600 25 400 416 16
cert_test_block_3 153600 26 416 432 16
cert_test_block_3 153600 27 432 448 16
cert_test_block_3 153600 28 448 464 16
cert_test_block_3 153600 29 464 480 16
cert_test_block_3 153600 30 480 496 16
cert_test_block_3 153600 31 496 512 16
cert_test_block_3 153600 32 512 528 16
cert_test_block_3 153600 33 528 544 16
cert_test_block_3 153600 34 544 560 16
cert_test_block_3 153600 35 560 576 16
cert_test_block_3 153600 36 576 592 16
cert_test_block_3 153600 37 592 608 16
cert_test_block_3 153600 38 608 624 16
cert_test_block_3 153600 39 624 640 16
theorem test153600_complete : Interval test153600 0 640 :=
  (interval_append test153600 0 320 640
  (interval_append test153600 0 160 320
  (interval_append test153600 0 80 160
  (interval_append test153600 0 32 80
  (interval_append test153600 0 16 32
  test153600_block_0
  test153600_block_1)
  (interval_append test153600 32 48 80
  test153600_block_2
  (interval_append test153600 48 64 80
  test153600_block_3
  test153600_block_4)))
  (interval_append test153600 80 112 160
  (interval_append test153600 80 96 112
  test153600_block_5
  test153600_block_6)
  (interval_append test153600 112 128 160
  test153600_block_7
  (interval_append test153600 128 144 160
  test153600_block_8
  test153600_block_9))))
  (interval_append test153600 160 240 320
  (interval_append test153600 160 192 240
  (interval_append test153600 160 176 192
  test153600_block_10
  test153600_block_11)
  (interval_append test153600 192 208 240
  test153600_block_12
  (interval_append test153600 208 224 240
  test153600_block_13
  test153600_block_14)))
  (interval_append test153600 240 272 320
  (interval_append test153600 240 256 272
  test153600_block_15
  test153600_block_16)
  (interval_append test153600 272 288 320
  test153600_block_17
  (interval_append test153600 288 304 320
  test153600_block_18
  test153600_block_19)))))
  (interval_append test153600 320 480 640
  (interval_append test153600 320 400 480
  (interval_append test153600 320 352 400
  (interval_append test153600 320 336 352
  test153600_block_20
  test153600_block_21)
  (interval_append test153600 352 368 400
  test153600_block_22
  (interval_append test153600 368 384 400
  test153600_block_23
  test153600_block_24)))
  (interval_append test153600 400 432 480
  (interval_append test153600 400 416 432
  test153600_block_25
  test153600_block_26)
  (interval_append test153600 432 448 480
  test153600_block_27
  (interval_append test153600 448 464 480
  test153600_block_28
  test153600_block_29))))
  (interval_append test153600 480 560 640
  (interval_append test153600 480 512 560
  (interval_append test153600 480 496 512
  test153600_block_30
  test153600_block_31)
  (interval_append test153600 512 528 560
  test153600_block_32
  (interval_append test153600 528 544 560
  test153600_block_33
  test153600_block_34)))
  (interval_append test153600 560 592 640
  (interval_append test153600 560 576 592
  test153600_block_35
  test153600_block_36)
  (interval_append test153600 592 608 640
  test153600_block_37
  (interval_append test153600 608 624 640
  test153600_block_38
  test153600_block_39))))))
cert_nodeInterval_3 153600 154240
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
cert_test_11 154240
cert_test_block_3 154240 0 0 16 16
cert_test_block_3 154240 1 16 32 16
cert_test_block_3 154240 2 32 48 16
cert_test_block_3 154240 3 48 64 16
cert_test_block_3 154240 4 64 80 16
cert_test_block_3 154240 5 80 96 16
cert_test_block_3 154240 6 96 112 16
cert_test_block_3 154240 7 112 128 16
cert_test_block_3 154240 8 128 144 16
cert_test_block_3 154240 9 144 160 16
cert_test_block_3 154240 10 160 176 16
cert_test_block_3 154240 11 176 192 16
cert_test_block_3 154240 12 192 208 16
cert_test_block_3 154240 13 208 224 16
cert_test_block_3 154240 14 224 240 16
cert_test_block_3 154240 15 240 256 16
cert_test_block_3 154240 16 256 272 16
cert_test_block_3 154240 17 272 288 16
cert_test_block_3 154240 18 288 304 16
cert_test_block_3 154240 19 304 320 16
cert_test_block_3 154240 20 320 336 16
cert_test_block_3 154240 21 336 352 16
cert_test_block_3 154240 22 352 368 16
cert_test_block_3 154240 23 368 384 16
cert_test_block_3 154240 24 384 400 16
cert_test_block_3 154240 25 400 416 16
cert_test_block_3 154240 26 416 432 16
cert_test_block_3 154240 27 432 448 16
cert_test_block_3 154240 28 448 464 16
cert_test_block_3 154240 29 464 480 16
cert_test_block_3 154240 30 480 496 16
cert_test_block_3 154240 31 496 512 16
cert_test_block_3 154240 32 512 528 16
cert_test_block_3 154240 33 528 544 16
cert_test_block_3 154240 34 544 560 16
cert_test_block_3 154240 35 560 576 16
cert_test_block_3 154240 36 576 592 16
cert_test_block_3 154240 37 592 608 16
cert_test_block_3 154240 38 608 624 16
cert_test_block_3 154240 39 624 640 16
theorem test154240_complete : Interval test154240 0 640 :=
  (interval_append test154240 0 320 640
  (interval_append test154240 0 160 320
  (interval_append test154240 0 80 160
  (interval_append test154240 0 32 80
  (interval_append test154240 0 16 32
  test154240_block_0
  test154240_block_1)
  (interval_append test154240 32 48 80
  test154240_block_2
  (interval_append test154240 48 64 80
  test154240_block_3
  test154240_block_4)))
  (interval_append test154240 80 112 160
  (interval_append test154240 80 96 112
  test154240_block_5
  test154240_block_6)
  (interval_append test154240 112 128 160
  test154240_block_7
  (interval_append test154240 128 144 160
  test154240_block_8
  test154240_block_9))))
  (interval_append test154240 160 240 320
  (interval_append test154240 160 192 240
  (interval_append test154240 160 176 192
  test154240_block_10
  test154240_block_11)
  (interval_append test154240 192 208 240
  test154240_block_12
  (interval_append test154240 208 224 240
  test154240_block_13
  test154240_block_14)))
  (interval_append test154240 240 272 320
  (interval_append test154240 240 256 272
  test154240_block_15
  test154240_block_16)
  (interval_append test154240 272 288 320
  test154240_block_17
  (interval_append test154240 288 304 320
  test154240_block_18
  test154240_block_19)))))
  (interval_append test154240 320 480 640
  (interval_append test154240 320 400 480
  (interval_append test154240 320 352 400
  (interval_append test154240 320 336 352
  test154240_block_20
  test154240_block_21)
  (interval_append test154240 352 368 400
  test154240_block_22
  (interval_append test154240 368 384 400
  test154240_block_23
  test154240_block_24)))
  (interval_append test154240 400 432 480
  (interval_append test154240 400 416 432
  test154240_block_25
  test154240_block_26)
  (interval_append test154240 432 448 480
  test154240_block_27
  (interval_append test154240 448 464 480
  test154240_block_28
  test154240_block_29))))
  (interval_append test154240 480 560 640
  (interval_append test154240 480 512 560
  (interval_append test154240 480 496 512
  test154240_block_30
  test154240_block_31)
  (interval_append test154240 512 528 560
  test154240_block_32
  (interval_append test154240 528 544 560
  test154240_block_33
  test154240_block_34)))
  (interval_append test154240 560 592 640
  (interval_append test154240 560 576 592
  test154240_block_35
  test154240_block_36)
  (interval_append test154240 592 608 640
  test154240_block_37
  (interval_append test154240 608 624 640
  test154240_block_38
  test154240_block_39))))))
cert_nodeInterval_3 154240 154880
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
cert_test_11 154880
cert_test_block_3 154880 0 0 16 16
cert_test_block_3 154880 1 16 32 16
cert_test_block_3 154880 2 32 48 16
cert_test_block_3 154880 3 48 64 16
cert_test_block_3 154880 4 64 80 16
cert_test_block_3 154880 5 80 96 16
cert_test_block_3 154880 6 96 112 16
cert_test_block_3 154880 7 112 128 16
cert_test_block_3 154880 8 128 144 16
cert_test_block_3 154880 9 144 160 16
cert_test_block_3 154880 10 160 176 16
cert_test_block_3 154880 11 176 192 16
cert_test_block_3 154880 12 192 208 16
cert_test_block_3 154880 13 208 224 16
cert_test_block_3 154880 14 224 240 16
cert_test_block_3 154880 15 240 256 16
cert_test_block_3 154880 16 256 272 16
cert_test_block_3 154880 17 272 288 16
cert_test_block_3 154880 18 288 304 16
cert_test_block_3 154880 19 304 320 16
cert_test_block_3 154880 20 320 336 16
cert_test_block_3 154880 21 336 352 16
cert_test_block_3 154880 22 352 368 16
cert_test_block_3 154880 23 368 384 16
cert_test_block_3 154880 24 384 400 16
cert_test_block_3 154880 25 400 416 16
cert_test_block_3 154880 26 416 432 16
cert_test_block_3 154880 27 432 448 16
cert_test_block_3 154880 28 448 464 16
cert_test_block_3 154880 29 464 480 16
cert_test_block_3 154880 30 480 496 16
cert_test_block_3 154880 31 496 512 16
cert_test_block_3 154880 32 512 528 16
cert_test_block_3 154880 33 528 544 16
cert_test_block_3 154880 34 544 560 16
cert_test_block_3 154880 35 560 576 16
cert_test_block_3 154880 36 576 592 16
cert_test_block_3 154880 37 592 608 16
cert_test_block_3 154880 38 608 624 16
cert_test_block_3 154880 39 624 640 16
theorem test154880_complete : Interval test154880 0 640 :=
  (interval_append test154880 0 320 640
  (interval_append test154880 0 160 320
  (interval_append test154880 0 80 160
  (interval_append test154880 0 32 80
  (interval_append test154880 0 16 32
  test154880_block_0
  test154880_block_1)
  (interval_append test154880 32 48 80
  test154880_block_2
  (interval_append test154880 48 64 80
  test154880_block_3
  test154880_block_4)))
  (interval_append test154880 80 112 160
  (interval_append test154880 80 96 112
  test154880_block_5
  test154880_block_6)
  (interval_append test154880 112 128 160
  test154880_block_7
  (interval_append test154880 128 144 160
  test154880_block_8
  test154880_block_9))))
  (interval_append test154880 160 240 320
  (interval_append test154880 160 192 240
  (interval_append test154880 160 176 192
  test154880_block_10
  test154880_block_11)
  (interval_append test154880 192 208 240
  test154880_block_12
  (interval_append test154880 208 224 240
  test154880_block_13
  test154880_block_14)))
  (interval_append test154880 240 272 320
  (interval_append test154880 240 256 272
  test154880_block_15
  test154880_block_16)
  (interval_append test154880 272 288 320
  test154880_block_17
  (interval_append test154880 288 304 320
  test154880_block_18
  test154880_block_19)))))
  (interval_append test154880 320 480 640
  (interval_append test154880 320 400 480
  (interval_append test154880 320 352 400
  (interval_append test154880 320 336 352
  test154880_block_20
  test154880_block_21)
  (interval_append test154880 352 368 400
  test154880_block_22
  (interval_append test154880 368 384 400
  test154880_block_23
  test154880_block_24)))
  (interval_append test154880 400 432 480
  (interval_append test154880 400 416 432
  test154880_block_25
  test154880_block_26)
  (interval_append test154880 432 448 480
  test154880_block_27
  (interval_append test154880 448 464 480
  test154880_block_28
  test154880_block_29))))
  (interval_append test154880 480 560 640
  (interval_append test154880 480 512 560
  (interval_append test154880 480 496 512
  test154880_block_30
  test154880_block_31)
  (interval_append test154880 512 528 560
  test154880_block_32
  (interval_append test154880 528 544 560
  test154880_block_33
  test154880_block_34)))
  (interval_append test154880 560 592 640
  (interval_append test154880 560 576 592
  test154880_block_35
  test154880_block_36)
  (interval_append test154880 592 608 640
  test154880_block_37
  (interval_append test154880 608 624 640
  test154880_block_38
  test154880_block_39))))))
cert_nodeInterval_3 154880 155520
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
cert_test_11 155520
cert_test_block_3 155520 0 0 16 16
cert_test_block_3 155520 1 16 32 16
cert_test_block_3 155520 2 32 48 16
cert_test_block_3 155520 3 48 64 16
cert_test_block_3 155520 4 64 80 16
cert_test_block_3 155520 5 80 96 16
cert_test_block_3 155520 6 96 112 16
cert_test_block_3 155520 7 112 128 16
cert_test_block_3 155520 8 128 144 16
cert_test_block_3 155520 9 144 160 16
cert_test_block_3 155520 10 160 176 16
cert_test_block_3 155520 11 176 192 16
cert_test_block_3 155520 12 192 208 16
cert_test_block_3 155520 13 208 224 16
cert_test_block_3 155520 14 224 240 16
cert_test_block_3 155520 15 240 256 16
cert_test_block_3 155520 16 256 272 16
cert_test_block_3 155520 17 272 288 16
cert_test_block_3 155520 18 288 304 16
cert_test_block_3 155520 19 304 320 16
cert_test_block_3 155520 20 320 336 16
cert_test_block_3 155520 21 336 352 16
cert_test_block_3 155520 22 352 368 16
cert_test_block_3 155520 23 368 384 16
cert_test_block_3 155520 24 384 400 16
cert_test_block_3 155520 25 400 416 16
cert_test_block_3 155520 26 416 432 16
cert_test_block_3 155520 27 432 448 16
cert_test_block_3 155520 28 448 464 16
cert_test_block_3 155520 29 464 480 16
cert_test_block_3 155520 30 480 496 16
cert_test_block_3 155520 31 496 512 16
cert_test_block_3 155520 32 512 528 16
cert_test_block_3 155520 33 528 544 16
cert_test_block_3 155520 34 544 560 16
cert_test_block_3 155520 35 560 576 16
cert_test_block_3 155520 36 576 592 16
cert_test_block_3 155520 37 592 608 16
cert_test_block_3 155520 38 608 624 16
cert_test_block_3 155520 39 624 640 16
theorem test155520_complete : Interval test155520 0 640 :=
  (interval_append test155520 0 320 640
  (interval_append test155520 0 160 320
  (interval_append test155520 0 80 160
  (interval_append test155520 0 32 80
  (interval_append test155520 0 16 32
  test155520_block_0
  test155520_block_1)
  (interval_append test155520 32 48 80
  test155520_block_2
  (interval_append test155520 48 64 80
  test155520_block_3
  test155520_block_4)))
  (interval_append test155520 80 112 160
  (interval_append test155520 80 96 112
  test155520_block_5
  test155520_block_6)
  (interval_append test155520 112 128 160
  test155520_block_7
  (interval_append test155520 128 144 160
  test155520_block_8
  test155520_block_9))))
  (interval_append test155520 160 240 320
  (interval_append test155520 160 192 240
  (interval_append test155520 160 176 192
  test155520_block_10
  test155520_block_11)
  (interval_append test155520 192 208 240
  test155520_block_12
  (interval_append test155520 208 224 240
  test155520_block_13
  test155520_block_14)))
  (interval_append test155520 240 272 320
  (interval_append test155520 240 256 272
  test155520_block_15
  test155520_block_16)
  (interval_append test155520 272 288 320
  test155520_block_17
  (interval_append test155520 288 304 320
  test155520_block_18
  test155520_block_19)))))
  (interval_append test155520 320 480 640
  (interval_append test155520 320 400 480
  (interval_append test155520 320 352 400
  (interval_append test155520 320 336 352
  test155520_block_20
  test155520_block_21)
  (interval_append test155520 352 368 400
  test155520_block_22
  (interval_append test155520 368 384 400
  test155520_block_23
  test155520_block_24)))
  (interval_append test155520 400 432 480
  (interval_append test155520 400 416 432
  test155520_block_25
  test155520_block_26)
  (interval_append test155520 432 448 480
  test155520_block_27
  (interval_append test155520 448 464 480
  test155520_block_28
  test155520_block_29))))
  (interval_append test155520 480 560 640
  (interval_append test155520 480 512 560
  (interval_append test155520 480 496 512
  test155520_block_30
  test155520_block_31)
  (interval_append test155520 512 528 560
  test155520_block_32
  (interval_append test155520 528 544 560
  test155520_block_33
  test155520_block_34)))
  (interval_append test155520 560 592 640
  (interval_append test155520 560 576 592
  test155520_block_35
  test155520_block_36)
  (interval_append test155520 592 608 640
  test155520_block_37
  (interval_append test155520 608 624 640
  test155520_block_38
  test155520_block_39))))))
cert_nodeInterval_3 155520 156160
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
cert_test_11 156160
cert_test_block_3 156160 0 0 16 16
cert_test_block_3 156160 1 16 32 16
cert_test_block_3 156160 2 32 48 16
cert_test_block_3 156160 3 48 64 16
cert_test_block_3 156160 4 64 80 16
cert_test_block_3 156160 5 80 96 16
cert_test_block_3 156160 6 96 112 16
cert_test_block_3 156160 7 112 128 16
cert_test_block_3 156160 8 128 144 16
cert_test_block_3 156160 9 144 160 16
cert_test_block_3 156160 10 160 176 16
cert_test_block_3 156160 11 176 192 16
cert_test_block_3 156160 12 192 208 16
cert_test_block_3 156160 13 208 224 16
cert_test_block_3 156160 14 224 240 16
cert_test_block_3 156160 15 240 256 16
cert_test_block_3 156160 16 256 272 16
cert_test_block_3 156160 17 272 288 16
cert_test_block_3 156160 18 288 304 16
cert_test_block_3 156160 19 304 320 16
cert_test_block_3 156160 20 320 336 16
cert_test_block_3 156160 21 336 352 16
cert_test_block_3 156160 22 352 368 16
cert_test_block_3 156160 23 368 384 16
cert_test_block_3 156160 24 384 400 16
cert_test_block_3 156160 25 400 416 16
cert_test_block_3 156160 26 416 432 16
cert_test_block_3 156160 27 432 448 16
cert_test_block_3 156160 28 448 464 16
cert_test_block_3 156160 29 464 480 16
cert_test_block_3 156160 30 480 496 16
cert_test_block_3 156160 31 496 512 16
cert_test_block_3 156160 32 512 528 16
cert_test_block_3 156160 33 528 544 16
cert_test_block_3 156160 34 544 560 16
cert_test_block_3 156160 35 560 576 16
cert_test_block_3 156160 36 576 592 16
cert_test_block_3 156160 37 592 608 16
cert_test_block_3 156160 38 608 624 16
cert_test_block_3 156160 39 624 640 16
theorem test156160_complete : Interval test156160 0 640 :=
  (interval_append test156160 0 320 640
  (interval_append test156160 0 160 320
  (interval_append test156160 0 80 160
  (interval_append test156160 0 32 80
  (interval_append test156160 0 16 32
  test156160_block_0
  test156160_block_1)
  (interval_append test156160 32 48 80
  test156160_block_2
  (interval_append test156160 48 64 80
  test156160_block_3
  test156160_block_4)))
  (interval_append test156160 80 112 160
  (interval_append test156160 80 96 112
  test156160_block_5
  test156160_block_6)
  (interval_append test156160 112 128 160
  test156160_block_7
  (interval_append test156160 128 144 160
  test156160_block_8
  test156160_block_9))))
  (interval_append test156160 160 240 320
  (interval_append test156160 160 192 240
  (interval_append test156160 160 176 192
  test156160_block_10
  test156160_block_11)
  (interval_append test156160 192 208 240
  test156160_block_12
  (interval_append test156160 208 224 240
  test156160_block_13
  test156160_block_14)))
  (interval_append test156160 240 272 320
  (interval_append test156160 240 256 272
  test156160_block_15
  test156160_block_16)
  (interval_append test156160 272 288 320
  test156160_block_17
  (interval_append test156160 288 304 320
  test156160_block_18
  test156160_block_19)))))
  (interval_append test156160 320 480 640
  (interval_append test156160 320 400 480
  (interval_append test156160 320 352 400
  (interval_append test156160 320 336 352
  test156160_block_20
  test156160_block_21)
  (interval_append test156160 352 368 400
  test156160_block_22
  (interval_append test156160 368 384 400
  test156160_block_23
  test156160_block_24)))
  (interval_append test156160 400 432 480
  (interval_append test156160 400 416 432
  test156160_block_25
  test156160_block_26)
  (interval_append test156160 432 448 480
  test156160_block_27
  (interval_append test156160 448 464 480
  test156160_block_28
  test156160_block_29))))
  (interval_append test156160 480 560 640
  (interval_append test156160 480 512 560
  (interval_append test156160 480 496 512
  test156160_block_30
  test156160_block_31)
  (interval_append test156160 512 528 560
  test156160_block_32
  (interval_append test156160 528 544 560
  test156160_block_33
  test156160_block_34)))
  (interval_append test156160 560 592 640
  (interval_append test156160 560 576 592
  test156160_block_35
  test156160_block_36)
  (interval_append test156160 592 608 640
  test156160_block_37
  (interval_append test156160 608 624 640
  test156160_block_38
  test156160_block_39))))))
cert_nodeInterval_3 156160 156800
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
cert_test_11 156800
cert_test_block_3 156800 0 0 16 16
cert_test_block_3 156800 1 16 32 16
cert_test_block_3 156800 2 32 48 16
cert_test_block_3 156800 3 48 64 16
cert_test_block_3 156800 4 64 80 16
cert_test_block_3 156800 5 80 96 16
cert_test_block_3 156800 6 96 112 16
cert_test_block_3 156800 7 112 128 16
cert_test_block_3 156800 8 128 144 16
cert_test_block_3 156800 9 144 160 16
cert_test_block_3 156800 10 160 176 16
cert_test_block_3 156800 11 176 192 16
cert_test_block_3 156800 12 192 208 16
cert_test_block_3 156800 13 208 224 16
cert_test_block_3 156800 14 224 240 16
cert_test_block_3 156800 15 240 256 16
cert_test_block_3 156800 16 256 272 16
cert_test_block_3 156800 17 272 288 16
cert_test_block_3 156800 18 288 304 16
cert_test_block_3 156800 19 304 320 16
cert_test_block_3 156800 20 320 336 16
cert_test_block_3 156800 21 336 352 16
cert_test_block_3 156800 22 352 368 16
cert_test_block_3 156800 23 368 384 16
cert_test_block_3 156800 24 384 400 16
cert_test_block_3 156800 25 400 416 16
cert_test_block_3 156800 26 416 432 16
cert_test_block_3 156800 27 432 448 16
cert_test_block_3 156800 28 448 464 16
cert_test_block_3 156800 29 464 480 16
cert_test_block_3 156800 30 480 496 16
cert_test_block_3 156800 31 496 512 16
cert_test_block_3 156800 32 512 528 16
cert_test_block_3 156800 33 528 544 16
cert_test_block_3 156800 34 544 560 16
cert_test_block_3 156800 35 560 576 16
cert_test_block_3 156800 36 576 592 16
cert_test_block_3 156800 37 592 608 16
cert_test_block_3 156800 38 608 624 16
cert_test_block_3 156800 39 624 640 16
theorem test156800_complete : Interval test156800 0 640 :=
  (interval_append test156800 0 320 640
  (interval_append test156800 0 160 320
  (interval_append test156800 0 80 160
  (interval_append test156800 0 32 80
  (interval_append test156800 0 16 32
  test156800_block_0
  test156800_block_1)
  (interval_append test156800 32 48 80
  test156800_block_2
  (interval_append test156800 48 64 80
  test156800_block_3
  test156800_block_4)))
  (interval_append test156800 80 112 160
  (interval_append test156800 80 96 112
  test156800_block_5
  test156800_block_6)
  (interval_append test156800 112 128 160
  test156800_block_7
  (interval_append test156800 128 144 160
  test156800_block_8
  test156800_block_9))))
  (interval_append test156800 160 240 320
  (interval_append test156800 160 192 240
  (interval_append test156800 160 176 192
  test156800_block_10
  test156800_block_11)
  (interval_append test156800 192 208 240
  test156800_block_12
  (interval_append test156800 208 224 240
  test156800_block_13
  test156800_block_14)))
  (interval_append test156800 240 272 320
  (interval_append test156800 240 256 272
  test156800_block_15
  test156800_block_16)
  (interval_append test156800 272 288 320
  test156800_block_17
  (interval_append test156800 288 304 320
  test156800_block_18
  test156800_block_19)))))
  (interval_append test156800 320 480 640
  (interval_append test156800 320 400 480
  (interval_append test156800 320 352 400
  (interval_append test156800 320 336 352
  test156800_block_20
  test156800_block_21)
  (interval_append test156800 352 368 400
  test156800_block_22
  (interval_append test156800 368 384 400
  test156800_block_23
  test156800_block_24)))
  (interval_append test156800 400 432 480
  (interval_append test156800 400 416 432
  test156800_block_25
  test156800_block_26)
  (interval_append test156800 432 448 480
  test156800_block_27
  (interval_append test156800 448 464 480
  test156800_block_28
  test156800_block_29))))
  (interval_append test156800 480 560 640
  (interval_append test156800 480 512 560
  (interval_append test156800 480 496 512
  test156800_block_30
  test156800_block_31)
  (interval_append test156800 512 528 560
  test156800_block_32
  (interval_append test156800 528 544 560
  test156800_block_33
  test156800_block_34)))
  (interval_append test156800 560 592 640
  (interval_append test156800 560 576 592
  test156800_block_35
  test156800_block_36)
  (interval_append test156800 592 608 640
  test156800_block_37
  (interval_append test156800 608 624 640
  test156800_block_38
  test156800_block_39))))))
cert_nodeInterval_3 156800 157440
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
cert_test_11 157440
cert_test_block_3 157440 0 0 16 16
cert_test_block_3 157440 1 16 32 16
cert_test_block_3 157440 2 32 48 16
cert_test_block_3 157440 3 48 64 16
cert_test_block_3 157440 4 64 74 10
theorem test157440_complete : Interval test157440 0 74 :=
  (interval_append test157440 0 32 74
  (interval_append test157440 0 16 32
  test157440_block_0
  test157440_block_1)
  (interval_append test157440 32 48 74
  test157440_block_2
  (interval_append test157440 48 64 74
  test157440_block_3
  test157440_block_4)))
cert_nodeInterval_3 157440 157514
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
