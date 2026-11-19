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
cert_test_11 91520
cert_test_block_3 91520 0 0 16 16
cert_test_block_3 91520 1 16 32 16
cert_test_block_3 91520 2 32 48 16
cert_test_block_3 91520 3 48 64 16
cert_test_block_3 91520 4 64 80 16
cert_test_block_3 91520 5 80 96 16
cert_test_block_3 91520 6 96 112 16
cert_test_block_3 91520 7 112 128 16
cert_test_block_3 91520 8 128 144 16
cert_test_block_3 91520 9 144 160 16
cert_test_block_3 91520 10 160 176 16
cert_test_block_3 91520 11 176 192 16
cert_test_block_3 91520 12 192 208 16
cert_test_block_3 91520 13 208 224 16
cert_test_block_3 91520 14 224 240 16
cert_test_block_3 91520 15 240 256 16
cert_test_block_3 91520 16 256 272 16
cert_test_block_3 91520 17 272 288 16
cert_test_block_3 91520 18 288 304 16
cert_test_block_3 91520 19 304 320 16
cert_test_block_3 91520 20 320 336 16
cert_test_block_3 91520 21 336 352 16
cert_test_block_3 91520 22 352 368 16
cert_test_block_3 91520 23 368 384 16
cert_test_block_3 91520 24 384 400 16
cert_test_block_3 91520 25 400 416 16
cert_test_block_3 91520 26 416 432 16
cert_test_block_3 91520 27 432 448 16
cert_test_block_3 91520 28 448 464 16
cert_test_block_3 91520 29 464 480 16
cert_test_block_3 91520 30 480 496 16
cert_test_block_3 91520 31 496 512 16
cert_test_block_3 91520 32 512 528 16
cert_test_block_3 91520 33 528 544 16
cert_test_block_3 91520 34 544 560 16
cert_test_block_3 91520 35 560 576 16
cert_test_block_3 91520 36 576 592 16
cert_test_block_3 91520 37 592 608 16
cert_test_block_3 91520 38 608 624 16
cert_test_block_3 91520 39 624 640 16
theorem test91520_complete : Interval test91520 0 640 :=
  (interval_append test91520 0 320 640
  (interval_append test91520 0 160 320
  (interval_append test91520 0 80 160
  (interval_append test91520 0 32 80
  (interval_append test91520 0 16 32
  test91520_block_0
  test91520_block_1)
  (interval_append test91520 32 48 80
  test91520_block_2
  (interval_append test91520 48 64 80
  test91520_block_3
  test91520_block_4)))
  (interval_append test91520 80 112 160
  (interval_append test91520 80 96 112
  test91520_block_5
  test91520_block_6)
  (interval_append test91520 112 128 160
  test91520_block_7
  (interval_append test91520 128 144 160
  test91520_block_8
  test91520_block_9))))
  (interval_append test91520 160 240 320
  (interval_append test91520 160 192 240
  (interval_append test91520 160 176 192
  test91520_block_10
  test91520_block_11)
  (interval_append test91520 192 208 240
  test91520_block_12
  (interval_append test91520 208 224 240
  test91520_block_13
  test91520_block_14)))
  (interval_append test91520 240 272 320
  (interval_append test91520 240 256 272
  test91520_block_15
  test91520_block_16)
  (interval_append test91520 272 288 320
  test91520_block_17
  (interval_append test91520 288 304 320
  test91520_block_18
  test91520_block_19)))))
  (interval_append test91520 320 480 640
  (interval_append test91520 320 400 480
  (interval_append test91520 320 352 400
  (interval_append test91520 320 336 352
  test91520_block_20
  test91520_block_21)
  (interval_append test91520 352 368 400
  test91520_block_22
  (interval_append test91520 368 384 400
  test91520_block_23
  test91520_block_24)))
  (interval_append test91520 400 432 480
  (interval_append test91520 400 416 432
  test91520_block_25
  test91520_block_26)
  (interval_append test91520 432 448 480
  test91520_block_27
  (interval_append test91520 448 464 480
  test91520_block_28
  test91520_block_29))))
  (interval_append test91520 480 560 640
  (interval_append test91520 480 512 560
  (interval_append test91520 480 496 512
  test91520_block_30
  test91520_block_31)
  (interval_append test91520 512 528 560
  test91520_block_32
  (interval_append test91520 528 544 560
  test91520_block_33
  test91520_block_34)))
  (interval_append test91520 560 592 640
  (interval_append test91520 560 576 592
  test91520_block_35
  test91520_block_36)
  (interval_append test91520 592 608 640
  test91520_block_37
  (interval_append test91520 608 624 640
  test91520_block_38
  test91520_block_39))))))
cert_nodeInterval_3 91520 92160
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
cert_test_11 92160
cert_test_block_3 92160 0 0 16 16
cert_test_block_3 92160 1 16 32 16
cert_test_block_3 92160 2 32 48 16
cert_test_block_3 92160 3 48 64 16
cert_test_block_3 92160 4 64 80 16
cert_test_block_3 92160 5 80 96 16
cert_test_block_3 92160 6 96 112 16
cert_test_block_3 92160 7 112 128 16
cert_test_block_3 92160 8 128 144 16
cert_test_block_3 92160 9 144 160 16
cert_test_block_3 92160 10 160 176 16
cert_test_block_3 92160 11 176 192 16
cert_test_block_3 92160 12 192 208 16
cert_test_block_3 92160 13 208 224 16
cert_test_block_3 92160 14 224 240 16
cert_test_block_3 92160 15 240 256 16
cert_test_block_3 92160 16 256 272 16
cert_test_block_3 92160 17 272 288 16
cert_test_block_3 92160 18 288 304 16
cert_test_block_3 92160 19 304 320 16
cert_test_block_3 92160 20 320 336 16
cert_test_block_3 92160 21 336 352 16
cert_test_block_3 92160 22 352 368 16
cert_test_block_3 92160 23 368 384 16
cert_test_block_3 92160 24 384 400 16
cert_test_block_3 92160 25 400 416 16
cert_test_block_3 92160 26 416 432 16
cert_test_block_3 92160 27 432 448 16
cert_test_block_3 92160 28 448 464 16
cert_test_block_3 92160 29 464 480 16
cert_test_block_3 92160 30 480 496 16
cert_test_block_3 92160 31 496 512 16
cert_test_block_3 92160 32 512 528 16
cert_test_block_3 92160 33 528 544 16
cert_test_block_3 92160 34 544 560 16
cert_test_block_3 92160 35 560 576 16
cert_test_block_3 92160 36 576 592 16
cert_test_block_3 92160 37 592 608 16
cert_test_block_3 92160 38 608 624 16
cert_test_block_3 92160 39 624 640 16
theorem test92160_complete : Interval test92160 0 640 :=
  (interval_append test92160 0 320 640
  (interval_append test92160 0 160 320
  (interval_append test92160 0 80 160
  (interval_append test92160 0 32 80
  (interval_append test92160 0 16 32
  test92160_block_0
  test92160_block_1)
  (interval_append test92160 32 48 80
  test92160_block_2
  (interval_append test92160 48 64 80
  test92160_block_3
  test92160_block_4)))
  (interval_append test92160 80 112 160
  (interval_append test92160 80 96 112
  test92160_block_5
  test92160_block_6)
  (interval_append test92160 112 128 160
  test92160_block_7
  (interval_append test92160 128 144 160
  test92160_block_8
  test92160_block_9))))
  (interval_append test92160 160 240 320
  (interval_append test92160 160 192 240
  (interval_append test92160 160 176 192
  test92160_block_10
  test92160_block_11)
  (interval_append test92160 192 208 240
  test92160_block_12
  (interval_append test92160 208 224 240
  test92160_block_13
  test92160_block_14)))
  (interval_append test92160 240 272 320
  (interval_append test92160 240 256 272
  test92160_block_15
  test92160_block_16)
  (interval_append test92160 272 288 320
  test92160_block_17
  (interval_append test92160 288 304 320
  test92160_block_18
  test92160_block_19)))))
  (interval_append test92160 320 480 640
  (interval_append test92160 320 400 480
  (interval_append test92160 320 352 400
  (interval_append test92160 320 336 352
  test92160_block_20
  test92160_block_21)
  (interval_append test92160 352 368 400
  test92160_block_22
  (interval_append test92160 368 384 400
  test92160_block_23
  test92160_block_24)))
  (interval_append test92160 400 432 480
  (interval_append test92160 400 416 432
  test92160_block_25
  test92160_block_26)
  (interval_append test92160 432 448 480
  test92160_block_27
  (interval_append test92160 448 464 480
  test92160_block_28
  test92160_block_29))))
  (interval_append test92160 480 560 640
  (interval_append test92160 480 512 560
  (interval_append test92160 480 496 512
  test92160_block_30
  test92160_block_31)
  (interval_append test92160 512 528 560
  test92160_block_32
  (interval_append test92160 528 544 560
  test92160_block_33
  test92160_block_34)))
  (interval_append test92160 560 592 640
  (interval_append test92160 560 576 592
  test92160_block_35
  test92160_block_36)
  (interval_append test92160 592 608 640
  test92160_block_37
  (interval_append test92160 608 624 640
  test92160_block_38
  test92160_block_39))))))
cert_nodeInterval_3 92160 92800
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
cert_test_11 92800
cert_test_block_3 92800 0 0 16 16
cert_test_block_3 92800 1 16 32 16
cert_test_block_3 92800 2 32 48 16
cert_test_block_3 92800 3 48 64 16
cert_test_block_3 92800 4 64 80 16
cert_test_block_3 92800 5 80 96 16
cert_test_block_3 92800 6 96 112 16
cert_test_block_3 92800 7 112 128 16
cert_test_block_3 92800 8 128 144 16
cert_test_block_3 92800 9 144 160 16
cert_test_block_3 92800 10 160 176 16
cert_test_block_3 92800 11 176 192 16
cert_test_block_3 92800 12 192 208 16
cert_test_block_3 92800 13 208 224 16
cert_test_block_3 92800 14 224 240 16
cert_test_block_3 92800 15 240 256 16
cert_test_block_3 92800 16 256 272 16
cert_test_block_3 92800 17 272 288 16
cert_test_block_3 92800 18 288 304 16
cert_test_block_3 92800 19 304 320 16
cert_test_block_3 92800 20 320 336 16
cert_test_block_3 92800 21 336 352 16
cert_test_block_3 92800 22 352 368 16
cert_test_block_3 92800 23 368 384 16
cert_test_block_3 92800 24 384 400 16
cert_test_block_3 92800 25 400 416 16
cert_test_block_3 92800 26 416 432 16
cert_test_block_3 92800 27 432 448 16
cert_test_block_3 92800 28 448 464 16
cert_test_block_3 92800 29 464 480 16
cert_test_block_3 92800 30 480 496 16
cert_test_block_3 92800 31 496 512 16
cert_test_block_3 92800 32 512 528 16
cert_test_block_3 92800 33 528 544 16
cert_test_block_3 92800 34 544 560 16
cert_test_block_3 92800 35 560 576 16
cert_test_block_3 92800 36 576 592 16
cert_test_block_3 92800 37 592 608 16
cert_test_block_3 92800 38 608 624 16
cert_test_block_3 92800 39 624 640 16
theorem test92800_complete : Interval test92800 0 640 :=
  (interval_append test92800 0 320 640
  (interval_append test92800 0 160 320
  (interval_append test92800 0 80 160
  (interval_append test92800 0 32 80
  (interval_append test92800 0 16 32
  test92800_block_0
  test92800_block_1)
  (interval_append test92800 32 48 80
  test92800_block_2
  (interval_append test92800 48 64 80
  test92800_block_3
  test92800_block_4)))
  (interval_append test92800 80 112 160
  (interval_append test92800 80 96 112
  test92800_block_5
  test92800_block_6)
  (interval_append test92800 112 128 160
  test92800_block_7
  (interval_append test92800 128 144 160
  test92800_block_8
  test92800_block_9))))
  (interval_append test92800 160 240 320
  (interval_append test92800 160 192 240
  (interval_append test92800 160 176 192
  test92800_block_10
  test92800_block_11)
  (interval_append test92800 192 208 240
  test92800_block_12
  (interval_append test92800 208 224 240
  test92800_block_13
  test92800_block_14)))
  (interval_append test92800 240 272 320
  (interval_append test92800 240 256 272
  test92800_block_15
  test92800_block_16)
  (interval_append test92800 272 288 320
  test92800_block_17
  (interval_append test92800 288 304 320
  test92800_block_18
  test92800_block_19)))))
  (interval_append test92800 320 480 640
  (interval_append test92800 320 400 480
  (interval_append test92800 320 352 400
  (interval_append test92800 320 336 352
  test92800_block_20
  test92800_block_21)
  (interval_append test92800 352 368 400
  test92800_block_22
  (interval_append test92800 368 384 400
  test92800_block_23
  test92800_block_24)))
  (interval_append test92800 400 432 480
  (interval_append test92800 400 416 432
  test92800_block_25
  test92800_block_26)
  (interval_append test92800 432 448 480
  test92800_block_27
  (interval_append test92800 448 464 480
  test92800_block_28
  test92800_block_29))))
  (interval_append test92800 480 560 640
  (interval_append test92800 480 512 560
  (interval_append test92800 480 496 512
  test92800_block_30
  test92800_block_31)
  (interval_append test92800 512 528 560
  test92800_block_32
  (interval_append test92800 528 544 560
  test92800_block_33
  test92800_block_34)))
  (interval_append test92800 560 592 640
  (interval_append test92800 560 576 592
  test92800_block_35
  test92800_block_36)
  (interval_append test92800 592 608 640
  test92800_block_37
  (interval_append test92800 608 624 640
  test92800_block_38
  test92800_block_39))))))
cert_nodeInterval_3 92800 93440
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
cert_test_11 93440
cert_test_block_3 93440 0 0 16 16
cert_test_block_3 93440 1 16 32 16
cert_test_block_3 93440 2 32 48 16
cert_test_block_3 93440 3 48 64 16
cert_test_block_3 93440 4 64 80 16
cert_test_block_3 93440 5 80 96 16
cert_test_block_3 93440 6 96 112 16
cert_test_block_3 93440 7 112 128 16
cert_test_block_3 93440 8 128 144 16
cert_test_block_3 93440 9 144 160 16
cert_test_block_3 93440 10 160 176 16
cert_test_block_3 93440 11 176 192 16
cert_test_block_3 93440 12 192 208 16
cert_test_block_3 93440 13 208 224 16
cert_test_block_3 93440 14 224 240 16
cert_test_block_3 93440 15 240 256 16
cert_test_block_3 93440 16 256 272 16
cert_test_block_3 93440 17 272 288 16
cert_test_block_3 93440 18 288 304 16
cert_test_block_3 93440 19 304 320 16
cert_test_block_3 93440 20 320 336 16
cert_test_block_3 93440 21 336 352 16
cert_test_block_3 93440 22 352 368 16
cert_test_block_3 93440 23 368 384 16
cert_test_block_3 93440 24 384 400 16
cert_test_block_3 93440 25 400 416 16
cert_test_block_3 93440 26 416 432 16
cert_test_block_3 93440 27 432 448 16
cert_test_block_3 93440 28 448 464 16
cert_test_block_3 93440 29 464 480 16
cert_test_block_3 93440 30 480 496 16
cert_test_block_3 93440 31 496 512 16
cert_test_block_3 93440 32 512 528 16
cert_test_block_3 93440 33 528 544 16
cert_test_block_3 93440 34 544 560 16
cert_test_block_3 93440 35 560 576 16
cert_test_block_3 93440 36 576 592 16
cert_test_block_3 93440 37 592 608 16
cert_test_block_3 93440 38 608 624 16
cert_test_block_3 93440 39 624 640 16
theorem test93440_complete : Interval test93440 0 640 :=
  (interval_append test93440 0 320 640
  (interval_append test93440 0 160 320
  (interval_append test93440 0 80 160
  (interval_append test93440 0 32 80
  (interval_append test93440 0 16 32
  test93440_block_0
  test93440_block_1)
  (interval_append test93440 32 48 80
  test93440_block_2
  (interval_append test93440 48 64 80
  test93440_block_3
  test93440_block_4)))
  (interval_append test93440 80 112 160
  (interval_append test93440 80 96 112
  test93440_block_5
  test93440_block_6)
  (interval_append test93440 112 128 160
  test93440_block_7
  (interval_append test93440 128 144 160
  test93440_block_8
  test93440_block_9))))
  (interval_append test93440 160 240 320
  (interval_append test93440 160 192 240
  (interval_append test93440 160 176 192
  test93440_block_10
  test93440_block_11)
  (interval_append test93440 192 208 240
  test93440_block_12
  (interval_append test93440 208 224 240
  test93440_block_13
  test93440_block_14)))
  (interval_append test93440 240 272 320
  (interval_append test93440 240 256 272
  test93440_block_15
  test93440_block_16)
  (interval_append test93440 272 288 320
  test93440_block_17
  (interval_append test93440 288 304 320
  test93440_block_18
  test93440_block_19)))))
  (interval_append test93440 320 480 640
  (interval_append test93440 320 400 480
  (interval_append test93440 320 352 400
  (interval_append test93440 320 336 352
  test93440_block_20
  test93440_block_21)
  (interval_append test93440 352 368 400
  test93440_block_22
  (interval_append test93440 368 384 400
  test93440_block_23
  test93440_block_24)))
  (interval_append test93440 400 432 480
  (interval_append test93440 400 416 432
  test93440_block_25
  test93440_block_26)
  (interval_append test93440 432 448 480
  test93440_block_27
  (interval_append test93440 448 464 480
  test93440_block_28
  test93440_block_29))))
  (interval_append test93440 480 560 640
  (interval_append test93440 480 512 560
  (interval_append test93440 480 496 512
  test93440_block_30
  test93440_block_31)
  (interval_append test93440 512 528 560
  test93440_block_32
  (interval_append test93440 528 544 560
  test93440_block_33
  test93440_block_34)))
  (interval_append test93440 560 592 640
  (interval_append test93440 560 576 592
  test93440_block_35
  test93440_block_36)
  (interval_append test93440 592 608 640
  test93440_block_37
  (interval_append test93440 608 624 640
  test93440_block_38
  test93440_block_39))))))
cert_nodeInterval_3 93440 94080
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
cert_test_11 94080
cert_test_block_3 94080 0 0 16 16
cert_test_block_3 94080 1 16 32 16
cert_test_block_3 94080 2 32 48 16
cert_test_block_3 94080 3 48 64 16
cert_test_block_3 94080 4 64 80 16
cert_test_block_3 94080 5 80 96 16
cert_test_block_3 94080 6 96 112 16
cert_test_block_3 94080 7 112 128 16
cert_test_block_3 94080 8 128 144 16
cert_test_block_3 94080 9 144 160 16
cert_test_block_3 94080 10 160 176 16
cert_test_block_3 94080 11 176 192 16
cert_test_block_3 94080 12 192 208 16
cert_test_block_3 94080 13 208 224 16
cert_test_block_3 94080 14 224 240 16
cert_test_block_3 94080 15 240 256 16
cert_test_block_3 94080 16 256 272 16
cert_test_block_3 94080 17 272 288 16
cert_test_block_3 94080 18 288 304 16
cert_test_block_3 94080 19 304 320 16
cert_test_block_3 94080 20 320 336 16
cert_test_block_3 94080 21 336 352 16
cert_test_block_3 94080 22 352 368 16
cert_test_block_3 94080 23 368 384 16
cert_test_block_3 94080 24 384 400 16
cert_test_block_3 94080 25 400 416 16
cert_test_block_3 94080 26 416 432 16
cert_test_block_3 94080 27 432 448 16
cert_test_block_3 94080 28 448 464 16
cert_test_block_3 94080 29 464 480 16
cert_test_block_3 94080 30 480 496 16
cert_test_block_3 94080 31 496 512 16
cert_test_block_3 94080 32 512 528 16
cert_test_block_3 94080 33 528 544 16
cert_test_block_3 94080 34 544 560 16
cert_test_block_3 94080 35 560 576 16
cert_test_block_3 94080 36 576 592 16
cert_test_block_3 94080 37 592 608 16
cert_test_block_3 94080 38 608 624 16
cert_test_block_3 94080 39 624 640 16
theorem test94080_complete : Interval test94080 0 640 :=
  (interval_append test94080 0 320 640
  (interval_append test94080 0 160 320
  (interval_append test94080 0 80 160
  (interval_append test94080 0 32 80
  (interval_append test94080 0 16 32
  test94080_block_0
  test94080_block_1)
  (interval_append test94080 32 48 80
  test94080_block_2
  (interval_append test94080 48 64 80
  test94080_block_3
  test94080_block_4)))
  (interval_append test94080 80 112 160
  (interval_append test94080 80 96 112
  test94080_block_5
  test94080_block_6)
  (interval_append test94080 112 128 160
  test94080_block_7
  (interval_append test94080 128 144 160
  test94080_block_8
  test94080_block_9))))
  (interval_append test94080 160 240 320
  (interval_append test94080 160 192 240
  (interval_append test94080 160 176 192
  test94080_block_10
  test94080_block_11)
  (interval_append test94080 192 208 240
  test94080_block_12
  (interval_append test94080 208 224 240
  test94080_block_13
  test94080_block_14)))
  (interval_append test94080 240 272 320
  (interval_append test94080 240 256 272
  test94080_block_15
  test94080_block_16)
  (interval_append test94080 272 288 320
  test94080_block_17
  (interval_append test94080 288 304 320
  test94080_block_18
  test94080_block_19)))))
  (interval_append test94080 320 480 640
  (interval_append test94080 320 400 480
  (interval_append test94080 320 352 400
  (interval_append test94080 320 336 352
  test94080_block_20
  test94080_block_21)
  (interval_append test94080 352 368 400
  test94080_block_22
  (interval_append test94080 368 384 400
  test94080_block_23
  test94080_block_24)))
  (interval_append test94080 400 432 480
  (interval_append test94080 400 416 432
  test94080_block_25
  test94080_block_26)
  (interval_append test94080 432 448 480
  test94080_block_27
  (interval_append test94080 448 464 480
  test94080_block_28
  test94080_block_29))))
  (interval_append test94080 480 560 640
  (interval_append test94080 480 512 560
  (interval_append test94080 480 496 512
  test94080_block_30
  test94080_block_31)
  (interval_append test94080 512 528 560
  test94080_block_32
  (interval_append test94080 528 544 560
  test94080_block_33
  test94080_block_34)))
  (interval_append test94080 560 592 640
  (interval_append test94080 560 576 592
  test94080_block_35
  test94080_block_36)
  (interval_append test94080 592 608 640
  test94080_block_37
  (interval_append test94080 608 624 640
  test94080_block_38
  test94080_block_39))))))
cert_nodeInterval_3 94080 94720
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
cert_test_11 94720
cert_test_block_3 94720 0 0 16 16
cert_test_block_3 94720 1 16 32 16
cert_test_block_3 94720 2 32 48 16
cert_test_block_3 94720 3 48 64 16
cert_test_block_3 94720 4 64 80 16
cert_test_block_3 94720 5 80 96 16
cert_test_block_3 94720 6 96 112 16
cert_test_block_3 94720 7 112 128 16
cert_test_block_3 94720 8 128 144 16
cert_test_block_3 94720 9 144 160 16
cert_test_block_3 94720 10 160 176 16
cert_test_block_3 94720 11 176 192 16
cert_test_block_3 94720 12 192 208 16
cert_test_block_3 94720 13 208 224 16
cert_test_block_3 94720 14 224 240 16
cert_test_block_3 94720 15 240 256 16
cert_test_block_3 94720 16 256 272 16
cert_test_block_3 94720 17 272 288 16
cert_test_block_3 94720 18 288 304 16
cert_test_block_3 94720 19 304 320 16
cert_test_block_3 94720 20 320 336 16
cert_test_block_3 94720 21 336 352 16
cert_test_block_3 94720 22 352 368 16
cert_test_block_3 94720 23 368 384 16
cert_test_block_3 94720 24 384 400 16
cert_test_block_3 94720 25 400 416 16
cert_test_block_3 94720 26 416 432 16
cert_test_block_3 94720 27 432 448 16
cert_test_block_3 94720 28 448 464 16
cert_test_block_3 94720 29 464 480 16
cert_test_block_3 94720 30 480 496 16
cert_test_block_3 94720 31 496 512 16
cert_test_block_3 94720 32 512 528 16
cert_test_block_3 94720 33 528 544 16
cert_test_block_3 94720 34 544 560 16
cert_test_block_3 94720 35 560 576 16
cert_test_block_3 94720 36 576 592 16
cert_test_block_3 94720 37 592 608 16
cert_test_block_3 94720 38 608 624 16
cert_test_block_3 94720 39 624 640 16
theorem test94720_complete : Interval test94720 0 640 :=
  (interval_append test94720 0 320 640
  (interval_append test94720 0 160 320
  (interval_append test94720 0 80 160
  (interval_append test94720 0 32 80
  (interval_append test94720 0 16 32
  test94720_block_0
  test94720_block_1)
  (interval_append test94720 32 48 80
  test94720_block_2
  (interval_append test94720 48 64 80
  test94720_block_3
  test94720_block_4)))
  (interval_append test94720 80 112 160
  (interval_append test94720 80 96 112
  test94720_block_5
  test94720_block_6)
  (interval_append test94720 112 128 160
  test94720_block_7
  (interval_append test94720 128 144 160
  test94720_block_8
  test94720_block_9))))
  (interval_append test94720 160 240 320
  (interval_append test94720 160 192 240
  (interval_append test94720 160 176 192
  test94720_block_10
  test94720_block_11)
  (interval_append test94720 192 208 240
  test94720_block_12
  (interval_append test94720 208 224 240
  test94720_block_13
  test94720_block_14)))
  (interval_append test94720 240 272 320
  (interval_append test94720 240 256 272
  test94720_block_15
  test94720_block_16)
  (interval_append test94720 272 288 320
  test94720_block_17
  (interval_append test94720 288 304 320
  test94720_block_18
  test94720_block_19)))))
  (interval_append test94720 320 480 640
  (interval_append test94720 320 400 480
  (interval_append test94720 320 352 400
  (interval_append test94720 320 336 352
  test94720_block_20
  test94720_block_21)
  (interval_append test94720 352 368 400
  test94720_block_22
  (interval_append test94720 368 384 400
  test94720_block_23
  test94720_block_24)))
  (interval_append test94720 400 432 480
  (interval_append test94720 400 416 432
  test94720_block_25
  test94720_block_26)
  (interval_append test94720 432 448 480
  test94720_block_27
  (interval_append test94720 448 464 480
  test94720_block_28
  test94720_block_29))))
  (interval_append test94720 480 560 640
  (interval_append test94720 480 512 560
  (interval_append test94720 480 496 512
  test94720_block_30
  test94720_block_31)
  (interval_append test94720 512 528 560
  test94720_block_32
  (interval_append test94720 528 544 560
  test94720_block_33
  test94720_block_34)))
  (interval_append test94720 560 592 640
  (interval_append test94720 560 576 592
  test94720_block_35
  test94720_block_36)
  (interval_append test94720 592 608 640
  test94720_block_37
  (interval_append test94720 608 624 640
  test94720_block_38
  test94720_block_39))))))
cert_nodeInterval_3 94720 95360
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
cert_test_11 95360
cert_test_block_3 95360 0 0 16 16
cert_test_block_3 95360 1 16 32 16
cert_test_block_3 95360 2 32 48 16
cert_test_block_3 95360 3 48 64 16
cert_test_block_3 95360 4 64 80 16
cert_test_block_3 95360 5 80 96 16
cert_test_block_3 95360 6 96 112 16
cert_test_block_3 95360 7 112 128 16
cert_test_block_3 95360 8 128 144 16
cert_test_block_3 95360 9 144 160 16
cert_test_block_3 95360 10 160 176 16
cert_test_block_3 95360 11 176 192 16
cert_test_block_3 95360 12 192 208 16
cert_test_block_3 95360 13 208 224 16
cert_test_block_3 95360 14 224 240 16
cert_test_block_3 95360 15 240 256 16
cert_test_block_3 95360 16 256 272 16
cert_test_block_3 95360 17 272 288 16
cert_test_block_3 95360 18 288 304 16
cert_test_block_3 95360 19 304 320 16
cert_test_block_3 95360 20 320 336 16
cert_test_block_3 95360 21 336 352 16
cert_test_block_3 95360 22 352 368 16
cert_test_block_3 95360 23 368 384 16
cert_test_block_3 95360 24 384 400 16
cert_test_block_3 95360 25 400 416 16
cert_test_block_3 95360 26 416 432 16
cert_test_block_3 95360 27 432 448 16
cert_test_block_3 95360 28 448 464 16
cert_test_block_3 95360 29 464 480 16
cert_test_block_3 95360 30 480 496 16
cert_test_block_3 95360 31 496 512 16
cert_test_block_3 95360 32 512 528 16
cert_test_block_3 95360 33 528 544 16
cert_test_block_3 95360 34 544 560 16
cert_test_block_3 95360 35 560 576 16
cert_test_block_3 95360 36 576 592 16
cert_test_block_3 95360 37 592 608 16
cert_test_block_3 95360 38 608 624 16
cert_test_block_3 95360 39 624 640 16
theorem test95360_complete : Interval test95360 0 640 :=
  (interval_append test95360 0 320 640
  (interval_append test95360 0 160 320
  (interval_append test95360 0 80 160
  (interval_append test95360 0 32 80
  (interval_append test95360 0 16 32
  test95360_block_0
  test95360_block_1)
  (interval_append test95360 32 48 80
  test95360_block_2
  (interval_append test95360 48 64 80
  test95360_block_3
  test95360_block_4)))
  (interval_append test95360 80 112 160
  (interval_append test95360 80 96 112
  test95360_block_5
  test95360_block_6)
  (interval_append test95360 112 128 160
  test95360_block_7
  (interval_append test95360 128 144 160
  test95360_block_8
  test95360_block_9))))
  (interval_append test95360 160 240 320
  (interval_append test95360 160 192 240
  (interval_append test95360 160 176 192
  test95360_block_10
  test95360_block_11)
  (interval_append test95360 192 208 240
  test95360_block_12
  (interval_append test95360 208 224 240
  test95360_block_13
  test95360_block_14)))
  (interval_append test95360 240 272 320
  (interval_append test95360 240 256 272
  test95360_block_15
  test95360_block_16)
  (interval_append test95360 272 288 320
  test95360_block_17
  (interval_append test95360 288 304 320
  test95360_block_18
  test95360_block_19)))))
  (interval_append test95360 320 480 640
  (interval_append test95360 320 400 480
  (interval_append test95360 320 352 400
  (interval_append test95360 320 336 352
  test95360_block_20
  test95360_block_21)
  (interval_append test95360 352 368 400
  test95360_block_22
  (interval_append test95360 368 384 400
  test95360_block_23
  test95360_block_24)))
  (interval_append test95360 400 432 480
  (interval_append test95360 400 416 432
  test95360_block_25
  test95360_block_26)
  (interval_append test95360 432 448 480
  test95360_block_27
  (interval_append test95360 448 464 480
  test95360_block_28
  test95360_block_29))))
  (interval_append test95360 480 560 640
  (interval_append test95360 480 512 560
  (interval_append test95360 480 496 512
  test95360_block_30
  test95360_block_31)
  (interval_append test95360 512 528 560
  test95360_block_32
  (interval_append test95360 528 544 560
  test95360_block_33
  test95360_block_34)))
  (interval_append test95360 560 592 640
  (interval_append test95360 560 576 592
  test95360_block_35
  test95360_block_36)
  (interval_append test95360 592 608 640
  test95360_block_37
  (interval_append test95360 608 624 640
  test95360_block_38
  test95360_block_39))))))
cert_nodeInterval_3 95360 96000
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
cert_test_11 96000
cert_test_block_3 96000 0 0 16 16
cert_test_block_3 96000 1 16 32 16
cert_test_block_3 96000 2 32 48 16
cert_test_block_3 96000 3 48 64 16
cert_test_block_3 96000 4 64 80 16
cert_test_block_3 96000 5 80 96 16
cert_test_block_3 96000 6 96 112 16
cert_test_block_3 96000 7 112 128 16
cert_test_block_3 96000 8 128 144 16
cert_test_block_3 96000 9 144 160 16
cert_test_block_3 96000 10 160 176 16
cert_test_block_3 96000 11 176 192 16
cert_test_block_3 96000 12 192 208 16
cert_test_block_3 96000 13 208 224 16
cert_test_block_3 96000 14 224 240 16
cert_test_block_3 96000 15 240 256 16
cert_test_block_3 96000 16 256 272 16
cert_test_block_3 96000 17 272 288 16
cert_test_block_3 96000 18 288 304 16
cert_test_block_3 96000 19 304 320 16
cert_test_block_3 96000 20 320 336 16
cert_test_block_3 96000 21 336 352 16
cert_test_block_3 96000 22 352 368 16
cert_test_block_3 96000 23 368 384 16
cert_test_block_3 96000 24 384 400 16
cert_test_block_3 96000 25 400 416 16
cert_test_block_3 96000 26 416 432 16
cert_test_block_3 96000 27 432 448 16
cert_test_block_3 96000 28 448 464 16
cert_test_block_3 96000 29 464 480 16
cert_test_block_3 96000 30 480 496 16
cert_test_block_3 96000 31 496 512 16
cert_test_block_3 96000 32 512 528 16
cert_test_block_3 96000 33 528 544 16
cert_test_block_3 96000 34 544 560 16
cert_test_block_3 96000 35 560 576 16
cert_test_block_3 96000 36 576 592 16
cert_test_block_3 96000 37 592 608 16
cert_test_block_3 96000 38 608 624 16
cert_test_block_3 96000 39 624 640 16
theorem test96000_complete : Interval test96000 0 640 :=
  (interval_append test96000 0 320 640
  (interval_append test96000 0 160 320
  (interval_append test96000 0 80 160
  (interval_append test96000 0 32 80
  (interval_append test96000 0 16 32
  test96000_block_0
  test96000_block_1)
  (interval_append test96000 32 48 80
  test96000_block_2
  (interval_append test96000 48 64 80
  test96000_block_3
  test96000_block_4)))
  (interval_append test96000 80 112 160
  (interval_append test96000 80 96 112
  test96000_block_5
  test96000_block_6)
  (interval_append test96000 112 128 160
  test96000_block_7
  (interval_append test96000 128 144 160
  test96000_block_8
  test96000_block_9))))
  (interval_append test96000 160 240 320
  (interval_append test96000 160 192 240
  (interval_append test96000 160 176 192
  test96000_block_10
  test96000_block_11)
  (interval_append test96000 192 208 240
  test96000_block_12
  (interval_append test96000 208 224 240
  test96000_block_13
  test96000_block_14)))
  (interval_append test96000 240 272 320
  (interval_append test96000 240 256 272
  test96000_block_15
  test96000_block_16)
  (interval_append test96000 272 288 320
  test96000_block_17
  (interval_append test96000 288 304 320
  test96000_block_18
  test96000_block_19)))))
  (interval_append test96000 320 480 640
  (interval_append test96000 320 400 480
  (interval_append test96000 320 352 400
  (interval_append test96000 320 336 352
  test96000_block_20
  test96000_block_21)
  (interval_append test96000 352 368 400
  test96000_block_22
  (interval_append test96000 368 384 400
  test96000_block_23
  test96000_block_24)))
  (interval_append test96000 400 432 480
  (interval_append test96000 400 416 432
  test96000_block_25
  test96000_block_26)
  (interval_append test96000 432 448 480
  test96000_block_27
  (interval_append test96000 448 464 480
  test96000_block_28
  test96000_block_29))))
  (interval_append test96000 480 560 640
  (interval_append test96000 480 512 560
  (interval_append test96000 480 496 512
  test96000_block_30
  test96000_block_31)
  (interval_append test96000 512 528 560
  test96000_block_32
  (interval_append test96000 528 544 560
  test96000_block_33
  test96000_block_34)))
  (interval_append test96000 560 592 640
  (interval_append test96000 560 576 592
  test96000_block_35
  test96000_block_36)
  (interval_append test96000 592 608 640
  test96000_block_37
  (interval_append test96000 608 624 640
  test96000_block_38
  test96000_block_39))))))
cert_nodeInterval_3 96000 96640
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
cert_test_11 96640
cert_test_block_3 96640 0 0 16 16
cert_test_block_3 96640 1 16 32 16
cert_test_block_3 96640 2 32 48 16
cert_test_block_3 96640 3 48 64 16
cert_test_block_3 96640 4 64 80 16
cert_test_block_3 96640 5 80 96 16
cert_test_block_3 96640 6 96 112 16
cert_test_block_3 96640 7 112 128 16
cert_test_block_3 96640 8 128 144 16
cert_test_block_3 96640 9 144 160 16
cert_test_block_3 96640 10 160 176 16
cert_test_block_3 96640 11 176 192 16
cert_test_block_3 96640 12 192 208 16
cert_test_block_3 96640 13 208 224 16
cert_test_block_3 96640 14 224 240 16
cert_test_block_3 96640 15 240 256 16
cert_test_block_3 96640 16 256 272 16
cert_test_block_3 96640 17 272 288 16
cert_test_block_3 96640 18 288 304 16
cert_test_block_3 96640 19 304 320 16
cert_test_block_3 96640 20 320 336 16
cert_test_block_3 96640 21 336 352 16
cert_test_block_3 96640 22 352 368 16
cert_test_block_3 96640 23 368 384 16
cert_test_block_3 96640 24 384 400 16
cert_test_block_3 96640 25 400 416 16
cert_test_block_3 96640 26 416 432 16
cert_test_block_3 96640 27 432 448 16
cert_test_block_3 96640 28 448 464 16
cert_test_block_3 96640 29 464 480 16
cert_test_block_3 96640 30 480 496 16
cert_test_block_3 96640 31 496 512 16
cert_test_block_3 96640 32 512 528 16
cert_test_block_3 96640 33 528 544 16
cert_test_block_3 96640 34 544 560 16
cert_test_block_3 96640 35 560 576 16
cert_test_block_3 96640 36 576 592 16
cert_test_block_3 96640 37 592 608 16
cert_test_block_3 96640 38 608 624 16
cert_test_block_3 96640 39 624 640 16
theorem test96640_complete : Interval test96640 0 640 :=
  (interval_append test96640 0 320 640
  (interval_append test96640 0 160 320
  (interval_append test96640 0 80 160
  (interval_append test96640 0 32 80
  (interval_append test96640 0 16 32
  test96640_block_0
  test96640_block_1)
  (interval_append test96640 32 48 80
  test96640_block_2
  (interval_append test96640 48 64 80
  test96640_block_3
  test96640_block_4)))
  (interval_append test96640 80 112 160
  (interval_append test96640 80 96 112
  test96640_block_5
  test96640_block_6)
  (interval_append test96640 112 128 160
  test96640_block_7
  (interval_append test96640 128 144 160
  test96640_block_8
  test96640_block_9))))
  (interval_append test96640 160 240 320
  (interval_append test96640 160 192 240
  (interval_append test96640 160 176 192
  test96640_block_10
  test96640_block_11)
  (interval_append test96640 192 208 240
  test96640_block_12
  (interval_append test96640 208 224 240
  test96640_block_13
  test96640_block_14)))
  (interval_append test96640 240 272 320
  (interval_append test96640 240 256 272
  test96640_block_15
  test96640_block_16)
  (interval_append test96640 272 288 320
  test96640_block_17
  (interval_append test96640 288 304 320
  test96640_block_18
  test96640_block_19)))))
  (interval_append test96640 320 480 640
  (interval_append test96640 320 400 480
  (interval_append test96640 320 352 400
  (interval_append test96640 320 336 352
  test96640_block_20
  test96640_block_21)
  (interval_append test96640 352 368 400
  test96640_block_22
  (interval_append test96640 368 384 400
  test96640_block_23
  test96640_block_24)))
  (interval_append test96640 400 432 480
  (interval_append test96640 400 416 432
  test96640_block_25
  test96640_block_26)
  (interval_append test96640 432 448 480
  test96640_block_27
  (interval_append test96640 448 464 480
  test96640_block_28
  test96640_block_29))))
  (interval_append test96640 480 560 640
  (interval_append test96640 480 512 560
  (interval_append test96640 480 496 512
  test96640_block_30
  test96640_block_31)
  (interval_append test96640 512 528 560
  test96640_block_32
  (interval_append test96640 528 544 560
  test96640_block_33
  test96640_block_34)))
  (interval_append test96640 560 592 640
  (interval_append test96640 560 576 592
  test96640_block_35
  test96640_block_36)
  (interval_append test96640 592 608 640
  test96640_block_37
  (interval_append test96640 608 624 640
  test96640_block_38
  test96640_block_39))))))
cert_nodeInterval_3 96640 97280
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
cert_test_11 97280
cert_test_block_3 97280 0 0 16 16
cert_test_block_3 97280 1 16 32 16
cert_test_block_3 97280 2 32 48 16
cert_test_block_3 97280 3 48 64 16
cert_test_block_3 97280 4 64 80 16
cert_test_block_3 97280 5 80 96 16
cert_test_block_3 97280 6 96 112 16
cert_test_block_3 97280 7 112 128 16
cert_test_block_3 97280 8 128 144 16
cert_test_block_3 97280 9 144 160 16
cert_test_block_3 97280 10 160 176 16
cert_test_block_3 97280 11 176 192 16
cert_test_block_3 97280 12 192 208 16
cert_test_block_3 97280 13 208 224 16
cert_test_block_3 97280 14 224 240 16
cert_test_block_3 97280 15 240 256 16
cert_test_block_3 97280 16 256 272 16
cert_test_block_3 97280 17 272 288 16
cert_test_block_3 97280 18 288 304 16
cert_test_block_3 97280 19 304 320 16
cert_test_block_3 97280 20 320 336 16
cert_test_block_3 97280 21 336 352 16
cert_test_block_3 97280 22 352 368 16
cert_test_block_3 97280 23 368 384 16
cert_test_block_3 97280 24 384 400 16
cert_test_block_3 97280 25 400 416 16
cert_test_block_3 97280 26 416 432 16
cert_test_block_3 97280 27 432 448 16
cert_test_block_3 97280 28 448 464 16
cert_test_block_3 97280 29 464 480 16
cert_test_block_3 97280 30 480 496 16
cert_test_block_3 97280 31 496 512 16
cert_test_block_3 97280 32 512 528 16
cert_test_block_3 97280 33 528 544 16
cert_test_block_3 97280 34 544 560 16
cert_test_block_3 97280 35 560 576 16
cert_test_block_3 97280 36 576 592 16
cert_test_block_3 97280 37 592 608 16
cert_test_block_3 97280 38 608 624 16
cert_test_block_3 97280 39 624 640 16
theorem test97280_complete : Interval test97280 0 640 :=
  (interval_append test97280 0 320 640
  (interval_append test97280 0 160 320
  (interval_append test97280 0 80 160
  (interval_append test97280 0 32 80
  (interval_append test97280 0 16 32
  test97280_block_0
  test97280_block_1)
  (interval_append test97280 32 48 80
  test97280_block_2
  (interval_append test97280 48 64 80
  test97280_block_3
  test97280_block_4)))
  (interval_append test97280 80 112 160
  (interval_append test97280 80 96 112
  test97280_block_5
  test97280_block_6)
  (interval_append test97280 112 128 160
  test97280_block_7
  (interval_append test97280 128 144 160
  test97280_block_8
  test97280_block_9))))
  (interval_append test97280 160 240 320
  (interval_append test97280 160 192 240
  (interval_append test97280 160 176 192
  test97280_block_10
  test97280_block_11)
  (interval_append test97280 192 208 240
  test97280_block_12
  (interval_append test97280 208 224 240
  test97280_block_13
  test97280_block_14)))
  (interval_append test97280 240 272 320
  (interval_append test97280 240 256 272
  test97280_block_15
  test97280_block_16)
  (interval_append test97280 272 288 320
  test97280_block_17
  (interval_append test97280 288 304 320
  test97280_block_18
  test97280_block_19)))))
  (interval_append test97280 320 480 640
  (interval_append test97280 320 400 480
  (interval_append test97280 320 352 400
  (interval_append test97280 320 336 352
  test97280_block_20
  test97280_block_21)
  (interval_append test97280 352 368 400
  test97280_block_22
  (interval_append test97280 368 384 400
  test97280_block_23
  test97280_block_24)))
  (interval_append test97280 400 432 480
  (interval_append test97280 400 416 432
  test97280_block_25
  test97280_block_26)
  (interval_append test97280 432 448 480
  test97280_block_27
  (interval_append test97280 448 464 480
  test97280_block_28
  test97280_block_29))))
  (interval_append test97280 480 560 640
  (interval_append test97280 480 512 560
  (interval_append test97280 480 496 512
  test97280_block_30
  test97280_block_31)
  (interval_append test97280 512 528 560
  test97280_block_32
  (interval_append test97280 528 544 560
  test97280_block_33
  test97280_block_34)))
  (interval_append test97280 560 592 640
  (interval_append test97280 560 576 592
  test97280_block_35
  test97280_block_36)
  (interval_append test97280 592 608 640
  test97280_block_37
  (interval_append test97280 608 624 640
  test97280_block_38
  test97280_block_39))))))
cert_nodeInterval_3 97280 97920
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
cert_test_11 97920
cert_test_block_3 97920 0 0 16 16
cert_test_block_3 97920 1 16 32 16
cert_test_block_3 97920 2 32 48 16
cert_test_block_3 97920 3 48 64 16
cert_test_block_3 97920 4 64 80 16
cert_test_block_3 97920 5 80 96 16
cert_test_block_3 97920 6 96 112 16
cert_test_block_3 97920 7 112 128 16
cert_test_block_3 97920 8 128 144 16
cert_test_block_3 97920 9 144 160 16
cert_test_block_3 97920 10 160 176 16
cert_test_block_3 97920 11 176 192 16
cert_test_block_3 97920 12 192 208 16
cert_test_block_3 97920 13 208 224 16
cert_test_block_3 97920 14 224 240 16
cert_test_block_3 97920 15 240 256 16
cert_test_block_3 97920 16 256 272 16
cert_test_block_3 97920 17 272 288 16
cert_test_block_3 97920 18 288 304 16
cert_test_block_3 97920 19 304 320 16
cert_test_block_3 97920 20 320 336 16
cert_test_block_3 97920 21 336 352 16
cert_test_block_3 97920 22 352 368 16
cert_test_block_3 97920 23 368 384 16
cert_test_block_3 97920 24 384 400 16
cert_test_block_3 97920 25 400 416 16
cert_test_block_3 97920 26 416 432 16
cert_test_block_3 97920 27 432 448 16
cert_test_block_3 97920 28 448 464 16
cert_test_block_3 97920 29 464 480 16
cert_test_block_3 97920 30 480 496 16
cert_test_block_3 97920 31 496 512 16
cert_test_block_3 97920 32 512 528 16
cert_test_block_3 97920 33 528 544 16
cert_test_block_3 97920 34 544 560 16
cert_test_block_3 97920 35 560 576 16
cert_test_block_3 97920 36 576 592 16
cert_test_block_3 97920 37 592 608 16
cert_test_block_3 97920 38 608 624 16
cert_test_block_3 97920 39 624 640 16
theorem test97920_complete : Interval test97920 0 640 :=
  (interval_append test97920 0 320 640
  (interval_append test97920 0 160 320
  (interval_append test97920 0 80 160
  (interval_append test97920 0 32 80
  (interval_append test97920 0 16 32
  test97920_block_0
  test97920_block_1)
  (interval_append test97920 32 48 80
  test97920_block_2
  (interval_append test97920 48 64 80
  test97920_block_3
  test97920_block_4)))
  (interval_append test97920 80 112 160
  (interval_append test97920 80 96 112
  test97920_block_5
  test97920_block_6)
  (interval_append test97920 112 128 160
  test97920_block_7
  (interval_append test97920 128 144 160
  test97920_block_8
  test97920_block_9))))
  (interval_append test97920 160 240 320
  (interval_append test97920 160 192 240
  (interval_append test97920 160 176 192
  test97920_block_10
  test97920_block_11)
  (interval_append test97920 192 208 240
  test97920_block_12
  (interval_append test97920 208 224 240
  test97920_block_13
  test97920_block_14)))
  (interval_append test97920 240 272 320
  (interval_append test97920 240 256 272
  test97920_block_15
  test97920_block_16)
  (interval_append test97920 272 288 320
  test97920_block_17
  (interval_append test97920 288 304 320
  test97920_block_18
  test97920_block_19)))))
  (interval_append test97920 320 480 640
  (interval_append test97920 320 400 480
  (interval_append test97920 320 352 400
  (interval_append test97920 320 336 352
  test97920_block_20
  test97920_block_21)
  (interval_append test97920 352 368 400
  test97920_block_22
  (interval_append test97920 368 384 400
  test97920_block_23
  test97920_block_24)))
  (interval_append test97920 400 432 480
  (interval_append test97920 400 416 432
  test97920_block_25
  test97920_block_26)
  (interval_append test97920 432 448 480
  test97920_block_27
  (interval_append test97920 448 464 480
  test97920_block_28
  test97920_block_29))))
  (interval_append test97920 480 560 640
  (interval_append test97920 480 512 560
  (interval_append test97920 480 496 512
  test97920_block_30
  test97920_block_31)
  (interval_append test97920 512 528 560
  test97920_block_32
  (interval_append test97920 528 544 560
  test97920_block_33
  test97920_block_34)))
  (interval_append test97920 560 592 640
  (interval_append test97920 560 576 592
  test97920_block_35
  test97920_block_36)
  (interval_append test97920 592 608 640
  test97920_block_37
  (interval_append test97920 608 624 640
  test97920_block_38
  test97920_block_39))))))
cert_nodeInterval_3 97920 98560
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
cert_test_11 98560
cert_test_block_3 98560 0 0 16 16
cert_test_block_3 98560 1 16 32 16
cert_test_block_3 98560 2 32 48 16
cert_test_block_3 98560 3 48 64 16
cert_test_block_3 98560 4 64 80 16
cert_test_block_3 98560 5 80 96 16
cert_test_block_3 98560 6 96 112 16
cert_test_block_3 98560 7 112 128 16
cert_test_block_3 98560 8 128 144 16
cert_test_block_3 98560 9 144 160 16
cert_test_block_3 98560 10 160 176 16
cert_test_block_3 98560 11 176 192 16
cert_test_block_3 98560 12 192 208 16
cert_test_block_3 98560 13 208 224 16
cert_test_block_3 98560 14 224 240 16
cert_test_block_3 98560 15 240 256 16
cert_test_block_3 98560 16 256 272 16
cert_test_block_3 98560 17 272 288 16
cert_test_block_3 98560 18 288 304 16
cert_test_block_3 98560 19 304 320 16
cert_test_block_3 98560 20 320 336 16
cert_test_block_3 98560 21 336 352 16
cert_test_block_3 98560 22 352 368 16
cert_test_block_3 98560 23 368 384 16
cert_test_block_3 98560 24 384 400 16
cert_test_block_3 98560 25 400 416 16
cert_test_block_3 98560 26 416 432 16
cert_test_block_3 98560 27 432 448 16
cert_test_block_3 98560 28 448 464 16
cert_test_block_3 98560 29 464 480 16
cert_test_block_3 98560 30 480 496 16
cert_test_block_3 98560 31 496 512 16
cert_test_block_3 98560 32 512 528 16
cert_test_block_3 98560 33 528 544 16
cert_test_block_3 98560 34 544 560 16
cert_test_block_3 98560 35 560 576 16
cert_test_block_3 98560 36 576 592 16
cert_test_block_3 98560 37 592 608 16
cert_test_block_3 98560 38 608 624 16
cert_test_block_3 98560 39 624 640 16
theorem test98560_complete : Interval test98560 0 640 :=
  (interval_append test98560 0 320 640
  (interval_append test98560 0 160 320
  (interval_append test98560 0 80 160
  (interval_append test98560 0 32 80
  (interval_append test98560 0 16 32
  test98560_block_0
  test98560_block_1)
  (interval_append test98560 32 48 80
  test98560_block_2
  (interval_append test98560 48 64 80
  test98560_block_3
  test98560_block_4)))
  (interval_append test98560 80 112 160
  (interval_append test98560 80 96 112
  test98560_block_5
  test98560_block_6)
  (interval_append test98560 112 128 160
  test98560_block_7
  (interval_append test98560 128 144 160
  test98560_block_8
  test98560_block_9))))
  (interval_append test98560 160 240 320
  (interval_append test98560 160 192 240
  (interval_append test98560 160 176 192
  test98560_block_10
  test98560_block_11)
  (interval_append test98560 192 208 240
  test98560_block_12
  (interval_append test98560 208 224 240
  test98560_block_13
  test98560_block_14)))
  (interval_append test98560 240 272 320
  (interval_append test98560 240 256 272
  test98560_block_15
  test98560_block_16)
  (interval_append test98560 272 288 320
  test98560_block_17
  (interval_append test98560 288 304 320
  test98560_block_18
  test98560_block_19)))))
  (interval_append test98560 320 480 640
  (interval_append test98560 320 400 480
  (interval_append test98560 320 352 400
  (interval_append test98560 320 336 352
  test98560_block_20
  test98560_block_21)
  (interval_append test98560 352 368 400
  test98560_block_22
  (interval_append test98560 368 384 400
  test98560_block_23
  test98560_block_24)))
  (interval_append test98560 400 432 480
  (interval_append test98560 400 416 432
  test98560_block_25
  test98560_block_26)
  (interval_append test98560 432 448 480
  test98560_block_27
  (interval_append test98560 448 464 480
  test98560_block_28
  test98560_block_29))))
  (interval_append test98560 480 560 640
  (interval_append test98560 480 512 560
  (interval_append test98560 480 496 512
  test98560_block_30
  test98560_block_31)
  (interval_append test98560 512 528 560
  test98560_block_32
  (interval_append test98560 528 544 560
  test98560_block_33
  test98560_block_34)))
  (interval_append test98560 560 592 640
  (interval_append test98560 560 576 592
  test98560_block_35
  test98560_block_36)
  (interval_append test98560 592 608 640
  test98560_block_37
  (interval_append test98560 608 624 640
  test98560_block_38
  test98560_block_39))))))
cert_nodeInterval_3 98560 99200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
