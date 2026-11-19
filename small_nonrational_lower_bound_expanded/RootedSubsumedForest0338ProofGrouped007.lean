module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 42880
cert_test_block_3 42880 0 0 16 16
cert_test_block_3 42880 1 16 32 16
cert_test_block_3 42880 2 32 48 16
cert_test_block_3 42880 3 48 64 16
cert_test_block_3 42880 4 64 80 16
cert_test_block_3 42880 5 80 96 16
cert_test_block_3 42880 6 96 112 16
cert_test_block_3 42880 7 112 128 16
cert_test_block_3 42880 8 128 144 16
cert_test_block_3 42880 9 144 160 16
cert_test_block_3 42880 10 160 176 16
cert_test_block_3 42880 11 176 192 16
cert_test_block_3 42880 12 192 208 16
cert_test_block_3 42880 13 208 224 16
cert_test_block_3 42880 14 224 240 16
cert_test_block_3 42880 15 240 256 16
cert_test_block_3 42880 16 256 272 16
cert_test_block_3 42880 17 272 288 16
cert_test_block_3 42880 18 288 304 16
cert_test_block_3 42880 19 304 320 16
cert_test_block_3 42880 20 320 336 16
cert_test_block_3 42880 21 336 352 16
cert_test_block_3 42880 22 352 368 16
cert_test_block_3 42880 23 368 384 16
cert_test_block_3 42880 24 384 400 16
cert_test_block_3 42880 25 400 416 16
cert_test_block_3 42880 26 416 432 16
cert_test_block_3 42880 27 432 448 16
cert_test_block_3 42880 28 448 464 16
cert_test_block_3 42880 29 464 480 16
cert_test_block_3 42880 30 480 496 16
cert_test_block_3 42880 31 496 512 16
cert_test_block_3 42880 32 512 528 16
cert_test_block_3 42880 33 528 544 16
cert_test_block_3 42880 34 544 560 16
cert_test_block_3 42880 35 560 576 16
cert_test_block_3 42880 36 576 592 16
cert_test_block_3 42880 37 592 608 16
cert_test_block_3 42880 38 608 624 16
cert_test_block_3 42880 39 624 640 16
theorem test42880_complete : Interval test42880 0 640 :=
  (interval_append test42880 0 320 640
  (interval_append test42880 0 160 320
  (interval_append test42880 0 80 160
  (interval_append test42880 0 32 80
  (interval_append test42880 0 16 32
  test42880_block_0
  test42880_block_1)
  (interval_append test42880 32 48 80
  test42880_block_2
  (interval_append test42880 48 64 80
  test42880_block_3
  test42880_block_4)))
  (interval_append test42880 80 112 160
  (interval_append test42880 80 96 112
  test42880_block_5
  test42880_block_6)
  (interval_append test42880 112 128 160
  test42880_block_7
  (interval_append test42880 128 144 160
  test42880_block_8
  test42880_block_9))))
  (interval_append test42880 160 240 320
  (interval_append test42880 160 192 240
  (interval_append test42880 160 176 192
  test42880_block_10
  test42880_block_11)
  (interval_append test42880 192 208 240
  test42880_block_12
  (interval_append test42880 208 224 240
  test42880_block_13
  test42880_block_14)))
  (interval_append test42880 240 272 320
  (interval_append test42880 240 256 272
  test42880_block_15
  test42880_block_16)
  (interval_append test42880 272 288 320
  test42880_block_17
  (interval_append test42880 288 304 320
  test42880_block_18
  test42880_block_19)))))
  (interval_append test42880 320 480 640
  (interval_append test42880 320 400 480
  (interval_append test42880 320 352 400
  (interval_append test42880 320 336 352
  test42880_block_20
  test42880_block_21)
  (interval_append test42880 352 368 400
  test42880_block_22
  (interval_append test42880 368 384 400
  test42880_block_23
  test42880_block_24)))
  (interval_append test42880 400 432 480
  (interval_append test42880 400 416 432
  test42880_block_25
  test42880_block_26)
  (interval_append test42880 432 448 480
  test42880_block_27
  (interval_append test42880 448 464 480
  test42880_block_28
  test42880_block_29))))
  (interval_append test42880 480 560 640
  (interval_append test42880 480 512 560
  (interval_append test42880 480 496 512
  test42880_block_30
  test42880_block_31)
  (interval_append test42880 512 528 560
  test42880_block_32
  (interval_append test42880 528 544 560
  test42880_block_33
  test42880_block_34)))
  (interval_append test42880 560 592 640
  (interval_append test42880 560 576 592
  test42880_block_35
  test42880_block_36)
  (interval_append test42880 592 608 640
  test42880_block_37
  (interval_append test42880 608 624 640
  test42880_block_38
  test42880_block_39))))))
cert_nodeInterval_3 42880 43520
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 43520
cert_test_block_3 43520 0 0 16 16
cert_test_block_3 43520 1 16 32 16
cert_test_block_3 43520 2 32 48 16
cert_test_block_3 43520 3 48 64 16
cert_test_block_3 43520 4 64 80 16
cert_test_block_3 43520 5 80 96 16
cert_test_block_3 43520 6 96 112 16
cert_test_block_3 43520 7 112 128 16
cert_test_block_3 43520 8 128 144 16
cert_test_block_3 43520 9 144 160 16
cert_test_block_3 43520 10 160 176 16
cert_test_block_3 43520 11 176 192 16
cert_test_block_3 43520 12 192 208 16
cert_test_block_3 43520 13 208 224 16
cert_test_block_3 43520 14 224 240 16
cert_test_block_3 43520 15 240 256 16
cert_test_block_3 43520 16 256 272 16
cert_test_block_3 43520 17 272 288 16
cert_test_block_3 43520 18 288 304 16
cert_test_block_3 43520 19 304 320 16
cert_test_block_3 43520 20 320 336 16
cert_test_block_3 43520 21 336 352 16
cert_test_block_3 43520 22 352 368 16
cert_test_block_3 43520 23 368 384 16
cert_test_block_3 43520 24 384 400 16
cert_test_block_3 43520 25 400 416 16
cert_test_block_3 43520 26 416 432 16
cert_test_block_3 43520 27 432 448 16
cert_test_block_3 43520 28 448 464 16
cert_test_block_3 43520 29 464 480 16
cert_test_block_3 43520 30 480 496 16
cert_test_block_3 43520 31 496 512 16
cert_test_block_3 43520 32 512 528 16
cert_test_block_3 43520 33 528 544 16
cert_test_block_3 43520 34 544 560 16
cert_test_block_3 43520 35 560 576 16
cert_test_block_3 43520 36 576 592 16
cert_test_block_3 43520 37 592 608 16
cert_test_block_3 43520 38 608 624 16
cert_test_block_3 43520 39 624 640 16
theorem test43520_complete : Interval test43520 0 640 :=
  (interval_append test43520 0 320 640
  (interval_append test43520 0 160 320
  (interval_append test43520 0 80 160
  (interval_append test43520 0 32 80
  (interval_append test43520 0 16 32
  test43520_block_0
  test43520_block_1)
  (interval_append test43520 32 48 80
  test43520_block_2
  (interval_append test43520 48 64 80
  test43520_block_3
  test43520_block_4)))
  (interval_append test43520 80 112 160
  (interval_append test43520 80 96 112
  test43520_block_5
  test43520_block_6)
  (interval_append test43520 112 128 160
  test43520_block_7
  (interval_append test43520 128 144 160
  test43520_block_8
  test43520_block_9))))
  (interval_append test43520 160 240 320
  (interval_append test43520 160 192 240
  (interval_append test43520 160 176 192
  test43520_block_10
  test43520_block_11)
  (interval_append test43520 192 208 240
  test43520_block_12
  (interval_append test43520 208 224 240
  test43520_block_13
  test43520_block_14)))
  (interval_append test43520 240 272 320
  (interval_append test43520 240 256 272
  test43520_block_15
  test43520_block_16)
  (interval_append test43520 272 288 320
  test43520_block_17
  (interval_append test43520 288 304 320
  test43520_block_18
  test43520_block_19)))))
  (interval_append test43520 320 480 640
  (interval_append test43520 320 400 480
  (interval_append test43520 320 352 400
  (interval_append test43520 320 336 352
  test43520_block_20
  test43520_block_21)
  (interval_append test43520 352 368 400
  test43520_block_22
  (interval_append test43520 368 384 400
  test43520_block_23
  test43520_block_24)))
  (interval_append test43520 400 432 480
  (interval_append test43520 400 416 432
  test43520_block_25
  test43520_block_26)
  (interval_append test43520 432 448 480
  test43520_block_27
  (interval_append test43520 448 464 480
  test43520_block_28
  test43520_block_29))))
  (interval_append test43520 480 560 640
  (interval_append test43520 480 512 560
  (interval_append test43520 480 496 512
  test43520_block_30
  test43520_block_31)
  (interval_append test43520 512 528 560
  test43520_block_32
  (interval_append test43520 528 544 560
  test43520_block_33
  test43520_block_34)))
  (interval_append test43520 560 592 640
  (interval_append test43520 560 576 592
  test43520_block_35
  test43520_block_36)
  (interval_append test43520 592 608 640
  test43520_block_37
  (interval_append test43520 608 624 640
  test43520_block_38
  test43520_block_39))))))
cert_nodeInterval_3 43520 44160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 44160
cert_test_block_3 44160 0 0 16 16
cert_test_block_3 44160 1 16 32 16
cert_test_block_3 44160 2 32 48 16
cert_test_block_3 44160 3 48 64 16
cert_test_block_3 44160 4 64 80 16
cert_test_block_3 44160 5 80 96 16
cert_test_block_3 44160 6 96 112 16
cert_test_block_3 44160 7 112 128 16
cert_test_block_3 44160 8 128 144 16
cert_test_block_3 44160 9 144 160 16
cert_test_block_3 44160 10 160 176 16
cert_test_block_3 44160 11 176 192 16
cert_test_block_3 44160 12 192 208 16
cert_test_block_3 44160 13 208 224 16
cert_test_block_3 44160 14 224 240 16
cert_test_block_3 44160 15 240 256 16
cert_test_block_3 44160 16 256 272 16
cert_test_block_3 44160 17 272 288 16
cert_test_block_3 44160 18 288 304 16
cert_test_block_3 44160 19 304 320 16
cert_test_block_3 44160 20 320 336 16
cert_test_block_3 44160 21 336 352 16
cert_test_block_3 44160 22 352 368 16
cert_test_block_3 44160 23 368 384 16
cert_test_block_3 44160 24 384 400 16
cert_test_block_3 44160 25 400 416 16
cert_test_block_3 44160 26 416 432 16
cert_test_block_3 44160 27 432 448 16
cert_test_block_3 44160 28 448 464 16
cert_test_block_3 44160 29 464 480 16
cert_test_block_3 44160 30 480 496 16
cert_test_block_3 44160 31 496 512 16
cert_test_block_3 44160 32 512 528 16
cert_test_block_3 44160 33 528 544 16
cert_test_block_3 44160 34 544 560 16
cert_test_block_3 44160 35 560 576 16
cert_test_block_3 44160 36 576 592 16
cert_test_block_3 44160 37 592 608 16
cert_test_block_3 44160 38 608 624 16
cert_test_block_3 44160 39 624 640 16
theorem test44160_complete : Interval test44160 0 640 :=
  (interval_append test44160 0 320 640
  (interval_append test44160 0 160 320
  (interval_append test44160 0 80 160
  (interval_append test44160 0 32 80
  (interval_append test44160 0 16 32
  test44160_block_0
  test44160_block_1)
  (interval_append test44160 32 48 80
  test44160_block_2
  (interval_append test44160 48 64 80
  test44160_block_3
  test44160_block_4)))
  (interval_append test44160 80 112 160
  (interval_append test44160 80 96 112
  test44160_block_5
  test44160_block_6)
  (interval_append test44160 112 128 160
  test44160_block_7
  (interval_append test44160 128 144 160
  test44160_block_8
  test44160_block_9))))
  (interval_append test44160 160 240 320
  (interval_append test44160 160 192 240
  (interval_append test44160 160 176 192
  test44160_block_10
  test44160_block_11)
  (interval_append test44160 192 208 240
  test44160_block_12
  (interval_append test44160 208 224 240
  test44160_block_13
  test44160_block_14)))
  (interval_append test44160 240 272 320
  (interval_append test44160 240 256 272
  test44160_block_15
  test44160_block_16)
  (interval_append test44160 272 288 320
  test44160_block_17
  (interval_append test44160 288 304 320
  test44160_block_18
  test44160_block_19)))))
  (interval_append test44160 320 480 640
  (interval_append test44160 320 400 480
  (interval_append test44160 320 352 400
  (interval_append test44160 320 336 352
  test44160_block_20
  test44160_block_21)
  (interval_append test44160 352 368 400
  test44160_block_22
  (interval_append test44160 368 384 400
  test44160_block_23
  test44160_block_24)))
  (interval_append test44160 400 432 480
  (interval_append test44160 400 416 432
  test44160_block_25
  test44160_block_26)
  (interval_append test44160 432 448 480
  test44160_block_27
  (interval_append test44160 448 464 480
  test44160_block_28
  test44160_block_29))))
  (interval_append test44160 480 560 640
  (interval_append test44160 480 512 560
  (interval_append test44160 480 496 512
  test44160_block_30
  test44160_block_31)
  (interval_append test44160 512 528 560
  test44160_block_32
  (interval_append test44160 528 544 560
  test44160_block_33
  test44160_block_34)))
  (interval_append test44160 560 592 640
  (interval_append test44160 560 576 592
  test44160_block_35
  test44160_block_36)
  (interval_append test44160 592 608 640
  test44160_block_37
  (interval_append test44160 608 624 640
  test44160_block_38
  test44160_block_39))))))
cert_nodeInterval_3 44160 44800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 44800
cert_test_block_3 44800 0 0 16 16
cert_test_block_3 44800 1 16 32 16
cert_test_block_3 44800 2 32 48 16
cert_test_block_3 44800 3 48 64 16
cert_test_block_3 44800 4 64 80 16
cert_test_block_3 44800 5 80 96 16
cert_test_block_3 44800 6 96 112 16
cert_test_block_3 44800 7 112 128 16
cert_test_block_3 44800 8 128 144 16
cert_test_block_3 44800 9 144 160 16
cert_test_block_3 44800 10 160 176 16
cert_test_block_3 44800 11 176 192 16
cert_test_block_3 44800 12 192 208 16
cert_test_block_3 44800 13 208 224 16
cert_test_block_3 44800 14 224 240 16
cert_test_block_3 44800 15 240 256 16
cert_test_block_3 44800 16 256 272 16
cert_test_block_3 44800 17 272 288 16
cert_test_block_3 44800 18 288 304 16
cert_test_block_3 44800 19 304 320 16
cert_test_block_3 44800 20 320 336 16
cert_test_block_3 44800 21 336 352 16
cert_test_block_3 44800 22 352 368 16
cert_test_block_3 44800 23 368 384 16
cert_test_block_3 44800 24 384 400 16
cert_test_block_3 44800 25 400 416 16
cert_test_block_3 44800 26 416 432 16
cert_test_block_3 44800 27 432 448 16
cert_test_block_3 44800 28 448 464 16
cert_test_block_3 44800 29 464 480 16
cert_test_block_3 44800 30 480 496 16
cert_test_block_3 44800 31 496 512 16
cert_test_block_3 44800 32 512 528 16
cert_test_block_3 44800 33 528 544 16
cert_test_block_3 44800 34 544 560 16
cert_test_block_3 44800 35 560 576 16
cert_test_block_3 44800 36 576 592 16
cert_test_block_3 44800 37 592 608 16
cert_test_block_3 44800 38 608 624 16
cert_test_block_3 44800 39 624 640 16
theorem test44800_complete : Interval test44800 0 640 :=
  (interval_append test44800 0 320 640
  (interval_append test44800 0 160 320
  (interval_append test44800 0 80 160
  (interval_append test44800 0 32 80
  (interval_append test44800 0 16 32
  test44800_block_0
  test44800_block_1)
  (interval_append test44800 32 48 80
  test44800_block_2
  (interval_append test44800 48 64 80
  test44800_block_3
  test44800_block_4)))
  (interval_append test44800 80 112 160
  (interval_append test44800 80 96 112
  test44800_block_5
  test44800_block_6)
  (interval_append test44800 112 128 160
  test44800_block_7
  (interval_append test44800 128 144 160
  test44800_block_8
  test44800_block_9))))
  (interval_append test44800 160 240 320
  (interval_append test44800 160 192 240
  (interval_append test44800 160 176 192
  test44800_block_10
  test44800_block_11)
  (interval_append test44800 192 208 240
  test44800_block_12
  (interval_append test44800 208 224 240
  test44800_block_13
  test44800_block_14)))
  (interval_append test44800 240 272 320
  (interval_append test44800 240 256 272
  test44800_block_15
  test44800_block_16)
  (interval_append test44800 272 288 320
  test44800_block_17
  (interval_append test44800 288 304 320
  test44800_block_18
  test44800_block_19)))))
  (interval_append test44800 320 480 640
  (interval_append test44800 320 400 480
  (interval_append test44800 320 352 400
  (interval_append test44800 320 336 352
  test44800_block_20
  test44800_block_21)
  (interval_append test44800 352 368 400
  test44800_block_22
  (interval_append test44800 368 384 400
  test44800_block_23
  test44800_block_24)))
  (interval_append test44800 400 432 480
  (interval_append test44800 400 416 432
  test44800_block_25
  test44800_block_26)
  (interval_append test44800 432 448 480
  test44800_block_27
  (interval_append test44800 448 464 480
  test44800_block_28
  test44800_block_29))))
  (interval_append test44800 480 560 640
  (interval_append test44800 480 512 560
  (interval_append test44800 480 496 512
  test44800_block_30
  test44800_block_31)
  (interval_append test44800 512 528 560
  test44800_block_32
  (interval_append test44800 528 544 560
  test44800_block_33
  test44800_block_34)))
  (interval_append test44800 560 592 640
  (interval_append test44800 560 576 592
  test44800_block_35
  test44800_block_36)
  (interval_append test44800 592 608 640
  test44800_block_37
  (interval_append test44800 608 624 640
  test44800_block_38
  test44800_block_39))))))
cert_nodeInterval_3 44800 45440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 45440
cert_test_block_3 45440 0 0 16 16
cert_test_block_3 45440 1 16 32 16
cert_test_block_3 45440 2 32 48 16
cert_test_block_3 45440 3 48 64 16
cert_test_block_3 45440 4 64 80 16
cert_test_block_3 45440 5 80 96 16
cert_test_block_3 45440 6 96 112 16
cert_test_block_3 45440 7 112 128 16
cert_test_block_3 45440 8 128 144 16
cert_test_block_3 45440 9 144 160 16
cert_test_block_3 45440 10 160 176 16
cert_test_block_3 45440 11 176 192 16
cert_test_block_3 45440 12 192 208 16
cert_test_block_3 45440 13 208 224 16
cert_test_block_3 45440 14 224 240 16
cert_test_block_3 45440 15 240 256 16
cert_test_block_3 45440 16 256 272 16
cert_test_block_3 45440 17 272 288 16
cert_test_block_3 45440 18 288 304 16
cert_test_block_3 45440 19 304 320 16
cert_test_block_3 45440 20 320 336 16
cert_test_block_3 45440 21 336 352 16
cert_test_block_3 45440 22 352 368 16
cert_test_block_3 45440 23 368 384 16
cert_test_block_3 45440 24 384 400 16
cert_test_block_3 45440 25 400 416 16
cert_test_block_3 45440 26 416 432 16
cert_test_block_3 45440 27 432 448 16
cert_test_block_3 45440 28 448 464 16
cert_test_block_3 45440 29 464 480 16
cert_test_block_3 45440 30 480 496 16
cert_test_block_3 45440 31 496 512 16
cert_test_block_3 45440 32 512 528 16
cert_test_block_3 45440 33 528 544 16
cert_test_block_3 45440 34 544 560 16
cert_test_block_3 45440 35 560 576 16
cert_test_block_3 45440 36 576 592 16
cert_test_block_3 45440 37 592 608 16
cert_test_block_3 45440 38 608 624 16
cert_test_block_3 45440 39 624 640 16
theorem test45440_complete : Interval test45440 0 640 :=
  (interval_append test45440 0 320 640
  (interval_append test45440 0 160 320
  (interval_append test45440 0 80 160
  (interval_append test45440 0 32 80
  (interval_append test45440 0 16 32
  test45440_block_0
  test45440_block_1)
  (interval_append test45440 32 48 80
  test45440_block_2
  (interval_append test45440 48 64 80
  test45440_block_3
  test45440_block_4)))
  (interval_append test45440 80 112 160
  (interval_append test45440 80 96 112
  test45440_block_5
  test45440_block_6)
  (interval_append test45440 112 128 160
  test45440_block_7
  (interval_append test45440 128 144 160
  test45440_block_8
  test45440_block_9))))
  (interval_append test45440 160 240 320
  (interval_append test45440 160 192 240
  (interval_append test45440 160 176 192
  test45440_block_10
  test45440_block_11)
  (interval_append test45440 192 208 240
  test45440_block_12
  (interval_append test45440 208 224 240
  test45440_block_13
  test45440_block_14)))
  (interval_append test45440 240 272 320
  (interval_append test45440 240 256 272
  test45440_block_15
  test45440_block_16)
  (interval_append test45440 272 288 320
  test45440_block_17
  (interval_append test45440 288 304 320
  test45440_block_18
  test45440_block_19)))))
  (interval_append test45440 320 480 640
  (interval_append test45440 320 400 480
  (interval_append test45440 320 352 400
  (interval_append test45440 320 336 352
  test45440_block_20
  test45440_block_21)
  (interval_append test45440 352 368 400
  test45440_block_22
  (interval_append test45440 368 384 400
  test45440_block_23
  test45440_block_24)))
  (interval_append test45440 400 432 480
  (interval_append test45440 400 416 432
  test45440_block_25
  test45440_block_26)
  (interval_append test45440 432 448 480
  test45440_block_27
  (interval_append test45440 448 464 480
  test45440_block_28
  test45440_block_29))))
  (interval_append test45440 480 560 640
  (interval_append test45440 480 512 560
  (interval_append test45440 480 496 512
  test45440_block_30
  test45440_block_31)
  (interval_append test45440 512 528 560
  test45440_block_32
  (interval_append test45440 528 544 560
  test45440_block_33
  test45440_block_34)))
  (interval_append test45440 560 592 640
  (interval_append test45440 560 576 592
  test45440_block_35
  test45440_block_36)
  (interval_append test45440 592 608 640
  test45440_block_37
  (interval_append test45440 608 624 640
  test45440_block_38
  test45440_block_39))))))
cert_nodeInterval_3 45440 46080
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 46080
cert_test_block_3 46080 0 0 16 16
cert_test_block_3 46080 1 16 32 16
cert_test_block_3 46080 2 32 48 16
cert_test_block_3 46080 3 48 64 16
cert_test_block_3 46080 4 64 80 16
cert_test_block_3 46080 5 80 96 16
cert_test_block_3 46080 6 96 112 16
cert_test_block_3 46080 7 112 128 16
cert_test_block_3 46080 8 128 144 16
cert_test_block_3 46080 9 144 160 16
cert_test_block_3 46080 10 160 176 16
cert_test_block_3 46080 11 176 192 16
cert_test_block_3 46080 12 192 208 16
cert_test_block_3 46080 13 208 224 16
cert_test_block_3 46080 14 224 240 16
cert_test_block_3 46080 15 240 256 16
cert_test_block_3 46080 16 256 272 16
cert_test_block_3 46080 17 272 288 16
cert_test_block_3 46080 18 288 304 16
cert_test_block_3 46080 19 304 320 16
cert_test_block_3 46080 20 320 336 16
cert_test_block_3 46080 21 336 352 16
cert_test_block_3 46080 22 352 368 16
cert_test_block_3 46080 23 368 384 16
cert_test_block_3 46080 24 384 400 16
cert_test_block_3 46080 25 400 416 16
cert_test_block_3 46080 26 416 432 16
cert_test_block_3 46080 27 432 448 16
cert_test_block_3 46080 28 448 464 16
cert_test_block_3 46080 29 464 480 16
cert_test_block_3 46080 30 480 496 16
cert_test_block_3 46080 31 496 512 16
cert_test_block_3 46080 32 512 528 16
cert_test_block_3 46080 33 528 544 16
cert_test_block_3 46080 34 544 560 16
cert_test_block_3 46080 35 560 576 16
cert_test_block_3 46080 36 576 592 16
cert_test_block_3 46080 37 592 608 16
cert_test_block_3 46080 38 608 624 16
cert_test_block_3 46080 39 624 640 16
theorem test46080_complete : Interval test46080 0 640 :=
  (interval_append test46080 0 320 640
  (interval_append test46080 0 160 320
  (interval_append test46080 0 80 160
  (interval_append test46080 0 32 80
  (interval_append test46080 0 16 32
  test46080_block_0
  test46080_block_1)
  (interval_append test46080 32 48 80
  test46080_block_2
  (interval_append test46080 48 64 80
  test46080_block_3
  test46080_block_4)))
  (interval_append test46080 80 112 160
  (interval_append test46080 80 96 112
  test46080_block_5
  test46080_block_6)
  (interval_append test46080 112 128 160
  test46080_block_7
  (interval_append test46080 128 144 160
  test46080_block_8
  test46080_block_9))))
  (interval_append test46080 160 240 320
  (interval_append test46080 160 192 240
  (interval_append test46080 160 176 192
  test46080_block_10
  test46080_block_11)
  (interval_append test46080 192 208 240
  test46080_block_12
  (interval_append test46080 208 224 240
  test46080_block_13
  test46080_block_14)))
  (interval_append test46080 240 272 320
  (interval_append test46080 240 256 272
  test46080_block_15
  test46080_block_16)
  (interval_append test46080 272 288 320
  test46080_block_17
  (interval_append test46080 288 304 320
  test46080_block_18
  test46080_block_19)))))
  (interval_append test46080 320 480 640
  (interval_append test46080 320 400 480
  (interval_append test46080 320 352 400
  (interval_append test46080 320 336 352
  test46080_block_20
  test46080_block_21)
  (interval_append test46080 352 368 400
  test46080_block_22
  (interval_append test46080 368 384 400
  test46080_block_23
  test46080_block_24)))
  (interval_append test46080 400 432 480
  (interval_append test46080 400 416 432
  test46080_block_25
  test46080_block_26)
  (interval_append test46080 432 448 480
  test46080_block_27
  (interval_append test46080 448 464 480
  test46080_block_28
  test46080_block_29))))
  (interval_append test46080 480 560 640
  (interval_append test46080 480 512 560
  (interval_append test46080 480 496 512
  test46080_block_30
  test46080_block_31)
  (interval_append test46080 512 528 560
  test46080_block_32
  (interval_append test46080 528 544 560
  test46080_block_33
  test46080_block_34)))
  (interval_append test46080 560 592 640
  (interval_append test46080 560 576 592
  test46080_block_35
  test46080_block_36)
  (interval_append test46080 592 608 640
  test46080_block_37
  (interval_append test46080 608 624 640
  test46080_block_38
  test46080_block_39))))))
cert_nodeInterval_3 46080 46720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 46720
cert_test_block_3 46720 0 0 16 16
cert_test_block_3 46720 1 16 32 16
cert_test_block_3 46720 2 32 48 16
cert_test_block_3 46720 3 48 64 16
cert_test_block_3 46720 4 64 80 16
cert_test_block_3 46720 5 80 96 16
cert_test_block_3 46720 6 96 112 16
cert_test_block_3 46720 7 112 128 16
cert_test_block_3 46720 8 128 144 16
cert_test_block_3 46720 9 144 160 16
cert_test_block_3 46720 10 160 176 16
cert_test_block_3 46720 11 176 192 16
cert_test_block_3 46720 12 192 208 16
cert_test_block_3 46720 13 208 224 16
cert_test_block_3 46720 14 224 240 16
cert_test_block_3 46720 15 240 256 16
cert_test_block_3 46720 16 256 272 16
cert_test_block_3 46720 17 272 288 16
cert_test_block_3 46720 18 288 304 16
cert_test_block_3 46720 19 304 320 16
cert_test_block_3 46720 20 320 336 16
cert_test_block_3 46720 21 336 352 16
cert_test_block_3 46720 22 352 368 16
cert_test_block_3 46720 23 368 384 16
cert_test_block_3 46720 24 384 400 16
cert_test_block_3 46720 25 400 416 16
cert_test_block_3 46720 26 416 432 16
cert_test_block_3 46720 27 432 448 16
cert_test_block_3 46720 28 448 464 16
cert_test_block_3 46720 29 464 480 16
cert_test_block_3 46720 30 480 496 16
cert_test_block_3 46720 31 496 512 16
cert_test_block_3 46720 32 512 528 16
cert_test_block_3 46720 33 528 544 16
cert_test_block_3 46720 34 544 560 16
cert_test_block_3 46720 35 560 576 16
cert_test_block_3 46720 36 576 592 16
cert_test_block_3 46720 37 592 608 16
cert_test_block_3 46720 38 608 624 16
cert_test_block_3 46720 39 624 640 16
theorem test46720_complete : Interval test46720 0 640 :=
  (interval_append test46720 0 320 640
  (interval_append test46720 0 160 320
  (interval_append test46720 0 80 160
  (interval_append test46720 0 32 80
  (interval_append test46720 0 16 32
  test46720_block_0
  test46720_block_1)
  (interval_append test46720 32 48 80
  test46720_block_2
  (interval_append test46720 48 64 80
  test46720_block_3
  test46720_block_4)))
  (interval_append test46720 80 112 160
  (interval_append test46720 80 96 112
  test46720_block_5
  test46720_block_6)
  (interval_append test46720 112 128 160
  test46720_block_7
  (interval_append test46720 128 144 160
  test46720_block_8
  test46720_block_9))))
  (interval_append test46720 160 240 320
  (interval_append test46720 160 192 240
  (interval_append test46720 160 176 192
  test46720_block_10
  test46720_block_11)
  (interval_append test46720 192 208 240
  test46720_block_12
  (interval_append test46720 208 224 240
  test46720_block_13
  test46720_block_14)))
  (interval_append test46720 240 272 320
  (interval_append test46720 240 256 272
  test46720_block_15
  test46720_block_16)
  (interval_append test46720 272 288 320
  test46720_block_17
  (interval_append test46720 288 304 320
  test46720_block_18
  test46720_block_19)))))
  (interval_append test46720 320 480 640
  (interval_append test46720 320 400 480
  (interval_append test46720 320 352 400
  (interval_append test46720 320 336 352
  test46720_block_20
  test46720_block_21)
  (interval_append test46720 352 368 400
  test46720_block_22
  (interval_append test46720 368 384 400
  test46720_block_23
  test46720_block_24)))
  (interval_append test46720 400 432 480
  (interval_append test46720 400 416 432
  test46720_block_25
  test46720_block_26)
  (interval_append test46720 432 448 480
  test46720_block_27
  (interval_append test46720 448 464 480
  test46720_block_28
  test46720_block_29))))
  (interval_append test46720 480 560 640
  (interval_append test46720 480 512 560
  (interval_append test46720 480 496 512
  test46720_block_30
  test46720_block_31)
  (interval_append test46720 512 528 560
  test46720_block_32
  (interval_append test46720 528 544 560
  test46720_block_33
  test46720_block_34)))
  (interval_append test46720 560 592 640
  (interval_append test46720 560 576 592
  test46720_block_35
  test46720_block_36)
  (interval_append test46720 592 608 640
  test46720_block_37
  (interval_append test46720 608 624 640
  test46720_block_38
  test46720_block_39))))))
cert_nodeInterval_3 46720 47360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 47360
cert_test_block_3 47360 0 0 16 16
cert_test_block_3 47360 1 16 32 16
cert_test_block_3 47360 2 32 48 16
cert_test_block_3 47360 3 48 64 16
cert_test_block_3 47360 4 64 80 16
cert_test_block_3 47360 5 80 96 16
cert_test_block_3 47360 6 96 112 16
cert_test_block_3 47360 7 112 128 16
cert_test_block_3 47360 8 128 144 16
cert_test_block_3 47360 9 144 160 16
cert_test_block_3 47360 10 160 176 16
cert_test_block_3 47360 11 176 192 16
cert_test_block_3 47360 12 192 208 16
cert_test_block_3 47360 13 208 224 16
cert_test_block_3 47360 14 224 240 16
cert_test_block_3 47360 15 240 256 16
cert_test_block_3 47360 16 256 272 16
cert_test_block_3 47360 17 272 288 16
cert_test_block_3 47360 18 288 304 16
cert_test_block_3 47360 19 304 320 16
cert_test_block_3 47360 20 320 336 16
cert_test_block_3 47360 21 336 352 16
cert_test_block_3 47360 22 352 368 16
cert_test_block_3 47360 23 368 384 16
cert_test_block_3 47360 24 384 400 16
cert_test_block_3 47360 25 400 416 16
cert_test_block_3 47360 26 416 432 16
cert_test_block_3 47360 27 432 448 16
cert_test_block_3 47360 28 448 464 16
cert_test_block_3 47360 29 464 480 16
cert_test_block_3 47360 30 480 496 16
cert_test_block_3 47360 31 496 512 16
cert_test_block_3 47360 32 512 528 16
cert_test_block_3 47360 33 528 544 16
cert_test_block_3 47360 34 544 560 16
cert_test_block_3 47360 35 560 576 16
cert_test_block_3 47360 36 576 592 16
cert_test_block_3 47360 37 592 608 16
cert_test_block_3 47360 38 608 624 16
cert_test_block_3 47360 39 624 640 16
theorem test47360_complete : Interval test47360 0 640 :=
  (interval_append test47360 0 320 640
  (interval_append test47360 0 160 320
  (interval_append test47360 0 80 160
  (interval_append test47360 0 32 80
  (interval_append test47360 0 16 32
  test47360_block_0
  test47360_block_1)
  (interval_append test47360 32 48 80
  test47360_block_2
  (interval_append test47360 48 64 80
  test47360_block_3
  test47360_block_4)))
  (interval_append test47360 80 112 160
  (interval_append test47360 80 96 112
  test47360_block_5
  test47360_block_6)
  (interval_append test47360 112 128 160
  test47360_block_7
  (interval_append test47360 128 144 160
  test47360_block_8
  test47360_block_9))))
  (interval_append test47360 160 240 320
  (interval_append test47360 160 192 240
  (interval_append test47360 160 176 192
  test47360_block_10
  test47360_block_11)
  (interval_append test47360 192 208 240
  test47360_block_12
  (interval_append test47360 208 224 240
  test47360_block_13
  test47360_block_14)))
  (interval_append test47360 240 272 320
  (interval_append test47360 240 256 272
  test47360_block_15
  test47360_block_16)
  (interval_append test47360 272 288 320
  test47360_block_17
  (interval_append test47360 288 304 320
  test47360_block_18
  test47360_block_19)))))
  (interval_append test47360 320 480 640
  (interval_append test47360 320 400 480
  (interval_append test47360 320 352 400
  (interval_append test47360 320 336 352
  test47360_block_20
  test47360_block_21)
  (interval_append test47360 352 368 400
  test47360_block_22
  (interval_append test47360 368 384 400
  test47360_block_23
  test47360_block_24)))
  (interval_append test47360 400 432 480
  (interval_append test47360 400 416 432
  test47360_block_25
  test47360_block_26)
  (interval_append test47360 432 448 480
  test47360_block_27
  (interval_append test47360 448 464 480
  test47360_block_28
  test47360_block_29))))
  (interval_append test47360 480 560 640
  (interval_append test47360 480 512 560
  (interval_append test47360 480 496 512
  test47360_block_30
  test47360_block_31)
  (interval_append test47360 512 528 560
  test47360_block_32
  (interval_append test47360 528 544 560
  test47360_block_33
  test47360_block_34)))
  (interval_append test47360 560 592 640
  (interval_append test47360 560 576 592
  test47360_block_35
  test47360_block_36)
  (interval_append test47360 592 608 640
  test47360_block_37
  (interval_append test47360 608 624 640
  test47360_block_38
  test47360_block_39))))))
cert_nodeInterval_3 47360 48000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end
