module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 42240
cert_test_block_3 42240 0 0 16 16
cert_test_block_3 42240 1 16 32 16
cert_test_block_3 42240 2 32 48 16
cert_test_block_3 42240 3 48 64 16
cert_test_block_3 42240 4 64 80 16
cert_test_block_3 42240 5 80 96 16
cert_test_block_3 42240 6 96 112 16
cert_test_block_3 42240 7 112 128 16
cert_test_block_3 42240 8 128 144 16
cert_test_block_3 42240 9 144 160 16
cert_test_block_3 42240 10 160 176 16
cert_test_block_3 42240 11 176 192 16
cert_test_block_3 42240 12 192 208 16
cert_test_block_3 42240 13 208 224 16
cert_test_block_3 42240 14 224 240 16
cert_test_block_3 42240 15 240 256 16
cert_test_block_3 42240 16 256 272 16
cert_test_block_3 42240 17 272 288 16
cert_test_block_3 42240 18 288 304 16
cert_test_block_3 42240 19 304 320 16
cert_test_block_3 42240 20 320 336 16
cert_test_block_3 42240 21 336 352 16
cert_test_block_3 42240 22 352 368 16
cert_test_block_3 42240 23 368 384 16
cert_test_block_3 42240 24 384 400 16
cert_test_block_3 42240 25 400 416 16
cert_test_block_3 42240 26 416 432 16
cert_test_block_3 42240 27 432 448 16
cert_test_block_3 42240 28 448 464 16
cert_test_block_3 42240 29 464 480 16
cert_test_block_3 42240 30 480 496 16
cert_test_block_3 42240 31 496 512 16
cert_test_block_3 42240 32 512 528 16
cert_test_block_3 42240 33 528 544 16
cert_test_block_3 42240 34 544 560 16
cert_test_block_3 42240 35 560 576 16
cert_test_block_3 42240 36 576 592 16
cert_test_block_3 42240 37 592 608 16
cert_test_block_3 42240 38 608 624 16
cert_test_block_3 42240 39 624 640 16
theorem test42240_complete : Interval test42240 0 640 :=
  (interval_append test42240 0 320 640
  (interval_append test42240 0 160 320
  (interval_append test42240 0 80 160
  (interval_append test42240 0 32 80
  (interval_append test42240 0 16 32
  test42240_block_0
  test42240_block_1)
  (interval_append test42240 32 48 80
  test42240_block_2
  (interval_append test42240 48 64 80
  test42240_block_3
  test42240_block_4)))
  (interval_append test42240 80 112 160
  (interval_append test42240 80 96 112
  test42240_block_5
  test42240_block_6)
  (interval_append test42240 112 128 160
  test42240_block_7
  (interval_append test42240 128 144 160
  test42240_block_8
  test42240_block_9))))
  (interval_append test42240 160 240 320
  (interval_append test42240 160 192 240
  (interval_append test42240 160 176 192
  test42240_block_10
  test42240_block_11)
  (interval_append test42240 192 208 240
  test42240_block_12
  (interval_append test42240 208 224 240
  test42240_block_13
  test42240_block_14)))
  (interval_append test42240 240 272 320
  (interval_append test42240 240 256 272
  test42240_block_15
  test42240_block_16)
  (interval_append test42240 272 288 320
  test42240_block_17
  (interval_append test42240 288 304 320
  test42240_block_18
  test42240_block_19)))))
  (interval_append test42240 320 480 640
  (interval_append test42240 320 400 480
  (interval_append test42240 320 352 400
  (interval_append test42240 320 336 352
  test42240_block_20
  test42240_block_21)
  (interval_append test42240 352 368 400
  test42240_block_22
  (interval_append test42240 368 384 400
  test42240_block_23
  test42240_block_24)))
  (interval_append test42240 400 432 480
  (interval_append test42240 400 416 432
  test42240_block_25
  test42240_block_26)
  (interval_append test42240 432 448 480
  test42240_block_27
  (interval_append test42240 448 464 480
  test42240_block_28
  test42240_block_29))))
  (interval_append test42240 480 560 640
  (interval_append test42240 480 512 560
  (interval_append test42240 480 496 512
  test42240_block_30
  test42240_block_31)
  (interval_append test42240 512 528 560
  test42240_block_32
  (interval_append test42240 528 544 560
  test42240_block_33
  test42240_block_34)))
  (interval_append test42240 560 592 640
  (interval_append test42240 560 576 592
  test42240_block_35
  test42240_block_36)
  (interval_append test42240 592 608 640
  test42240_block_37
  (interval_append test42240 608 624 640
  test42240_block_38
  test42240_block_39))))))
cert_nodeInterval_3 42240 42880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end
