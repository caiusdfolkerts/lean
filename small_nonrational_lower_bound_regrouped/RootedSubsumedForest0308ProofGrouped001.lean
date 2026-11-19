module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0308Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 7680
cert_test_block_3 7680 0 0 16 16
cert_test_block_3 7680 1 16 32 16
cert_test_block_3 7680 2 32 48 16
cert_test_block_3 7680 3 48 64 16
cert_test_block_3 7680 4 64 80 16
cert_test_block_3 7680 5 80 96 16
cert_test_block_3 7680 6 96 112 16
cert_test_block_3 7680 7 112 128 16
cert_test_block_3 7680 8 128 144 16
cert_test_block_3 7680 9 144 160 16
cert_test_block_3 7680 10 160 176 16
cert_test_block_3 7680 11 176 192 16
cert_test_block_3 7680 12 192 208 16
cert_test_block_3 7680 13 208 224 16
cert_test_block_3 7680 14 224 240 16
cert_test_block_3 7680 15 240 256 16
cert_test_block_3 7680 16 256 272 16
cert_test_block_3 7680 17 272 288 16
cert_test_block_3 7680 18 288 304 16
cert_test_block_3 7680 19 304 320 16
cert_test_block_3 7680 20 320 336 16
cert_test_block_3 7680 21 336 352 16
cert_test_block_3 7680 22 352 368 16
cert_test_block_3 7680 23 368 384 16
cert_test_block_3 7680 24 384 400 16
cert_test_block_3 7680 25 400 416 16
cert_test_block_3 7680 26 416 432 16
cert_test_block_3 7680 27 432 448 16
cert_test_block_3 7680 28 448 464 16
cert_test_block_3 7680 29 464 480 16
cert_test_block_3 7680 30 480 496 16
cert_test_block_3 7680 31 496 512 16
cert_test_block_3 7680 32 512 528 16
cert_test_block_3 7680 33 528 544 16
cert_test_block_3 7680 34 544 560 16
cert_test_block_3 7680 35 560 576 16
cert_test_block_3 7680 36 576 592 16
cert_test_block_3 7680 37 592 608 16
cert_test_block_3 7680 38 608 624 16
cert_test_block_3 7680 39 624 640 16
theorem test7680_complete : Interval test7680 0 640 :=
  (interval_append test7680 0 320 640
  (interval_append test7680 0 160 320
  (interval_append test7680 0 80 160
  (interval_append test7680 0 32 80
  (interval_append test7680 0 16 32
  test7680_block_0
  test7680_block_1)
  (interval_append test7680 32 48 80
  test7680_block_2
  (interval_append test7680 48 64 80
  test7680_block_3
  test7680_block_4)))
  (interval_append test7680 80 112 160
  (interval_append test7680 80 96 112
  test7680_block_5
  test7680_block_6)
  (interval_append test7680 112 128 160
  test7680_block_7
  (interval_append test7680 128 144 160
  test7680_block_8
  test7680_block_9))))
  (interval_append test7680 160 240 320
  (interval_append test7680 160 192 240
  (interval_append test7680 160 176 192
  test7680_block_10
  test7680_block_11)
  (interval_append test7680 192 208 240
  test7680_block_12
  (interval_append test7680 208 224 240
  test7680_block_13
  test7680_block_14)))
  (interval_append test7680 240 272 320
  (interval_append test7680 240 256 272
  test7680_block_15
  test7680_block_16)
  (interval_append test7680 272 288 320
  test7680_block_17
  (interval_append test7680 288 304 320
  test7680_block_18
  test7680_block_19)))))
  (interval_append test7680 320 480 640
  (interval_append test7680 320 400 480
  (interval_append test7680 320 352 400
  (interval_append test7680 320 336 352
  test7680_block_20
  test7680_block_21)
  (interval_append test7680 352 368 400
  test7680_block_22
  (interval_append test7680 368 384 400
  test7680_block_23
  test7680_block_24)))
  (interval_append test7680 400 432 480
  (interval_append test7680 400 416 432
  test7680_block_25
  test7680_block_26)
  (interval_append test7680 432 448 480
  test7680_block_27
  (interval_append test7680 448 464 480
  test7680_block_28
  test7680_block_29))))
  (interval_append test7680 480 560 640
  (interval_append test7680 480 512 560
  (interval_append test7680 480 496 512
  test7680_block_30
  test7680_block_31)
  (interval_append test7680 512 528 560
  test7680_block_32
  (interval_append test7680 528 544 560
  test7680_block_33
  test7680_block_34)))
  (interval_append test7680 560 592 640
  (interval_append test7680 560 576 592
  test7680_block_35
  test7680_block_36)
  (interval_append test7680 592 608 640
  test7680_block_37
  (interval_append test7680 608 624 640
  test7680_block_38
  test7680_block_39))))))
cert_nodeInterval_3 7680 8320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 8320
cert_test_block_3 8320 0 0 16 16
cert_test_block_3 8320 1 16 32 16
cert_test_block_3 8320 2 32 48 16
cert_test_block_3 8320 3 48 64 16
cert_test_block_3 8320 4 64 80 16
cert_test_block_3 8320 5 80 96 16
cert_test_block_3 8320 6 96 112 16
cert_test_block_3 8320 7 112 128 16
cert_test_block_3 8320 8 128 144 16
cert_test_block_3 8320 9 144 160 16
cert_test_block_3 8320 10 160 176 16
cert_test_block_3 8320 11 176 192 16
cert_test_block_3 8320 12 192 208 16
cert_test_block_3 8320 13 208 224 16
cert_test_block_3 8320 14 224 240 16
cert_test_block_3 8320 15 240 256 16
cert_test_block_3 8320 16 256 272 16
cert_test_block_3 8320 17 272 288 16
cert_test_block_3 8320 18 288 304 16
cert_test_block_3 8320 19 304 320 16
cert_test_block_3 8320 20 320 336 16
cert_test_block_3 8320 21 336 352 16
cert_test_block_3 8320 22 352 368 16
cert_test_block_3 8320 23 368 384 16
cert_test_block_3 8320 24 384 400 16
cert_test_block_3 8320 25 400 416 16
cert_test_block_3 8320 26 416 432 16
cert_test_block_3 8320 27 432 448 16
cert_test_block_3 8320 28 448 464 16
cert_test_block_3 8320 29 464 480 16
cert_test_block_3 8320 30 480 496 16
cert_test_block_3 8320 31 496 512 16
cert_test_block_3 8320 32 512 528 16
cert_test_block_3 8320 33 528 544 16
cert_test_block_3 8320 34 544 560 16
cert_test_block_3 8320 35 560 576 16
cert_test_block_3 8320 36 576 592 16
cert_test_block_3 8320 37 592 608 16
cert_test_block_3 8320 38 608 624 16
cert_test_block_3 8320 39 624 640 16
theorem test8320_complete : Interval test8320 0 640 :=
  (interval_append test8320 0 320 640
  (interval_append test8320 0 160 320
  (interval_append test8320 0 80 160
  (interval_append test8320 0 32 80
  (interval_append test8320 0 16 32
  test8320_block_0
  test8320_block_1)
  (interval_append test8320 32 48 80
  test8320_block_2
  (interval_append test8320 48 64 80
  test8320_block_3
  test8320_block_4)))
  (interval_append test8320 80 112 160
  (interval_append test8320 80 96 112
  test8320_block_5
  test8320_block_6)
  (interval_append test8320 112 128 160
  test8320_block_7
  (interval_append test8320 128 144 160
  test8320_block_8
  test8320_block_9))))
  (interval_append test8320 160 240 320
  (interval_append test8320 160 192 240
  (interval_append test8320 160 176 192
  test8320_block_10
  test8320_block_11)
  (interval_append test8320 192 208 240
  test8320_block_12
  (interval_append test8320 208 224 240
  test8320_block_13
  test8320_block_14)))
  (interval_append test8320 240 272 320
  (interval_append test8320 240 256 272
  test8320_block_15
  test8320_block_16)
  (interval_append test8320 272 288 320
  test8320_block_17
  (interval_append test8320 288 304 320
  test8320_block_18
  test8320_block_19)))))
  (interval_append test8320 320 480 640
  (interval_append test8320 320 400 480
  (interval_append test8320 320 352 400
  (interval_append test8320 320 336 352
  test8320_block_20
  test8320_block_21)
  (interval_append test8320 352 368 400
  test8320_block_22
  (interval_append test8320 368 384 400
  test8320_block_23
  test8320_block_24)))
  (interval_append test8320 400 432 480
  (interval_append test8320 400 416 432
  test8320_block_25
  test8320_block_26)
  (interval_append test8320 432 448 480
  test8320_block_27
  (interval_append test8320 448 464 480
  test8320_block_28
  test8320_block_29))))
  (interval_append test8320 480 560 640
  (interval_append test8320 480 512 560
  (interval_append test8320 480 496 512
  test8320_block_30
  test8320_block_31)
  (interval_append test8320 512 528 560
  test8320_block_32
  (interval_append test8320 528 544 560
  test8320_block_33
  test8320_block_34)))
  (interval_append test8320 560 592 640
  (interval_append test8320 560 576 592
  test8320_block_35
  test8320_block_36)
  (interval_append test8320 592 608 640
  test8320_block_37
  (interval_append test8320 608 624 640
  test8320_block_38
  test8320_block_39))))))
cert_nodeInterval_3 8320 8960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 8960
cert_test_block_3 8960 0 0 16 16
cert_test_block_3 8960 1 16 32 16
cert_test_block_3 8960 2 32 48 16
cert_test_block_3 8960 3 48 64 16
cert_test_block_3 8960 4 64 80 16
cert_test_block_3 8960 5 80 96 16
cert_test_block_3 8960 6 96 112 16
cert_test_block_3 8960 7 112 128 16
cert_test_block_3 8960 8 128 144 16
cert_test_block_3 8960 9 144 160 16
cert_test_block_3 8960 10 160 176 16
cert_test_block_3 8960 11 176 192 16
cert_test_block_3 8960 12 192 208 16
cert_test_block_3 8960 13 208 224 16
cert_test_block_3 8960 14 224 240 16
cert_test_block_3 8960 15 240 256 16
cert_test_block_3 8960 16 256 272 16
cert_test_block_3 8960 17 272 288 16
cert_test_block_3 8960 18 288 304 16
cert_test_block_3 8960 19 304 320 16
cert_test_block_3 8960 20 320 336 16
cert_test_block_3 8960 21 336 352 16
cert_test_block_3 8960 22 352 368 16
cert_test_block_3 8960 23 368 384 16
cert_test_block_3 8960 24 384 400 16
cert_test_block_3 8960 25 400 416 16
cert_test_block_3 8960 26 416 432 16
cert_test_block_3 8960 27 432 448 16
cert_test_block_3 8960 28 448 464 16
cert_test_block_3 8960 29 464 480 16
cert_test_block_3 8960 30 480 496 16
cert_test_block_3 8960 31 496 512 16
cert_test_block_3 8960 32 512 528 16
cert_test_block_3 8960 33 528 544 16
cert_test_block_3 8960 34 544 560 16
cert_test_block_3 8960 35 560 576 16
cert_test_block_3 8960 36 576 592 16
cert_test_block_3 8960 37 592 608 16
cert_test_block_3 8960 38 608 624 16
cert_test_block_3 8960 39 624 640 16
theorem test8960_complete : Interval test8960 0 640 :=
  (interval_append test8960 0 320 640
  (interval_append test8960 0 160 320
  (interval_append test8960 0 80 160
  (interval_append test8960 0 32 80
  (interval_append test8960 0 16 32
  test8960_block_0
  test8960_block_1)
  (interval_append test8960 32 48 80
  test8960_block_2
  (interval_append test8960 48 64 80
  test8960_block_3
  test8960_block_4)))
  (interval_append test8960 80 112 160
  (interval_append test8960 80 96 112
  test8960_block_5
  test8960_block_6)
  (interval_append test8960 112 128 160
  test8960_block_7
  (interval_append test8960 128 144 160
  test8960_block_8
  test8960_block_9))))
  (interval_append test8960 160 240 320
  (interval_append test8960 160 192 240
  (interval_append test8960 160 176 192
  test8960_block_10
  test8960_block_11)
  (interval_append test8960 192 208 240
  test8960_block_12
  (interval_append test8960 208 224 240
  test8960_block_13
  test8960_block_14)))
  (interval_append test8960 240 272 320
  (interval_append test8960 240 256 272
  test8960_block_15
  test8960_block_16)
  (interval_append test8960 272 288 320
  test8960_block_17
  (interval_append test8960 288 304 320
  test8960_block_18
  test8960_block_19)))))
  (interval_append test8960 320 480 640
  (interval_append test8960 320 400 480
  (interval_append test8960 320 352 400
  (interval_append test8960 320 336 352
  test8960_block_20
  test8960_block_21)
  (interval_append test8960 352 368 400
  test8960_block_22
  (interval_append test8960 368 384 400
  test8960_block_23
  test8960_block_24)))
  (interval_append test8960 400 432 480
  (interval_append test8960 400 416 432
  test8960_block_25
  test8960_block_26)
  (interval_append test8960 432 448 480
  test8960_block_27
  (interval_append test8960 448 464 480
  test8960_block_28
  test8960_block_29))))
  (interval_append test8960 480 560 640
  (interval_append test8960 480 512 560
  (interval_append test8960 480 496 512
  test8960_block_30
  test8960_block_31)
  (interval_append test8960 512 528 560
  test8960_block_32
  (interval_append test8960 528 544 560
  test8960_block_33
  test8960_block_34)))
  (interval_append test8960 560 592 640
  (interval_append test8960 560 576 592
  test8960_block_35
  test8960_block_36)
  (interval_append test8960 592 608 640
  test8960_block_37
  (interval_append test8960 608 624 640
  test8960_block_38
  test8960_block_39))))))
cert_nodeInterval_3 8960 9600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 9600
cert_test_block_3 9600 0 0 16 16
cert_test_block_3 9600 1 16 32 16
cert_test_block_3 9600 2 32 48 16
cert_test_block_3 9600 3 48 64 16
cert_test_block_3 9600 4 64 80 16
cert_test_block_3 9600 5 80 96 16
cert_test_block_3 9600 6 96 112 16
cert_test_block_3 9600 7 112 128 16
cert_test_block_3 9600 8 128 144 16
cert_test_block_3 9600 9 144 160 16
cert_test_block_3 9600 10 160 176 16
cert_test_block_3 9600 11 176 192 16
cert_test_block_3 9600 12 192 208 16
cert_test_block_3 9600 13 208 224 16
cert_test_block_3 9600 14 224 240 16
cert_test_block_3 9600 15 240 256 16
cert_test_block_3 9600 16 256 272 16
cert_test_block_3 9600 17 272 288 16
cert_test_block_3 9600 18 288 304 16
cert_test_block_3 9600 19 304 320 16
cert_test_block_3 9600 20 320 336 16
cert_test_block_3 9600 21 336 352 16
cert_test_block_3 9600 22 352 368 16
cert_test_block_3 9600 23 368 384 16
cert_test_block_3 9600 24 384 400 16
cert_test_block_3 9600 25 400 416 16
cert_test_block_3 9600 26 416 432 16
cert_test_block_3 9600 27 432 448 16
cert_test_block_3 9600 28 448 464 16
cert_test_block_3 9600 29 464 480 16
cert_test_block_3 9600 30 480 496 16
cert_test_block_3 9600 31 496 512 16
cert_test_block_3 9600 32 512 528 16
cert_test_block_3 9600 33 528 544 16
cert_test_block_3 9600 34 544 560 16
cert_test_block_3 9600 35 560 576 16
cert_test_block_3 9600 36 576 592 16
cert_test_block_3 9600 37 592 608 16
cert_test_block_3 9600 38 608 624 16
cert_test_block_3 9600 39 624 640 16
theorem test9600_complete : Interval test9600 0 640 :=
  (interval_append test9600 0 320 640
  (interval_append test9600 0 160 320
  (interval_append test9600 0 80 160
  (interval_append test9600 0 32 80
  (interval_append test9600 0 16 32
  test9600_block_0
  test9600_block_1)
  (interval_append test9600 32 48 80
  test9600_block_2
  (interval_append test9600 48 64 80
  test9600_block_3
  test9600_block_4)))
  (interval_append test9600 80 112 160
  (interval_append test9600 80 96 112
  test9600_block_5
  test9600_block_6)
  (interval_append test9600 112 128 160
  test9600_block_7
  (interval_append test9600 128 144 160
  test9600_block_8
  test9600_block_9))))
  (interval_append test9600 160 240 320
  (interval_append test9600 160 192 240
  (interval_append test9600 160 176 192
  test9600_block_10
  test9600_block_11)
  (interval_append test9600 192 208 240
  test9600_block_12
  (interval_append test9600 208 224 240
  test9600_block_13
  test9600_block_14)))
  (interval_append test9600 240 272 320
  (interval_append test9600 240 256 272
  test9600_block_15
  test9600_block_16)
  (interval_append test9600 272 288 320
  test9600_block_17
  (interval_append test9600 288 304 320
  test9600_block_18
  test9600_block_19)))))
  (interval_append test9600 320 480 640
  (interval_append test9600 320 400 480
  (interval_append test9600 320 352 400
  (interval_append test9600 320 336 352
  test9600_block_20
  test9600_block_21)
  (interval_append test9600 352 368 400
  test9600_block_22
  (interval_append test9600 368 384 400
  test9600_block_23
  test9600_block_24)))
  (interval_append test9600 400 432 480
  (interval_append test9600 400 416 432
  test9600_block_25
  test9600_block_26)
  (interval_append test9600 432 448 480
  test9600_block_27
  (interval_append test9600 448 464 480
  test9600_block_28
  test9600_block_29))))
  (interval_append test9600 480 560 640
  (interval_append test9600 480 512 560
  (interval_append test9600 480 496 512
  test9600_block_30
  test9600_block_31)
  (interval_append test9600 512 528 560
  test9600_block_32
  (interval_append test9600 528 544 560
  test9600_block_33
  test9600_block_34)))
  (interval_append test9600 560 592 640
  (interval_append test9600 560 576 592
  test9600_block_35
  test9600_block_36)
  (interval_append test9600 592 608 640
  test9600_block_37
  (interval_append test9600 608 624 640
  test9600_block_38
  test9600_block_39))))))
cert_nodeInterval_3 9600 10240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 10240
cert_test_block_3 10240 0 0 16 16
cert_test_block_3 10240 1 16 32 16
cert_test_block_3 10240 2 32 48 16
cert_test_block_3 10240 3 48 64 16
cert_test_block_3 10240 4 64 80 16
cert_test_block_3 10240 5 80 96 16
cert_test_block_3 10240 6 96 112 16
cert_test_block_3 10240 7 112 128 16
cert_test_block_3 10240 8 128 144 16
cert_test_block_3 10240 9 144 160 16
cert_test_block_3 10240 10 160 176 16
cert_test_block_3 10240 11 176 192 16
cert_test_block_3 10240 12 192 208 16
cert_test_block_3 10240 13 208 224 16
cert_test_block_3 10240 14 224 240 16
cert_test_block_3 10240 15 240 256 16
cert_test_block_3 10240 16 256 272 16
cert_test_block_3 10240 17 272 288 16
cert_test_block_3 10240 18 288 304 16
cert_test_block_3 10240 19 304 320 16
cert_test_block_3 10240 20 320 336 16
cert_test_block_3 10240 21 336 352 16
cert_test_block_3 10240 22 352 368 16
cert_test_block_3 10240 23 368 384 16
cert_test_block_3 10240 24 384 400 16
cert_test_block_3 10240 25 400 416 16
cert_test_block_3 10240 26 416 432 16
cert_test_block_3 10240 27 432 448 16
cert_test_block_3 10240 28 448 464 16
cert_test_block_3 10240 29 464 480 16
cert_test_block_3 10240 30 480 496 16
cert_test_block_3 10240 31 496 512 16
cert_test_block_3 10240 32 512 528 16
cert_test_block_3 10240 33 528 544 16
cert_test_block_3 10240 34 544 560 16
cert_test_block_3 10240 35 560 576 16
cert_test_block_3 10240 36 576 592 16
cert_test_block_3 10240 37 592 608 16
cert_test_block_3 10240 38 608 624 16
cert_test_block_3 10240 39 624 640 16
theorem test10240_complete : Interval test10240 0 640 :=
  (interval_append test10240 0 320 640
  (interval_append test10240 0 160 320
  (interval_append test10240 0 80 160
  (interval_append test10240 0 32 80
  (interval_append test10240 0 16 32
  test10240_block_0
  test10240_block_1)
  (interval_append test10240 32 48 80
  test10240_block_2
  (interval_append test10240 48 64 80
  test10240_block_3
  test10240_block_4)))
  (interval_append test10240 80 112 160
  (interval_append test10240 80 96 112
  test10240_block_5
  test10240_block_6)
  (interval_append test10240 112 128 160
  test10240_block_7
  (interval_append test10240 128 144 160
  test10240_block_8
  test10240_block_9))))
  (interval_append test10240 160 240 320
  (interval_append test10240 160 192 240
  (interval_append test10240 160 176 192
  test10240_block_10
  test10240_block_11)
  (interval_append test10240 192 208 240
  test10240_block_12
  (interval_append test10240 208 224 240
  test10240_block_13
  test10240_block_14)))
  (interval_append test10240 240 272 320
  (interval_append test10240 240 256 272
  test10240_block_15
  test10240_block_16)
  (interval_append test10240 272 288 320
  test10240_block_17
  (interval_append test10240 288 304 320
  test10240_block_18
  test10240_block_19)))))
  (interval_append test10240 320 480 640
  (interval_append test10240 320 400 480
  (interval_append test10240 320 352 400
  (interval_append test10240 320 336 352
  test10240_block_20
  test10240_block_21)
  (interval_append test10240 352 368 400
  test10240_block_22
  (interval_append test10240 368 384 400
  test10240_block_23
  test10240_block_24)))
  (interval_append test10240 400 432 480
  (interval_append test10240 400 416 432
  test10240_block_25
  test10240_block_26)
  (interval_append test10240 432 448 480
  test10240_block_27
  (interval_append test10240 448 464 480
  test10240_block_28
  test10240_block_29))))
  (interval_append test10240 480 560 640
  (interval_append test10240 480 512 560
  (interval_append test10240 480 496 512
  test10240_block_30
  test10240_block_31)
  (interval_append test10240 512 528 560
  test10240_block_32
  (interval_append test10240 528 544 560
  test10240_block_33
  test10240_block_34)))
  (interval_append test10240 560 592 640
  (interval_append test10240 560 576 592
  test10240_block_35
  test10240_block_36)
  (interval_append test10240 592 608 640
  test10240_block_37
  (interval_append test10240 608 624 640
  test10240_block_38
  test10240_block_39))))))
cert_nodeInterval_3 10240 10880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 10880
cert_test_block_3 10880 0 0 16 16
cert_test_block_3 10880 1 16 32 16
cert_test_block_3 10880 2 32 48 16
cert_test_block_3 10880 3 48 64 16
cert_test_block_3 10880 4 64 80 16
cert_test_block_3 10880 5 80 96 16
cert_test_block_3 10880 6 96 112 16
cert_test_block_3 10880 7 112 128 16
cert_test_block_3 10880 8 128 144 16
cert_test_block_3 10880 9 144 160 16
cert_test_block_3 10880 10 160 176 16
cert_test_block_3 10880 11 176 192 16
cert_test_block_3 10880 12 192 208 16
cert_test_block_3 10880 13 208 224 16
cert_test_block_3 10880 14 224 240 16
cert_test_block_3 10880 15 240 256 16
cert_test_block_3 10880 16 256 272 16
cert_test_block_3 10880 17 272 288 16
cert_test_block_3 10880 18 288 304 16
cert_test_block_3 10880 19 304 320 16
cert_test_block_3 10880 20 320 336 16
cert_test_block_3 10880 21 336 352 16
cert_test_block_3 10880 22 352 368 16
cert_test_block_3 10880 23 368 384 16
cert_test_block_3 10880 24 384 400 16
cert_test_block_3 10880 25 400 416 16
cert_test_block_3 10880 26 416 432 16
cert_test_block_3 10880 27 432 448 16
cert_test_block_3 10880 28 448 464 16
cert_test_block_3 10880 29 464 480 16
cert_test_block_3 10880 30 480 496 16
cert_test_block_3 10880 31 496 512 16
cert_test_block_3 10880 32 512 528 16
cert_test_block_3 10880 33 528 544 16
cert_test_block_3 10880 34 544 560 16
cert_test_block_3 10880 35 560 576 16
cert_test_block_3 10880 36 576 592 16
cert_test_block_3 10880 37 592 608 16
cert_test_block_3 10880 38 608 624 16
cert_test_block_3 10880 39 624 640 16
theorem test10880_complete : Interval test10880 0 640 :=
  (interval_append test10880 0 320 640
  (interval_append test10880 0 160 320
  (interval_append test10880 0 80 160
  (interval_append test10880 0 32 80
  (interval_append test10880 0 16 32
  test10880_block_0
  test10880_block_1)
  (interval_append test10880 32 48 80
  test10880_block_2
  (interval_append test10880 48 64 80
  test10880_block_3
  test10880_block_4)))
  (interval_append test10880 80 112 160
  (interval_append test10880 80 96 112
  test10880_block_5
  test10880_block_6)
  (interval_append test10880 112 128 160
  test10880_block_7
  (interval_append test10880 128 144 160
  test10880_block_8
  test10880_block_9))))
  (interval_append test10880 160 240 320
  (interval_append test10880 160 192 240
  (interval_append test10880 160 176 192
  test10880_block_10
  test10880_block_11)
  (interval_append test10880 192 208 240
  test10880_block_12
  (interval_append test10880 208 224 240
  test10880_block_13
  test10880_block_14)))
  (interval_append test10880 240 272 320
  (interval_append test10880 240 256 272
  test10880_block_15
  test10880_block_16)
  (interval_append test10880 272 288 320
  test10880_block_17
  (interval_append test10880 288 304 320
  test10880_block_18
  test10880_block_19)))))
  (interval_append test10880 320 480 640
  (interval_append test10880 320 400 480
  (interval_append test10880 320 352 400
  (interval_append test10880 320 336 352
  test10880_block_20
  test10880_block_21)
  (interval_append test10880 352 368 400
  test10880_block_22
  (interval_append test10880 368 384 400
  test10880_block_23
  test10880_block_24)))
  (interval_append test10880 400 432 480
  (interval_append test10880 400 416 432
  test10880_block_25
  test10880_block_26)
  (interval_append test10880 432 448 480
  test10880_block_27
  (interval_append test10880 448 464 480
  test10880_block_28
  test10880_block_29))))
  (interval_append test10880 480 560 640
  (interval_append test10880 480 512 560
  (interval_append test10880 480 496 512
  test10880_block_30
  test10880_block_31)
  (interval_append test10880 512 528 560
  test10880_block_32
  (interval_append test10880 528 544 560
  test10880_block_33
  test10880_block_34)))
  (interval_append test10880 560 592 640
  (interval_append test10880 560 576 592
  test10880_block_35
  test10880_block_36)
  (interval_append test10880 592 608 640
  test10880_block_37
  (interval_append test10880 608 624 640
  test10880_block_38
  test10880_block_39))))))
cert_nodeInterval_3 10880 11520
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 11520
cert_test_block_3 11520 0 0 16 16
cert_test_block_3 11520 1 16 32 16
cert_test_block_3 11520 2 32 48 16
cert_test_block_3 11520 3 48 64 16
cert_test_block_3 11520 4 64 80 16
cert_test_block_3 11520 5 80 96 16
cert_test_block_3 11520 6 96 112 16
cert_test_block_3 11520 7 112 128 16
cert_test_block_3 11520 8 128 144 16
cert_test_block_3 11520 9 144 160 16
cert_test_block_3 11520 10 160 176 16
cert_test_block_3 11520 11 176 192 16
cert_test_block_3 11520 12 192 208 16
cert_test_block_3 11520 13 208 224 16
cert_test_block_3 11520 14 224 240 16
cert_test_block_3 11520 15 240 256 16
cert_test_block_3 11520 16 256 272 16
cert_test_block_3 11520 17 272 288 16
cert_test_block_3 11520 18 288 304 16
cert_test_block_3 11520 19 304 320 16
cert_test_block_3 11520 20 320 336 16
cert_test_block_3 11520 21 336 352 16
cert_test_block_3 11520 22 352 368 16
cert_test_block_3 11520 23 368 384 16
cert_test_block_3 11520 24 384 400 16
cert_test_block_3 11520 25 400 416 16
cert_test_block_3 11520 26 416 432 16
cert_test_block_3 11520 27 432 448 16
cert_test_block_3 11520 28 448 464 16
cert_test_block_3 11520 29 464 480 16
cert_test_block_3 11520 30 480 496 16
cert_test_block_3 11520 31 496 512 16
cert_test_block_3 11520 32 512 528 16
cert_test_block_3 11520 33 528 544 16
cert_test_block_3 11520 34 544 560 16
cert_test_block_3 11520 35 560 576 16
cert_test_block_3 11520 36 576 578 2
theorem test11520_complete : Interval test11520 0 578 :=
  (interval_append test11520 0 288 578
  (interval_append test11520 0 144 288
  (interval_append test11520 0 64 144
  (interval_append test11520 0 32 64
  (interval_append test11520 0 16 32
  test11520_block_0
  test11520_block_1)
  (interval_append test11520 32 48 64
  test11520_block_2
  test11520_block_3))
  (interval_append test11520 64 96 144
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)
  (interval_append test11520 96 112 144
  test11520_block_6
  (interval_append test11520 112 128 144
  test11520_block_7
  test11520_block_8))))
  (interval_append test11520 144 208 288
  (interval_append test11520 144 176 208
  (interval_append test11520 144 160 176
  test11520_block_9
  test11520_block_10)
  (interval_append test11520 176 192 208
  test11520_block_11
  test11520_block_12))
  (interval_append test11520 208 240 288
  (interval_append test11520 208 224 240
  test11520_block_13
  test11520_block_14)
  (interval_append test11520 240 256 288
  test11520_block_15
  (interval_append test11520 256 272 288
  test11520_block_16
  test11520_block_17)))))
  (interval_append test11520 288 432 578
  (interval_append test11520 288 352 432
  (interval_append test11520 288 320 352
  (interval_append test11520 288 304 320
  test11520_block_18
  test11520_block_19)
  (interval_append test11520 320 336 352
  test11520_block_20
  test11520_block_21))
  (interval_append test11520 352 384 432
  (interval_append test11520 352 368 384
  test11520_block_22
  test11520_block_23)
  (interval_append test11520 384 400 432
  test11520_block_24
  (interval_append test11520 400 416 432
  test11520_block_25
  test11520_block_26))))
  (interval_append test11520 432 512 578
  (interval_append test11520 432 464 512
  (interval_append test11520 432 448 464
  test11520_block_27
  test11520_block_28)
  (interval_append test11520 464 480 512
  test11520_block_29
  (interval_append test11520 480 496 512
  test11520_block_30
  test11520_block_31)))
  (interval_append test11520 512 544 578
  (interval_append test11520 512 528 544
  test11520_block_32
  test11520_block_33)
  (interval_append test11520 544 560 578
  test11520_block_34
  (interval_append test11520 560 576 578
  test11520_block_35
  test11520_block_36))))))
cert_nodeInterval_3 11520 12098
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
end
end
