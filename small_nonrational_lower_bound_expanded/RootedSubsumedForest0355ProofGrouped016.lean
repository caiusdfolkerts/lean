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
cert_test_11 121600
cert_test_block_3 121600 0 0 16 16
cert_test_block_3 121600 1 16 32 16
cert_test_block_3 121600 2 32 48 16
cert_test_block_3 121600 3 48 64 16
cert_test_block_3 121600 4 64 80 16
cert_test_block_3 121600 5 80 96 16
cert_test_block_3 121600 6 96 112 16
cert_test_block_3 121600 7 112 128 16
cert_test_block_3 121600 8 128 144 16
cert_test_block_3 121600 9 144 160 16
cert_test_block_3 121600 10 160 176 16
cert_test_block_3 121600 11 176 192 16
cert_test_block_3 121600 12 192 208 16
cert_test_block_3 121600 13 208 224 16
cert_test_block_3 121600 14 224 240 16
cert_test_block_3 121600 15 240 256 16
cert_test_block_3 121600 16 256 272 16
cert_test_block_3 121600 17 272 288 16
cert_test_block_3 121600 18 288 304 16
cert_test_block_3 121600 19 304 320 16
cert_test_block_3 121600 20 320 336 16
cert_test_block_3 121600 21 336 352 16
cert_test_block_3 121600 22 352 368 16
cert_test_block_3 121600 23 368 384 16
cert_test_block_3 121600 24 384 400 16
cert_test_block_3 121600 25 400 416 16
cert_test_block_3 121600 26 416 432 16
cert_test_block_3 121600 27 432 448 16
cert_test_block_3 121600 28 448 464 16
cert_test_block_3 121600 29 464 480 16
cert_test_block_3 121600 30 480 496 16
cert_test_block_3 121600 31 496 512 16
cert_test_block_3 121600 32 512 528 16
cert_test_block_3 121600 33 528 544 16
cert_test_block_3 121600 34 544 560 16
cert_test_block_3 121600 35 560 576 16
cert_test_block_3 121600 36 576 592 16
cert_test_block_3 121600 37 592 608 16
cert_test_block_3 121600 38 608 624 16
cert_test_block_3 121600 39 624 640 16
theorem test121600_complete : Interval test121600 0 640 :=
  (interval_append test121600 0 320 640
  (interval_append test121600 0 160 320
  (interval_append test121600 0 80 160
  (interval_append test121600 0 32 80
  (interval_append test121600 0 16 32
  test121600_block_0
  test121600_block_1)
  (interval_append test121600 32 48 80
  test121600_block_2
  (interval_append test121600 48 64 80
  test121600_block_3
  test121600_block_4)))
  (interval_append test121600 80 112 160
  (interval_append test121600 80 96 112
  test121600_block_5
  test121600_block_6)
  (interval_append test121600 112 128 160
  test121600_block_7
  (interval_append test121600 128 144 160
  test121600_block_8
  test121600_block_9))))
  (interval_append test121600 160 240 320
  (interval_append test121600 160 192 240
  (interval_append test121600 160 176 192
  test121600_block_10
  test121600_block_11)
  (interval_append test121600 192 208 240
  test121600_block_12
  (interval_append test121600 208 224 240
  test121600_block_13
  test121600_block_14)))
  (interval_append test121600 240 272 320
  (interval_append test121600 240 256 272
  test121600_block_15
  test121600_block_16)
  (interval_append test121600 272 288 320
  test121600_block_17
  (interval_append test121600 288 304 320
  test121600_block_18
  test121600_block_19)))))
  (interval_append test121600 320 480 640
  (interval_append test121600 320 400 480
  (interval_append test121600 320 352 400
  (interval_append test121600 320 336 352
  test121600_block_20
  test121600_block_21)
  (interval_append test121600 352 368 400
  test121600_block_22
  (interval_append test121600 368 384 400
  test121600_block_23
  test121600_block_24)))
  (interval_append test121600 400 432 480
  (interval_append test121600 400 416 432
  test121600_block_25
  test121600_block_26)
  (interval_append test121600 432 448 480
  test121600_block_27
  (interval_append test121600 448 464 480
  test121600_block_28
  test121600_block_29))))
  (interval_append test121600 480 560 640
  (interval_append test121600 480 512 560
  (interval_append test121600 480 496 512
  test121600_block_30
  test121600_block_31)
  (interval_append test121600 512 528 560
  test121600_block_32
  (interval_append test121600 528 544 560
  test121600_block_33
  test121600_block_34)))
  (interval_append test121600 560 592 640
  (interval_append test121600 560 576 592
  test121600_block_35
  test121600_block_36)
  (interval_append test121600 592 608 640
  test121600_block_37
  (interval_append test121600 608 624 640
  test121600_block_38
  test121600_block_39))))))
cert_nodeInterval_3 121600 122240
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
cert_test_11 122240
cert_test_block_3 122240 0 0 16 16
cert_test_block_3 122240 1 16 32 16
cert_test_block_3 122240 2 32 48 16
cert_test_block_3 122240 3 48 64 16
cert_test_block_3 122240 4 64 80 16
cert_test_block_3 122240 5 80 96 16
cert_test_block_3 122240 6 96 112 16
cert_test_block_3 122240 7 112 128 16
cert_test_block_3 122240 8 128 144 16
cert_test_block_3 122240 9 144 160 16
cert_test_block_3 122240 10 160 176 16
cert_test_block_3 122240 11 176 192 16
cert_test_block_3 122240 12 192 208 16
cert_test_block_3 122240 13 208 224 16
cert_test_block_3 122240 14 224 240 16
cert_test_block_3 122240 15 240 256 16
cert_test_block_3 122240 16 256 272 16
cert_test_block_3 122240 17 272 288 16
cert_test_block_3 122240 18 288 304 16
cert_test_block_3 122240 19 304 320 16
cert_test_block_3 122240 20 320 336 16
cert_test_block_3 122240 21 336 352 16
cert_test_block_3 122240 22 352 368 16
cert_test_block_3 122240 23 368 384 16
cert_test_block_3 122240 24 384 400 16
cert_test_block_3 122240 25 400 416 16
cert_test_block_3 122240 26 416 432 16
cert_test_block_3 122240 27 432 448 16
cert_test_block_3 122240 28 448 464 16
cert_test_block_3 122240 29 464 480 16
cert_test_block_3 122240 30 480 496 16
cert_test_block_3 122240 31 496 512 16
cert_test_block_3 122240 32 512 528 16
cert_test_block_3 122240 33 528 544 16
cert_test_block_3 122240 34 544 560 16
cert_test_block_3 122240 35 560 576 16
cert_test_block_3 122240 36 576 592 16
cert_test_block_3 122240 37 592 608 16
cert_test_block_3 122240 38 608 624 16
cert_test_block_3 122240 39 624 640 16
theorem test122240_complete : Interval test122240 0 640 :=
  (interval_append test122240 0 320 640
  (interval_append test122240 0 160 320
  (interval_append test122240 0 80 160
  (interval_append test122240 0 32 80
  (interval_append test122240 0 16 32
  test122240_block_0
  test122240_block_1)
  (interval_append test122240 32 48 80
  test122240_block_2
  (interval_append test122240 48 64 80
  test122240_block_3
  test122240_block_4)))
  (interval_append test122240 80 112 160
  (interval_append test122240 80 96 112
  test122240_block_5
  test122240_block_6)
  (interval_append test122240 112 128 160
  test122240_block_7
  (interval_append test122240 128 144 160
  test122240_block_8
  test122240_block_9))))
  (interval_append test122240 160 240 320
  (interval_append test122240 160 192 240
  (interval_append test122240 160 176 192
  test122240_block_10
  test122240_block_11)
  (interval_append test122240 192 208 240
  test122240_block_12
  (interval_append test122240 208 224 240
  test122240_block_13
  test122240_block_14)))
  (interval_append test122240 240 272 320
  (interval_append test122240 240 256 272
  test122240_block_15
  test122240_block_16)
  (interval_append test122240 272 288 320
  test122240_block_17
  (interval_append test122240 288 304 320
  test122240_block_18
  test122240_block_19)))))
  (interval_append test122240 320 480 640
  (interval_append test122240 320 400 480
  (interval_append test122240 320 352 400
  (interval_append test122240 320 336 352
  test122240_block_20
  test122240_block_21)
  (interval_append test122240 352 368 400
  test122240_block_22
  (interval_append test122240 368 384 400
  test122240_block_23
  test122240_block_24)))
  (interval_append test122240 400 432 480
  (interval_append test122240 400 416 432
  test122240_block_25
  test122240_block_26)
  (interval_append test122240 432 448 480
  test122240_block_27
  (interval_append test122240 448 464 480
  test122240_block_28
  test122240_block_29))))
  (interval_append test122240 480 560 640
  (interval_append test122240 480 512 560
  (interval_append test122240 480 496 512
  test122240_block_30
  test122240_block_31)
  (interval_append test122240 512 528 560
  test122240_block_32
  (interval_append test122240 528 544 560
  test122240_block_33
  test122240_block_34)))
  (interval_append test122240 560 592 640
  (interval_append test122240 560 576 592
  test122240_block_35
  test122240_block_36)
  (interval_append test122240 592 608 640
  test122240_block_37
  (interval_append test122240 608 624 640
  test122240_block_38
  test122240_block_39))))))
cert_nodeInterval_3 122240 122880
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
cert_test_11 122880
cert_test_block_3 122880 0 0 16 16
cert_test_block_3 122880 1 16 32 16
cert_test_block_3 122880 2 32 48 16
cert_test_block_3 122880 3 48 64 16
cert_test_block_3 122880 4 64 80 16
cert_test_block_3 122880 5 80 96 16
cert_test_block_3 122880 6 96 112 16
cert_test_block_3 122880 7 112 128 16
cert_test_block_3 122880 8 128 144 16
cert_test_block_3 122880 9 144 160 16
cert_test_block_3 122880 10 160 176 16
cert_test_block_3 122880 11 176 192 16
cert_test_block_3 122880 12 192 208 16
cert_test_block_3 122880 13 208 224 16
cert_test_block_3 122880 14 224 240 16
cert_test_block_3 122880 15 240 256 16
cert_test_block_3 122880 16 256 272 16
cert_test_block_3 122880 17 272 288 16
cert_test_block_3 122880 18 288 304 16
cert_test_block_3 122880 19 304 320 16
cert_test_block_3 122880 20 320 336 16
cert_test_block_3 122880 21 336 352 16
cert_test_block_3 122880 22 352 368 16
cert_test_block_3 122880 23 368 384 16
cert_test_block_3 122880 24 384 400 16
cert_test_block_3 122880 25 400 416 16
cert_test_block_3 122880 26 416 432 16
cert_test_block_3 122880 27 432 448 16
cert_test_block_3 122880 28 448 464 16
cert_test_block_3 122880 29 464 480 16
cert_test_block_3 122880 30 480 496 16
cert_test_block_3 122880 31 496 512 16
cert_test_block_3 122880 32 512 528 16
cert_test_block_3 122880 33 528 544 16
cert_test_block_3 122880 34 544 560 16
cert_test_block_3 122880 35 560 576 16
cert_test_block_3 122880 36 576 592 16
cert_test_block_3 122880 37 592 608 16
cert_test_block_3 122880 38 608 624 16
cert_test_block_3 122880 39 624 640 16
theorem test122880_complete : Interval test122880 0 640 :=
  (interval_append test122880 0 320 640
  (interval_append test122880 0 160 320
  (interval_append test122880 0 80 160
  (interval_append test122880 0 32 80
  (interval_append test122880 0 16 32
  test122880_block_0
  test122880_block_1)
  (interval_append test122880 32 48 80
  test122880_block_2
  (interval_append test122880 48 64 80
  test122880_block_3
  test122880_block_4)))
  (interval_append test122880 80 112 160
  (interval_append test122880 80 96 112
  test122880_block_5
  test122880_block_6)
  (interval_append test122880 112 128 160
  test122880_block_7
  (interval_append test122880 128 144 160
  test122880_block_8
  test122880_block_9))))
  (interval_append test122880 160 240 320
  (interval_append test122880 160 192 240
  (interval_append test122880 160 176 192
  test122880_block_10
  test122880_block_11)
  (interval_append test122880 192 208 240
  test122880_block_12
  (interval_append test122880 208 224 240
  test122880_block_13
  test122880_block_14)))
  (interval_append test122880 240 272 320
  (interval_append test122880 240 256 272
  test122880_block_15
  test122880_block_16)
  (interval_append test122880 272 288 320
  test122880_block_17
  (interval_append test122880 288 304 320
  test122880_block_18
  test122880_block_19)))))
  (interval_append test122880 320 480 640
  (interval_append test122880 320 400 480
  (interval_append test122880 320 352 400
  (interval_append test122880 320 336 352
  test122880_block_20
  test122880_block_21)
  (interval_append test122880 352 368 400
  test122880_block_22
  (interval_append test122880 368 384 400
  test122880_block_23
  test122880_block_24)))
  (interval_append test122880 400 432 480
  (interval_append test122880 400 416 432
  test122880_block_25
  test122880_block_26)
  (interval_append test122880 432 448 480
  test122880_block_27
  (interval_append test122880 448 464 480
  test122880_block_28
  test122880_block_29))))
  (interval_append test122880 480 560 640
  (interval_append test122880 480 512 560
  (interval_append test122880 480 496 512
  test122880_block_30
  test122880_block_31)
  (interval_append test122880 512 528 560
  test122880_block_32
  (interval_append test122880 528 544 560
  test122880_block_33
  test122880_block_34)))
  (interval_append test122880 560 592 640
  (interval_append test122880 560 576 592
  test122880_block_35
  test122880_block_36)
  (interval_append test122880 592 608 640
  test122880_block_37
  (interval_append test122880 608 624 640
  test122880_block_38
  test122880_block_39))))))
cert_nodeInterval_3 122880 123520
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
cert_test_11 123520
cert_test_block_3 123520 0 0 16 16
cert_test_block_3 123520 1 16 32 16
cert_test_block_3 123520 2 32 48 16
cert_test_block_3 123520 3 48 64 16
cert_test_block_3 123520 4 64 80 16
cert_test_block_3 123520 5 80 96 16
cert_test_block_3 123520 6 96 112 16
cert_test_block_3 123520 7 112 128 16
cert_test_block_3 123520 8 128 144 16
cert_test_block_3 123520 9 144 160 16
cert_test_block_3 123520 10 160 176 16
cert_test_block_3 123520 11 176 192 16
cert_test_block_3 123520 12 192 208 16
cert_test_block_3 123520 13 208 224 16
cert_test_block_3 123520 14 224 240 16
cert_test_block_3 123520 15 240 256 16
cert_test_block_3 123520 16 256 272 16
cert_test_block_3 123520 17 272 288 16
cert_test_block_3 123520 18 288 304 16
cert_test_block_3 123520 19 304 320 16
cert_test_block_3 123520 20 320 336 16
cert_test_block_3 123520 21 336 352 16
cert_test_block_3 123520 22 352 368 16
cert_test_block_3 123520 23 368 384 16
cert_test_block_3 123520 24 384 400 16
cert_test_block_3 123520 25 400 416 16
cert_test_block_3 123520 26 416 432 16
cert_test_block_3 123520 27 432 448 16
cert_test_block_3 123520 28 448 464 16
cert_test_block_3 123520 29 464 480 16
cert_test_block_3 123520 30 480 496 16
cert_test_block_3 123520 31 496 512 16
cert_test_block_3 123520 32 512 528 16
cert_test_block_3 123520 33 528 544 16
cert_test_block_3 123520 34 544 560 16
cert_test_block_3 123520 35 560 576 16
cert_test_block_3 123520 36 576 592 16
cert_test_block_3 123520 37 592 608 16
cert_test_block_3 123520 38 608 624 16
cert_test_block_3 123520 39 624 640 16
theorem test123520_complete : Interval test123520 0 640 :=
  (interval_append test123520 0 320 640
  (interval_append test123520 0 160 320
  (interval_append test123520 0 80 160
  (interval_append test123520 0 32 80
  (interval_append test123520 0 16 32
  test123520_block_0
  test123520_block_1)
  (interval_append test123520 32 48 80
  test123520_block_2
  (interval_append test123520 48 64 80
  test123520_block_3
  test123520_block_4)))
  (interval_append test123520 80 112 160
  (interval_append test123520 80 96 112
  test123520_block_5
  test123520_block_6)
  (interval_append test123520 112 128 160
  test123520_block_7
  (interval_append test123520 128 144 160
  test123520_block_8
  test123520_block_9))))
  (interval_append test123520 160 240 320
  (interval_append test123520 160 192 240
  (interval_append test123520 160 176 192
  test123520_block_10
  test123520_block_11)
  (interval_append test123520 192 208 240
  test123520_block_12
  (interval_append test123520 208 224 240
  test123520_block_13
  test123520_block_14)))
  (interval_append test123520 240 272 320
  (interval_append test123520 240 256 272
  test123520_block_15
  test123520_block_16)
  (interval_append test123520 272 288 320
  test123520_block_17
  (interval_append test123520 288 304 320
  test123520_block_18
  test123520_block_19)))))
  (interval_append test123520 320 480 640
  (interval_append test123520 320 400 480
  (interval_append test123520 320 352 400
  (interval_append test123520 320 336 352
  test123520_block_20
  test123520_block_21)
  (interval_append test123520 352 368 400
  test123520_block_22
  (interval_append test123520 368 384 400
  test123520_block_23
  test123520_block_24)))
  (interval_append test123520 400 432 480
  (interval_append test123520 400 416 432
  test123520_block_25
  test123520_block_26)
  (interval_append test123520 432 448 480
  test123520_block_27
  (interval_append test123520 448 464 480
  test123520_block_28
  test123520_block_29))))
  (interval_append test123520 480 560 640
  (interval_append test123520 480 512 560
  (interval_append test123520 480 496 512
  test123520_block_30
  test123520_block_31)
  (interval_append test123520 512 528 560
  test123520_block_32
  (interval_append test123520 528 544 560
  test123520_block_33
  test123520_block_34)))
  (interval_append test123520 560 592 640
  (interval_append test123520 560 576 592
  test123520_block_35
  test123520_block_36)
  (interval_append test123520 592 608 640
  test123520_block_37
  (interval_append test123520 608 624 640
  test123520_block_38
  test123520_block_39))))))
cert_nodeInterval_3 123520 124160
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
cert_test_11 124160
cert_test_block_3 124160 0 0 16 16
cert_test_block_3 124160 1 16 32 16
cert_test_block_3 124160 2 32 48 16
cert_test_block_3 124160 3 48 64 16
cert_test_block_3 124160 4 64 80 16
cert_test_block_3 124160 5 80 96 16
cert_test_block_3 124160 6 96 112 16
cert_test_block_3 124160 7 112 128 16
cert_test_block_3 124160 8 128 144 16
cert_test_block_3 124160 9 144 160 16
cert_test_block_3 124160 10 160 176 16
cert_test_block_3 124160 11 176 192 16
cert_test_block_3 124160 12 192 208 16
cert_test_block_3 124160 13 208 224 16
cert_test_block_3 124160 14 224 240 16
cert_test_block_3 124160 15 240 256 16
cert_test_block_3 124160 16 256 272 16
cert_test_block_3 124160 17 272 288 16
cert_test_block_3 124160 18 288 304 16
cert_test_block_3 124160 19 304 320 16
cert_test_block_3 124160 20 320 336 16
cert_test_block_3 124160 21 336 352 16
cert_test_block_3 124160 22 352 368 16
cert_test_block_3 124160 23 368 384 16
cert_test_block_3 124160 24 384 400 16
cert_test_block_3 124160 25 400 416 16
cert_test_block_3 124160 26 416 432 16
cert_test_block_3 124160 27 432 448 16
cert_test_block_3 124160 28 448 464 16
cert_test_block_3 124160 29 464 480 16
cert_test_block_3 124160 30 480 496 16
cert_test_block_3 124160 31 496 512 16
cert_test_block_3 124160 32 512 528 16
cert_test_block_3 124160 33 528 544 16
cert_test_block_3 124160 34 544 560 16
cert_test_block_3 124160 35 560 576 16
cert_test_block_3 124160 36 576 592 16
cert_test_block_3 124160 37 592 608 16
cert_test_block_3 124160 38 608 624 16
cert_test_block_3 124160 39 624 640 16
theorem test124160_complete : Interval test124160 0 640 :=
  (interval_append test124160 0 320 640
  (interval_append test124160 0 160 320
  (interval_append test124160 0 80 160
  (interval_append test124160 0 32 80
  (interval_append test124160 0 16 32
  test124160_block_0
  test124160_block_1)
  (interval_append test124160 32 48 80
  test124160_block_2
  (interval_append test124160 48 64 80
  test124160_block_3
  test124160_block_4)))
  (interval_append test124160 80 112 160
  (interval_append test124160 80 96 112
  test124160_block_5
  test124160_block_6)
  (interval_append test124160 112 128 160
  test124160_block_7
  (interval_append test124160 128 144 160
  test124160_block_8
  test124160_block_9))))
  (interval_append test124160 160 240 320
  (interval_append test124160 160 192 240
  (interval_append test124160 160 176 192
  test124160_block_10
  test124160_block_11)
  (interval_append test124160 192 208 240
  test124160_block_12
  (interval_append test124160 208 224 240
  test124160_block_13
  test124160_block_14)))
  (interval_append test124160 240 272 320
  (interval_append test124160 240 256 272
  test124160_block_15
  test124160_block_16)
  (interval_append test124160 272 288 320
  test124160_block_17
  (interval_append test124160 288 304 320
  test124160_block_18
  test124160_block_19)))))
  (interval_append test124160 320 480 640
  (interval_append test124160 320 400 480
  (interval_append test124160 320 352 400
  (interval_append test124160 320 336 352
  test124160_block_20
  test124160_block_21)
  (interval_append test124160 352 368 400
  test124160_block_22
  (interval_append test124160 368 384 400
  test124160_block_23
  test124160_block_24)))
  (interval_append test124160 400 432 480
  (interval_append test124160 400 416 432
  test124160_block_25
  test124160_block_26)
  (interval_append test124160 432 448 480
  test124160_block_27
  (interval_append test124160 448 464 480
  test124160_block_28
  test124160_block_29))))
  (interval_append test124160 480 560 640
  (interval_append test124160 480 512 560
  (interval_append test124160 480 496 512
  test124160_block_30
  test124160_block_31)
  (interval_append test124160 512 528 560
  test124160_block_32
  (interval_append test124160 528 544 560
  test124160_block_33
  test124160_block_34)))
  (interval_append test124160 560 592 640
  (interval_append test124160 560 576 592
  test124160_block_35
  test124160_block_36)
  (interval_append test124160 592 608 640
  test124160_block_37
  (interval_append test124160 608 624 640
  test124160_block_38
  test124160_block_39))))))
cert_nodeInterval_3 124160 124800
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
cert_test_11 124800
cert_test_block_3 124800 0 0 16 16
cert_test_block_3 124800 1 16 32 16
cert_test_block_3 124800 2 32 48 16
cert_test_block_3 124800 3 48 64 16
cert_test_block_3 124800 4 64 80 16
cert_test_block_3 124800 5 80 96 16
cert_test_block_3 124800 6 96 112 16
cert_test_block_3 124800 7 112 128 16
cert_test_block_3 124800 8 128 144 16
cert_test_block_3 124800 9 144 160 16
cert_test_block_3 124800 10 160 176 16
cert_test_block_3 124800 11 176 192 16
cert_test_block_3 124800 12 192 208 16
cert_test_block_3 124800 13 208 224 16
cert_test_block_3 124800 14 224 240 16
cert_test_block_3 124800 15 240 256 16
cert_test_block_3 124800 16 256 272 16
cert_test_block_3 124800 17 272 288 16
cert_test_block_3 124800 18 288 304 16
cert_test_block_3 124800 19 304 320 16
cert_test_block_3 124800 20 320 336 16
cert_test_block_3 124800 21 336 352 16
cert_test_block_3 124800 22 352 368 16
cert_test_block_3 124800 23 368 384 16
cert_test_block_3 124800 24 384 400 16
cert_test_block_3 124800 25 400 416 16
cert_test_block_3 124800 26 416 432 16
cert_test_block_3 124800 27 432 448 16
cert_test_block_3 124800 28 448 464 16
cert_test_block_3 124800 29 464 480 16
cert_test_block_3 124800 30 480 496 16
cert_test_block_3 124800 31 496 512 16
cert_test_block_3 124800 32 512 528 16
cert_test_block_3 124800 33 528 544 16
cert_test_block_3 124800 34 544 560 16
cert_test_block_3 124800 35 560 576 16
cert_test_block_3 124800 36 576 592 16
cert_test_block_3 124800 37 592 608 16
cert_test_block_3 124800 38 608 624 16
cert_test_block_3 124800 39 624 640 16
theorem test124800_complete : Interval test124800 0 640 :=
  (interval_append test124800 0 320 640
  (interval_append test124800 0 160 320
  (interval_append test124800 0 80 160
  (interval_append test124800 0 32 80
  (interval_append test124800 0 16 32
  test124800_block_0
  test124800_block_1)
  (interval_append test124800 32 48 80
  test124800_block_2
  (interval_append test124800 48 64 80
  test124800_block_3
  test124800_block_4)))
  (interval_append test124800 80 112 160
  (interval_append test124800 80 96 112
  test124800_block_5
  test124800_block_6)
  (interval_append test124800 112 128 160
  test124800_block_7
  (interval_append test124800 128 144 160
  test124800_block_8
  test124800_block_9))))
  (interval_append test124800 160 240 320
  (interval_append test124800 160 192 240
  (interval_append test124800 160 176 192
  test124800_block_10
  test124800_block_11)
  (interval_append test124800 192 208 240
  test124800_block_12
  (interval_append test124800 208 224 240
  test124800_block_13
  test124800_block_14)))
  (interval_append test124800 240 272 320
  (interval_append test124800 240 256 272
  test124800_block_15
  test124800_block_16)
  (interval_append test124800 272 288 320
  test124800_block_17
  (interval_append test124800 288 304 320
  test124800_block_18
  test124800_block_19)))))
  (interval_append test124800 320 480 640
  (interval_append test124800 320 400 480
  (interval_append test124800 320 352 400
  (interval_append test124800 320 336 352
  test124800_block_20
  test124800_block_21)
  (interval_append test124800 352 368 400
  test124800_block_22
  (interval_append test124800 368 384 400
  test124800_block_23
  test124800_block_24)))
  (interval_append test124800 400 432 480
  (interval_append test124800 400 416 432
  test124800_block_25
  test124800_block_26)
  (interval_append test124800 432 448 480
  test124800_block_27
  (interval_append test124800 448 464 480
  test124800_block_28
  test124800_block_29))))
  (interval_append test124800 480 560 640
  (interval_append test124800 480 512 560
  (interval_append test124800 480 496 512
  test124800_block_30
  test124800_block_31)
  (interval_append test124800 512 528 560
  test124800_block_32
  (interval_append test124800 528 544 560
  test124800_block_33
  test124800_block_34)))
  (interval_append test124800 560 592 640
  (interval_append test124800 560 576 592
  test124800_block_35
  test124800_block_36)
  (interval_append test124800 592 608 640
  test124800_block_37
  (interval_append test124800 608 624 640
  test124800_block_38
  test124800_block_39))))))
cert_nodeInterval_3 124800 125440
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
cert_test_11 125440
cert_test_block_3 125440 0 0 16 16
cert_test_block_3 125440 1 16 32 16
cert_test_block_3 125440 2 32 48 16
cert_test_block_3 125440 3 48 64 16
cert_test_block_3 125440 4 64 80 16
cert_test_block_3 125440 5 80 96 16
cert_test_block_3 125440 6 96 112 16
cert_test_block_3 125440 7 112 128 16
cert_test_block_3 125440 8 128 144 16
cert_test_block_3 125440 9 144 160 16
cert_test_block_3 125440 10 160 176 16
cert_test_block_3 125440 11 176 192 16
cert_test_block_3 125440 12 192 208 16
cert_test_block_3 125440 13 208 224 16
cert_test_block_3 125440 14 224 240 16
cert_test_block_3 125440 15 240 256 16
cert_test_block_3 125440 16 256 272 16
cert_test_block_3 125440 17 272 288 16
cert_test_block_3 125440 18 288 304 16
cert_test_block_3 125440 19 304 320 16
cert_test_block_3 125440 20 320 336 16
cert_test_block_3 125440 21 336 352 16
cert_test_block_3 125440 22 352 368 16
cert_test_block_3 125440 23 368 384 16
cert_test_block_3 125440 24 384 400 16
cert_test_block_3 125440 25 400 416 16
cert_test_block_3 125440 26 416 432 16
cert_test_block_3 125440 27 432 448 16
cert_test_block_3 125440 28 448 464 16
cert_test_block_3 125440 29 464 480 16
cert_test_block_3 125440 30 480 496 16
cert_test_block_3 125440 31 496 512 16
cert_test_block_3 125440 32 512 528 16
cert_test_block_3 125440 33 528 544 16
cert_test_block_3 125440 34 544 560 16
cert_test_block_3 125440 35 560 576 16
cert_test_block_3 125440 36 576 592 16
cert_test_block_3 125440 37 592 608 16
cert_test_block_3 125440 38 608 624 16
cert_test_block_3 125440 39 624 640 16
theorem test125440_complete : Interval test125440 0 640 :=
  (interval_append test125440 0 320 640
  (interval_append test125440 0 160 320
  (interval_append test125440 0 80 160
  (interval_append test125440 0 32 80
  (interval_append test125440 0 16 32
  test125440_block_0
  test125440_block_1)
  (interval_append test125440 32 48 80
  test125440_block_2
  (interval_append test125440 48 64 80
  test125440_block_3
  test125440_block_4)))
  (interval_append test125440 80 112 160
  (interval_append test125440 80 96 112
  test125440_block_5
  test125440_block_6)
  (interval_append test125440 112 128 160
  test125440_block_7
  (interval_append test125440 128 144 160
  test125440_block_8
  test125440_block_9))))
  (interval_append test125440 160 240 320
  (interval_append test125440 160 192 240
  (interval_append test125440 160 176 192
  test125440_block_10
  test125440_block_11)
  (interval_append test125440 192 208 240
  test125440_block_12
  (interval_append test125440 208 224 240
  test125440_block_13
  test125440_block_14)))
  (interval_append test125440 240 272 320
  (interval_append test125440 240 256 272
  test125440_block_15
  test125440_block_16)
  (interval_append test125440 272 288 320
  test125440_block_17
  (interval_append test125440 288 304 320
  test125440_block_18
  test125440_block_19)))))
  (interval_append test125440 320 480 640
  (interval_append test125440 320 400 480
  (interval_append test125440 320 352 400
  (interval_append test125440 320 336 352
  test125440_block_20
  test125440_block_21)
  (interval_append test125440 352 368 400
  test125440_block_22
  (interval_append test125440 368 384 400
  test125440_block_23
  test125440_block_24)))
  (interval_append test125440 400 432 480
  (interval_append test125440 400 416 432
  test125440_block_25
  test125440_block_26)
  (interval_append test125440 432 448 480
  test125440_block_27
  (interval_append test125440 448 464 480
  test125440_block_28
  test125440_block_29))))
  (interval_append test125440 480 560 640
  (interval_append test125440 480 512 560
  (interval_append test125440 480 496 512
  test125440_block_30
  test125440_block_31)
  (interval_append test125440 512 528 560
  test125440_block_32
  (interval_append test125440 528 544 560
  test125440_block_33
  test125440_block_34)))
  (interval_append test125440 560 592 640
  (interval_append test125440 560 576 592
  test125440_block_35
  test125440_block_36)
  (interval_append test125440 592 608 640
  test125440_block_37
  (interval_append test125440 608 624 640
  test125440_block_38
  test125440_block_39))))))
cert_nodeInterval_3 125440 126080
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
cert_test_11 126080
cert_test_block_3 126080 0 0 16 16
cert_test_block_3 126080 1 16 32 16
cert_test_block_3 126080 2 32 48 16
cert_test_block_3 126080 3 48 64 16
cert_test_block_3 126080 4 64 80 16
cert_test_block_3 126080 5 80 96 16
cert_test_block_3 126080 6 96 112 16
cert_test_block_3 126080 7 112 128 16
cert_test_block_3 126080 8 128 144 16
cert_test_block_3 126080 9 144 160 16
cert_test_block_3 126080 10 160 176 16
cert_test_block_3 126080 11 176 192 16
cert_test_block_3 126080 12 192 208 16
cert_test_block_3 126080 13 208 224 16
cert_test_block_3 126080 14 224 240 16
cert_test_block_3 126080 15 240 256 16
cert_test_block_3 126080 16 256 272 16
cert_test_block_3 126080 17 272 288 16
cert_test_block_3 126080 18 288 304 16
cert_test_block_3 126080 19 304 320 16
cert_test_block_3 126080 20 320 336 16
cert_test_block_3 126080 21 336 352 16
cert_test_block_3 126080 22 352 368 16
cert_test_block_3 126080 23 368 384 16
cert_test_block_3 126080 24 384 400 16
cert_test_block_3 126080 25 400 416 16
cert_test_block_3 126080 26 416 432 16
cert_test_block_3 126080 27 432 448 16
cert_test_block_3 126080 28 448 464 16
cert_test_block_3 126080 29 464 480 16
cert_test_block_3 126080 30 480 496 16
cert_test_block_3 126080 31 496 512 16
cert_test_block_3 126080 32 512 528 16
cert_test_block_3 126080 33 528 544 16
cert_test_block_3 126080 34 544 560 16
cert_test_block_3 126080 35 560 576 16
cert_test_block_3 126080 36 576 592 16
cert_test_block_3 126080 37 592 608 16
cert_test_block_3 126080 38 608 624 16
cert_test_block_3 126080 39 624 640 16
theorem test126080_complete : Interval test126080 0 640 :=
  (interval_append test126080 0 320 640
  (interval_append test126080 0 160 320
  (interval_append test126080 0 80 160
  (interval_append test126080 0 32 80
  (interval_append test126080 0 16 32
  test126080_block_0
  test126080_block_1)
  (interval_append test126080 32 48 80
  test126080_block_2
  (interval_append test126080 48 64 80
  test126080_block_3
  test126080_block_4)))
  (interval_append test126080 80 112 160
  (interval_append test126080 80 96 112
  test126080_block_5
  test126080_block_6)
  (interval_append test126080 112 128 160
  test126080_block_7
  (interval_append test126080 128 144 160
  test126080_block_8
  test126080_block_9))))
  (interval_append test126080 160 240 320
  (interval_append test126080 160 192 240
  (interval_append test126080 160 176 192
  test126080_block_10
  test126080_block_11)
  (interval_append test126080 192 208 240
  test126080_block_12
  (interval_append test126080 208 224 240
  test126080_block_13
  test126080_block_14)))
  (interval_append test126080 240 272 320
  (interval_append test126080 240 256 272
  test126080_block_15
  test126080_block_16)
  (interval_append test126080 272 288 320
  test126080_block_17
  (interval_append test126080 288 304 320
  test126080_block_18
  test126080_block_19)))))
  (interval_append test126080 320 480 640
  (interval_append test126080 320 400 480
  (interval_append test126080 320 352 400
  (interval_append test126080 320 336 352
  test126080_block_20
  test126080_block_21)
  (interval_append test126080 352 368 400
  test126080_block_22
  (interval_append test126080 368 384 400
  test126080_block_23
  test126080_block_24)))
  (interval_append test126080 400 432 480
  (interval_append test126080 400 416 432
  test126080_block_25
  test126080_block_26)
  (interval_append test126080 432 448 480
  test126080_block_27
  (interval_append test126080 448 464 480
  test126080_block_28
  test126080_block_29))))
  (interval_append test126080 480 560 640
  (interval_append test126080 480 512 560
  (interval_append test126080 480 496 512
  test126080_block_30
  test126080_block_31)
  (interval_append test126080 512 528 560
  test126080_block_32
  (interval_append test126080 528 544 560
  test126080_block_33
  test126080_block_34)))
  (interval_append test126080 560 592 640
  (interval_append test126080 560 576 592
  test126080_block_35
  test126080_block_36)
  (interval_append test126080 592 608 640
  test126080_block_37
  (interval_append test126080 608 624 640
  test126080_block_38
  test126080_block_39))))))
cert_nodeInterval_3 126080 126720
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
cert_test_11 126720
cert_test_block_3 126720 0 0 16 16
cert_test_block_3 126720 1 16 32 16
cert_test_block_3 126720 2 32 48 16
cert_test_block_3 126720 3 48 64 16
cert_test_block_3 126720 4 64 80 16
cert_test_block_3 126720 5 80 96 16
cert_test_block_3 126720 6 96 112 16
cert_test_block_3 126720 7 112 128 16
cert_test_block_3 126720 8 128 144 16
cert_test_block_3 126720 9 144 160 16
cert_test_block_3 126720 10 160 176 16
cert_test_block_3 126720 11 176 192 16
cert_test_block_3 126720 12 192 208 16
cert_test_block_3 126720 13 208 224 16
cert_test_block_3 126720 14 224 240 16
cert_test_block_3 126720 15 240 256 16
cert_test_block_3 126720 16 256 272 16
cert_test_block_3 126720 17 272 288 16
cert_test_block_3 126720 18 288 304 16
cert_test_block_3 126720 19 304 320 16
cert_test_block_3 126720 20 320 336 16
cert_test_block_3 126720 21 336 352 16
cert_test_block_3 126720 22 352 368 16
cert_test_block_3 126720 23 368 384 16
cert_test_block_3 126720 24 384 400 16
cert_test_block_3 126720 25 400 416 16
cert_test_block_3 126720 26 416 432 16
cert_test_block_3 126720 27 432 448 16
cert_test_block_3 126720 28 448 464 16
cert_test_block_3 126720 29 464 480 16
cert_test_block_3 126720 30 480 496 16
cert_test_block_3 126720 31 496 512 16
cert_test_block_3 126720 32 512 528 16
cert_test_block_3 126720 33 528 544 16
cert_test_block_3 126720 34 544 560 16
cert_test_block_3 126720 35 560 576 16
cert_test_block_3 126720 36 576 592 16
cert_test_block_3 126720 37 592 608 16
cert_test_block_3 126720 38 608 624 16
cert_test_block_3 126720 39 624 640 16
theorem test126720_complete : Interval test126720 0 640 :=
  (interval_append test126720 0 320 640
  (interval_append test126720 0 160 320
  (interval_append test126720 0 80 160
  (interval_append test126720 0 32 80
  (interval_append test126720 0 16 32
  test126720_block_0
  test126720_block_1)
  (interval_append test126720 32 48 80
  test126720_block_2
  (interval_append test126720 48 64 80
  test126720_block_3
  test126720_block_4)))
  (interval_append test126720 80 112 160
  (interval_append test126720 80 96 112
  test126720_block_5
  test126720_block_6)
  (interval_append test126720 112 128 160
  test126720_block_7
  (interval_append test126720 128 144 160
  test126720_block_8
  test126720_block_9))))
  (interval_append test126720 160 240 320
  (interval_append test126720 160 192 240
  (interval_append test126720 160 176 192
  test126720_block_10
  test126720_block_11)
  (interval_append test126720 192 208 240
  test126720_block_12
  (interval_append test126720 208 224 240
  test126720_block_13
  test126720_block_14)))
  (interval_append test126720 240 272 320
  (interval_append test126720 240 256 272
  test126720_block_15
  test126720_block_16)
  (interval_append test126720 272 288 320
  test126720_block_17
  (interval_append test126720 288 304 320
  test126720_block_18
  test126720_block_19)))))
  (interval_append test126720 320 480 640
  (interval_append test126720 320 400 480
  (interval_append test126720 320 352 400
  (interval_append test126720 320 336 352
  test126720_block_20
  test126720_block_21)
  (interval_append test126720 352 368 400
  test126720_block_22
  (interval_append test126720 368 384 400
  test126720_block_23
  test126720_block_24)))
  (interval_append test126720 400 432 480
  (interval_append test126720 400 416 432
  test126720_block_25
  test126720_block_26)
  (interval_append test126720 432 448 480
  test126720_block_27
  (interval_append test126720 448 464 480
  test126720_block_28
  test126720_block_29))))
  (interval_append test126720 480 560 640
  (interval_append test126720 480 512 560
  (interval_append test126720 480 496 512
  test126720_block_30
  test126720_block_31)
  (interval_append test126720 512 528 560
  test126720_block_32
  (interval_append test126720 528 544 560
  test126720_block_33
  test126720_block_34)))
  (interval_append test126720 560 592 640
  (interval_append test126720 560 576 592
  test126720_block_35
  test126720_block_36)
  (interval_append test126720 592 608 640
  test126720_block_37
  (interval_append test126720 608 624 640
  test126720_block_38
  test126720_block_39))))))
cert_nodeInterval_3 126720 127360
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
cert_test_11 127360
cert_test_block_3 127360 0 0 16 16
cert_test_block_3 127360 1 16 32 16
cert_test_block_3 127360 2 32 48 16
cert_test_block_3 127360 3 48 64 16
cert_test_block_3 127360 4 64 80 16
cert_test_block_3 127360 5 80 96 16
cert_test_block_3 127360 6 96 112 16
cert_test_block_3 127360 7 112 128 16
cert_test_block_3 127360 8 128 144 16
cert_test_block_3 127360 9 144 160 16
cert_test_block_3 127360 10 160 176 16
cert_test_block_3 127360 11 176 192 16
cert_test_block_3 127360 12 192 208 16
cert_test_block_3 127360 13 208 224 16
cert_test_block_3 127360 14 224 240 16
cert_test_block_3 127360 15 240 256 16
cert_test_block_3 127360 16 256 272 16
cert_test_block_3 127360 17 272 288 16
cert_test_block_3 127360 18 288 304 16
cert_test_block_3 127360 19 304 320 16
cert_test_block_3 127360 20 320 336 16
cert_test_block_3 127360 21 336 352 16
cert_test_block_3 127360 22 352 368 16
cert_test_block_3 127360 23 368 384 16
cert_test_block_3 127360 24 384 400 16
cert_test_block_3 127360 25 400 416 16
cert_test_block_3 127360 26 416 432 16
cert_test_block_3 127360 27 432 448 16
cert_test_block_3 127360 28 448 464 16
cert_test_block_3 127360 29 464 480 16
cert_test_block_3 127360 30 480 496 16
cert_test_block_3 127360 31 496 512 16
cert_test_block_3 127360 32 512 528 16
cert_test_block_3 127360 33 528 544 16
cert_test_block_3 127360 34 544 560 16
cert_test_block_3 127360 35 560 576 16
cert_test_block_3 127360 36 576 592 16
cert_test_block_3 127360 37 592 608 16
cert_test_block_3 127360 38 608 624 16
cert_test_block_3 127360 39 624 640 16
theorem test127360_complete : Interval test127360 0 640 :=
  (interval_append test127360 0 320 640
  (interval_append test127360 0 160 320
  (interval_append test127360 0 80 160
  (interval_append test127360 0 32 80
  (interval_append test127360 0 16 32
  test127360_block_0
  test127360_block_1)
  (interval_append test127360 32 48 80
  test127360_block_2
  (interval_append test127360 48 64 80
  test127360_block_3
  test127360_block_4)))
  (interval_append test127360 80 112 160
  (interval_append test127360 80 96 112
  test127360_block_5
  test127360_block_6)
  (interval_append test127360 112 128 160
  test127360_block_7
  (interval_append test127360 128 144 160
  test127360_block_8
  test127360_block_9))))
  (interval_append test127360 160 240 320
  (interval_append test127360 160 192 240
  (interval_append test127360 160 176 192
  test127360_block_10
  test127360_block_11)
  (interval_append test127360 192 208 240
  test127360_block_12
  (interval_append test127360 208 224 240
  test127360_block_13
  test127360_block_14)))
  (interval_append test127360 240 272 320
  (interval_append test127360 240 256 272
  test127360_block_15
  test127360_block_16)
  (interval_append test127360 272 288 320
  test127360_block_17
  (interval_append test127360 288 304 320
  test127360_block_18
  test127360_block_19)))))
  (interval_append test127360 320 480 640
  (interval_append test127360 320 400 480
  (interval_append test127360 320 352 400
  (interval_append test127360 320 336 352
  test127360_block_20
  test127360_block_21)
  (interval_append test127360 352 368 400
  test127360_block_22
  (interval_append test127360 368 384 400
  test127360_block_23
  test127360_block_24)))
  (interval_append test127360 400 432 480
  (interval_append test127360 400 416 432
  test127360_block_25
  test127360_block_26)
  (interval_append test127360 432 448 480
  test127360_block_27
  (interval_append test127360 448 464 480
  test127360_block_28
  test127360_block_29))))
  (interval_append test127360 480 560 640
  (interval_append test127360 480 512 560
  (interval_append test127360 480 496 512
  test127360_block_30
  test127360_block_31)
  (interval_append test127360 512 528 560
  test127360_block_32
  (interval_append test127360 528 544 560
  test127360_block_33
  test127360_block_34)))
  (interval_append test127360 560 592 640
  (interval_append test127360 560 576 592
  test127360_block_35
  test127360_block_36)
  (interval_append test127360 592 608 640
  test127360_block_37
  (interval_append test127360 608 624 640
  test127360_block_38
  test127360_block_39))))))
cert_nodeInterval_3 127360 128000
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
cert_test_11 128000
cert_test_block_3 128000 0 0 16 16
cert_test_block_3 128000 1 16 32 16
cert_test_block_3 128000 2 32 48 16
cert_test_block_3 128000 3 48 64 16
cert_test_block_3 128000 4 64 80 16
cert_test_block_3 128000 5 80 96 16
cert_test_block_3 128000 6 96 112 16
cert_test_block_3 128000 7 112 128 16
cert_test_block_3 128000 8 128 144 16
cert_test_block_3 128000 9 144 160 16
cert_test_block_3 128000 10 160 176 16
cert_test_block_3 128000 11 176 192 16
cert_test_block_3 128000 12 192 208 16
cert_test_block_3 128000 13 208 224 16
cert_test_block_3 128000 14 224 240 16
cert_test_block_3 128000 15 240 256 16
cert_test_block_3 128000 16 256 272 16
cert_test_block_3 128000 17 272 288 16
cert_test_block_3 128000 18 288 304 16
cert_test_block_3 128000 19 304 320 16
cert_test_block_3 128000 20 320 336 16
cert_test_block_3 128000 21 336 352 16
cert_test_block_3 128000 22 352 368 16
cert_test_block_3 128000 23 368 384 16
cert_test_block_3 128000 24 384 400 16
cert_test_block_3 128000 25 400 416 16
cert_test_block_3 128000 26 416 432 16
cert_test_block_3 128000 27 432 448 16
cert_test_block_3 128000 28 448 464 16
cert_test_block_3 128000 29 464 480 16
cert_test_block_3 128000 30 480 496 16
cert_test_block_3 128000 31 496 512 16
cert_test_block_3 128000 32 512 528 16
cert_test_block_3 128000 33 528 544 16
cert_test_block_3 128000 34 544 560 16
cert_test_block_3 128000 35 560 576 16
cert_test_block_3 128000 36 576 592 16
cert_test_block_3 128000 37 592 608 16
cert_test_block_3 128000 38 608 624 16
cert_test_block_3 128000 39 624 640 16
theorem test128000_complete : Interval test128000 0 640 :=
  (interval_append test128000 0 320 640
  (interval_append test128000 0 160 320
  (interval_append test128000 0 80 160
  (interval_append test128000 0 32 80
  (interval_append test128000 0 16 32
  test128000_block_0
  test128000_block_1)
  (interval_append test128000 32 48 80
  test128000_block_2
  (interval_append test128000 48 64 80
  test128000_block_3
  test128000_block_4)))
  (interval_append test128000 80 112 160
  (interval_append test128000 80 96 112
  test128000_block_5
  test128000_block_6)
  (interval_append test128000 112 128 160
  test128000_block_7
  (interval_append test128000 128 144 160
  test128000_block_8
  test128000_block_9))))
  (interval_append test128000 160 240 320
  (interval_append test128000 160 192 240
  (interval_append test128000 160 176 192
  test128000_block_10
  test128000_block_11)
  (interval_append test128000 192 208 240
  test128000_block_12
  (interval_append test128000 208 224 240
  test128000_block_13
  test128000_block_14)))
  (interval_append test128000 240 272 320
  (interval_append test128000 240 256 272
  test128000_block_15
  test128000_block_16)
  (interval_append test128000 272 288 320
  test128000_block_17
  (interval_append test128000 288 304 320
  test128000_block_18
  test128000_block_19)))))
  (interval_append test128000 320 480 640
  (interval_append test128000 320 400 480
  (interval_append test128000 320 352 400
  (interval_append test128000 320 336 352
  test128000_block_20
  test128000_block_21)
  (interval_append test128000 352 368 400
  test128000_block_22
  (interval_append test128000 368 384 400
  test128000_block_23
  test128000_block_24)))
  (interval_append test128000 400 432 480
  (interval_append test128000 400 416 432
  test128000_block_25
  test128000_block_26)
  (interval_append test128000 432 448 480
  test128000_block_27
  (interval_append test128000 448 464 480
  test128000_block_28
  test128000_block_29))))
  (interval_append test128000 480 560 640
  (interval_append test128000 480 512 560
  (interval_append test128000 480 496 512
  test128000_block_30
  test128000_block_31)
  (interval_append test128000 512 528 560
  test128000_block_32
  (interval_append test128000 528 544 560
  test128000_block_33
  test128000_block_34)))
  (interval_append test128000 560 592 640
  (interval_append test128000 560 576 592
  test128000_block_35
  test128000_block_36)
  (interval_append test128000 592 608 640
  test128000_block_37
  (interval_append test128000 608 624 640
  test128000_block_38
  test128000_block_39))))))
cert_nodeInterval_3 128000 128640
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
cert_test_11 128640
cert_test_block_3 128640 0 0 16 16
cert_test_block_3 128640 1 16 32 16
cert_test_block_3 128640 2 32 48 16
cert_test_block_3 128640 3 48 64 16
cert_test_block_3 128640 4 64 80 16
cert_test_block_3 128640 5 80 96 16
cert_test_block_3 128640 6 96 112 16
cert_test_block_3 128640 7 112 128 16
cert_test_block_3 128640 8 128 144 16
cert_test_block_3 128640 9 144 160 16
cert_test_block_3 128640 10 160 176 16
cert_test_block_3 128640 11 176 192 16
cert_test_block_3 128640 12 192 208 16
cert_test_block_3 128640 13 208 224 16
cert_test_block_3 128640 14 224 240 16
cert_test_block_3 128640 15 240 256 16
cert_test_block_3 128640 16 256 272 16
cert_test_block_3 128640 17 272 288 16
cert_test_block_3 128640 18 288 304 16
cert_test_block_3 128640 19 304 320 16
cert_test_block_3 128640 20 320 336 16
cert_test_block_3 128640 21 336 352 16
cert_test_block_3 128640 22 352 368 16
cert_test_block_3 128640 23 368 384 16
cert_test_block_3 128640 24 384 400 16
cert_test_block_3 128640 25 400 416 16
cert_test_block_3 128640 26 416 432 16
cert_test_block_3 128640 27 432 448 16
cert_test_block_3 128640 28 448 464 16
cert_test_block_3 128640 29 464 480 16
cert_test_block_3 128640 30 480 496 16
cert_test_block_3 128640 31 496 512 16
cert_test_block_3 128640 32 512 528 16
cert_test_block_3 128640 33 528 544 16
cert_test_block_3 128640 34 544 560 16
cert_test_block_3 128640 35 560 576 16
cert_test_block_3 128640 36 576 592 16
cert_test_block_3 128640 37 592 608 16
cert_test_block_3 128640 38 608 624 16
cert_test_block_3 128640 39 624 640 16
theorem test128640_complete : Interval test128640 0 640 :=
  (interval_append test128640 0 320 640
  (interval_append test128640 0 160 320
  (interval_append test128640 0 80 160
  (interval_append test128640 0 32 80
  (interval_append test128640 0 16 32
  test128640_block_0
  test128640_block_1)
  (interval_append test128640 32 48 80
  test128640_block_2
  (interval_append test128640 48 64 80
  test128640_block_3
  test128640_block_4)))
  (interval_append test128640 80 112 160
  (interval_append test128640 80 96 112
  test128640_block_5
  test128640_block_6)
  (interval_append test128640 112 128 160
  test128640_block_7
  (interval_append test128640 128 144 160
  test128640_block_8
  test128640_block_9))))
  (interval_append test128640 160 240 320
  (interval_append test128640 160 192 240
  (interval_append test128640 160 176 192
  test128640_block_10
  test128640_block_11)
  (interval_append test128640 192 208 240
  test128640_block_12
  (interval_append test128640 208 224 240
  test128640_block_13
  test128640_block_14)))
  (interval_append test128640 240 272 320
  (interval_append test128640 240 256 272
  test128640_block_15
  test128640_block_16)
  (interval_append test128640 272 288 320
  test128640_block_17
  (interval_append test128640 288 304 320
  test128640_block_18
  test128640_block_19)))))
  (interval_append test128640 320 480 640
  (interval_append test128640 320 400 480
  (interval_append test128640 320 352 400
  (interval_append test128640 320 336 352
  test128640_block_20
  test128640_block_21)
  (interval_append test128640 352 368 400
  test128640_block_22
  (interval_append test128640 368 384 400
  test128640_block_23
  test128640_block_24)))
  (interval_append test128640 400 432 480
  (interval_append test128640 400 416 432
  test128640_block_25
  test128640_block_26)
  (interval_append test128640 432 448 480
  test128640_block_27
  (interval_append test128640 448 464 480
  test128640_block_28
  test128640_block_29))))
  (interval_append test128640 480 560 640
  (interval_append test128640 480 512 560
  (interval_append test128640 480 496 512
  test128640_block_30
  test128640_block_31)
  (interval_append test128640 512 528 560
  test128640_block_32
  (interval_append test128640 528 544 560
  test128640_block_33
  test128640_block_34)))
  (interval_append test128640 560 592 640
  (interval_append test128640 560 576 592
  test128640_block_35
  test128640_block_36)
  (interval_append test128640 592 608 640
  test128640_block_37
  (interval_append test128640 608 624 640
  test128640_block_38
  test128640_block_39))))))
cert_nodeInterval_3 128640 129280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
