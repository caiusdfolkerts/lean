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
cert_test_11 134400
cert_test_block_3 134400 0 0 16 16
cert_test_block_3 134400 1 16 32 16
cert_test_block_3 134400 2 32 48 16
cert_test_block_3 134400 3 48 64 16
cert_test_block_3 134400 4 64 80 16
cert_test_block_3 134400 5 80 96 16
cert_test_block_3 134400 6 96 112 16
cert_test_block_3 134400 7 112 128 16
cert_test_block_3 134400 8 128 144 16
cert_test_block_3 134400 9 144 160 16
cert_test_block_3 134400 10 160 176 16
cert_test_block_3 134400 11 176 192 16
cert_test_block_3 134400 12 192 208 16
cert_test_block_3 134400 13 208 224 16
cert_test_block_3 134400 14 224 240 16
cert_test_block_3 134400 15 240 256 16
cert_test_block_3 134400 16 256 272 16
cert_test_block_3 134400 17 272 288 16
cert_test_block_3 134400 18 288 304 16
cert_test_block_3 134400 19 304 320 16
cert_test_block_3 134400 20 320 336 16
cert_test_block_3 134400 21 336 352 16
cert_test_block_3 134400 22 352 368 16
cert_test_block_3 134400 23 368 384 16
cert_test_block_3 134400 24 384 400 16
cert_test_block_3 134400 25 400 416 16
cert_test_block_3 134400 26 416 432 16
cert_test_block_3 134400 27 432 448 16
cert_test_block_3 134400 28 448 464 16
cert_test_block_3 134400 29 464 480 16
cert_test_block_3 134400 30 480 496 16
cert_test_block_3 134400 31 496 512 16
cert_test_block_3 134400 32 512 528 16
cert_test_block_3 134400 33 528 544 16
cert_test_block_3 134400 34 544 560 16
cert_test_block_3 134400 35 560 576 16
cert_test_block_3 134400 36 576 592 16
cert_test_block_3 134400 37 592 608 16
cert_test_block_3 134400 38 608 624 16
cert_test_block_3 134400 39 624 640 16
theorem test134400_complete : Interval test134400 0 640 :=
  (interval_append test134400 0 320 640
  (interval_append test134400 0 160 320
  (interval_append test134400 0 80 160
  (interval_append test134400 0 32 80
  (interval_append test134400 0 16 32
  test134400_block_0
  test134400_block_1)
  (interval_append test134400 32 48 80
  test134400_block_2
  (interval_append test134400 48 64 80
  test134400_block_3
  test134400_block_4)))
  (interval_append test134400 80 112 160
  (interval_append test134400 80 96 112
  test134400_block_5
  test134400_block_6)
  (interval_append test134400 112 128 160
  test134400_block_7
  (interval_append test134400 128 144 160
  test134400_block_8
  test134400_block_9))))
  (interval_append test134400 160 240 320
  (interval_append test134400 160 192 240
  (interval_append test134400 160 176 192
  test134400_block_10
  test134400_block_11)
  (interval_append test134400 192 208 240
  test134400_block_12
  (interval_append test134400 208 224 240
  test134400_block_13
  test134400_block_14)))
  (interval_append test134400 240 272 320
  (interval_append test134400 240 256 272
  test134400_block_15
  test134400_block_16)
  (interval_append test134400 272 288 320
  test134400_block_17
  (interval_append test134400 288 304 320
  test134400_block_18
  test134400_block_19)))))
  (interval_append test134400 320 480 640
  (interval_append test134400 320 400 480
  (interval_append test134400 320 352 400
  (interval_append test134400 320 336 352
  test134400_block_20
  test134400_block_21)
  (interval_append test134400 352 368 400
  test134400_block_22
  (interval_append test134400 368 384 400
  test134400_block_23
  test134400_block_24)))
  (interval_append test134400 400 432 480
  (interval_append test134400 400 416 432
  test134400_block_25
  test134400_block_26)
  (interval_append test134400 432 448 480
  test134400_block_27
  (interval_append test134400 448 464 480
  test134400_block_28
  test134400_block_29))))
  (interval_append test134400 480 560 640
  (interval_append test134400 480 512 560
  (interval_append test134400 480 496 512
  test134400_block_30
  test134400_block_31)
  (interval_append test134400 512 528 560
  test134400_block_32
  (interval_append test134400 528 544 560
  test134400_block_33
  test134400_block_34)))
  (interval_append test134400 560 592 640
  (interval_append test134400 560 576 592
  test134400_block_35
  test134400_block_36)
  (interval_append test134400 592 608 640
  test134400_block_37
  (interval_append test134400 608 624 640
  test134400_block_38
  test134400_block_39))))))
cert_nodeInterval_3 134400 135040
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
cert_test_11 135040
cert_test_block_3 135040 0 0 16 16
cert_test_block_3 135040 1 16 32 16
cert_test_block_3 135040 2 32 48 16
cert_test_block_3 135040 3 48 64 16
cert_test_block_3 135040 4 64 80 16
cert_test_block_3 135040 5 80 96 16
cert_test_block_3 135040 6 96 112 16
cert_test_block_3 135040 7 112 128 16
cert_test_block_3 135040 8 128 144 16
cert_test_block_3 135040 9 144 160 16
cert_test_block_3 135040 10 160 176 16
cert_test_block_3 135040 11 176 192 16
cert_test_block_3 135040 12 192 208 16
cert_test_block_3 135040 13 208 224 16
cert_test_block_3 135040 14 224 240 16
cert_test_block_3 135040 15 240 256 16
cert_test_block_3 135040 16 256 272 16
cert_test_block_3 135040 17 272 288 16
cert_test_block_3 135040 18 288 304 16
cert_test_block_3 135040 19 304 320 16
cert_test_block_3 135040 20 320 336 16
cert_test_block_3 135040 21 336 352 16
cert_test_block_3 135040 22 352 368 16
cert_test_block_3 135040 23 368 384 16
cert_test_block_3 135040 24 384 400 16
cert_test_block_3 135040 25 400 416 16
cert_test_block_3 135040 26 416 432 16
cert_test_block_3 135040 27 432 448 16
cert_test_block_3 135040 28 448 464 16
cert_test_block_3 135040 29 464 480 16
cert_test_block_3 135040 30 480 496 16
cert_test_block_3 135040 31 496 512 16
cert_test_block_3 135040 32 512 528 16
cert_test_block_3 135040 33 528 544 16
cert_test_block_3 135040 34 544 560 16
cert_test_block_3 135040 35 560 576 16
cert_test_block_3 135040 36 576 592 16
cert_test_block_3 135040 37 592 608 16
cert_test_block_3 135040 38 608 624 16
cert_test_block_3 135040 39 624 640 16
theorem test135040_complete : Interval test135040 0 640 :=
  (interval_append test135040 0 320 640
  (interval_append test135040 0 160 320
  (interval_append test135040 0 80 160
  (interval_append test135040 0 32 80
  (interval_append test135040 0 16 32
  test135040_block_0
  test135040_block_1)
  (interval_append test135040 32 48 80
  test135040_block_2
  (interval_append test135040 48 64 80
  test135040_block_3
  test135040_block_4)))
  (interval_append test135040 80 112 160
  (interval_append test135040 80 96 112
  test135040_block_5
  test135040_block_6)
  (interval_append test135040 112 128 160
  test135040_block_7
  (interval_append test135040 128 144 160
  test135040_block_8
  test135040_block_9))))
  (interval_append test135040 160 240 320
  (interval_append test135040 160 192 240
  (interval_append test135040 160 176 192
  test135040_block_10
  test135040_block_11)
  (interval_append test135040 192 208 240
  test135040_block_12
  (interval_append test135040 208 224 240
  test135040_block_13
  test135040_block_14)))
  (interval_append test135040 240 272 320
  (interval_append test135040 240 256 272
  test135040_block_15
  test135040_block_16)
  (interval_append test135040 272 288 320
  test135040_block_17
  (interval_append test135040 288 304 320
  test135040_block_18
  test135040_block_19)))))
  (interval_append test135040 320 480 640
  (interval_append test135040 320 400 480
  (interval_append test135040 320 352 400
  (interval_append test135040 320 336 352
  test135040_block_20
  test135040_block_21)
  (interval_append test135040 352 368 400
  test135040_block_22
  (interval_append test135040 368 384 400
  test135040_block_23
  test135040_block_24)))
  (interval_append test135040 400 432 480
  (interval_append test135040 400 416 432
  test135040_block_25
  test135040_block_26)
  (interval_append test135040 432 448 480
  test135040_block_27
  (interval_append test135040 448 464 480
  test135040_block_28
  test135040_block_29))))
  (interval_append test135040 480 560 640
  (interval_append test135040 480 512 560
  (interval_append test135040 480 496 512
  test135040_block_30
  test135040_block_31)
  (interval_append test135040 512 528 560
  test135040_block_32
  (interval_append test135040 528 544 560
  test135040_block_33
  test135040_block_34)))
  (interval_append test135040 560 592 640
  (interval_append test135040 560 576 592
  test135040_block_35
  test135040_block_36)
  (interval_append test135040 592 608 640
  test135040_block_37
  (interval_append test135040 608 624 640
  test135040_block_38
  test135040_block_39))))))
cert_nodeInterval_3 135040 135680
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
cert_test_11 135680
cert_test_block_3 135680 0 0 16 16
cert_test_block_3 135680 1 16 32 16
cert_test_block_3 135680 2 32 48 16
cert_test_block_3 135680 3 48 64 16
cert_test_block_3 135680 4 64 80 16
cert_test_block_3 135680 5 80 96 16
cert_test_block_3 135680 6 96 112 16
cert_test_block_3 135680 7 112 128 16
cert_test_block_3 135680 8 128 144 16
cert_test_block_3 135680 9 144 160 16
cert_test_block_3 135680 10 160 176 16
cert_test_block_3 135680 11 176 192 16
cert_test_block_3 135680 12 192 208 16
cert_test_block_3 135680 13 208 224 16
cert_test_block_3 135680 14 224 240 16
cert_test_block_3 135680 15 240 256 16
cert_test_block_3 135680 16 256 272 16
cert_test_block_3 135680 17 272 288 16
cert_test_block_3 135680 18 288 304 16
cert_test_block_3 135680 19 304 320 16
cert_test_block_3 135680 20 320 336 16
cert_test_block_3 135680 21 336 352 16
cert_test_block_3 135680 22 352 368 16
cert_test_block_3 135680 23 368 384 16
cert_test_block_3 135680 24 384 400 16
cert_test_block_3 135680 25 400 416 16
cert_test_block_3 135680 26 416 432 16
cert_test_block_3 135680 27 432 448 16
cert_test_block_3 135680 28 448 464 16
cert_test_block_3 135680 29 464 480 16
cert_test_block_3 135680 30 480 496 16
cert_test_block_3 135680 31 496 512 16
cert_test_block_3 135680 32 512 528 16
cert_test_block_3 135680 33 528 544 16
cert_test_block_3 135680 34 544 560 16
cert_test_block_3 135680 35 560 576 16
cert_test_block_3 135680 36 576 592 16
cert_test_block_3 135680 37 592 608 16
cert_test_block_3 135680 38 608 624 16
cert_test_block_3 135680 39 624 640 16
theorem test135680_complete : Interval test135680 0 640 :=
  (interval_append test135680 0 320 640
  (interval_append test135680 0 160 320
  (interval_append test135680 0 80 160
  (interval_append test135680 0 32 80
  (interval_append test135680 0 16 32
  test135680_block_0
  test135680_block_1)
  (interval_append test135680 32 48 80
  test135680_block_2
  (interval_append test135680 48 64 80
  test135680_block_3
  test135680_block_4)))
  (interval_append test135680 80 112 160
  (interval_append test135680 80 96 112
  test135680_block_5
  test135680_block_6)
  (interval_append test135680 112 128 160
  test135680_block_7
  (interval_append test135680 128 144 160
  test135680_block_8
  test135680_block_9))))
  (interval_append test135680 160 240 320
  (interval_append test135680 160 192 240
  (interval_append test135680 160 176 192
  test135680_block_10
  test135680_block_11)
  (interval_append test135680 192 208 240
  test135680_block_12
  (interval_append test135680 208 224 240
  test135680_block_13
  test135680_block_14)))
  (interval_append test135680 240 272 320
  (interval_append test135680 240 256 272
  test135680_block_15
  test135680_block_16)
  (interval_append test135680 272 288 320
  test135680_block_17
  (interval_append test135680 288 304 320
  test135680_block_18
  test135680_block_19)))))
  (interval_append test135680 320 480 640
  (interval_append test135680 320 400 480
  (interval_append test135680 320 352 400
  (interval_append test135680 320 336 352
  test135680_block_20
  test135680_block_21)
  (interval_append test135680 352 368 400
  test135680_block_22
  (interval_append test135680 368 384 400
  test135680_block_23
  test135680_block_24)))
  (interval_append test135680 400 432 480
  (interval_append test135680 400 416 432
  test135680_block_25
  test135680_block_26)
  (interval_append test135680 432 448 480
  test135680_block_27
  (interval_append test135680 448 464 480
  test135680_block_28
  test135680_block_29))))
  (interval_append test135680 480 560 640
  (interval_append test135680 480 512 560
  (interval_append test135680 480 496 512
  test135680_block_30
  test135680_block_31)
  (interval_append test135680 512 528 560
  test135680_block_32
  (interval_append test135680 528 544 560
  test135680_block_33
  test135680_block_34)))
  (interval_append test135680 560 592 640
  (interval_append test135680 560 576 592
  test135680_block_35
  test135680_block_36)
  (interval_append test135680 592 608 640
  test135680_block_37
  (interval_append test135680 608 624 640
  test135680_block_38
  test135680_block_39))))))
cert_nodeInterval_3 135680 136320
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
cert_test_11 136320
cert_test_block_3 136320 0 0 16 16
cert_test_block_3 136320 1 16 32 16
cert_test_block_3 136320 2 32 48 16
cert_test_block_3 136320 3 48 64 16
cert_test_block_3 136320 4 64 80 16
cert_test_block_3 136320 5 80 96 16
cert_test_block_3 136320 6 96 112 16
cert_test_block_3 136320 7 112 128 16
cert_test_block_3 136320 8 128 144 16
cert_test_block_3 136320 9 144 160 16
cert_test_block_3 136320 10 160 176 16
cert_test_block_3 136320 11 176 192 16
cert_test_block_3 136320 12 192 208 16
cert_test_block_3 136320 13 208 224 16
cert_test_block_3 136320 14 224 240 16
cert_test_block_3 136320 15 240 256 16
cert_test_block_3 136320 16 256 272 16
cert_test_block_3 136320 17 272 288 16
cert_test_block_3 136320 18 288 304 16
cert_test_block_3 136320 19 304 320 16
cert_test_block_3 136320 20 320 336 16
cert_test_block_3 136320 21 336 352 16
cert_test_block_3 136320 22 352 368 16
cert_test_block_3 136320 23 368 384 16
cert_test_block_3 136320 24 384 400 16
cert_test_block_3 136320 25 400 416 16
cert_test_block_3 136320 26 416 432 16
cert_test_block_3 136320 27 432 448 16
cert_test_block_3 136320 28 448 464 16
cert_test_block_3 136320 29 464 480 16
cert_test_block_3 136320 30 480 496 16
cert_test_block_3 136320 31 496 512 16
cert_test_block_3 136320 32 512 528 16
cert_test_block_3 136320 33 528 544 16
cert_test_block_3 136320 34 544 560 16
cert_test_block_3 136320 35 560 576 16
cert_test_block_3 136320 36 576 592 16
cert_test_block_3 136320 37 592 608 16
cert_test_block_3 136320 38 608 624 16
cert_test_block_3 136320 39 624 640 16
theorem test136320_complete : Interval test136320 0 640 :=
  (interval_append test136320 0 320 640
  (interval_append test136320 0 160 320
  (interval_append test136320 0 80 160
  (interval_append test136320 0 32 80
  (interval_append test136320 0 16 32
  test136320_block_0
  test136320_block_1)
  (interval_append test136320 32 48 80
  test136320_block_2
  (interval_append test136320 48 64 80
  test136320_block_3
  test136320_block_4)))
  (interval_append test136320 80 112 160
  (interval_append test136320 80 96 112
  test136320_block_5
  test136320_block_6)
  (interval_append test136320 112 128 160
  test136320_block_7
  (interval_append test136320 128 144 160
  test136320_block_8
  test136320_block_9))))
  (interval_append test136320 160 240 320
  (interval_append test136320 160 192 240
  (interval_append test136320 160 176 192
  test136320_block_10
  test136320_block_11)
  (interval_append test136320 192 208 240
  test136320_block_12
  (interval_append test136320 208 224 240
  test136320_block_13
  test136320_block_14)))
  (interval_append test136320 240 272 320
  (interval_append test136320 240 256 272
  test136320_block_15
  test136320_block_16)
  (interval_append test136320 272 288 320
  test136320_block_17
  (interval_append test136320 288 304 320
  test136320_block_18
  test136320_block_19)))))
  (interval_append test136320 320 480 640
  (interval_append test136320 320 400 480
  (interval_append test136320 320 352 400
  (interval_append test136320 320 336 352
  test136320_block_20
  test136320_block_21)
  (interval_append test136320 352 368 400
  test136320_block_22
  (interval_append test136320 368 384 400
  test136320_block_23
  test136320_block_24)))
  (interval_append test136320 400 432 480
  (interval_append test136320 400 416 432
  test136320_block_25
  test136320_block_26)
  (interval_append test136320 432 448 480
  test136320_block_27
  (interval_append test136320 448 464 480
  test136320_block_28
  test136320_block_29))))
  (interval_append test136320 480 560 640
  (interval_append test136320 480 512 560
  (interval_append test136320 480 496 512
  test136320_block_30
  test136320_block_31)
  (interval_append test136320 512 528 560
  test136320_block_32
  (interval_append test136320 528 544 560
  test136320_block_33
  test136320_block_34)))
  (interval_append test136320 560 592 640
  (interval_append test136320 560 576 592
  test136320_block_35
  test136320_block_36)
  (interval_append test136320 592 608 640
  test136320_block_37
  (interval_append test136320 608 624 640
  test136320_block_38
  test136320_block_39))))))
cert_nodeInterval_3 136320 136960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
