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
cert_test_11 106880
cert_test_block_3 106880 0 0 16 16
cert_test_block_3 106880 1 16 32 16
cert_test_block_3 106880 2 32 48 16
cert_test_block_3 106880 3 48 64 16
cert_test_block_3 106880 4 64 80 16
cert_test_block_3 106880 5 80 96 16
cert_test_block_3 106880 6 96 112 16
cert_test_block_3 106880 7 112 128 16
cert_test_block_3 106880 8 128 144 16
cert_test_block_3 106880 9 144 160 16
cert_test_block_3 106880 10 160 176 16
cert_test_block_3 106880 11 176 192 16
cert_test_block_3 106880 12 192 208 16
cert_test_block_3 106880 13 208 224 16
cert_test_block_3 106880 14 224 240 16
cert_test_block_3 106880 15 240 256 16
cert_test_block_3 106880 16 256 272 16
cert_test_block_3 106880 17 272 288 16
cert_test_block_3 106880 18 288 304 16
cert_test_block_3 106880 19 304 320 16
cert_test_block_3 106880 20 320 336 16
cert_test_block_3 106880 21 336 352 16
cert_test_block_3 106880 22 352 368 16
cert_test_block_3 106880 23 368 384 16
cert_test_block_3 106880 24 384 400 16
cert_test_block_3 106880 25 400 416 16
cert_test_block_3 106880 26 416 432 16
cert_test_block_3 106880 27 432 448 16
cert_test_block_3 106880 28 448 464 16
cert_test_block_3 106880 29 464 480 16
cert_test_block_3 106880 30 480 496 16
cert_test_block_3 106880 31 496 512 16
cert_test_block_3 106880 32 512 528 16
cert_test_block_3 106880 33 528 544 16
cert_test_block_3 106880 34 544 560 16
cert_test_block_3 106880 35 560 576 16
cert_test_block_3 106880 36 576 592 16
cert_test_block_3 106880 37 592 608 16
cert_test_block_3 106880 38 608 624 16
cert_test_block_3 106880 39 624 640 16
theorem test106880_complete : Interval test106880 0 640 :=
  (interval_append test106880 0 320 640
  (interval_append test106880 0 160 320
  (interval_append test106880 0 80 160
  (interval_append test106880 0 32 80
  (interval_append test106880 0 16 32
  test106880_block_0
  test106880_block_1)
  (interval_append test106880 32 48 80
  test106880_block_2
  (interval_append test106880 48 64 80
  test106880_block_3
  test106880_block_4)))
  (interval_append test106880 80 112 160
  (interval_append test106880 80 96 112
  test106880_block_5
  test106880_block_6)
  (interval_append test106880 112 128 160
  test106880_block_7
  (interval_append test106880 128 144 160
  test106880_block_8
  test106880_block_9))))
  (interval_append test106880 160 240 320
  (interval_append test106880 160 192 240
  (interval_append test106880 160 176 192
  test106880_block_10
  test106880_block_11)
  (interval_append test106880 192 208 240
  test106880_block_12
  (interval_append test106880 208 224 240
  test106880_block_13
  test106880_block_14)))
  (interval_append test106880 240 272 320
  (interval_append test106880 240 256 272
  test106880_block_15
  test106880_block_16)
  (interval_append test106880 272 288 320
  test106880_block_17
  (interval_append test106880 288 304 320
  test106880_block_18
  test106880_block_19)))))
  (interval_append test106880 320 480 640
  (interval_append test106880 320 400 480
  (interval_append test106880 320 352 400
  (interval_append test106880 320 336 352
  test106880_block_20
  test106880_block_21)
  (interval_append test106880 352 368 400
  test106880_block_22
  (interval_append test106880 368 384 400
  test106880_block_23
  test106880_block_24)))
  (interval_append test106880 400 432 480
  (interval_append test106880 400 416 432
  test106880_block_25
  test106880_block_26)
  (interval_append test106880 432 448 480
  test106880_block_27
  (interval_append test106880 448 464 480
  test106880_block_28
  test106880_block_29))))
  (interval_append test106880 480 560 640
  (interval_append test106880 480 512 560
  (interval_append test106880 480 496 512
  test106880_block_30
  test106880_block_31)
  (interval_append test106880 512 528 560
  test106880_block_32
  (interval_append test106880 528 544 560
  test106880_block_33
  test106880_block_34)))
  (interval_append test106880 560 592 640
  (interval_append test106880 560 576 592
  test106880_block_35
  test106880_block_36)
  (interval_append test106880 592 608 640
  test106880_block_37
  (interval_append test106880 608 624 640
  test106880_block_38
  test106880_block_39))))))
cert_nodeInterval_3 106880 107520
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
cert_test_11 107520
cert_test_block_3 107520 0 0 16 16
cert_test_block_3 107520 1 16 32 16
cert_test_block_3 107520 2 32 48 16
cert_test_block_3 107520 3 48 64 16
cert_test_block_3 107520 4 64 80 16
cert_test_block_3 107520 5 80 96 16
cert_test_block_3 107520 6 96 112 16
cert_test_block_3 107520 7 112 128 16
cert_test_block_3 107520 8 128 144 16
cert_test_block_3 107520 9 144 160 16
cert_test_block_3 107520 10 160 176 16
cert_test_block_3 107520 11 176 192 16
cert_test_block_3 107520 12 192 208 16
cert_test_block_3 107520 13 208 224 16
cert_test_block_3 107520 14 224 240 16
cert_test_block_3 107520 15 240 256 16
cert_test_block_3 107520 16 256 272 16
cert_test_block_3 107520 17 272 288 16
cert_test_block_3 107520 18 288 304 16
cert_test_block_3 107520 19 304 320 16
cert_test_block_3 107520 20 320 336 16
cert_test_block_3 107520 21 336 352 16
cert_test_block_3 107520 22 352 368 16
cert_test_block_3 107520 23 368 384 16
cert_test_block_3 107520 24 384 400 16
cert_test_block_3 107520 25 400 416 16
cert_test_block_3 107520 26 416 432 16
cert_test_block_3 107520 27 432 448 16
cert_test_block_3 107520 28 448 464 16
cert_test_block_3 107520 29 464 480 16
cert_test_block_3 107520 30 480 496 16
cert_test_block_3 107520 31 496 512 16
cert_test_block_3 107520 32 512 528 16
cert_test_block_3 107520 33 528 544 16
cert_test_block_3 107520 34 544 560 16
cert_test_block_3 107520 35 560 576 16
cert_test_block_3 107520 36 576 592 16
cert_test_block_3 107520 37 592 608 16
cert_test_block_3 107520 38 608 624 16
cert_test_block_3 107520 39 624 640 16
theorem test107520_complete : Interval test107520 0 640 :=
  (interval_append test107520 0 320 640
  (interval_append test107520 0 160 320
  (interval_append test107520 0 80 160
  (interval_append test107520 0 32 80
  (interval_append test107520 0 16 32
  test107520_block_0
  test107520_block_1)
  (interval_append test107520 32 48 80
  test107520_block_2
  (interval_append test107520 48 64 80
  test107520_block_3
  test107520_block_4)))
  (interval_append test107520 80 112 160
  (interval_append test107520 80 96 112
  test107520_block_5
  test107520_block_6)
  (interval_append test107520 112 128 160
  test107520_block_7
  (interval_append test107520 128 144 160
  test107520_block_8
  test107520_block_9))))
  (interval_append test107520 160 240 320
  (interval_append test107520 160 192 240
  (interval_append test107520 160 176 192
  test107520_block_10
  test107520_block_11)
  (interval_append test107520 192 208 240
  test107520_block_12
  (interval_append test107520 208 224 240
  test107520_block_13
  test107520_block_14)))
  (interval_append test107520 240 272 320
  (interval_append test107520 240 256 272
  test107520_block_15
  test107520_block_16)
  (interval_append test107520 272 288 320
  test107520_block_17
  (interval_append test107520 288 304 320
  test107520_block_18
  test107520_block_19)))))
  (interval_append test107520 320 480 640
  (interval_append test107520 320 400 480
  (interval_append test107520 320 352 400
  (interval_append test107520 320 336 352
  test107520_block_20
  test107520_block_21)
  (interval_append test107520 352 368 400
  test107520_block_22
  (interval_append test107520 368 384 400
  test107520_block_23
  test107520_block_24)))
  (interval_append test107520 400 432 480
  (interval_append test107520 400 416 432
  test107520_block_25
  test107520_block_26)
  (interval_append test107520 432 448 480
  test107520_block_27
  (interval_append test107520 448 464 480
  test107520_block_28
  test107520_block_29))))
  (interval_append test107520 480 560 640
  (interval_append test107520 480 512 560
  (interval_append test107520 480 496 512
  test107520_block_30
  test107520_block_31)
  (interval_append test107520 512 528 560
  test107520_block_32
  (interval_append test107520 528 544 560
  test107520_block_33
  test107520_block_34)))
  (interval_append test107520 560 592 640
  (interval_append test107520 560 576 592
  test107520_block_35
  test107520_block_36)
  (interval_append test107520 592 608 640
  test107520_block_37
  (interval_append test107520 608 624 640
  test107520_block_38
  test107520_block_39))))))
cert_nodeInterval_3 107520 108160
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
cert_test_11 108160
cert_test_block_3 108160 0 0 16 16
cert_test_block_3 108160 1 16 32 16
cert_test_block_3 108160 2 32 48 16
cert_test_block_3 108160 3 48 64 16
cert_test_block_3 108160 4 64 80 16
cert_test_block_3 108160 5 80 96 16
cert_test_block_3 108160 6 96 112 16
cert_test_block_3 108160 7 112 128 16
cert_test_block_3 108160 8 128 144 16
cert_test_block_3 108160 9 144 160 16
cert_test_block_3 108160 10 160 176 16
cert_test_block_3 108160 11 176 192 16
cert_test_block_3 108160 12 192 208 16
cert_test_block_3 108160 13 208 224 16
cert_test_block_3 108160 14 224 240 16
cert_test_block_3 108160 15 240 256 16
cert_test_block_3 108160 16 256 272 16
cert_test_block_3 108160 17 272 288 16
cert_test_block_3 108160 18 288 304 16
cert_test_block_3 108160 19 304 320 16
cert_test_block_3 108160 20 320 336 16
cert_test_block_3 108160 21 336 352 16
cert_test_block_3 108160 22 352 368 16
cert_test_block_3 108160 23 368 384 16
cert_test_block_3 108160 24 384 400 16
cert_test_block_3 108160 25 400 416 16
cert_test_block_3 108160 26 416 432 16
cert_test_block_3 108160 27 432 448 16
cert_test_block_3 108160 28 448 464 16
cert_test_block_3 108160 29 464 480 16
cert_test_block_3 108160 30 480 496 16
cert_test_block_3 108160 31 496 512 16
cert_test_block_3 108160 32 512 528 16
cert_test_block_3 108160 33 528 544 16
cert_test_block_3 108160 34 544 560 16
cert_test_block_3 108160 35 560 576 16
cert_test_block_3 108160 36 576 592 16
cert_test_block_3 108160 37 592 608 16
cert_test_block_3 108160 38 608 624 16
cert_test_block_3 108160 39 624 640 16
theorem test108160_complete : Interval test108160 0 640 :=
  (interval_append test108160 0 320 640
  (interval_append test108160 0 160 320
  (interval_append test108160 0 80 160
  (interval_append test108160 0 32 80
  (interval_append test108160 0 16 32
  test108160_block_0
  test108160_block_1)
  (interval_append test108160 32 48 80
  test108160_block_2
  (interval_append test108160 48 64 80
  test108160_block_3
  test108160_block_4)))
  (interval_append test108160 80 112 160
  (interval_append test108160 80 96 112
  test108160_block_5
  test108160_block_6)
  (interval_append test108160 112 128 160
  test108160_block_7
  (interval_append test108160 128 144 160
  test108160_block_8
  test108160_block_9))))
  (interval_append test108160 160 240 320
  (interval_append test108160 160 192 240
  (interval_append test108160 160 176 192
  test108160_block_10
  test108160_block_11)
  (interval_append test108160 192 208 240
  test108160_block_12
  (interval_append test108160 208 224 240
  test108160_block_13
  test108160_block_14)))
  (interval_append test108160 240 272 320
  (interval_append test108160 240 256 272
  test108160_block_15
  test108160_block_16)
  (interval_append test108160 272 288 320
  test108160_block_17
  (interval_append test108160 288 304 320
  test108160_block_18
  test108160_block_19)))))
  (interval_append test108160 320 480 640
  (interval_append test108160 320 400 480
  (interval_append test108160 320 352 400
  (interval_append test108160 320 336 352
  test108160_block_20
  test108160_block_21)
  (interval_append test108160 352 368 400
  test108160_block_22
  (interval_append test108160 368 384 400
  test108160_block_23
  test108160_block_24)))
  (interval_append test108160 400 432 480
  (interval_append test108160 400 416 432
  test108160_block_25
  test108160_block_26)
  (interval_append test108160 432 448 480
  test108160_block_27
  (interval_append test108160 448 464 480
  test108160_block_28
  test108160_block_29))))
  (interval_append test108160 480 560 640
  (interval_append test108160 480 512 560
  (interval_append test108160 480 496 512
  test108160_block_30
  test108160_block_31)
  (interval_append test108160 512 528 560
  test108160_block_32
  (interval_append test108160 528 544 560
  test108160_block_33
  test108160_block_34)))
  (interval_append test108160 560 592 640
  (interval_append test108160 560 576 592
  test108160_block_35
  test108160_block_36)
  (interval_append test108160 592 608 640
  test108160_block_37
  (interval_append test108160 608 624 640
  test108160_block_38
  test108160_block_39))))))
cert_nodeInterval_3 108160 108800
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
cert_test_11 108800
cert_test_block_3 108800 0 0 16 16
cert_test_block_3 108800 1 16 32 16
cert_test_block_3 108800 2 32 48 16
cert_test_block_3 108800 3 48 64 16
cert_test_block_3 108800 4 64 80 16
cert_test_block_3 108800 5 80 96 16
cert_test_block_3 108800 6 96 112 16
cert_test_block_3 108800 7 112 128 16
cert_test_block_3 108800 8 128 144 16
cert_test_block_3 108800 9 144 160 16
cert_test_block_3 108800 10 160 176 16
cert_test_block_3 108800 11 176 192 16
cert_test_block_3 108800 12 192 208 16
cert_test_block_3 108800 13 208 224 16
cert_test_block_3 108800 14 224 240 16
cert_test_block_3 108800 15 240 256 16
cert_test_block_3 108800 16 256 272 16
cert_test_block_3 108800 17 272 288 16
cert_test_block_3 108800 18 288 304 16
cert_test_block_3 108800 19 304 320 16
cert_test_block_3 108800 20 320 336 16
cert_test_block_3 108800 21 336 352 16
cert_test_block_3 108800 22 352 368 16
cert_test_block_3 108800 23 368 384 16
cert_test_block_3 108800 24 384 400 16
cert_test_block_3 108800 25 400 416 16
cert_test_block_3 108800 26 416 432 16
cert_test_block_3 108800 27 432 448 16
cert_test_block_3 108800 28 448 464 16
cert_test_block_3 108800 29 464 480 16
cert_test_block_3 108800 30 480 496 16
cert_test_block_3 108800 31 496 512 16
cert_test_block_3 108800 32 512 528 16
cert_test_block_3 108800 33 528 544 16
cert_test_block_3 108800 34 544 560 16
cert_test_block_3 108800 35 560 576 16
cert_test_block_3 108800 36 576 592 16
cert_test_block_3 108800 37 592 608 16
cert_test_block_3 108800 38 608 624 16
cert_test_block_3 108800 39 624 640 16
theorem test108800_complete : Interval test108800 0 640 :=
  (interval_append test108800 0 320 640
  (interval_append test108800 0 160 320
  (interval_append test108800 0 80 160
  (interval_append test108800 0 32 80
  (interval_append test108800 0 16 32
  test108800_block_0
  test108800_block_1)
  (interval_append test108800 32 48 80
  test108800_block_2
  (interval_append test108800 48 64 80
  test108800_block_3
  test108800_block_4)))
  (interval_append test108800 80 112 160
  (interval_append test108800 80 96 112
  test108800_block_5
  test108800_block_6)
  (interval_append test108800 112 128 160
  test108800_block_7
  (interval_append test108800 128 144 160
  test108800_block_8
  test108800_block_9))))
  (interval_append test108800 160 240 320
  (interval_append test108800 160 192 240
  (interval_append test108800 160 176 192
  test108800_block_10
  test108800_block_11)
  (interval_append test108800 192 208 240
  test108800_block_12
  (interval_append test108800 208 224 240
  test108800_block_13
  test108800_block_14)))
  (interval_append test108800 240 272 320
  (interval_append test108800 240 256 272
  test108800_block_15
  test108800_block_16)
  (interval_append test108800 272 288 320
  test108800_block_17
  (interval_append test108800 288 304 320
  test108800_block_18
  test108800_block_19)))))
  (interval_append test108800 320 480 640
  (interval_append test108800 320 400 480
  (interval_append test108800 320 352 400
  (interval_append test108800 320 336 352
  test108800_block_20
  test108800_block_21)
  (interval_append test108800 352 368 400
  test108800_block_22
  (interval_append test108800 368 384 400
  test108800_block_23
  test108800_block_24)))
  (interval_append test108800 400 432 480
  (interval_append test108800 400 416 432
  test108800_block_25
  test108800_block_26)
  (interval_append test108800 432 448 480
  test108800_block_27
  (interval_append test108800 448 464 480
  test108800_block_28
  test108800_block_29))))
  (interval_append test108800 480 560 640
  (interval_append test108800 480 512 560
  (interval_append test108800 480 496 512
  test108800_block_30
  test108800_block_31)
  (interval_append test108800 512 528 560
  test108800_block_32
  (interval_append test108800 528 544 560
  test108800_block_33
  test108800_block_34)))
  (interval_append test108800 560 592 640
  (interval_append test108800 560 576 592
  test108800_block_35
  test108800_block_36)
  (interval_append test108800 592 608 640
  test108800_block_37
  (interval_append test108800 608 624 640
  test108800_block_38
  test108800_block_39))))))
cert_nodeInterval_3 108800 109440
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
cert_test_11 109440
cert_test_block_3 109440 0 0 16 16
cert_test_block_3 109440 1 16 32 16
cert_test_block_3 109440 2 32 48 16
cert_test_block_3 109440 3 48 64 16
cert_test_block_3 109440 4 64 80 16
cert_test_block_3 109440 5 80 96 16
cert_test_block_3 109440 6 96 112 16
cert_test_block_3 109440 7 112 128 16
cert_test_block_3 109440 8 128 144 16
cert_test_block_3 109440 9 144 160 16
cert_test_block_3 109440 10 160 176 16
cert_test_block_3 109440 11 176 192 16
cert_test_block_3 109440 12 192 208 16
cert_test_block_3 109440 13 208 224 16
cert_test_block_3 109440 14 224 240 16
cert_test_block_3 109440 15 240 256 16
cert_test_block_3 109440 16 256 272 16
cert_test_block_3 109440 17 272 288 16
cert_test_block_3 109440 18 288 304 16
cert_test_block_3 109440 19 304 320 16
cert_test_block_3 109440 20 320 336 16
cert_test_block_3 109440 21 336 352 16
cert_test_block_3 109440 22 352 368 16
cert_test_block_3 109440 23 368 384 16
cert_test_block_3 109440 24 384 400 16
cert_test_block_3 109440 25 400 416 16
cert_test_block_3 109440 26 416 432 16
cert_test_block_3 109440 27 432 448 16
cert_test_block_3 109440 28 448 464 16
cert_test_block_3 109440 29 464 480 16
cert_test_block_3 109440 30 480 496 16
cert_test_block_3 109440 31 496 512 16
cert_test_block_3 109440 32 512 528 16
cert_test_block_3 109440 33 528 544 16
cert_test_block_3 109440 34 544 560 16
cert_test_block_3 109440 35 560 576 16
cert_test_block_3 109440 36 576 592 16
cert_test_block_3 109440 37 592 608 16
cert_test_block_3 109440 38 608 624 16
cert_test_block_3 109440 39 624 640 16
theorem test109440_complete : Interval test109440 0 640 :=
  (interval_append test109440 0 320 640
  (interval_append test109440 0 160 320
  (interval_append test109440 0 80 160
  (interval_append test109440 0 32 80
  (interval_append test109440 0 16 32
  test109440_block_0
  test109440_block_1)
  (interval_append test109440 32 48 80
  test109440_block_2
  (interval_append test109440 48 64 80
  test109440_block_3
  test109440_block_4)))
  (interval_append test109440 80 112 160
  (interval_append test109440 80 96 112
  test109440_block_5
  test109440_block_6)
  (interval_append test109440 112 128 160
  test109440_block_7
  (interval_append test109440 128 144 160
  test109440_block_8
  test109440_block_9))))
  (interval_append test109440 160 240 320
  (interval_append test109440 160 192 240
  (interval_append test109440 160 176 192
  test109440_block_10
  test109440_block_11)
  (interval_append test109440 192 208 240
  test109440_block_12
  (interval_append test109440 208 224 240
  test109440_block_13
  test109440_block_14)))
  (interval_append test109440 240 272 320
  (interval_append test109440 240 256 272
  test109440_block_15
  test109440_block_16)
  (interval_append test109440 272 288 320
  test109440_block_17
  (interval_append test109440 288 304 320
  test109440_block_18
  test109440_block_19)))))
  (interval_append test109440 320 480 640
  (interval_append test109440 320 400 480
  (interval_append test109440 320 352 400
  (interval_append test109440 320 336 352
  test109440_block_20
  test109440_block_21)
  (interval_append test109440 352 368 400
  test109440_block_22
  (interval_append test109440 368 384 400
  test109440_block_23
  test109440_block_24)))
  (interval_append test109440 400 432 480
  (interval_append test109440 400 416 432
  test109440_block_25
  test109440_block_26)
  (interval_append test109440 432 448 480
  test109440_block_27
  (interval_append test109440 448 464 480
  test109440_block_28
  test109440_block_29))))
  (interval_append test109440 480 560 640
  (interval_append test109440 480 512 560
  (interval_append test109440 480 496 512
  test109440_block_30
  test109440_block_31)
  (interval_append test109440 512 528 560
  test109440_block_32
  (interval_append test109440 528 544 560
  test109440_block_33
  test109440_block_34)))
  (interval_append test109440 560 592 640
  (interval_append test109440 560 576 592
  test109440_block_35
  test109440_block_36)
  (interval_append test109440 592 608 640
  test109440_block_37
  (interval_append test109440 608 624 640
  test109440_block_38
  test109440_block_39))))))
cert_nodeInterval_3 109440 110080
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
cert_test_11 110080
cert_test_block_3 110080 0 0 16 16
cert_test_block_3 110080 1 16 32 16
cert_test_block_3 110080 2 32 48 16
cert_test_block_3 110080 3 48 64 16
cert_test_block_3 110080 4 64 80 16
cert_test_block_3 110080 5 80 96 16
cert_test_block_3 110080 6 96 112 16
cert_test_block_3 110080 7 112 128 16
cert_test_block_3 110080 8 128 144 16
cert_test_block_3 110080 9 144 160 16
cert_test_block_3 110080 10 160 176 16
cert_test_block_3 110080 11 176 192 16
cert_test_block_3 110080 12 192 208 16
cert_test_block_3 110080 13 208 224 16
cert_test_block_3 110080 14 224 240 16
cert_test_block_3 110080 15 240 256 16
cert_test_block_3 110080 16 256 272 16
cert_test_block_3 110080 17 272 288 16
cert_test_block_3 110080 18 288 304 16
cert_test_block_3 110080 19 304 320 16
cert_test_block_3 110080 20 320 336 16
cert_test_block_3 110080 21 336 352 16
cert_test_block_3 110080 22 352 368 16
cert_test_block_3 110080 23 368 384 16
cert_test_block_3 110080 24 384 400 16
cert_test_block_3 110080 25 400 416 16
cert_test_block_3 110080 26 416 432 16
cert_test_block_3 110080 27 432 448 16
cert_test_block_3 110080 28 448 464 16
cert_test_block_3 110080 29 464 480 16
cert_test_block_3 110080 30 480 496 16
cert_test_block_3 110080 31 496 512 16
cert_test_block_3 110080 32 512 528 16
cert_test_block_3 110080 33 528 544 16
cert_test_block_3 110080 34 544 560 16
cert_test_block_3 110080 35 560 576 16
cert_test_block_3 110080 36 576 592 16
cert_test_block_3 110080 37 592 608 16
cert_test_block_3 110080 38 608 624 16
cert_test_block_3 110080 39 624 640 16
theorem test110080_complete : Interval test110080 0 640 :=
  (interval_append test110080 0 320 640
  (interval_append test110080 0 160 320
  (interval_append test110080 0 80 160
  (interval_append test110080 0 32 80
  (interval_append test110080 0 16 32
  test110080_block_0
  test110080_block_1)
  (interval_append test110080 32 48 80
  test110080_block_2
  (interval_append test110080 48 64 80
  test110080_block_3
  test110080_block_4)))
  (interval_append test110080 80 112 160
  (interval_append test110080 80 96 112
  test110080_block_5
  test110080_block_6)
  (interval_append test110080 112 128 160
  test110080_block_7
  (interval_append test110080 128 144 160
  test110080_block_8
  test110080_block_9))))
  (interval_append test110080 160 240 320
  (interval_append test110080 160 192 240
  (interval_append test110080 160 176 192
  test110080_block_10
  test110080_block_11)
  (interval_append test110080 192 208 240
  test110080_block_12
  (interval_append test110080 208 224 240
  test110080_block_13
  test110080_block_14)))
  (interval_append test110080 240 272 320
  (interval_append test110080 240 256 272
  test110080_block_15
  test110080_block_16)
  (interval_append test110080 272 288 320
  test110080_block_17
  (interval_append test110080 288 304 320
  test110080_block_18
  test110080_block_19)))))
  (interval_append test110080 320 480 640
  (interval_append test110080 320 400 480
  (interval_append test110080 320 352 400
  (interval_append test110080 320 336 352
  test110080_block_20
  test110080_block_21)
  (interval_append test110080 352 368 400
  test110080_block_22
  (interval_append test110080 368 384 400
  test110080_block_23
  test110080_block_24)))
  (interval_append test110080 400 432 480
  (interval_append test110080 400 416 432
  test110080_block_25
  test110080_block_26)
  (interval_append test110080 432 448 480
  test110080_block_27
  (interval_append test110080 448 464 480
  test110080_block_28
  test110080_block_29))))
  (interval_append test110080 480 560 640
  (interval_append test110080 480 512 560
  (interval_append test110080 480 496 512
  test110080_block_30
  test110080_block_31)
  (interval_append test110080 512 528 560
  test110080_block_32
  (interval_append test110080 528 544 560
  test110080_block_33
  test110080_block_34)))
  (interval_append test110080 560 592 640
  (interval_append test110080 560 576 592
  test110080_block_35
  test110080_block_36)
  (interval_append test110080 592 608 640
  test110080_block_37
  (interval_append test110080 608 624 640
  test110080_block_38
  test110080_block_39))))))
cert_nodeInterval_3 110080 110720
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
cert_test_11 110720
cert_test_block_3 110720 0 0 16 16
cert_test_block_3 110720 1 16 32 16
cert_test_block_3 110720 2 32 48 16
cert_test_block_3 110720 3 48 64 16
cert_test_block_3 110720 4 64 80 16
cert_test_block_3 110720 5 80 96 16
cert_test_block_3 110720 6 96 112 16
cert_test_block_3 110720 7 112 128 16
cert_test_block_3 110720 8 128 144 16
cert_test_block_3 110720 9 144 160 16
cert_test_block_3 110720 10 160 176 16
cert_test_block_3 110720 11 176 192 16
cert_test_block_3 110720 12 192 208 16
cert_test_block_3 110720 13 208 224 16
cert_test_block_3 110720 14 224 240 16
cert_test_block_3 110720 15 240 256 16
cert_test_block_3 110720 16 256 272 16
cert_test_block_3 110720 17 272 288 16
cert_test_block_3 110720 18 288 304 16
cert_test_block_3 110720 19 304 320 16
cert_test_block_3 110720 20 320 336 16
cert_test_block_3 110720 21 336 352 16
cert_test_block_3 110720 22 352 368 16
cert_test_block_3 110720 23 368 384 16
cert_test_block_3 110720 24 384 400 16
cert_test_block_3 110720 25 400 416 16
cert_test_block_3 110720 26 416 432 16
cert_test_block_3 110720 27 432 448 16
cert_test_block_3 110720 28 448 464 16
cert_test_block_3 110720 29 464 480 16
cert_test_block_3 110720 30 480 496 16
cert_test_block_3 110720 31 496 512 16
cert_test_block_3 110720 32 512 528 16
cert_test_block_3 110720 33 528 544 16
cert_test_block_3 110720 34 544 560 16
cert_test_block_3 110720 35 560 576 16
cert_test_block_3 110720 36 576 592 16
cert_test_block_3 110720 37 592 608 16
cert_test_block_3 110720 38 608 624 16
cert_test_block_3 110720 39 624 640 16
theorem test110720_complete : Interval test110720 0 640 :=
  (interval_append test110720 0 320 640
  (interval_append test110720 0 160 320
  (interval_append test110720 0 80 160
  (interval_append test110720 0 32 80
  (interval_append test110720 0 16 32
  test110720_block_0
  test110720_block_1)
  (interval_append test110720 32 48 80
  test110720_block_2
  (interval_append test110720 48 64 80
  test110720_block_3
  test110720_block_4)))
  (interval_append test110720 80 112 160
  (interval_append test110720 80 96 112
  test110720_block_5
  test110720_block_6)
  (interval_append test110720 112 128 160
  test110720_block_7
  (interval_append test110720 128 144 160
  test110720_block_8
  test110720_block_9))))
  (interval_append test110720 160 240 320
  (interval_append test110720 160 192 240
  (interval_append test110720 160 176 192
  test110720_block_10
  test110720_block_11)
  (interval_append test110720 192 208 240
  test110720_block_12
  (interval_append test110720 208 224 240
  test110720_block_13
  test110720_block_14)))
  (interval_append test110720 240 272 320
  (interval_append test110720 240 256 272
  test110720_block_15
  test110720_block_16)
  (interval_append test110720 272 288 320
  test110720_block_17
  (interval_append test110720 288 304 320
  test110720_block_18
  test110720_block_19)))))
  (interval_append test110720 320 480 640
  (interval_append test110720 320 400 480
  (interval_append test110720 320 352 400
  (interval_append test110720 320 336 352
  test110720_block_20
  test110720_block_21)
  (interval_append test110720 352 368 400
  test110720_block_22
  (interval_append test110720 368 384 400
  test110720_block_23
  test110720_block_24)))
  (interval_append test110720 400 432 480
  (interval_append test110720 400 416 432
  test110720_block_25
  test110720_block_26)
  (interval_append test110720 432 448 480
  test110720_block_27
  (interval_append test110720 448 464 480
  test110720_block_28
  test110720_block_29))))
  (interval_append test110720 480 560 640
  (interval_append test110720 480 512 560
  (interval_append test110720 480 496 512
  test110720_block_30
  test110720_block_31)
  (interval_append test110720 512 528 560
  test110720_block_32
  (interval_append test110720 528 544 560
  test110720_block_33
  test110720_block_34)))
  (interval_append test110720 560 592 640
  (interval_append test110720 560 576 592
  test110720_block_35
  test110720_block_36)
  (interval_append test110720 592 608 640
  test110720_block_37
  (interval_append test110720 608 624 640
  test110720_block_38
  test110720_block_39))))))
cert_nodeInterval_3 110720 111360
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
cert_test_11 111360
cert_test_block_3 111360 0 0 16 16
cert_test_block_3 111360 1 16 32 16
cert_test_block_3 111360 2 32 48 16
cert_test_block_3 111360 3 48 64 16
cert_test_block_3 111360 4 64 80 16
cert_test_block_3 111360 5 80 96 16
cert_test_block_3 111360 6 96 112 16
cert_test_block_3 111360 7 112 128 16
cert_test_block_3 111360 8 128 144 16
cert_test_block_3 111360 9 144 160 16
cert_test_block_3 111360 10 160 176 16
cert_test_block_3 111360 11 176 192 16
cert_test_block_3 111360 12 192 208 16
cert_test_block_3 111360 13 208 224 16
cert_test_block_3 111360 14 224 240 16
cert_test_block_3 111360 15 240 256 16
cert_test_block_3 111360 16 256 272 16
cert_test_block_3 111360 17 272 288 16
cert_test_block_3 111360 18 288 304 16
cert_test_block_3 111360 19 304 320 16
cert_test_block_3 111360 20 320 336 16
cert_test_block_3 111360 21 336 352 16
cert_test_block_3 111360 22 352 368 16
cert_test_block_3 111360 23 368 384 16
cert_test_block_3 111360 24 384 400 16
cert_test_block_3 111360 25 400 416 16
cert_test_block_3 111360 26 416 432 16
cert_test_block_3 111360 27 432 448 16
cert_test_block_3 111360 28 448 464 16
cert_test_block_3 111360 29 464 480 16
cert_test_block_3 111360 30 480 496 16
cert_test_block_3 111360 31 496 512 16
cert_test_block_3 111360 32 512 528 16
cert_test_block_3 111360 33 528 544 16
cert_test_block_3 111360 34 544 560 16
cert_test_block_3 111360 35 560 576 16
cert_test_block_3 111360 36 576 592 16
cert_test_block_3 111360 37 592 608 16
cert_test_block_3 111360 38 608 624 16
cert_test_block_3 111360 39 624 640 16
theorem test111360_complete : Interval test111360 0 640 :=
  (interval_append test111360 0 320 640
  (interval_append test111360 0 160 320
  (interval_append test111360 0 80 160
  (interval_append test111360 0 32 80
  (interval_append test111360 0 16 32
  test111360_block_0
  test111360_block_1)
  (interval_append test111360 32 48 80
  test111360_block_2
  (interval_append test111360 48 64 80
  test111360_block_3
  test111360_block_4)))
  (interval_append test111360 80 112 160
  (interval_append test111360 80 96 112
  test111360_block_5
  test111360_block_6)
  (interval_append test111360 112 128 160
  test111360_block_7
  (interval_append test111360 128 144 160
  test111360_block_8
  test111360_block_9))))
  (interval_append test111360 160 240 320
  (interval_append test111360 160 192 240
  (interval_append test111360 160 176 192
  test111360_block_10
  test111360_block_11)
  (interval_append test111360 192 208 240
  test111360_block_12
  (interval_append test111360 208 224 240
  test111360_block_13
  test111360_block_14)))
  (interval_append test111360 240 272 320
  (interval_append test111360 240 256 272
  test111360_block_15
  test111360_block_16)
  (interval_append test111360 272 288 320
  test111360_block_17
  (interval_append test111360 288 304 320
  test111360_block_18
  test111360_block_19)))))
  (interval_append test111360 320 480 640
  (interval_append test111360 320 400 480
  (interval_append test111360 320 352 400
  (interval_append test111360 320 336 352
  test111360_block_20
  test111360_block_21)
  (interval_append test111360 352 368 400
  test111360_block_22
  (interval_append test111360 368 384 400
  test111360_block_23
  test111360_block_24)))
  (interval_append test111360 400 432 480
  (interval_append test111360 400 416 432
  test111360_block_25
  test111360_block_26)
  (interval_append test111360 432 448 480
  test111360_block_27
  (interval_append test111360 448 464 480
  test111360_block_28
  test111360_block_29))))
  (interval_append test111360 480 560 640
  (interval_append test111360 480 512 560
  (interval_append test111360 480 496 512
  test111360_block_30
  test111360_block_31)
  (interval_append test111360 512 528 560
  test111360_block_32
  (interval_append test111360 528 544 560
  test111360_block_33
  test111360_block_34)))
  (interval_append test111360 560 592 640
  (interval_append test111360 560 576 592
  test111360_block_35
  test111360_block_36)
  (interval_append test111360 592 608 640
  test111360_block_37
  (interval_append test111360 608 624 640
  test111360_block_38
  test111360_block_39))))))
cert_nodeInterval_3 111360 112000
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
cert_test_11 112000
cert_test_block_3 112000 0 0 16 16
cert_test_block_3 112000 1 16 32 16
cert_test_block_3 112000 2 32 48 16
cert_test_block_3 112000 3 48 64 16
cert_test_block_3 112000 4 64 80 16
cert_test_block_3 112000 5 80 96 16
cert_test_block_3 112000 6 96 112 16
cert_test_block_3 112000 7 112 128 16
cert_test_block_3 112000 8 128 144 16
cert_test_block_3 112000 9 144 160 16
cert_test_block_3 112000 10 160 176 16
cert_test_block_3 112000 11 176 192 16
cert_test_block_3 112000 12 192 208 16
cert_test_block_3 112000 13 208 224 16
cert_test_block_3 112000 14 224 240 16
cert_test_block_3 112000 15 240 256 16
cert_test_block_3 112000 16 256 272 16
cert_test_block_3 112000 17 272 288 16
cert_test_block_3 112000 18 288 304 16
cert_test_block_3 112000 19 304 320 16
cert_test_block_3 112000 20 320 336 16
cert_test_block_3 112000 21 336 352 16
cert_test_block_3 112000 22 352 368 16
cert_test_block_3 112000 23 368 384 16
cert_test_block_3 112000 24 384 400 16
cert_test_block_3 112000 25 400 416 16
cert_test_block_3 112000 26 416 432 16
cert_test_block_3 112000 27 432 448 16
cert_test_block_3 112000 28 448 464 16
cert_test_block_3 112000 29 464 480 16
cert_test_block_3 112000 30 480 496 16
cert_test_block_3 112000 31 496 512 16
cert_test_block_3 112000 32 512 528 16
cert_test_block_3 112000 33 528 544 16
cert_test_block_3 112000 34 544 560 16
cert_test_block_3 112000 35 560 576 16
cert_test_block_3 112000 36 576 592 16
cert_test_block_3 112000 37 592 608 16
cert_test_block_3 112000 38 608 624 16
cert_test_block_3 112000 39 624 640 16
theorem test112000_complete : Interval test112000 0 640 :=
  (interval_append test112000 0 320 640
  (interval_append test112000 0 160 320
  (interval_append test112000 0 80 160
  (interval_append test112000 0 32 80
  (interval_append test112000 0 16 32
  test112000_block_0
  test112000_block_1)
  (interval_append test112000 32 48 80
  test112000_block_2
  (interval_append test112000 48 64 80
  test112000_block_3
  test112000_block_4)))
  (interval_append test112000 80 112 160
  (interval_append test112000 80 96 112
  test112000_block_5
  test112000_block_6)
  (interval_append test112000 112 128 160
  test112000_block_7
  (interval_append test112000 128 144 160
  test112000_block_8
  test112000_block_9))))
  (interval_append test112000 160 240 320
  (interval_append test112000 160 192 240
  (interval_append test112000 160 176 192
  test112000_block_10
  test112000_block_11)
  (interval_append test112000 192 208 240
  test112000_block_12
  (interval_append test112000 208 224 240
  test112000_block_13
  test112000_block_14)))
  (interval_append test112000 240 272 320
  (interval_append test112000 240 256 272
  test112000_block_15
  test112000_block_16)
  (interval_append test112000 272 288 320
  test112000_block_17
  (interval_append test112000 288 304 320
  test112000_block_18
  test112000_block_19)))))
  (interval_append test112000 320 480 640
  (interval_append test112000 320 400 480
  (interval_append test112000 320 352 400
  (interval_append test112000 320 336 352
  test112000_block_20
  test112000_block_21)
  (interval_append test112000 352 368 400
  test112000_block_22
  (interval_append test112000 368 384 400
  test112000_block_23
  test112000_block_24)))
  (interval_append test112000 400 432 480
  (interval_append test112000 400 416 432
  test112000_block_25
  test112000_block_26)
  (interval_append test112000 432 448 480
  test112000_block_27
  (interval_append test112000 448 464 480
  test112000_block_28
  test112000_block_29))))
  (interval_append test112000 480 560 640
  (interval_append test112000 480 512 560
  (interval_append test112000 480 496 512
  test112000_block_30
  test112000_block_31)
  (interval_append test112000 512 528 560
  test112000_block_32
  (interval_append test112000 528 544 560
  test112000_block_33
  test112000_block_34)))
  (interval_append test112000 560 592 640
  (interval_append test112000 560 576 592
  test112000_block_35
  test112000_block_36)
  (interval_append test112000 592 608 640
  test112000_block_37
  (interval_append test112000 608 624 640
  test112000_block_38
  test112000_block_39))))))
cert_nodeInterval_3 112000 112640
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
cert_test_11 112640
cert_test_block_3 112640 0 0 16 16
cert_test_block_3 112640 1 16 32 16
cert_test_block_3 112640 2 32 48 16
cert_test_block_3 112640 3 48 64 16
cert_test_block_3 112640 4 64 80 16
cert_test_block_3 112640 5 80 96 16
cert_test_block_3 112640 6 96 112 16
cert_test_block_3 112640 7 112 128 16
cert_test_block_3 112640 8 128 144 16
cert_test_block_3 112640 9 144 160 16
cert_test_block_3 112640 10 160 176 16
cert_test_block_3 112640 11 176 192 16
cert_test_block_3 112640 12 192 208 16
cert_test_block_3 112640 13 208 224 16
cert_test_block_3 112640 14 224 240 16
cert_test_block_3 112640 15 240 256 16
cert_test_block_3 112640 16 256 272 16
cert_test_block_3 112640 17 272 288 16
cert_test_block_3 112640 18 288 304 16
cert_test_block_3 112640 19 304 320 16
cert_test_block_3 112640 20 320 336 16
cert_test_block_3 112640 21 336 352 16
cert_test_block_3 112640 22 352 368 16
cert_test_block_3 112640 23 368 384 16
cert_test_block_3 112640 24 384 400 16
cert_test_block_3 112640 25 400 416 16
cert_test_block_3 112640 26 416 432 16
cert_test_block_3 112640 27 432 448 16
cert_test_block_3 112640 28 448 464 16
cert_test_block_3 112640 29 464 480 16
cert_test_block_3 112640 30 480 496 16
cert_test_block_3 112640 31 496 512 16
cert_test_block_3 112640 32 512 528 16
cert_test_block_3 112640 33 528 544 16
cert_test_block_3 112640 34 544 560 16
cert_test_block_3 112640 35 560 576 16
cert_test_block_3 112640 36 576 592 16
cert_test_block_3 112640 37 592 608 16
cert_test_block_3 112640 38 608 624 16
cert_test_block_3 112640 39 624 640 16
theorem test112640_complete : Interval test112640 0 640 :=
  (interval_append test112640 0 320 640
  (interval_append test112640 0 160 320
  (interval_append test112640 0 80 160
  (interval_append test112640 0 32 80
  (interval_append test112640 0 16 32
  test112640_block_0
  test112640_block_1)
  (interval_append test112640 32 48 80
  test112640_block_2
  (interval_append test112640 48 64 80
  test112640_block_3
  test112640_block_4)))
  (interval_append test112640 80 112 160
  (interval_append test112640 80 96 112
  test112640_block_5
  test112640_block_6)
  (interval_append test112640 112 128 160
  test112640_block_7
  (interval_append test112640 128 144 160
  test112640_block_8
  test112640_block_9))))
  (interval_append test112640 160 240 320
  (interval_append test112640 160 192 240
  (interval_append test112640 160 176 192
  test112640_block_10
  test112640_block_11)
  (interval_append test112640 192 208 240
  test112640_block_12
  (interval_append test112640 208 224 240
  test112640_block_13
  test112640_block_14)))
  (interval_append test112640 240 272 320
  (interval_append test112640 240 256 272
  test112640_block_15
  test112640_block_16)
  (interval_append test112640 272 288 320
  test112640_block_17
  (interval_append test112640 288 304 320
  test112640_block_18
  test112640_block_19)))))
  (interval_append test112640 320 480 640
  (interval_append test112640 320 400 480
  (interval_append test112640 320 352 400
  (interval_append test112640 320 336 352
  test112640_block_20
  test112640_block_21)
  (interval_append test112640 352 368 400
  test112640_block_22
  (interval_append test112640 368 384 400
  test112640_block_23
  test112640_block_24)))
  (interval_append test112640 400 432 480
  (interval_append test112640 400 416 432
  test112640_block_25
  test112640_block_26)
  (interval_append test112640 432 448 480
  test112640_block_27
  (interval_append test112640 448 464 480
  test112640_block_28
  test112640_block_29))))
  (interval_append test112640 480 560 640
  (interval_append test112640 480 512 560
  (interval_append test112640 480 496 512
  test112640_block_30
  test112640_block_31)
  (interval_append test112640 512 528 560
  test112640_block_32
  (interval_append test112640 528 544 560
  test112640_block_33
  test112640_block_34)))
  (interval_append test112640 560 592 640
  (interval_append test112640 560 576 592
  test112640_block_35
  test112640_block_36)
  (interval_append test112640 592 608 640
  test112640_block_37
  (interval_append test112640 608 624 640
  test112640_block_38
  test112640_block_39))))))
cert_nodeInterval_3 112640 113280
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
cert_test_11 113280
cert_test_block_3 113280 0 0 16 16
cert_test_block_3 113280 1 16 32 16
cert_test_block_3 113280 2 32 48 16
cert_test_block_3 113280 3 48 64 16
cert_test_block_3 113280 4 64 80 16
cert_test_block_3 113280 5 80 96 16
cert_test_block_3 113280 6 96 112 16
cert_test_block_3 113280 7 112 128 16
cert_test_block_3 113280 8 128 144 16
cert_test_block_3 113280 9 144 160 16
cert_test_block_3 113280 10 160 176 16
cert_test_block_3 113280 11 176 192 16
cert_test_block_3 113280 12 192 208 16
cert_test_block_3 113280 13 208 224 16
cert_test_block_3 113280 14 224 240 16
cert_test_block_3 113280 15 240 256 16
cert_test_block_3 113280 16 256 272 16
cert_test_block_3 113280 17 272 288 16
cert_test_block_3 113280 18 288 304 16
cert_test_block_3 113280 19 304 320 16
cert_test_block_3 113280 20 320 336 16
cert_test_block_3 113280 21 336 352 16
cert_test_block_3 113280 22 352 368 16
cert_test_block_3 113280 23 368 384 16
cert_test_block_3 113280 24 384 400 16
cert_test_block_3 113280 25 400 416 16
cert_test_block_3 113280 26 416 432 16
cert_test_block_3 113280 27 432 448 16
cert_test_block_3 113280 28 448 464 16
cert_test_block_3 113280 29 464 480 16
cert_test_block_3 113280 30 480 496 16
cert_test_block_3 113280 31 496 512 16
cert_test_block_3 113280 32 512 528 16
cert_test_block_3 113280 33 528 544 16
cert_test_block_3 113280 34 544 560 16
cert_test_block_3 113280 35 560 576 16
cert_test_block_3 113280 36 576 592 16
cert_test_block_3 113280 37 592 608 16
cert_test_block_3 113280 38 608 624 16
cert_test_block_3 113280 39 624 640 16
theorem test113280_complete : Interval test113280 0 640 :=
  (interval_append test113280 0 320 640
  (interval_append test113280 0 160 320
  (interval_append test113280 0 80 160
  (interval_append test113280 0 32 80
  (interval_append test113280 0 16 32
  test113280_block_0
  test113280_block_1)
  (interval_append test113280 32 48 80
  test113280_block_2
  (interval_append test113280 48 64 80
  test113280_block_3
  test113280_block_4)))
  (interval_append test113280 80 112 160
  (interval_append test113280 80 96 112
  test113280_block_5
  test113280_block_6)
  (interval_append test113280 112 128 160
  test113280_block_7
  (interval_append test113280 128 144 160
  test113280_block_8
  test113280_block_9))))
  (interval_append test113280 160 240 320
  (interval_append test113280 160 192 240
  (interval_append test113280 160 176 192
  test113280_block_10
  test113280_block_11)
  (interval_append test113280 192 208 240
  test113280_block_12
  (interval_append test113280 208 224 240
  test113280_block_13
  test113280_block_14)))
  (interval_append test113280 240 272 320
  (interval_append test113280 240 256 272
  test113280_block_15
  test113280_block_16)
  (interval_append test113280 272 288 320
  test113280_block_17
  (interval_append test113280 288 304 320
  test113280_block_18
  test113280_block_19)))))
  (interval_append test113280 320 480 640
  (interval_append test113280 320 400 480
  (interval_append test113280 320 352 400
  (interval_append test113280 320 336 352
  test113280_block_20
  test113280_block_21)
  (interval_append test113280 352 368 400
  test113280_block_22
  (interval_append test113280 368 384 400
  test113280_block_23
  test113280_block_24)))
  (interval_append test113280 400 432 480
  (interval_append test113280 400 416 432
  test113280_block_25
  test113280_block_26)
  (interval_append test113280 432 448 480
  test113280_block_27
  (interval_append test113280 448 464 480
  test113280_block_28
  test113280_block_29))))
  (interval_append test113280 480 560 640
  (interval_append test113280 480 512 560
  (interval_append test113280 480 496 512
  test113280_block_30
  test113280_block_31)
  (interval_append test113280 512 528 560
  test113280_block_32
  (interval_append test113280 528 544 560
  test113280_block_33
  test113280_block_34)))
  (interval_append test113280 560 592 640
  (interval_append test113280 560 576 592
  test113280_block_35
  test113280_block_36)
  (interval_append test113280 592 608 640
  test113280_block_37
  (interval_append test113280 608 624 640
  test113280_block_38
  test113280_block_39))))))
cert_nodeInterval_3 113280 113920
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
cert_test_11 113920
cert_test_block_3 113920 0 0 16 16
cert_test_block_3 113920 1 16 32 16
cert_test_block_3 113920 2 32 48 16
cert_test_block_3 113920 3 48 64 16
cert_test_block_3 113920 4 64 80 16
cert_test_block_3 113920 5 80 96 16
cert_test_block_3 113920 6 96 112 16
cert_test_block_3 113920 7 112 128 16
cert_test_block_3 113920 8 128 144 16
cert_test_block_3 113920 9 144 160 16
cert_test_block_3 113920 10 160 176 16
cert_test_block_3 113920 11 176 192 16
cert_test_block_3 113920 12 192 208 16
cert_test_block_3 113920 13 208 224 16
cert_test_block_3 113920 14 224 240 16
cert_test_block_3 113920 15 240 256 16
cert_test_block_3 113920 16 256 272 16
cert_test_block_3 113920 17 272 288 16
cert_test_block_3 113920 18 288 304 16
cert_test_block_3 113920 19 304 320 16
cert_test_block_3 113920 20 320 336 16
cert_test_block_3 113920 21 336 352 16
cert_test_block_3 113920 22 352 368 16
cert_test_block_3 113920 23 368 384 16
cert_test_block_3 113920 24 384 400 16
cert_test_block_3 113920 25 400 416 16
cert_test_block_3 113920 26 416 432 16
cert_test_block_3 113920 27 432 448 16
cert_test_block_3 113920 28 448 464 16
cert_test_block_3 113920 29 464 480 16
cert_test_block_3 113920 30 480 496 16
cert_test_block_3 113920 31 496 512 16
cert_test_block_3 113920 32 512 528 16
cert_test_block_3 113920 33 528 544 16
cert_test_block_3 113920 34 544 560 16
cert_test_block_3 113920 35 560 576 16
cert_test_block_3 113920 36 576 592 16
cert_test_block_3 113920 37 592 608 16
cert_test_block_3 113920 38 608 624 16
cert_test_block_3 113920 39 624 640 16
theorem test113920_complete : Interval test113920 0 640 :=
  (interval_append test113920 0 320 640
  (interval_append test113920 0 160 320
  (interval_append test113920 0 80 160
  (interval_append test113920 0 32 80
  (interval_append test113920 0 16 32
  test113920_block_0
  test113920_block_1)
  (interval_append test113920 32 48 80
  test113920_block_2
  (interval_append test113920 48 64 80
  test113920_block_3
  test113920_block_4)))
  (interval_append test113920 80 112 160
  (interval_append test113920 80 96 112
  test113920_block_5
  test113920_block_6)
  (interval_append test113920 112 128 160
  test113920_block_7
  (interval_append test113920 128 144 160
  test113920_block_8
  test113920_block_9))))
  (interval_append test113920 160 240 320
  (interval_append test113920 160 192 240
  (interval_append test113920 160 176 192
  test113920_block_10
  test113920_block_11)
  (interval_append test113920 192 208 240
  test113920_block_12
  (interval_append test113920 208 224 240
  test113920_block_13
  test113920_block_14)))
  (interval_append test113920 240 272 320
  (interval_append test113920 240 256 272
  test113920_block_15
  test113920_block_16)
  (interval_append test113920 272 288 320
  test113920_block_17
  (interval_append test113920 288 304 320
  test113920_block_18
  test113920_block_19)))))
  (interval_append test113920 320 480 640
  (interval_append test113920 320 400 480
  (interval_append test113920 320 352 400
  (interval_append test113920 320 336 352
  test113920_block_20
  test113920_block_21)
  (interval_append test113920 352 368 400
  test113920_block_22
  (interval_append test113920 368 384 400
  test113920_block_23
  test113920_block_24)))
  (interval_append test113920 400 432 480
  (interval_append test113920 400 416 432
  test113920_block_25
  test113920_block_26)
  (interval_append test113920 432 448 480
  test113920_block_27
  (interval_append test113920 448 464 480
  test113920_block_28
  test113920_block_29))))
  (interval_append test113920 480 560 640
  (interval_append test113920 480 512 560
  (interval_append test113920 480 496 512
  test113920_block_30
  test113920_block_31)
  (interval_append test113920 512 528 560
  test113920_block_32
  (interval_append test113920 528 544 560
  test113920_block_33
  test113920_block_34)))
  (interval_append test113920 560 592 640
  (interval_append test113920 560 576 592
  test113920_block_35
  test113920_block_36)
  (interval_append test113920 592 608 640
  test113920_block_37
  (interval_append test113920 608 624 640
  test113920_block_38
  test113920_block_39))))))
cert_nodeInterval_3 113920 114560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
