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
cert_test_11 143360
cert_test_block_3 143360 0 0 16 16
cert_test_block_3 143360 1 16 32 16
cert_test_block_3 143360 2 32 48 16
cert_test_block_3 143360 3 48 64 16
cert_test_block_3 143360 4 64 80 16
cert_test_block_3 143360 5 80 96 16
cert_test_block_3 143360 6 96 112 16
cert_test_block_3 143360 7 112 128 16
cert_test_block_3 143360 8 128 144 16
cert_test_block_3 143360 9 144 160 16
cert_test_block_3 143360 10 160 176 16
cert_test_block_3 143360 11 176 192 16
cert_test_block_3 143360 12 192 208 16
cert_test_block_3 143360 13 208 224 16
cert_test_block_3 143360 14 224 240 16
cert_test_block_3 143360 15 240 256 16
cert_test_block_3 143360 16 256 272 16
cert_test_block_3 143360 17 272 288 16
cert_test_block_3 143360 18 288 304 16
cert_test_block_3 143360 19 304 320 16
cert_test_block_3 143360 20 320 336 16
cert_test_block_3 143360 21 336 352 16
cert_test_block_3 143360 22 352 368 16
cert_test_block_3 143360 23 368 384 16
cert_test_block_3 143360 24 384 400 16
cert_test_block_3 143360 25 400 416 16
cert_test_block_3 143360 26 416 432 16
cert_test_block_3 143360 27 432 448 16
cert_test_block_3 143360 28 448 464 16
cert_test_block_3 143360 29 464 480 16
cert_test_block_3 143360 30 480 496 16
cert_test_block_3 143360 31 496 512 16
cert_test_block_3 143360 32 512 528 16
cert_test_block_3 143360 33 528 544 16
cert_test_block_3 143360 34 544 560 16
cert_test_block_3 143360 35 560 576 16
cert_test_block_3 143360 36 576 592 16
cert_test_block_3 143360 37 592 608 16
cert_test_block_3 143360 38 608 624 16
cert_test_block_3 143360 39 624 640 16
theorem test143360_complete : Interval test143360 0 640 :=
  (interval_append test143360 0 320 640
  (interval_append test143360 0 160 320
  (interval_append test143360 0 80 160
  (interval_append test143360 0 32 80
  (interval_append test143360 0 16 32
  test143360_block_0
  test143360_block_1)
  (interval_append test143360 32 48 80
  test143360_block_2
  (interval_append test143360 48 64 80
  test143360_block_3
  test143360_block_4)))
  (interval_append test143360 80 112 160
  (interval_append test143360 80 96 112
  test143360_block_5
  test143360_block_6)
  (interval_append test143360 112 128 160
  test143360_block_7
  (interval_append test143360 128 144 160
  test143360_block_8
  test143360_block_9))))
  (interval_append test143360 160 240 320
  (interval_append test143360 160 192 240
  (interval_append test143360 160 176 192
  test143360_block_10
  test143360_block_11)
  (interval_append test143360 192 208 240
  test143360_block_12
  (interval_append test143360 208 224 240
  test143360_block_13
  test143360_block_14)))
  (interval_append test143360 240 272 320
  (interval_append test143360 240 256 272
  test143360_block_15
  test143360_block_16)
  (interval_append test143360 272 288 320
  test143360_block_17
  (interval_append test143360 288 304 320
  test143360_block_18
  test143360_block_19)))))
  (interval_append test143360 320 480 640
  (interval_append test143360 320 400 480
  (interval_append test143360 320 352 400
  (interval_append test143360 320 336 352
  test143360_block_20
  test143360_block_21)
  (interval_append test143360 352 368 400
  test143360_block_22
  (interval_append test143360 368 384 400
  test143360_block_23
  test143360_block_24)))
  (interval_append test143360 400 432 480
  (interval_append test143360 400 416 432
  test143360_block_25
  test143360_block_26)
  (interval_append test143360 432 448 480
  test143360_block_27
  (interval_append test143360 448 464 480
  test143360_block_28
  test143360_block_29))))
  (interval_append test143360 480 560 640
  (interval_append test143360 480 512 560
  (interval_append test143360 480 496 512
  test143360_block_30
  test143360_block_31)
  (interval_append test143360 512 528 560
  test143360_block_32
  (interval_append test143360 528 544 560
  test143360_block_33
  test143360_block_34)))
  (interval_append test143360 560 592 640
  (interval_append test143360 560 576 592
  test143360_block_35
  test143360_block_36)
  (interval_append test143360 592 608 640
  test143360_block_37
  (interval_append test143360 608 624 640
  test143360_block_38
  test143360_block_39))))))
cert_nodeInterval_3 143360 144000
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
cert_test_11 144000
cert_test_block_3 144000 0 0 16 16
cert_test_block_3 144000 1 16 32 16
cert_test_block_3 144000 2 32 48 16
cert_test_block_3 144000 3 48 64 16
cert_test_block_3 144000 4 64 80 16
cert_test_block_3 144000 5 80 96 16
cert_test_block_3 144000 6 96 112 16
cert_test_block_3 144000 7 112 128 16
cert_test_block_3 144000 8 128 144 16
cert_test_block_3 144000 9 144 160 16
cert_test_block_3 144000 10 160 176 16
cert_test_block_3 144000 11 176 192 16
cert_test_block_3 144000 12 192 208 16
cert_test_block_3 144000 13 208 224 16
cert_test_block_3 144000 14 224 240 16
cert_test_block_3 144000 15 240 256 16
cert_test_block_3 144000 16 256 272 16
cert_test_block_3 144000 17 272 288 16
cert_test_block_3 144000 18 288 304 16
cert_test_block_3 144000 19 304 320 16
cert_test_block_3 144000 20 320 336 16
cert_test_block_3 144000 21 336 352 16
cert_test_block_3 144000 22 352 368 16
cert_test_block_3 144000 23 368 384 16
cert_test_block_3 144000 24 384 400 16
cert_test_block_3 144000 25 400 416 16
cert_test_block_3 144000 26 416 432 16
cert_test_block_3 144000 27 432 448 16
cert_test_block_3 144000 28 448 464 16
cert_test_block_3 144000 29 464 480 16
cert_test_block_3 144000 30 480 496 16
cert_test_block_3 144000 31 496 512 16
cert_test_block_3 144000 32 512 528 16
cert_test_block_3 144000 33 528 544 16
cert_test_block_3 144000 34 544 560 16
cert_test_block_3 144000 35 560 576 16
cert_test_block_3 144000 36 576 592 16
cert_test_block_3 144000 37 592 608 16
cert_test_block_3 144000 38 608 624 16
cert_test_block_3 144000 39 624 640 16
theorem test144000_complete : Interval test144000 0 640 :=
  (interval_append test144000 0 320 640
  (interval_append test144000 0 160 320
  (interval_append test144000 0 80 160
  (interval_append test144000 0 32 80
  (interval_append test144000 0 16 32
  test144000_block_0
  test144000_block_1)
  (interval_append test144000 32 48 80
  test144000_block_2
  (interval_append test144000 48 64 80
  test144000_block_3
  test144000_block_4)))
  (interval_append test144000 80 112 160
  (interval_append test144000 80 96 112
  test144000_block_5
  test144000_block_6)
  (interval_append test144000 112 128 160
  test144000_block_7
  (interval_append test144000 128 144 160
  test144000_block_8
  test144000_block_9))))
  (interval_append test144000 160 240 320
  (interval_append test144000 160 192 240
  (interval_append test144000 160 176 192
  test144000_block_10
  test144000_block_11)
  (interval_append test144000 192 208 240
  test144000_block_12
  (interval_append test144000 208 224 240
  test144000_block_13
  test144000_block_14)))
  (interval_append test144000 240 272 320
  (interval_append test144000 240 256 272
  test144000_block_15
  test144000_block_16)
  (interval_append test144000 272 288 320
  test144000_block_17
  (interval_append test144000 288 304 320
  test144000_block_18
  test144000_block_19)))))
  (interval_append test144000 320 480 640
  (interval_append test144000 320 400 480
  (interval_append test144000 320 352 400
  (interval_append test144000 320 336 352
  test144000_block_20
  test144000_block_21)
  (interval_append test144000 352 368 400
  test144000_block_22
  (interval_append test144000 368 384 400
  test144000_block_23
  test144000_block_24)))
  (interval_append test144000 400 432 480
  (interval_append test144000 400 416 432
  test144000_block_25
  test144000_block_26)
  (interval_append test144000 432 448 480
  test144000_block_27
  (interval_append test144000 448 464 480
  test144000_block_28
  test144000_block_29))))
  (interval_append test144000 480 560 640
  (interval_append test144000 480 512 560
  (interval_append test144000 480 496 512
  test144000_block_30
  test144000_block_31)
  (interval_append test144000 512 528 560
  test144000_block_32
  (interval_append test144000 528 544 560
  test144000_block_33
  test144000_block_34)))
  (interval_append test144000 560 592 640
  (interval_append test144000 560 576 592
  test144000_block_35
  test144000_block_36)
  (interval_append test144000 592 608 640
  test144000_block_37
  (interval_append test144000 608 624 640
  test144000_block_38
  test144000_block_39))))))
cert_nodeInterval_3 144000 144640
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
cert_test_11 144640
cert_test_block_3 144640 0 0 16 16
cert_test_block_3 144640 1 16 32 16
cert_test_block_3 144640 2 32 48 16
cert_test_block_3 144640 3 48 64 16
cert_test_block_3 144640 4 64 80 16
cert_test_block_3 144640 5 80 96 16
cert_test_block_3 144640 6 96 112 16
cert_test_block_3 144640 7 112 128 16
cert_test_block_3 144640 8 128 144 16
cert_test_block_3 144640 9 144 160 16
cert_test_block_3 144640 10 160 176 16
cert_test_block_3 144640 11 176 192 16
cert_test_block_3 144640 12 192 208 16
cert_test_block_3 144640 13 208 224 16
cert_test_block_3 144640 14 224 240 16
cert_test_block_3 144640 15 240 256 16
cert_test_block_3 144640 16 256 272 16
cert_test_block_3 144640 17 272 288 16
cert_test_block_3 144640 18 288 304 16
cert_test_block_3 144640 19 304 320 16
cert_test_block_3 144640 20 320 336 16
cert_test_block_3 144640 21 336 352 16
cert_test_block_3 144640 22 352 368 16
cert_test_block_3 144640 23 368 384 16
cert_test_block_3 144640 24 384 400 16
cert_test_block_3 144640 25 400 416 16
cert_test_block_3 144640 26 416 432 16
cert_test_block_3 144640 27 432 448 16
cert_test_block_3 144640 28 448 464 16
cert_test_block_3 144640 29 464 480 16
cert_test_block_3 144640 30 480 496 16
cert_test_block_3 144640 31 496 512 16
cert_test_block_3 144640 32 512 528 16
cert_test_block_3 144640 33 528 544 16
cert_test_block_3 144640 34 544 560 16
cert_test_block_3 144640 35 560 576 16
cert_test_block_3 144640 36 576 592 16
cert_test_block_3 144640 37 592 608 16
cert_test_block_3 144640 38 608 624 16
cert_test_block_3 144640 39 624 640 16
theorem test144640_complete : Interval test144640 0 640 :=
  (interval_append test144640 0 320 640
  (interval_append test144640 0 160 320
  (interval_append test144640 0 80 160
  (interval_append test144640 0 32 80
  (interval_append test144640 0 16 32
  test144640_block_0
  test144640_block_1)
  (interval_append test144640 32 48 80
  test144640_block_2
  (interval_append test144640 48 64 80
  test144640_block_3
  test144640_block_4)))
  (interval_append test144640 80 112 160
  (interval_append test144640 80 96 112
  test144640_block_5
  test144640_block_6)
  (interval_append test144640 112 128 160
  test144640_block_7
  (interval_append test144640 128 144 160
  test144640_block_8
  test144640_block_9))))
  (interval_append test144640 160 240 320
  (interval_append test144640 160 192 240
  (interval_append test144640 160 176 192
  test144640_block_10
  test144640_block_11)
  (interval_append test144640 192 208 240
  test144640_block_12
  (interval_append test144640 208 224 240
  test144640_block_13
  test144640_block_14)))
  (interval_append test144640 240 272 320
  (interval_append test144640 240 256 272
  test144640_block_15
  test144640_block_16)
  (interval_append test144640 272 288 320
  test144640_block_17
  (interval_append test144640 288 304 320
  test144640_block_18
  test144640_block_19)))))
  (interval_append test144640 320 480 640
  (interval_append test144640 320 400 480
  (interval_append test144640 320 352 400
  (interval_append test144640 320 336 352
  test144640_block_20
  test144640_block_21)
  (interval_append test144640 352 368 400
  test144640_block_22
  (interval_append test144640 368 384 400
  test144640_block_23
  test144640_block_24)))
  (interval_append test144640 400 432 480
  (interval_append test144640 400 416 432
  test144640_block_25
  test144640_block_26)
  (interval_append test144640 432 448 480
  test144640_block_27
  (interval_append test144640 448 464 480
  test144640_block_28
  test144640_block_29))))
  (interval_append test144640 480 560 640
  (interval_append test144640 480 512 560
  (interval_append test144640 480 496 512
  test144640_block_30
  test144640_block_31)
  (interval_append test144640 512 528 560
  test144640_block_32
  (interval_append test144640 528 544 560
  test144640_block_33
  test144640_block_34)))
  (interval_append test144640 560 592 640
  (interval_append test144640 560 576 592
  test144640_block_35
  test144640_block_36)
  (interval_append test144640 592 608 640
  test144640_block_37
  (interval_append test144640 608 624 640
  test144640_block_38
  test144640_block_39))))))
cert_nodeInterval_3 144640 145280
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
cert_test_11 145280
cert_test_block_3 145280 0 0 16 16
cert_test_block_3 145280 1 16 32 16
cert_test_block_3 145280 2 32 48 16
cert_test_block_3 145280 3 48 64 16
cert_test_block_3 145280 4 64 80 16
cert_test_block_3 145280 5 80 96 16
cert_test_block_3 145280 6 96 112 16
cert_test_block_3 145280 7 112 128 16
cert_test_block_3 145280 8 128 144 16
cert_test_block_3 145280 9 144 160 16
cert_test_block_3 145280 10 160 176 16
cert_test_block_3 145280 11 176 192 16
cert_test_block_3 145280 12 192 208 16
cert_test_block_3 145280 13 208 224 16
cert_test_block_3 145280 14 224 240 16
cert_test_block_3 145280 15 240 256 16
cert_test_block_3 145280 16 256 272 16
cert_test_block_3 145280 17 272 288 16
cert_test_block_3 145280 18 288 304 16
cert_test_block_3 145280 19 304 320 16
cert_test_block_3 145280 20 320 336 16
cert_test_block_3 145280 21 336 352 16
cert_test_block_3 145280 22 352 368 16
cert_test_block_3 145280 23 368 384 16
cert_test_block_3 145280 24 384 400 16
cert_test_block_3 145280 25 400 416 16
cert_test_block_3 145280 26 416 432 16
cert_test_block_3 145280 27 432 448 16
cert_test_block_3 145280 28 448 464 16
cert_test_block_3 145280 29 464 480 16
cert_test_block_3 145280 30 480 496 16
cert_test_block_3 145280 31 496 512 16
cert_test_block_3 145280 32 512 528 16
cert_test_block_3 145280 33 528 544 16
cert_test_block_3 145280 34 544 560 16
cert_test_block_3 145280 35 560 576 16
cert_test_block_3 145280 36 576 592 16
cert_test_block_3 145280 37 592 608 16
cert_test_block_3 145280 38 608 624 16
cert_test_block_3 145280 39 624 640 16
theorem test145280_complete : Interval test145280 0 640 :=
  (interval_append test145280 0 320 640
  (interval_append test145280 0 160 320
  (interval_append test145280 0 80 160
  (interval_append test145280 0 32 80
  (interval_append test145280 0 16 32
  test145280_block_0
  test145280_block_1)
  (interval_append test145280 32 48 80
  test145280_block_2
  (interval_append test145280 48 64 80
  test145280_block_3
  test145280_block_4)))
  (interval_append test145280 80 112 160
  (interval_append test145280 80 96 112
  test145280_block_5
  test145280_block_6)
  (interval_append test145280 112 128 160
  test145280_block_7
  (interval_append test145280 128 144 160
  test145280_block_8
  test145280_block_9))))
  (interval_append test145280 160 240 320
  (interval_append test145280 160 192 240
  (interval_append test145280 160 176 192
  test145280_block_10
  test145280_block_11)
  (interval_append test145280 192 208 240
  test145280_block_12
  (interval_append test145280 208 224 240
  test145280_block_13
  test145280_block_14)))
  (interval_append test145280 240 272 320
  (interval_append test145280 240 256 272
  test145280_block_15
  test145280_block_16)
  (interval_append test145280 272 288 320
  test145280_block_17
  (interval_append test145280 288 304 320
  test145280_block_18
  test145280_block_19)))))
  (interval_append test145280 320 480 640
  (interval_append test145280 320 400 480
  (interval_append test145280 320 352 400
  (interval_append test145280 320 336 352
  test145280_block_20
  test145280_block_21)
  (interval_append test145280 352 368 400
  test145280_block_22
  (interval_append test145280 368 384 400
  test145280_block_23
  test145280_block_24)))
  (interval_append test145280 400 432 480
  (interval_append test145280 400 416 432
  test145280_block_25
  test145280_block_26)
  (interval_append test145280 432 448 480
  test145280_block_27
  (interval_append test145280 448 464 480
  test145280_block_28
  test145280_block_29))))
  (interval_append test145280 480 560 640
  (interval_append test145280 480 512 560
  (interval_append test145280 480 496 512
  test145280_block_30
  test145280_block_31)
  (interval_append test145280 512 528 560
  test145280_block_32
  (interval_append test145280 528 544 560
  test145280_block_33
  test145280_block_34)))
  (interval_append test145280 560 592 640
  (interval_append test145280 560 576 592
  test145280_block_35
  test145280_block_36)
  (interval_append test145280 592 608 640
  test145280_block_37
  (interval_append test145280 608 624 640
  test145280_block_38
  test145280_block_39))))))
cert_nodeInterval_3 145280 145920
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
cert_test_11 145920
cert_test_block_3 145920 0 0 16 16
cert_test_block_3 145920 1 16 32 16
cert_test_block_3 145920 2 32 48 16
cert_test_block_3 145920 3 48 64 16
cert_test_block_3 145920 4 64 80 16
cert_test_block_3 145920 5 80 96 16
cert_test_block_3 145920 6 96 112 16
cert_test_block_3 145920 7 112 128 16
cert_test_block_3 145920 8 128 144 16
cert_test_block_3 145920 9 144 160 16
cert_test_block_3 145920 10 160 176 16
cert_test_block_3 145920 11 176 192 16
cert_test_block_3 145920 12 192 208 16
cert_test_block_3 145920 13 208 224 16
cert_test_block_3 145920 14 224 240 16
cert_test_block_3 145920 15 240 256 16
cert_test_block_3 145920 16 256 272 16
cert_test_block_3 145920 17 272 288 16
cert_test_block_3 145920 18 288 304 16
cert_test_block_3 145920 19 304 320 16
cert_test_block_3 145920 20 320 336 16
cert_test_block_3 145920 21 336 352 16
cert_test_block_3 145920 22 352 368 16
cert_test_block_3 145920 23 368 384 16
cert_test_block_3 145920 24 384 400 16
cert_test_block_3 145920 25 400 416 16
cert_test_block_3 145920 26 416 432 16
cert_test_block_3 145920 27 432 448 16
cert_test_block_3 145920 28 448 464 16
cert_test_block_3 145920 29 464 480 16
cert_test_block_3 145920 30 480 496 16
cert_test_block_3 145920 31 496 512 16
cert_test_block_3 145920 32 512 528 16
cert_test_block_3 145920 33 528 544 16
cert_test_block_3 145920 34 544 560 16
cert_test_block_3 145920 35 560 576 16
cert_test_block_3 145920 36 576 592 16
cert_test_block_3 145920 37 592 608 16
cert_test_block_3 145920 38 608 624 16
cert_test_block_3 145920 39 624 640 16
theorem test145920_complete : Interval test145920 0 640 :=
  (interval_append test145920 0 320 640
  (interval_append test145920 0 160 320
  (interval_append test145920 0 80 160
  (interval_append test145920 0 32 80
  (interval_append test145920 0 16 32
  test145920_block_0
  test145920_block_1)
  (interval_append test145920 32 48 80
  test145920_block_2
  (interval_append test145920 48 64 80
  test145920_block_3
  test145920_block_4)))
  (interval_append test145920 80 112 160
  (interval_append test145920 80 96 112
  test145920_block_5
  test145920_block_6)
  (interval_append test145920 112 128 160
  test145920_block_7
  (interval_append test145920 128 144 160
  test145920_block_8
  test145920_block_9))))
  (interval_append test145920 160 240 320
  (interval_append test145920 160 192 240
  (interval_append test145920 160 176 192
  test145920_block_10
  test145920_block_11)
  (interval_append test145920 192 208 240
  test145920_block_12
  (interval_append test145920 208 224 240
  test145920_block_13
  test145920_block_14)))
  (interval_append test145920 240 272 320
  (interval_append test145920 240 256 272
  test145920_block_15
  test145920_block_16)
  (interval_append test145920 272 288 320
  test145920_block_17
  (interval_append test145920 288 304 320
  test145920_block_18
  test145920_block_19)))))
  (interval_append test145920 320 480 640
  (interval_append test145920 320 400 480
  (interval_append test145920 320 352 400
  (interval_append test145920 320 336 352
  test145920_block_20
  test145920_block_21)
  (interval_append test145920 352 368 400
  test145920_block_22
  (interval_append test145920 368 384 400
  test145920_block_23
  test145920_block_24)))
  (interval_append test145920 400 432 480
  (interval_append test145920 400 416 432
  test145920_block_25
  test145920_block_26)
  (interval_append test145920 432 448 480
  test145920_block_27
  (interval_append test145920 448 464 480
  test145920_block_28
  test145920_block_29))))
  (interval_append test145920 480 560 640
  (interval_append test145920 480 512 560
  (interval_append test145920 480 496 512
  test145920_block_30
  test145920_block_31)
  (interval_append test145920 512 528 560
  test145920_block_32
  (interval_append test145920 528 544 560
  test145920_block_33
  test145920_block_34)))
  (interval_append test145920 560 592 640
  (interval_append test145920 560 576 592
  test145920_block_35
  test145920_block_36)
  (interval_append test145920 592 608 640
  test145920_block_37
  (interval_append test145920 608 624 640
  test145920_block_38
  test145920_block_39))))))
cert_nodeInterval_3 145920 146560
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
cert_test_11 146560
cert_test_block_3 146560 0 0 16 16
cert_test_block_3 146560 1 16 32 16
cert_test_block_3 146560 2 32 48 16
cert_test_block_3 146560 3 48 64 16
cert_test_block_3 146560 4 64 80 16
cert_test_block_3 146560 5 80 96 16
cert_test_block_3 146560 6 96 112 16
cert_test_block_3 146560 7 112 128 16
cert_test_block_3 146560 8 128 144 16
cert_test_block_3 146560 9 144 160 16
cert_test_block_3 146560 10 160 176 16
cert_test_block_3 146560 11 176 192 16
cert_test_block_3 146560 12 192 208 16
cert_test_block_3 146560 13 208 224 16
cert_test_block_3 146560 14 224 240 16
cert_test_block_3 146560 15 240 256 16
cert_test_block_3 146560 16 256 272 16
cert_test_block_3 146560 17 272 288 16
cert_test_block_3 146560 18 288 304 16
cert_test_block_3 146560 19 304 320 16
cert_test_block_3 146560 20 320 336 16
cert_test_block_3 146560 21 336 352 16
cert_test_block_3 146560 22 352 368 16
cert_test_block_3 146560 23 368 384 16
cert_test_block_3 146560 24 384 400 16
cert_test_block_3 146560 25 400 416 16
cert_test_block_3 146560 26 416 432 16
cert_test_block_3 146560 27 432 448 16
cert_test_block_3 146560 28 448 464 16
cert_test_block_3 146560 29 464 480 16
cert_test_block_3 146560 30 480 496 16
cert_test_block_3 146560 31 496 512 16
cert_test_block_3 146560 32 512 528 16
cert_test_block_3 146560 33 528 544 16
cert_test_block_3 146560 34 544 560 16
cert_test_block_3 146560 35 560 576 16
cert_test_block_3 146560 36 576 592 16
cert_test_block_3 146560 37 592 608 16
cert_test_block_3 146560 38 608 624 16
cert_test_block_3 146560 39 624 640 16
theorem test146560_complete : Interval test146560 0 640 :=
  (interval_append test146560 0 320 640
  (interval_append test146560 0 160 320
  (interval_append test146560 0 80 160
  (interval_append test146560 0 32 80
  (interval_append test146560 0 16 32
  test146560_block_0
  test146560_block_1)
  (interval_append test146560 32 48 80
  test146560_block_2
  (interval_append test146560 48 64 80
  test146560_block_3
  test146560_block_4)))
  (interval_append test146560 80 112 160
  (interval_append test146560 80 96 112
  test146560_block_5
  test146560_block_6)
  (interval_append test146560 112 128 160
  test146560_block_7
  (interval_append test146560 128 144 160
  test146560_block_8
  test146560_block_9))))
  (interval_append test146560 160 240 320
  (interval_append test146560 160 192 240
  (interval_append test146560 160 176 192
  test146560_block_10
  test146560_block_11)
  (interval_append test146560 192 208 240
  test146560_block_12
  (interval_append test146560 208 224 240
  test146560_block_13
  test146560_block_14)))
  (interval_append test146560 240 272 320
  (interval_append test146560 240 256 272
  test146560_block_15
  test146560_block_16)
  (interval_append test146560 272 288 320
  test146560_block_17
  (interval_append test146560 288 304 320
  test146560_block_18
  test146560_block_19)))))
  (interval_append test146560 320 480 640
  (interval_append test146560 320 400 480
  (interval_append test146560 320 352 400
  (interval_append test146560 320 336 352
  test146560_block_20
  test146560_block_21)
  (interval_append test146560 352 368 400
  test146560_block_22
  (interval_append test146560 368 384 400
  test146560_block_23
  test146560_block_24)))
  (interval_append test146560 400 432 480
  (interval_append test146560 400 416 432
  test146560_block_25
  test146560_block_26)
  (interval_append test146560 432 448 480
  test146560_block_27
  (interval_append test146560 448 464 480
  test146560_block_28
  test146560_block_29))))
  (interval_append test146560 480 560 640
  (interval_append test146560 480 512 560
  (interval_append test146560 480 496 512
  test146560_block_30
  test146560_block_31)
  (interval_append test146560 512 528 560
  test146560_block_32
  (interval_append test146560 528 544 560
  test146560_block_33
  test146560_block_34)))
  (interval_append test146560 560 592 640
  (interval_append test146560 560 576 592
  test146560_block_35
  test146560_block_36)
  (interval_append test146560 592 608 640
  test146560_block_37
  (interval_append test146560 608 624 640
  test146560_block_38
  test146560_block_39))))))
cert_nodeInterval_3 146560 147200
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
cert_test_11 147200
cert_test_block_3 147200 0 0 16 16
cert_test_block_3 147200 1 16 32 16
cert_test_block_3 147200 2 32 48 16
cert_test_block_3 147200 3 48 64 16
cert_test_block_3 147200 4 64 80 16
cert_test_block_3 147200 5 80 96 16
cert_test_block_3 147200 6 96 112 16
cert_test_block_3 147200 7 112 128 16
cert_test_block_3 147200 8 128 144 16
cert_test_block_3 147200 9 144 160 16
cert_test_block_3 147200 10 160 176 16
cert_test_block_3 147200 11 176 192 16
cert_test_block_3 147200 12 192 208 16
cert_test_block_3 147200 13 208 224 16
cert_test_block_3 147200 14 224 240 16
cert_test_block_3 147200 15 240 256 16
cert_test_block_3 147200 16 256 272 16
cert_test_block_3 147200 17 272 288 16
cert_test_block_3 147200 18 288 304 16
cert_test_block_3 147200 19 304 320 16
cert_test_block_3 147200 20 320 336 16
cert_test_block_3 147200 21 336 352 16
cert_test_block_3 147200 22 352 368 16
cert_test_block_3 147200 23 368 384 16
cert_test_block_3 147200 24 384 400 16
cert_test_block_3 147200 25 400 416 16
cert_test_block_3 147200 26 416 432 16
cert_test_block_3 147200 27 432 448 16
cert_test_block_3 147200 28 448 464 16
cert_test_block_3 147200 29 464 480 16
cert_test_block_3 147200 30 480 496 16
cert_test_block_3 147200 31 496 512 16
cert_test_block_3 147200 32 512 528 16
cert_test_block_3 147200 33 528 544 16
cert_test_block_3 147200 34 544 560 16
cert_test_block_3 147200 35 560 576 16
cert_test_block_3 147200 36 576 592 16
cert_test_block_3 147200 37 592 608 16
cert_test_block_3 147200 38 608 624 16
cert_test_block_3 147200 39 624 640 16
theorem test147200_complete : Interval test147200 0 640 :=
  (interval_append test147200 0 320 640
  (interval_append test147200 0 160 320
  (interval_append test147200 0 80 160
  (interval_append test147200 0 32 80
  (interval_append test147200 0 16 32
  test147200_block_0
  test147200_block_1)
  (interval_append test147200 32 48 80
  test147200_block_2
  (interval_append test147200 48 64 80
  test147200_block_3
  test147200_block_4)))
  (interval_append test147200 80 112 160
  (interval_append test147200 80 96 112
  test147200_block_5
  test147200_block_6)
  (interval_append test147200 112 128 160
  test147200_block_7
  (interval_append test147200 128 144 160
  test147200_block_8
  test147200_block_9))))
  (interval_append test147200 160 240 320
  (interval_append test147200 160 192 240
  (interval_append test147200 160 176 192
  test147200_block_10
  test147200_block_11)
  (interval_append test147200 192 208 240
  test147200_block_12
  (interval_append test147200 208 224 240
  test147200_block_13
  test147200_block_14)))
  (interval_append test147200 240 272 320
  (interval_append test147200 240 256 272
  test147200_block_15
  test147200_block_16)
  (interval_append test147200 272 288 320
  test147200_block_17
  (interval_append test147200 288 304 320
  test147200_block_18
  test147200_block_19)))))
  (interval_append test147200 320 480 640
  (interval_append test147200 320 400 480
  (interval_append test147200 320 352 400
  (interval_append test147200 320 336 352
  test147200_block_20
  test147200_block_21)
  (interval_append test147200 352 368 400
  test147200_block_22
  (interval_append test147200 368 384 400
  test147200_block_23
  test147200_block_24)))
  (interval_append test147200 400 432 480
  (interval_append test147200 400 416 432
  test147200_block_25
  test147200_block_26)
  (interval_append test147200 432 448 480
  test147200_block_27
  (interval_append test147200 448 464 480
  test147200_block_28
  test147200_block_29))))
  (interval_append test147200 480 560 640
  (interval_append test147200 480 512 560
  (interval_append test147200 480 496 512
  test147200_block_30
  test147200_block_31)
  (interval_append test147200 512 528 560
  test147200_block_32
  (interval_append test147200 528 544 560
  test147200_block_33
  test147200_block_34)))
  (interval_append test147200 560 592 640
  (interval_append test147200 560 576 592
  test147200_block_35
  test147200_block_36)
  (interval_append test147200 592 608 640
  test147200_block_37
  (interval_append test147200 608 624 640
  test147200_block_38
  test147200_block_39))))))
cert_nodeInterval_3 147200 147840
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
cert_test_11 147840
cert_test_block_3 147840 0 0 16 16
cert_test_block_3 147840 1 16 32 16
cert_test_block_3 147840 2 32 48 16
cert_test_block_3 147840 3 48 64 16
cert_test_block_3 147840 4 64 80 16
cert_test_block_3 147840 5 80 96 16
cert_test_block_3 147840 6 96 112 16
cert_test_block_3 147840 7 112 128 16
cert_test_block_3 147840 8 128 144 16
cert_test_block_3 147840 9 144 160 16
cert_test_block_3 147840 10 160 176 16
cert_test_block_3 147840 11 176 192 16
cert_test_block_3 147840 12 192 208 16
cert_test_block_3 147840 13 208 224 16
cert_test_block_3 147840 14 224 240 16
cert_test_block_3 147840 15 240 256 16
cert_test_block_3 147840 16 256 272 16
cert_test_block_3 147840 17 272 288 16
cert_test_block_3 147840 18 288 304 16
cert_test_block_3 147840 19 304 320 16
cert_test_block_3 147840 20 320 336 16
cert_test_block_3 147840 21 336 352 16
cert_test_block_3 147840 22 352 368 16
cert_test_block_3 147840 23 368 384 16
cert_test_block_3 147840 24 384 400 16
cert_test_block_3 147840 25 400 416 16
cert_test_block_3 147840 26 416 432 16
cert_test_block_3 147840 27 432 448 16
cert_test_block_3 147840 28 448 464 16
cert_test_block_3 147840 29 464 480 16
cert_test_block_3 147840 30 480 496 16
cert_test_block_3 147840 31 496 512 16
cert_test_block_3 147840 32 512 528 16
cert_test_block_3 147840 33 528 544 16
cert_test_block_3 147840 34 544 560 16
cert_test_block_3 147840 35 560 576 16
cert_test_block_3 147840 36 576 592 16
cert_test_block_3 147840 37 592 608 16
cert_test_block_3 147840 38 608 624 16
cert_test_block_3 147840 39 624 640 16
theorem test147840_complete : Interval test147840 0 640 :=
  (interval_append test147840 0 320 640
  (interval_append test147840 0 160 320
  (interval_append test147840 0 80 160
  (interval_append test147840 0 32 80
  (interval_append test147840 0 16 32
  test147840_block_0
  test147840_block_1)
  (interval_append test147840 32 48 80
  test147840_block_2
  (interval_append test147840 48 64 80
  test147840_block_3
  test147840_block_4)))
  (interval_append test147840 80 112 160
  (interval_append test147840 80 96 112
  test147840_block_5
  test147840_block_6)
  (interval_append test147840 112 128 160
  test147840_block_7
  (interval_append test147840 128 144 160
  test147840_block_8
  test147840_block_9))))
  (interval_append test147840 160 240 320
  (interval_append test147840 160 192 240
  (interval_append test147840 160 176 192
  test147840_block_10
  test147840_block_11)
  (interval_append test147840 192 208 240
  test147840_block_12
  (interval_append test147840 208 224 240
  test147840_block_13
  test147840_block_14)))
  (interval_append test147840 240 272 320
  (interval_append test147840 240 256 272
  test147840_block_15
  test147840_block_16)
  (interval_append test147840 272 288 320
  test147840_block_17
  (interval_append test147840 288 304 320
  test147840_block_18
  test147840_block_19)))))
  (interval_append test147840 320 480 640
  (interval_append test147840 320 400 480
  (interval_append test147840 320 352 400
  (interval_append test147840 320 336 352
  test147840_block_20
  test147840_block_21)
  (interval_append test147840 352 368 400
  test147840_block_22
  (interval_append test147840 368 384 400
  test147840_block_23
  test147840_block_24)))
  (interval_append test147840 400 432 480
  (interval_append test147840 400 416 432
  test147840_block_25
  test147840_block_26)
  (interval_append test147840 432 448 480
  test147840_block_27
  (interval_append test147840 448 464 480
  test147840_block_28
  test147840_block_29))))
  (interval_append test147840 480 560 640
  (interval_append test147840 480 512 560
  (interval_append test147840 480 496 512
  test147840_block_30
  test147840_block_31)
  (interval_append test147840 512 528 560
  test147840_block_32
  (interval_append test147840 528 544 560
  test147840_block_33
  test147840_block_34)))
  (interval_append test147840 560 592 640
  (interval_append test147840 560 576 592
  test147840_block_35
  test147840_block_36)
  (interval_append test147840 592 608 640
  test147840_block_37
  (interval_append test147840 608 624 640
  test147840_block_38
  test147840_block_39))))))
cert_nodeInterval_3 147840 148480
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
cert_test_11 148480
cert_test_block_3 148480 0 0 16 16
cert_test_block_3 148480 1 16 32 16
cert_test_block_3 148480 2 32 48 16
cert_test_block_3 148480 3 48 64 16
cert_test_block_3 148480 4 64 80 16
cert_test_block_3 148480 5 80 96 16
cert_test_block_3 148480 6 96 112 16
cert_test_block_3 148480 7 112 128 16
cert_test_block_3 148480 8 128 144 16
cert_test_block_3 148480 9 144 160 16
cert_test_block_3 148480 10 160 176 16
cert_test_block_3 148480 11 176 192 16
cert_test_block_3 148480 12 192 208 16
cert_test_block_3 148480 13 208 224 16
cert_test_block_3 148480 14 224 240 16
cert_test_block_3 148480 15 240 256 16
cert_test_block_3 148480 16 256 272 16
cert_test_block_3 148480 17 272 288 16
cert_test_block_3 148480 18 288 304 16
cert_test_block_3 148480 19 304 320 16
cert_test_block_3 148480 20 320 336 16
cert_test_block_3 148480 21 336 352 16
cert_test_block_3 148480 22 352 368 16
cert_test_block_3 148480 23 368 384 16
cert_test_block_3 148480 24 384 400 16
cert_test_block_3 148480 25 400 416 16
cert_test_block_3 148480 26 416 432 16
cert_test_block_3 148480 27 432 448 16
cert_test_block_3 148480 28 448 464 16
cert_test_block_3 148480 29 464 480 16
cert_test_block_3 148480 30 480 496 16
cert_test_block_3 148480 31 496 512 16
cert_test_block_3 148480 32 512 528 16
cert_test_block_3 148480 33 528 544 16
cert_test_block_3 148480 34 544 560 16
cert_test_block_3 148480 35 560 576 16
cert_test_block_3 148480 36 576 592 16
cert_test_block_3 148480 37 592 608 16
cert_test_block_3 148480 38 608 624 16
cert_test_block_3 148480 39 624 640 16
theorem test148480_complete : Interval test148480 0 640 :=
  (interval_append test148480 0 320 640
  (interval_append test148480 0 160 320
  (interval_append test148480 0 80 160
  (interval_append test148480 0 32 80
  (interval_append test148480 0 16 32
  test148480_block_0
  test148480_block_1)
  (interval_append test148480 32 48 80
  test148480_block_2
  (interval_append test148480 48 64 80
  test148480_block_3
  test148480_block_4)))
  (interval_append test148480 80 112 160
  (interval_append test148480 80 96 112
  test148480_block_5
  test148480_block_6)
  (interval_append test148480 112 128 160
  test148480_block_7
  (interval_append test148480 128 144 160
  test148480_block_8
  test148480_block_9))))
  (interval_append test148480 160 240 320
  (interval_append test148480 160 192 240
  (interval_append test148480 160 176 192
  test148480_block_10
  test148480_block_11)
  (interval_append test148480 192 208 240
  test148480_block_12
  (interval_append test148480 208 224 240
  test148480_block_13
  test148480_block_14)))
  (interval_append test148480 240 272 320
  (interval_append test148480 240 256 272
  test148480_block_15
  test148480_block_16)
  (interval_append test148480 272 288 320
  test148480_block_17
  (interval_append test148480 288 304 320
  test148480_block_18
  test148480_block_19)))))
  (interval_append test148480 320 480 640
  (interval_append test148480 320 400 480
  (interval_append test148480 320 352 400
  (interval_append test148480 320 336 352
  test148480_block_20
  test148480_block_21)
  (interval_append test148480 352 368 400
  test148480_block_22
  (interval_append test148480 368 384 400
  test148480_block_23
  test148480_block_24)))
  (interval_append test148480 400 432 480
  (interval_append test148480 400 416 432
  test148480_block_25
  test148480_block_26)
  (interval_append test148480 432 448 480
  test148480_block_27
  (interval_append test148480 448 464 480
  test148480_block_28
  test148480_block_29))))
  (interval_append test148480 480 560 640
  (interval_append test148480 480 512 560
  (interval_append test148480 480 496 512
  test148480_block_30
  test148480_block_31)
  (interval_append test148480 512 528 560
  test148480_block_32
  (interval_append test148480 528 544 560
  test148480_block_33
  test148480_block_34)))
  (interval_append test148480 560 592 640
  (interval_append test148480 560 576 592
  test148480_block_35
  test148480_block_36)
  (interval_append test148480 592 608 640
  test148480_block_37
  (interval_append test148480 608 624 640
  test148480_block_38
  test148480_block_39))))))
cert_nodeInterval_3 148480 149120
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
cert_test_11 149120
cert_test_block_3 149120 0 0 16 16
cert_test_block_3 149120 1 16 32 16
cert_test_block_3 149120 2 32 48 16
cert_test_block_3 149120 3 48 64 16
cert_test_block_3 149120 4 64 80 16
cert_test_block_3 149120 5 80 96 16
cert_test_block_3 149120 6 96 112 16
cert_test_block_3 149120 7 112 128 16
cert_test_block_3 149120 8 128 144 16
cert_test_block_3 149120 9 144 160 16
cert_test_block_3 149120 10 160 176 16
cert_test_block_3 149120 11 176 192 16
cert_test_block_3 149120 12 192 208 16
cert_test_block_3 149120 13 208 224 16
cert_test_block_3 149120 14 224 240 16
cert_test_block_3 149120 15 240 256 16
cert_test_block_3 149120 16 256 272 16
cert_test_block_3 149120 17 272 288 16
cert_test_block_3 149120 18 288 304 16
cert_test_block_3 149120 19 304 320 16
cert_test_block_3 149120 20 320 336 16
cert_test_block_3 149120 21 336 352 16
cert_test_block_3 149120 22 352 368 16
cert_test_block_3 149120 23 368 384 16
cert_test_block_3 149120 24 384 400 16
cert_test_block_3 149120 25 400 416 16
cert_test_block_3 149120 26 416 432 16
cert_test_block_3 149120 27 432 448 16
cert_test_block_3 149120 28 448 464 16
cert_test_block_3 149120 29 464 480 16
cert_test_block_3 149120 30 480 496 16
cert_test_block_3 149120 31 496 512 16
cert_test_block_3 149120 32 512 528 16
cert_test_block_3 149120 33 528 544 16
cert_test_block_3 149120 34 544 560 16
cert_test_block_3 149120 35 560 576 16
cert_test_block_3 149120 36 576 592 16
cert_test_block_3 149120 37 592 608 16
cert_test_block_3 149120 38 608 624 16
cert_test_block_3 149120 39 624 640 16
theorem test149120_complete : Interval test149120 0 640 :=
  (interval_append test149120 0 320 640
  (interval_append test149120 0 160 320
  (interval_append test149120 0 80 160
  (interval_append test149120 0 32 80
  (interval_append test149120 0 16 32
  test149120_block_0
  test149120_block_1)
  (interval_append test149120 32 48 80
  test149120_block_2
  (interval_append test149120 48 64 80
  test149120_block_3
  test149120_block_4)))
  (interval_append test149120 80 112 160
  (interval_append test149120 80 96 112
  test149120_block_5
  test149120_block_6)
  (interval_append test149120 112 128 160
  test149120_block_7
  (interval_append test149120 128 144 160
  test149120_block_8
  test149120_block_9))))
  (interval_append test149120 160 240 320
  (interval_append test149120 160 192 240
  (interval_append test149120 160 176 192
  test149120_block_10
  test149120_block_11)
  (interval_append test149120 192 208 240
  test149120_block_12
  (interval_append test149120 208 224 240
  test149120_block_13
  test149120_block_14)))
  (interval_append test149120 240 272 320
  (interval_append test149120 240 256 272
  test149120_block_15
  test149120_block_16)
  (interval_append test149120 272 288 320
  test149120_block_17
  (interval_append test149120 288 304 320
  test149120_block_18
  test149120_block_19)))))
  (interval_append test149120 320 480 640
  (interval_append test149120 320 400 480
  (interval_append test149120 320 352 400
  (interval_append test149120 320 336 352
  test149120_block_20
  test149120_block_21)
  (interval_append test149120 352 368 400
  test149120_block_22
  (interval_append test149120 368 384 400
  test149120_block_23
  test149120_block_24)))
  (interval_append test149120 400 432 480
  (interval_append test149120 400 416 432
  test149120_block_25
  test149120_block_26)
  (interval_append test149120 432 448 480
  test149120_block_27
  (interval_append test149120 448 464 480
  test149120_block_28
  test149120_block_29))))
  (interval_append test149120 480 560 640
  (interval_append test149120 480 512 560
  (interval_append test149120 480 496 512
  test149120_block_30
  test149120_block_31)
  (interval_append test149120 512 528 560
  test149120_block_32
  (interval_append test149120 528 544 560
  test149120_block_33
  test149120_block_34)))
  (interval_append test149120 560 592 640
  (interval_append test149120 560 576 592
  test149120_block_35
  test149120_block_36)
  (interval_append test149120 592 608 640
  test149120_block_37
  (interval_append test149120 608 624 640
  test149120_block_38
  test149120_block_39))))))
cert_nodeInterval_3 149120 149760
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
cert_test_11 149760
cert_test_block_3 149760 0 0 16 16
cert_test_block_3 149760 1 16 32 16
cert_test_block_3 149760 2 32 48 16
cert_test_block_3 149760 3 48 64 16
cert_test_block_3 149760 4 64 80 16
cert_test_block_3 149760 5 80 96 16
cert_test_block_3 149760 6 96 112 16
cert_test_block_3 149760 7 112 128 16
cert_test_block_3 149760 8 128 144 16
cert_test_block_3 149760 9 144 160 16
cert_test_block_3 149760 10 160 176 16
cert_test_block_3 149760 11 176 192 16
cert_test_block_3 149760 12 192 208 16
cert_test_block_3 149760 13 208 224 16
cert_test_block_3 149760 14 224 240 16
cert_test_block_3 149760 15 240 256 16
cert_test_block_3 149760 16 256 272 16
cert_test_block_3 149760 17 272 288 16
cert_test_block_3 149760 18 288 304 16
cert_test_block_3 149760 19 304 320 16
cert_test_block_3 149760 20 320 336 16
cert_test_block_3 149760 21 336 352 16
cert_test_block_3 149760 22 352 368 16
cert_test_block_3 149760 23 368 384 16
cert_test_block_3 149760 24 384 400 16
cert_test_block_3 149760 25 400 416 16
cert_test_block_3 149760 26 416 432 16
cert_test_block_3 149760 27 432 448 16
cert_test_block_3 149760 28 448 464 16
cert_test_block_3 149760 29 464 480 16
cert_test_block_3 149760 30 480 496 16
cert_test_block_3 149760 31 496 512 16
cert_test_block_3 149760 32 512 528 16
cert_test_block_3 149760 33 528 544 16
cert_test_block_3 149760 34 544 560 16
cert_test_block_3 149760 35 560 576 16
cert_test_block_3 149760 36 576 592 16
cert_test_block_3 149760 37 592 608 16
cert_test_block_3 149760 38 608 624 16
cert_test_block_3 149760 39 624 640 16
theorem test149760_complete : Interval test149760 0 640 :=
  (interval_append test149760 0 320 640
  (interval_append test149760 0 160 320
  (interval_append test149760 0 80 160
  (interval_append test149760 0 32 80
  (interval_append test149760 0 16 32
  test149760_block_0
  test149760_block_1)
  (interval_append test149760 32 48 80
  test149760_block_2
  (interval_append test149760 48 64 80
  test149760_block_3
  test149760_block_4)))
  (interval_append test149760 80 112 160
  (interval_append test149760 80 96 112
  test149760_block_5
  test149760_block_6)
  (interval_append test149760 112 128 160
  test149760_block_7
  (interval_append test149760 128 144 160
  test149760_block_8
  test149760_block_9))))
  (interval_append test149760 160 240 320
  (interval_append test149760 160 192 240
  (interval_append test149760 160 176 192
  test149760_block_10
  test149760_block_11)
  (interval_append test149760 192 208 240
  test149760_block_12
  (interval_append test149760 208 224 240
  test149760_block_13
  test149760_block_14)))
  (interval_append test149760 240 272 320
  (interval_append test149760 240 256 272
  test149760_block_15
  test149760_block_16)
  (interval_append test149760 272 288 320
  test149760_block_17
  (interval_append test149760 288 304 320
  test149760_block_18
  test149760_block_19)))))
  (interval_append test149760 320 480 640
  (interval_append test149760 320 400 480
  (interval_append test149760 320 352 400
  (interval_append test149760 320 336 352
  test149760_block_20
  test149760_block_21)
  (interval_append test149760 352 368 400
  test149760_block_22
  (interval_append test149760 368 384 400
  test149760_block_23
  test149760_block_24)))
  (interval_append test149760 400 432 480
  (interval_append test149760 400 416 432
  test149760_block_25
  test149760_block_26)
  (interval_append test149760 432 448 480
  test149760_block_27
  (interval_append test149760 448 464 480
  test149760_block_28
  test149760_block_29))))
  (interval_append test149760 480 560 640
  (interval_append test149760 480 512 560
  (interval_append test149760 480 496 512
  test149760_block_30
  test149760_block_31)
  (interval_append test149760 512 528 560
  test149760_block_32
  (interval_append test149760 528 544 560
  test149760_block_33
  test149760_block_34)))
  (interval_append test149760 560 592 640
  (interval_append test149760 560 576 592
  test149760_block_35
  test149760_block_36)
  (interval_append test149760 592 608 640
  test149760_block_37
  (interval_append test149760 608 624 640
  test149760_block_38
  test149760_block_39))))))
cert_nodeInterval_3 149760 150400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
