module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0317Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 0
cert_test_block_3 0 0 0 16 16
cert_test_block_3 0 1 16 32 16
cert_test_block_3 0 2 32 48 16
cert_test_block_3 0 3 48 64 16
cert_test_block_3 0 4 64 80 16
cert_test_block_3 0 5 80 96 16
cert_test_block_3 0 6 96 112 16
cert_test_block_3 0 7 112 128 16
cert_test_block_3 0 8 128 144 16
cert_test_block_3 0 9 144 160 16
cert_test_block_3 0 10 160 176 16
cert_test_block_3 0 11 176 192 16
cert_test_block_3 0 12 192 208 16
cert_test_block_3 0 13 208 224 16
cert_test_block_3 0 14 224 240 16
cert_test_block_3 0 15 240 256 16
cert_test_block_3 0 16 256 272 16
cert_test_block_3 0 17 272 288 16
cert_test_block_3 0 18 288 304 16
cert_test_block_3 0 19 304 320 16
cert_test_block_3 0 20 320 336 16
cert_test_block_3 0 21 336 352 16
cert_test_block_3 0 22 352 368 16
cert_test_block_3 0 23 368 384 16
cert_test_block_3 0 24 384 400 16
cert_test_block_3 0 25 400 416 16
cert_test_block_3 0 26 416 432 16
cert_test_block_3 0 27 432 448 16
cert_test_block_3 0 28 448 464 16
cert_test_block_3 0 29 464 480 16
cert_test_block_3 0 30 480 496 16
cert_test_block_3 0 31 496 512 16
cert_test_block_3 0 32 512 528 16
cert_test_block_3 0 33 528 544 16
cert_test_block_3 0 34 544 560 16
cert_test_block_3 0 35 560 576 16
cert_test_block_3 0 36 576 592 16
cert_test_block_3 0 37 592 608 16
cert_test_block_3 0 38 608 624 16
cert_test_block_3 0 39 624 640 16
theorem test0_complete : Interval test0 0 640 :=
  (interval_append test0 0 320 640
  (interval_append test0 0 160 320
  (interval_append test0 0 80 160
  (interval_append test0 0 32 80
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 80
  test0_block_2
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)))
  (interval_append test0 80 112 160
  (interval_append test0 80 96 112
  test0_block_5
  test0_block_6)
  (interval_append test0 112 128 160
  test0_block_7
  (interval_append test0 128 144 160
  test0_block_8
  test0_block_9))))
  (interval_append test0 160 240 320
  (interval_append test0 160 192 240
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11)
  (interval_append test0 192 208 240
  test0_block_12
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14)))
  (interval_append test0 240 272 320
  (interval_append test0 240 256 272
  test0_block_15
  test0_block_16)
  (interval_append test0 272 288 320
  test0_block_17
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19)))))
  (interval_append test0 320 480 640
  (interval_append test0 320 400 480
  (interval_append test0 320 352 400
  (interval_append test0 320 336 352
  test0_block_20
  test0_block_21)
  (interval_append test0 352 368 400
  test0_block_22
  (interval_append test0 368 384 400
  test0_block_23
  test0_block_24)))
  (interval_append test0 400 432 480
  (interval_append test0 400 416 432
  test0_block_25
  test0_block_26)
  (interval_append test0 432 448 480
  test0_block_27
  (interval_append test0 448 464 480
  test0_block_28
  test0_block_29))))
  (interval_append test0 480 560 640
  (interval_append test0 480 512 560
  (interval_append test0 480 496 512
  test0_block_30
  test0_block_31)
  (interval_append test0 512 528 560
  test0_block_32
  (interval_append test0 528 544 560
  test0_block_33
  test0_block_34)))
  (interval_append test0 560 592 640
  (interval_append test0 560 576 592
  test0_block_35
  test0_block_36)
  (interval_append test0 592 608 640
  test0_block_37
  (interval_append test0 608 624 640
  test0_block_38
  test0_block_39))))))
cert_nodeInterval_3 0 640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 640
cert_test_block_3 640 0 0 16 16
cert_test_block_3 640 1 16 32 16
cert_test_block_3 640 2 32 48 16
cert_test_block_3 640 3 48 64 16
cert_test_block_3 640 4 64 80 16
cert_test_block_3 640 5 80 96 16
cert_test_block_3 640 6 96 112 16
cert_test_block_3 640 7 112 128 16
cert_test_block_3 640 8 128 144 16
cert_test_block_3 640 9 144 160 16
cert_test_block_3 640 10 160 176 16
cert_test_block_3 640 11 176 192 16
cert_test_block_3 640 12 192 208 16
cert_test_block_3 640 13 208 224 16
cert_test_block_3 640 14 224 240 16
cert_test_block_3 640 15 240 256 16
cert_test_block_3 640 16 256 272 16
cert_test_block_3 640 17 272 288 16
cert_test_block_3 640 18 288 304 16
cert_test_block_3 640 19 304 320 16
cert_test_block_3 640 20 320 336 16
cert_test_block_3 640 21 336 352 16
cert_test_block_3 640 22 352 368 16
cert_test_block_3 640 23 368 384 16
cert_test_block_3 640 24 384 400 16
cert_test_block_3 640 25 400 416 16
cert_test_block_3 640 26 416 432 16
cert_test_block_3 640 27 432 448 16
cert_test_block_3 640 28 448 464 16
cert_test_block_3 640 29 464 480 16
cert_test_block_3 640 30 480 496 16
cert_test_block_3 640 31 496 512 16
cert_test_block_3 640 32 512 528 16
cert_test_block_3 640 33 528 544 16
cert_test_block_3 640 34 544 560 16
cert_test_block_3 640 35 560 576 16
cert_test_block_3 640 36 576 592 16
cert_test_block_3 640 37 592 608 16
cert_test_block_3 640 38 608 624 16
cert_test_block_3 640 39 624 640 16
theorem test640_complete : Interval test640 0 640 :=
  (interval_append test640 0 320 640
  (interval_append test640 0 160 320
  (interval_append test640 0 80 160
  (interval_append test640 0 32 80
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 80
  test640_block_2
  (interval_append test640 48 64 80
  test640_block_3
  test640_block_4)))
  (interval_append test640 80 112 160
  (interval_append test640 80 96 112
  test640_block_5
  test640_block_6)
  (interval_append test640 112 128 160
  test640_block_7
  (interval_append test640 128 144 160
  test640_block_8
  test640_block_9))))
  (interval_append test640 160 240 320
  (interval_append test640 160 192 240
  (interval_append test640 160 176 192
  test640_block_10
  test640_block_11)
  (interval_append test640 192 208 240
  test640_block_12
  (interval_append test640 208 224 240
  test640_block_13
  test640_block_14)))
  (interval_append test640 240 272 320
  (interval_append test640 240 256 272
  test640_block_15
  test640_block_16)
  (interval_append test640 272 288 320
  test640_block_17
  (interval_append test640 288 304 320
  test640_block_18
  test640_block_19)))))
  (interval_append test640 320 480 640
  (interval_append test640 320 400 480
  (interval_append test640 320 352 400
  (interval_append test640 320 336 352
  test640_block_20
  test640_block_21)
  (interval_append test640 352 368 400
  test640_block_22
  (interval_append test640 368 384 400
  test640_block_23
  test640_block_24)))
  (interval_append test640 400 432 480
  (interval_append test640 400 416 432
  test640_block_25
  test640_block_26)
  (interval_append test640 432 448 480
  test640_block_27
  (interval_append test640 448 464 480
  test640_block_28
  test640_block_29))))
  (interval_append test640 480 560 640
  (interval_append test640 480 512 560
  (interval_append test640 480 496 512
  test640_block_30
  test640_block_31)
  (interval_append test640 512 528 560
  test640_block_32
  (interval_append test640 528 544 560
  test640_block_33
  test640_block_34)))
  (interval_append test640 560 592 640
  (interval_append test640 560 576 592
  test640_block_35
  test640_block_36)
  (interval_append test640 592 608 640
  test640_block_37
  (interval_append test640 608 624 640
  test640_block_38
  test640_block_39))))))
cert_nodeInterval_3 640 1280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1280
cert_test_block_3 1280 0 0 16 16
cert_test_block_3 1280 1 16 32 16
cert_test_block_3 1280 2 32 48 16
cert_test_block_3 1280 3 48 64 16
cert_test_block_3 1280 4 64 80 16
cert_test_block_3 1280 5 80 96 16
cert_test_block_3 1280 6 96 112 16
cert_test_block_3 1280 7 112 128 16
cert_test_block_3 1280 8 128 144 16
cert_test_block_3 1280 9 144 160 16
cert_test_block_3 1280 10 160 176 16
cert_test_block_3 1280 11 176 192 16
cert_test_block_3 1280 12 192 208 16
cert_test_block_3 1280 13 208 224 16
cert_test_block_3 1280 14 224 240 16
cert_test_block_3 1280 15 240 256 16
cert_test_block_3 1280 16 256 272 16
cert_test_block_3 1280 17 272 288 16
cert_test_block_3 1280 18 288 304 16
cert_test_block_3 1280 19 304 320 16
cert_test_block_3 1280 20 320 336 16
cert_test_block_3 1280 21 336 352 16
cert_test_block_3 1280 22 352 368 16
cert_test_block_3 1280 23 368 384 16
cert_test_block_3 1280 24 384 400 16
cert_test_block_3 1280 25 400 416 16
cert_test_block_3 1280 26 416 432 16
cert_test_block_3 1280 27 432 448 16
cert_test_block_3 1280 28 448 464 16
cert_test_block_3 1280 29 464 480 16
cert_test_block_3 1280 30 480 496 16
cert_test_block_3 1280 31 496 512 16
cert_test_block_3 1280 32 512 528 16
cert_test_block_3 1280 33 528 544 16
cert_test_block_3 1280 34 544 560 16
cert_test_block_3 1280 35 560 576 16
cert_test_block_3 1280 36 576 592 16
cert_test_block_3 1280 37 592 608 16
cert_test_block_3 1280 38 608 624 16
cert_test_block_3 1280 39 624 640 16
theorem test1280_complete : Interval test1280 0 640 :=
  (interval_append test1280 0 320 640
  (interval_append test1280 0 160 320
  (interval_append test1280 0 80 160
  (interval_append test1280 0 32 80
  (interval_append test1280 0 16 32
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 32 48 80
  test1280_block_2
  (interval_append test1280 48 64 80
  test1280_block_3
  test1280_block_4)))
  (interval_append test1280 80 112 160
  (interval_append test1280 80 96 112
  test1280_block_5
  test1280_block_6)
  (interval_append test1280 112 128 160
  test1280_block_7
  (interval_append test1280 128 144 160
  test1280_block_8
  test1280_block_9))))
  (interval_append test1280 160 240 320
  (interval_append test1280 160 192 240
  (interval_append test1280 160 176 192
  test1280_block_10
  test1280_block_11)
  (interval_append test1280 192 208 240
  test1280_block_12
  (interval_append test1280 208 224 240
  test1280_block_13
  test1280_block_14)))
  (interval_append test1280 240 272 320
  (interval_append test1280 240 256 272
  test1280_block_15
  test1280_block_16)
  (interval_append test1280 272 288 320
  test1280_block_17
  (interval_append test1280 288 304 320
  test1280_block_18
  test1280_block_19)))))
  (interval_append test1280 320 480 640
  (interval_append test1280 320 400 480
  (interval_append test1280 320 352 400
  (interval_append test1280 320 336 352
  test1280_block_20
  test1280_block_21)
  (interval_append test1280 352 368 400
  test1280_block_22
  (interval_append test1280 368 384 400
  test1280_block_23
  test1280_block_24)))
  (interval_append test1280 400 432 480
  (interval_append test1280 400 416 432
  test1280_block_25
  test1280_block_26)
  (interval_append test1280 432 448 480
  test1280_block_27
  (interval_append test1280 448 464 480
  test1280_block_28
  test1280_block_29))))
  (interval_append test1280 480 560 640
  (interval_append test1280 480 512 560
  (interval_append test1280 480 496 512
  test1280_block_30
  test1280_block_31)
  (interval_append test1280 512 528 560
  test1280_block_32
  (interval_append test1280 528 544 560
  test1280_block_33
  test1280_block_34)))
  (interval_append test1280 560 592 640
  (interval_append test1280 560 576 592
  test1280_block_35
  test1280_block_36)
  (interval_append test1280 592 608 640
  test1280_block_37
  (interval_append test1280 608 624 640
  test1280_block_38
  test1280_block_39))))))
cert_nodeInterval_3 1280 1920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1920
cert_test_block_3 1920 0 0 16 16
cert_test_block_3 1920 1 16 32 16
cert_test_block_3 1920 2 32 48 16
cert_test_block_3 1920 3 48 64 16
cert_test_block_3 1920 4 64 80 16
cert_test_block_3 1920 5 80 96 16
cert_test_block_3 1920 6 96 112 16
cert_test_block_3 1920 7 112 128 16
cert_test_block_3 1920 8 128 144 16
cert_test_block_3 1920 9 144 160 16
cert_test_block_3 1920 10 160 176 16
cert_test_block_3 1920 11 176 192 16
cert_test_block_3 1920 12 192 208 16
cert_test_block_3 1920 13 208 224 16
cert_test_block_3 1920 14 224 240 16
cert_test_block_3 1920 15 240 256 16
cert_test_block_3 1920 16 256 272 16
cert_test_block_3 1920 17 272 288 16
cert_test_block_3 1920 18 288 304 16
cert_test_block_3 1920 19 304 320 16
cert_test_block_3 1920 20 320 336 16
cert_test_block_3 1920 21 336 352 16
cert_test_block_3 1920 22 352 368 16
cert_test_block_3 1920 23 368 384 16
cert_test_block_3 1920 24 384 400 16
cert_test_block_3 1920 25 400 416 16
cert_test_block_3 1920 26 416 432 16
cert_test_block_3 1920 27 432 448 16
cert_test_block_3 1920 28 448 464 16
cert_test_block_3 1920 29 464 480 16
cert_test_block_3 1920 30 480 496 16
cert_test_block_3 1920 31 496 512 16
cert_test_block_3 1920 32 512 528 16
cert_test_block_3 1920 33 528 544 16
cert_test_block_3 1920 34 544 560 16
cert_test_block_3 1920 35 560 576 16
cert_test_block_3 1920 36 576 592 16
cert_test_block_3 1920 37 592 608 16
cert_test_block_3 1920 38 608 624 16
cert_test_block_3 1920 39 624 640 16
theorem test1920_complete : Interval test1920 0 640 :=
  (interval_append test1920 0 320 640
  (interval_append test1920 0 160 320
  (interval_append test1920 0 80 160
  (interval_append test1920 0 32 80
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 80
  test1920_block_2
  (interval_append test1920 48 64 80
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 80 112 160
  (interval_append test1920 80 96 112
  test1920_block_5
  test1920_block_6)
  (interval_append test1920 112 128 160
  test1920_block_7
  (interval_append test1920 128 144 160
  test1920_block_8
  test1920_block_9))))
  (interval_append test1920 160 240 320
  (interval_append test1920 160 192 240
  (interval_append test1920 160 176 192
  test1920_block_10
  test1920_block_11)
  (interval_append test1920 192 208 240
  test1920_block_12
  (interval_append test1920 208 224 240
  test1920_block_13
  test1920_block_14)))
  (interval_append test1920 240 272 320
  (interval_append test1920 240 256 272
  test1920_block_15
  test1920_block_16)
  (interval_append test1920 272 288 320
  test1920_block_17
  (interval_append test1920 288 304 320
  test1920_block_18
  test1920_block_19)))))
  (interval_append test1920 320 480 640
  (interval_append test1920 320 400 480
  (interval_append test1920 320 352 400
  (interval_append test1920 320 336 352
  test1920_block_20
  test1920_block_21)
  (interval_append test1920 352 368 400
  test1920_block_22
  (interval_append test1920 368 384 400
  test1920_block_23
  test1920_block_24)))
  (interval_append test1920 400 432 480
  (interval_append test1920 400 416 432
  test1920_block_25
  test1920_block_26)
  (interval_append test1920 432 448 480
  test1920_block_27
  (interval_append test1920 448 464 480
  test1920_block_28
  test1920_block_29))))
  (interval_append test1920 480 560 640
  (interval_append test1920 480 512 560
  (interval_append test1920 480 496 512
  test1920_block_30
  test1920_block_31)
  (interval_append test1920 512 528 560
  test1920_block_32
  (interval_append test1920 528 544 560
  test1920_block_33
  test1920_block_34)))
  (interval_append test1920 560 592 640
  (interval_append test1920 560 576 592
  test1920_block_35
  test1920_block_36)
  (interval_append test1920 592 608 640
  test1920_block_37
  (interval_append test1920 608 624 640
  test1920_block_38
  test1920_block_39))))))
cert_nodeInterval_3 1920 2560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 2560
cert_test_block_3 2560 0 0 16 16
cert_test_block_3 2560 1 16 32 16
cert_test_block_3 2560 2 32 48 16
cert_test_block_3 2560 3 48 64 16
cert_test_block_3 2560 4 64 80 16
cert_test_block_3 2560 5 80 96 16
cert_test_block_3 2560 6 96 112 16
cert_test_block_3 2560 7 112 128 16
cert_test_block_3 2560 8 128 144 16
cert_test_block_3 2560 9 144 160 16
cert_test_block_3 2560 10 160 176 16
cert_test_block_3 2560 11 176 192 16
cert_test_block_3 2560 12 192 208 16
cert_test_block_3 2560 13 208 224 16
cert_test_block_3 2560 14 224 240 16
cert_test_block_3 2560 15 240 256 16
cert_test_block_3 2560 16 256 272 16
cert_test_block_3 2560 17 272 288 16
cert_test_block_3 2560 18 288 304 16
cert_test_block_3 2560 19 304 320 16
cert_test_block_3 2560 20 320 336 16
cert_test_block_3 2560 21 336 352 16
cert_test_block_3 2560 22 352 368 16
cert_test_block_3 2560 23 368 384 16
cert_test_block_3 2560 24 384 400 16
cert_test_block_3 2560 25 400 416 16
cert_test_block_3 2560 26 416 432 16
cert_test_block_3 2560 27 432 448 16
cert_test_block_3 2560 28 448 464 16
cert_test_block_3 2560 29 464 480 16
cert_test_block_3 2560 30 480 496 16
cert_test_block_3 2560 31 496 512 16
cert_test_block_3 2560 32 512 528 16
cert_test_block_3 2560 33 528 544 16
cert_test_block_3 2560 34 544 560 16
cert_test_block_3 2560 35 560 576 16
cert_test_block_3 2560 36 576 592 16
cert_test_block_3 2560 37 592 608 16
cert_test_block_3 2560 38 608 624 16
cert_test_block_3 2560 39 624 640 16
theorem test2560_complete : Interval test2560 0 640 :=
  (interval_append test2560 0 320 640
  (interval_append test2560 0 160 320
  (interval_append test2560 0 80 160
  (interval_append test2560 0 32 80
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 80
  test2560_block_2
  (interval_append test2560 48 64 80
  test2560_block_3
  test2560_block_4)))
  (interval_append test2560 80 112 160
  (interval_append test2560 80 96 112
  test2560_block_5
  test2560_block_6)
  (interval_append test2560 112 128 160
  test2560_block_7
  (interval_append test2560 128 144 160
  test2560_block_8
  test2560_block_9))))
  (interval_append test2560 160 240 320
  (interval_append test2560 160 192 240
  (interval_append test2560 160 176 192
  test2560_block_10
  test2560_block_11)
  (interval_append test2560 192 208 240
  test2560_block_12
  (interval_append test2560 208 224 240
  test2560_block_13
  test2560_block_14)))
  (interval_append test2560 240 272 320
  (interval_append test2560 240 256 272
  test2560_block_15
  test2560_block_16)
  (interval_append test2560 272 288 320
  test2560_block_17
  (interval_append test2560 288 304 320
  test2560_block_18
  test2560_block_19)))))
  (interval_append test2560 320 480 640
  (interval_append test2560 320 400 480
  (interval_append test2560 320 352 400
  (interval_append test2560 320 336 352
  test2560_block_20
  test2560_block_21)
  (interval_append test2560 352 368 400
  test2560_block_22
  (interval_append test2560 368 384 400
  test2560_block_23
  test2560_block_24)))
  (interval_append test2560 400 432 480
  (interval_append test2560 400 416 432
  test2560_block_25
  test2560_block_26)
  (interval_append test2560 432 448 480
  test2560_block_27
  (interval_append test2560 448 464 480
  test2560_block_28
  test2560_block_29))))
  (interval_append test2560 480 560 640
  (interval_append test2560 480 512 560
  (interval_append test2560 480 496 512
  test2560_block_30
  test2560_block_31)
  (interval_append test2560 512 528 560
  test2560_block_32
  (interval_append test2560 528 544 560
  test2560_block_33
  test2560_block_34)))
  (interval_append test2560 560 592 640
  (interval_append test2560 560 576 592
  test2560_block_35
  test2560_block_36)
  (interval_append test2560 592 608 640
  test2560_block_37
  (interval_append test2560 608 624 640
  test2560_block_38
  test2560_block_39))))))
cert_nodeInterval_3 2560 3200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3200
cert_test_block_3 3200 0 0 16 16
cert_test_block_3 3200 1 16 32 16
cert_test_block_3 3200 2 32 48 16
cert_test_block_3 3200 3 48 64 16
cert_test_block_3 3200 4 64 80 16
cert_test_block_3 3200 5 80 96 16
cert_test_block_3 3200 6 96 112 16
cert_test_block_3 3200 7 112 128 16
cert_test_block_3 3200 8 128 144 16
cert_test_block_3 3200 9 144 160 16
cert_test_block_3 3200 10 160 176 16
cert_test_block_3 3200 11 176 192 16
cert_test_block_3 3200 12 192 208 16
cert_test_block_3 3200 13 208 224 16
cert_test_block_3 3200 14 224 240 16
cert_test_block_3 3200 15 240 256 16
cert_test_block_3 3200 16 256 272 16
cert_test_block_3 3200 17 272 288 16
cert_test_block_3 3200 18 288 304 16
cert_test_block_3 3200 19 304 320 16
cert_test_block_3 3200 20 320 336 16
cert_test_block_3 3200 21 336 352 16
cert_test_block_3 3200 22 352 368 16
cert_test_block_3 3200 23 368 384 16
cert_test_block_3 3200 24 384 400 16
cert_test_block_3 3200 25 400 416 16
cert_test_block_3 3200 26 416 432 16
cert_test_block_3 3200 27 432 448 16
cert_test_block_3 3200 28 448 464 16
cert_test_block_3 3200 29 464 480 16
cert_test_block_3 3200 30 480 496 16
cert_test_block_3 3200 31 496 512 16
cert_test_block_3 3200 32 512 528 16
cert_test_block_3 3200 33 528 544 16
cert_test_block_3 3200 34 544 560 16
cert_test_block_3 3200 35 560 576 16
cert_test_block_3 3200 36 576 592 16
cert_test_block_3 3200 37 592 608 16
cert_test_block_3 3200 38 608 624 16
cert_test_block_3 3200 39 624 640 16
theorem test3200_complete : Interval test3200 0 640 :=
  (interval_append test3200 0 320 640
  (interval_append test3200 0 160 320
  (interval_append test3200 0 80 160
  (interval_append test3200 0 32 80
  (interval_append test3200 0 16 32
  test3200_block_0
  test3200_block_1)
  (interval_append test3200 32 48 80
  test3200_block_2
  (interval_append test3200 48 64 80
  test3200_block_3
  test3200_block_4)))
  (interval_append test3200 80 112 160
  (interval_append test3200 80 96 112
  test3200_block_5
  test3200_block_6)
  (interval_append test3200 112 128 160
  test3200_block_7
  (interval_append test3200 128 144 160
  test3200_block_8
  test3200_block_9))))
  (interval_append test3200 160 240 320
  (interval_append test3200 160 192 240
  (interval_append test3200 160 176 192
  test3200_block_10
  test3200_block_11)
  (interval_append test3200 192 208 240
  test3200_block_12
  (interval_append test3200 208 224 240
  test3200_block_13
  test3200_block_14)))
  (interval_append test3200 240 272 320
  (interval_append test3200 240 256 272
  test3200_block_15
  test3200_block_16)
  (interval_append test3200 272 288 320
  test3200_block_17
  (interval_append test3200 288 304 320
  test3200_block_18
  test3200_block_19)))))
  (interval_append test3200 320 480 640
  (interval_append test3200 320 400 480
  (interval_append test3200 320 352 400
  (interval_append test3200 320 336 352
  test3200_block_20
  test3200_block_21)
  (interval_append test3200 352 368 400
  test3200_block_22
  (interval_append test3200 368 384 400
  test3200_block_23
  test3200_block_24)))
  (interval_append test3200 400 432 480
  (interval_append test3200 400 416 432
  test3200_block_25
  test3200_block_26)
  (interval_append test3200 432 448 480
  test3200_block_27
  (interval_append test3200 448 464 480
  test3200_block_28
  test3200_block_29))))
  (interval_append test3200 480 560 640
  (interval_append test3200 480 512 560
  (interval_append test3200 480 496 512
  test3200_block_30
  test3200_block_31)
  (interval_append test3200 512 528 560
  test3200_block_32
  (interval_append test3200 528 544 560
  test3200_block_33
  test3200_block_34)))
  (interval_append test3200 560 592 640
  (interval_append test3200 560 576 592
  test3200_block_35
  test3200_block_36)
  (interval_append test3200 592 608 640
  test3200_block_37
  (interval_append test3200 608 624 640
  test3200_block_38
  test3200_block_39))))))
cert_nodeInterval_3 3200 3840
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 3840
cert_test_block_3 3840 0 0 16 16
cert_test_block_3 3840 1 16 32 16
cert_test_block_3 3840 2 32 48 16
cert_test_block_3 3840 3 48 64 16
cert_test_block_3 3840 4 64 80 16
cert_test_block_3 3840 5 80 96 16
cert_test_block_3 3840 6 96 112 16
cert_test_block_3 3840 7 112 128 16
cert_test_block_3 3840 8 128 144 16
cert_test_block_3 3840 9 144 160 16
cert_test_block_3 3840 10 160 176 16
cert_test_block_3 3840 11 176 192 16
cert_test_block_3 3840 12 192 208 16
cert_test_block_3 3840 13 208 224 16
cert_test_block_3 3840 14 224 240 16
cert_test_block_3 3840 15 240 256 16
cert_test_block_3 3840 16 256 272 16
cert_test_block_3 3840 17 272 288 16
cert_test_block_3 3840 18 288 304 16
cert_test_block_3 3840 19 304 320 16
cert_test_block_3 3840 20 320 336 16
cert_test_block_3 3840 21 336 352 16
cert_test_block_3 3840 22 352 368 16
cert_test_block_3 3840 23 368 384 16
cert_test_block_3 3840 24 384 400 16
cert_test_block_3 3840 25 400 416 16
cert_test_block_3 3840 26 416 432 16
cert_test_block_3 3840 27 432 448 16
cert_test_block_3 3840 28 448 464 16
cert_test_block_3 3840 29 464 480 16
cert_test_block_3 3840 30 480 496 16
cert_test_block_3 3840 31 496 512 16
cert_test_block_3 3840 32 512 528 16
cert_test_block_3 3840 33 528 544 16
cert_test_block_3 3840 34 544 560 16
cert_test_block_3 3840 35 560 576 16
cert_test_block_3 3840 36 576 592 16
cert_test_block_3 3840 37 592 608 16
cert_test_block_3 3840 38 608 624 16
cert_test_block_3 3840 39 624 640 16
theorem test3840_complete : Interval test3840 0 640 :=
  (interval_append test3840 0 320 640
  (interval_append test3840 0 160 320
  (interval_append test3840 0 80 160
  (interval_append test3840 0 32 80
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 80
  test3840_block_2
  (interval_append test3840 48 64 80
  test3840_block_3
  test3840_block_4)))
  (interval_append test3840 80 112 160
  (interval_append test3840 80 96 112
  test3840_block_5
  test3840_block_6)
  (interval_append test3840 112 128 160
  test3840_block_7
  (interval_append test3840 128 144 160
  test3840_block_8
  test3840_block_9))))
  (interval_append test3840 160 240 320
  (interval_append test3840 160 192 240
  (interval_append test3840 160 176 192
  test3840_block_10
  test3840_block_11)
  (interval_append test3840 192 208 240
  test3840_block_12
  (interval_append test3840 208 224 240
  test3840_block_13
  test3840_block_14)))
  (interval_append test3840 240 272 320
  (interval_append test3840 240 256 272
  test3840_block_15
  test3840_block_16)
  (interval_append test3840 272 288 320
  test3840_block_17
  (interval_append test3840 288 304 320
  test3840_block_18
  test3840_block_19)))))
  (interval_append test3840 320 480 640
  (interval_append test3840 320 400 480
  (interval_append test3840 320 352 400
  (interval_append test3840 320 336 352
  test3840_block_20
  test3840_block_21)
  (interval_append test3840 352 368 400
  test3840_block_22
  (interval_append test3840 368 384 400
  test3840_block_23
  test3840_block_24)))
  (interval_append test3840 400 432 480
  (interval_append test3840 400 416 432
  test3840_block_25
  test3840_block_26)
  (interval_append test3840 432 448 480
  test3840_block_27
  (interval_append test3840 448 464 480
  test3840_block_28
  test3840_block_29))))
  (interval_append test3840 480 560 640
  (interval_append test3840 480 512 560
  (interval_append test3840 480 496 512
  test3840_block_30
  test3840_block_31)
  (interval_append test3840 512 528 560
  test3840_block_32
  (interval_append test3840 528 544 560
  test3840_block_33
  test3840_block_34)))
  (interval_append test3840 560 592 640
  (interval_append test3840 560 576 592
  test3840_block_35
  test3840_block_36)
  (interval_append test3840 592 608 640
  test3840_block_37
  (interval_append test3840 608 624 640
  test3840_block_38
  test3840_block_39))))))
cert_nodeInterval_3 3840 4480
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 4480
cert_test_block_3 4480 0 0 16 16
cert_test_block_3 4480 1 16 32 16
cert_test_block_3 4480 2 32 48 16
cert_test_block_3 4480 3 48 64 16
cert_test_block_3 4480 4 64 80 16
cert_test_block_3 4480 5 80 96 16
cert_test_block_3 4480 6 96 112 16
cert_test_block_3 4480 7 112 128 16
cert_test_block_3 4480 8 128 144 16
cert_test_block_3 4480 9 144 160 16
cert_test_block_3 4480 10 160 176 16
cert_test_block_3 4480 11 176 192 16
cert_test_block_3 4480 12 192 208 16
cert_test_block_3 4480 13 208 224 16
cert_test_block_3 4480 14 224 240 16
cert_test_block_3 4480 15 240 256 16
cert_test_block_3 4480 16 256 272 16
cert_test_block_3 4480 17 272 288 16
cert_test_block_3 4480 18 288 304 16
cert_test_block_3 4480 19 304 320 16
cert_test_block_3 4480 20 320 336 16
cert_test_block_3 4480 21 336 352 16
cert_test_block_3 4480 22 352 368 16
cert_test_block_3 4480 23 368 384 16
cert_test_block_3 4480 24 384 400 16
cert_test_block_3 4480 25 400 416 16
cert_test_block_3 4480 26 416 432 16
cert_test_block_3 4480 27 432 448 16
cert_test_block_3 4480 28 448 464 16
cert_test_block_3 4480 29 464 480 16
cert_test_block_3 4480 30 480 496 16
cert_test_block_3 4480 31 496 512 16
cert_test_block_3 4480 32 512 528 16
cert_test_block_3 4480 33 528 544 16
cert_test_block_3 4480 34 544 560 16
cert_test_block_3 4480 35 560 576 16
cert_test_block_3 4480 36 576 592 16
cert_test_block_3 4480 37 592 608 16
cert_test_block_3 4480 38 608 624 16
cert_test_block_3 4480 39 624 640 16
theorem test4480_complete : Interval test4480 0 640 :=
  (interval_append test4480 0 320 640
  (interval_append test4480 0 160 320
  (interval_append test4480 0 80 160
  (interval_append test4480 0 32 80
  (interval_append test4480 0 16 32
  test4480_block_0
  test4480_block_1)
  (interval_append test4480 32 48 80
  test4480_block_2
  (interval_append test4480 48 64 80
  test4480_block_3
  test4480_block_4)))
  (interval_append test4480 80 112 160
  (interval_append test4480 80 96 112
  test4480_block_5
  test4480_block_6)
  (interval_append test4480 112 128 160
  test4480_block_7
  (interval_append test4480 128 144 160
  test4480_block_8
  test4480_block_9))))
  (interval_append test4480 160 240 320
  (interval_append test4480 160 192 240
  (interval_append test4480 160 176 192
  test4480_block_10
  test4480_block_11)
  (interval_append test4480 192 208 240
  test4480_block_12
  (interval_append test4480 208 224 240
  test4480_block_13
  test4480_block_14)))
  (interval_append test4480 240 272 320
  (interval_append test4480 240 256 272
  test4480_block_15
  test4480_block_16)
  (interval_append test4480 272 288 320
  test4480_block_17
  (interval_append test4480 288 304 320
  test4480_block_18
  test4480_block_19)))))
  (interval_append test4480 320 480 640
  (interval_append test4480 320 400 480
  (interval_append test4480 320 352 400
  (interval_append test4480 320 336 352
  test4480_block_20
  test4480_block_21)
  (interval_append test4480 352 368 400
  test4480_block_22
  (interval_append test4480 368 384 400
  test4480_block_23
  test4480_block_24)))
  (interval_append test4480 400 432 480
  (interval_append test4480 400 416 432
  test4480_block_25
  test4480_block_26)
  (interval_append test4480 432 448 480
  test4480_block_27
  (interval_append test4480 448 464 480
  test4480_block_28
  test4480_block_29))))
  (interval_append test4480 480 560 640
  (interval_append test4480 480 512 560
  (interval_append test4480 480 496 512
  test4480_block_30
  test4480_block_31)
  (interval_append test4480 512 528 560
  test4480_block_32
  (interval_append test4480 528 544 560
  test4480_block_33
  test4480_block_34)))
  (interval_append test4480 560 592 640
  (interval_append test4480 560 576 592
  test4480_block_35
  test4480_block_36)
  (interval_append test4480 592 608 640
  test4480_block_37
  (interval_append test4480 608 624 640
  test4480_block_38
  test4480_block_39))))))
cert_nodeInterval_3 4480 5120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5120
cert_test_block_3 5120 0 0 16 16
cert_test_block_3 5120 1 16 32 16
cert_test_block_3 5120 2 32 48 16
cert_test_block_3 5120 3 48 64 16
cert_test_block_3 5120 4 64 80 16
cert_test_block_3 5120 5 80 96 16
cert_test_block_3 5120 6 96 112 16
cert_test_block_3 5120 7 112 128 16
cert_test_block_3 5120 8 128 144 16
cert_test_block_3 5120 9 144 160 16
cert_test_block_3 5120 10 160 176 16
cert_test_block_3 5120 11 176 192 16
cert_test_block_3 5120 12 192 208 16
cert_test_block_3 5120 13 208 224 16
cert_test_block_3 5120 14 224 240 16
cert_test_block_3 5120 15 240 256 16
cert_test_block_3 5120 16 256 272 16
cert_test_block_3 5120 17 272 288 16
cert_test_block_3 5120 18 288 304 16
cert_test_block_3 5120 19 304 320 16
cert_test_block_3 5120 20 320 336 16
cert_test_block_3 5120 21 336 352 16
cert_test_block_3 5120 22 352 368 16
cert_test_block_3 5120 23 368 384 16
cert_test_block_3 5120 24 384 400 16
cert_test_block_3 5120 25 400 416 16
cert_test_block_3 5120 26 416 432 16
cert_test_block_3 5120 27 432 448 16
cert_test_block_3 5120 28 448 464 16
cert_test_block_3 5120 29 464 480 16
cert_test_block_3 5120 30 480 496 16
cert_test_block_3 5120 31 496 512 16
cert_test_block_3 5120 32 512 528 16
cert_test_block_3 5120 33 528 544 16
cert_test_block_3 5120 34 544 560 16
cert_test_block_3 5120 35 560 576 16
cert_test_block_3 5120 36 576 592 16
cert_test_block_3 5120 37 592 608 16
cert_test_block_3 5120 38 608 624 16
cert_test_block_3 5120 39 624 640 16
theorem test5120_complete : Interval test5120 0 640 :=
  (interval_append test5120 0 320 640
  (interval_append test5120 0 160 320
  (interval_append test5120 0 80 160
  (interval_append test5120 0 32 80
  (interval_append test5120 0 16 32
  test5120_block_0
  test5120_block_1)
  (interval_append test5120 32 48 80
  test5120_block_2
  (interval_append test5120 48 64 80
  test5120_block_3
  test5120_block_4)))
  (interval_append test5120 80 112 160
  (interval_append test5120 80 96 112
  test5120_block_5
  test5120_block_6)
  (interval_append test5120 112 128 160
  test5120_block_7
  (interval_append test5120 128 144 160
  test5120_block_8
  test5120_block_9))))
  (interval_append test5120 160 240 320
  (interval_append test5120 160 192 240
  (interval_append test5120 160 176 192
  test5120_block_10
  test5120_block_11)
  (interval_append test5120 192 208 240
  test5120_block_12
  (interval_append test5120 208 224 240
  test5120_block_13
  test5120_block_14)))
  (interval_append test5120 240 272 320
  (interval_append test5120 240 256 272
  test5120_block_15
  test5120_block_16)
  (interval_append test5120 272 288 320
  test5120_block_17
  (interval_append test5120 288 304 320
  test5120_block_18
  test5120_block_19)))))
  (interval_append test5120 320 480 640
  (interval_append test5120 320 400 480
  (interval_append test5120 320 352 400
  (interval_append test5120 320 336 352
  test5120_block_20
  test5120_block_21)
  (interval_append test5120 352 368 400
  test5120_block_22
  (interval_append test5120 368 384 400
  test5120_block_23
  test5120_block_24)))
  (interval_append test5120 400 432 480
  (interval_append test5120 400 416 432
  test5120_block_25
  test5120_block_26)
  (interval_append test5120 432 448 480
  test5120_block_27
  (interval_append test5120 448 464 480
  test5120_block_28
  test5120_block_29))))
  (interval_append test5120 480 560 640
  (interval_append test5120 480 512 560
  (interval_append test5120 480 496 512
  test5120_block_30
  test5120_block_31)
  (interval_append test5120 512 528 560
  test5120_block_32
  (interval_append test5120 528 544 560
  test5120_block_33
  test5120_block_34)))
  (interval_append test5120 560 592 640
  (interval_append test5120 560 576 592
  test5120_block_35
  test5120_block_36)
  (interval_append test5120 592 608 640
  test5120_block_37
  (interval_append test5120 608 624 640
  test5120_block_38
  test5120_block_39))))))
cert_nodeInterval_3 5120 5760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 5760
cert_test_block_3 5760 0 0 16 16
cert_test_block_3 5760 1 16 32 16
cert_test_block_3 5760 2 32 48 16
cert_test_block_3 5760 3 48 64 16
cert_test_block_3 5760 4 64 80 16
cert_test_block_3 5760 5 80 96 16
cert_test_block_3 5760 6 96 112 16
cert_test_block_3 5760 7 112 128 16
cert_test_block_3 5760 8 128 144 16
cert_test_block_3 5760 9 144 160 16
cert_test_block_3 5760 10 160 176 16
cert_test_block_3 5760 11 176 192 16
cert_test_block_3 5760 12 192 208 16
cert_test_block_3 5760 13 208 224 16
cert_test_block_3 5760 14 224 240 16
cert_test_block_3 5760 15 240 256 16
cert_test_block_3 5760 16 256 272 16
cert_test_block_3 5760 17 272 288 16
cert_test_block_3 5760 18 288 304 16
cert_test_block_3 5760 19 304 320 16
cert_test_block_3 5760 20 320 336 16
cert_test_block_3 5760 21 336 352 16
cert_test_block_3 5760 22 352 368 16
cert_test_block_3 5760 23 368 384 16
cert_test_block_3 5760 24 384 400 16
cert_test_block_3 5760 25 400 416 16
cert_test_block_3 5760 26 416 432 16
cert_test_block_3 5760 27 432 448 16
cert_test_block_3 5760 28 448 464 16
cert_test_block_3 5760 29 464 480 16
cert_test_block_3 5760 30 480 496 16
cert_test_block_3 5760 31 496 512 16
cert_test_block_3 5760 32 512 528 16
cert_test_block_3 5760 33 528 544 16
cert_test_block_3 5760 34 544 560 16
cert_test_block_3 5760 35 560 576 16
cert_test_block_3 5760 36 576 592 16
cert_test_block_3 5760 37 592 608 16
cert_test_block_3 5760 38 608 624 16
cert_test_block_3 5760 39 624 640 16
theorem test5760_complete : Interval test5760 0 640 :=
  (interval_append test5760 0 320 640
  (interval_append test5760 0 160 320
  (interval_append test5760 0 80 160
  (interval_append test5760 0 32 80
  (interval_append test5760 0 16 32
  test5760_block_0
  test5760_block_1)
  (interval_append test5760 32 48 80
  test5760_block_2
  (interval_append test5760 48 64 80
  test5760_block_3
  test5760_block_4)))
  (interval_append test5760 80 112 160
  (interval_append test5760 80 96 112
  test5760_block_5
  test5760_block_6)
  (interval_append test5760 112 128 160
  test5760_block_7
  (interval_append test5760 128 144 160
  test5760_block_8
  test5760_block_9))))
  (interval_append test5760 160 240 320
  (interval_append test5760 160 192 240
  (interval_append test5760 160 176 192
  test5760_block_10
  test5760_block_11)
  (interval_append test5760 192 208 240
  test5760_block_12
  (interval_append test5760 208 224 240
  test5760_block_13
  test5760_block_14)))
  (interval_append test5760 240 272 320
  (interval_append test5760 240 256 272
  test5760_block_15
  test5760_block_16)
  (interval_append test5760 272 288 320
  test5760_block_17
  (interval_append test5760 288 304 320
  test5760_block_18
  test5760_block_19)))))
  (interval_append test5760 320 480 640
  (interval_append test5760 320 400 480
  (interval_append test5760 320 352 400
  (interval_append test5760 320 336 352
  test5760_block_20
  test5760_block_21)
  (interval_append test5760 352 368 400
  test5760_block_22
  (interval_append test5760 368 384 400
  test5760_block_23
  test5760_block_24)))
  (interval_append test5760 400 432 480
  (interval_append test5760 400 416 432
  test5760_block_25
  test5760_block_26)
  (interval_append test5760 432 448 480
  test5760_block_27
  (interval_append test5760 448 464 480
  test5760_block_28
  test5760_block_29))))
  (interval_append test5760 480 560 640
  (interval_append test5760 480 512 560
  (interval_append test5760 480 496 512
  test5760_block_30
  test5760_block_31)
  (interval_append test5760 512 528 560
  test5760_block_32
  (interval_append test5760 528 544 560
  test5760_block_33
  test5760_block_34)))
  (interval_append test5760 560 592 640
  (interval_append test5760 560 576 592
  test5760_block_35
  test5760_block_36)
  (interval_append test5760 592 608 640
  test5760_block_37
  (interval_append test5760 608 624 640
  test5760_block_38
  test5760_block_39))))))
cert_nodeInterval_3 5760 6400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 6400
cert_test_block_3 6400 0 0 16 16
cert_test_block_3 6400 1 16 32 16
cert_test_block_3 6400 2 32 48 16
cert_test_block_3 6400 3 48 64 16
cert_test_block_3 6400 4 64 80 16
cert_test_block_3 6400 5 80 96 16
cert_test_block_3 6400 6 96 112 16
cert_test_block_3 6400 7 112 128 16
cert_test_block_3 6400 8 128 144 16
cert_test_block_3 6400 9 144 160 16
cert_test_block_3 6400 10 160 176 16
cert_test_block_3 6400 11 176 192 16
cert_test_block_3 6400 12 192 208 16
cert_test_block_3 6400 13 208 224 16
cert_test_block_3 6400 14 224 240 16
cert_test_block_3 6400 15 240 256 16
cert_test_block_3 6400 16 256 272 16
cert_test_block_3 6400 17 272 288 16
cert_test_block_3 6400 18 288 304 16
cert_test_block_3 6400 19 304 320 16
cert_test_block_3 6400 20 320 336 16
cert_test_block_3 6400 21 336 352 16
cert_test_block_3 6400 22 352 368 16
cert_test_block_3 6400 23 368 384 16
cert_test_block_3 6400 24 384 400 16
cert_test_block_3 6400 25 400 416 16
cert_test_block_3 6400 26 416 432 16
cert_test_block_3 6400 27 432 448 16
cert_test_block_3 6400 28 448 464 16
cert_test_block_3 6400 29 464 480 16
cert_test_block_3 6400 30 480 496 16
cert_test_block_3 6400 31 496 512 16
cert_test_block_3 6400 32 512 528 16
cert_test_block_3 6400 33 528 544 16
cert_test_block_3 6400 34 544 560 16
cert_test_block_3 6400 35 560 576 16
cert_test_block_3 6400 36 576 592 16
cert_test_block_3 6400 37 592 608 16
cert_test_block_3 6400 38 608 624 16
cert_test_block_3 6400 39 624 640 16
theorem test6400_complete : Interval test6400 0 640 :=
  (interval_append test6400 0 320 640
  (interval_append test6400 0 160 320
  (interval_append test6400 0 80 160
  (interval_append test6400 0 32 80
  (interval_append test6400 0 16 32
  test6400_block_0
  test6400_block_1)
  (interval_append test6400 32 48 80
  test6400_block_2
  (interval_append test6400 48 64 80
  test6400_block_3
  test6400_block_4)))
  (interval_append test6400 80 112 160
  (interval_append test6400 80 96 112
  test6400_block_5
  test6400_block_6)
  (interval_append test6400 112 128 160
  test6400_block_7
  (interval_append test6400 128 144 160
  test6400_block_8
  test6400_block_9))))
  (interval_append test6400 160 240 320
  (interval_append test6400 160 192 240
  (interval_append test6400 160 176 192
  test6400_block_10
  test6400_block_11)
  (interval_append test6400 192 208 240
  test6400_block_12
  (interval_append test6400 208 224 240
  test6400_block_13
  test6400_block_14)))
  (interval_append test6400 240 272 320
  (interval_append test6400 240 256 272
  test6400_block_15
  test6400_block_16)
  (interval_append test6400 272 288 320
  test6400_block_17
  (interval_append test6400 288 304 320
  test6400_block_18
  test6400_block_19)))))
  (interval_append test6400 320 480 640
  (interval_append test6400 320 400 480
  (interval_append test6400 320 352 400
  (interval_append test6400 320 336 352
  test6400_block_20
  test6400_block_21)
  (interval_append test6400 352 368 400
  test6400_block_22
  (interval_append test6400 368 384 400
  test6400_block_23
  test6400_block_24)))
  (interval_append test6400 400 432 480
  (interval_append test6400 400 416 432
  test6400_block_25
  test6400_block_26)
  (interval_append test6400 432 448 480
  test6400_block_27
  (interval_append test6400 448 464 480
  test6400_block_28
  test6400_block_29))))
  (interval_append test6400 480 560 640
  (interval_append test6400 480 512 560
  (interval_append test6400 480 496 512
  test6400_block_30
  test6400_block_31)
  (interval_append test6400 512 528 560
  test6400_block_32
  (interval_append test6400 528 544 560
  test6400_block_33
  test6400_block_34)))
  (interval_append test6400 560 592 640
  (interval_append test6400 560 576 592
  test6400_block_35
  test6400_block_36)
  (interval_append test6400 592 608 640
  test6400_block_37
  (interval_append test6400 608 624 640
  test6400_block_38
  test6400_block_39))))))
cert_nodeInterval_3 6400 7040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 7040
cert_test_block_3 7040 0 0 16 16
cert_test_block_3 7040 1 16 32 16
cert_test_block_3 7040 2 32 48 16
cert_test_block_3 7040 3 48 64 16
cert_test_block_3 7040 4 64 80 16
cert_test_block_3 7040 5 80 96 16
cert_test_block_3 7040 6 96 112 16
cert_test_block_3 7040 7 112 128 16
cert_test_block_3 7040 8 128 144 16
cert_test_block_3 7040 9 144 160 16
cert_test_block_3 7040 10 160 176 16
cert_test_block_3 7040 11 176 192 16
cert_test_block_3 7040 12 192 208 16
cert_test_block_3 7040 13 208 224 16
cert_test_block_3 7040 14 224 240 16
cert_test_block_3 7040 15 240 256 16
cert_test_block_3 7040 16 256 272 16
cert_test_block_3 7040 17 272 288 16
cert_test_block_3 7040 18 288 304 16
cert_test_block_3 7040 19 304 320 16
cert_test_block_3 7040 20 320 336 16
cert_test_block_3 7040 21 336 352 16
cert_test_block_3 7040 22 352 368 16
cert_test_block_3 7040 23 368 384 16
cert_test_block_3 7040 24 384 400 16
cert_test_block_3 7040 25 400 416 16
cert_test_block_3 7040 26 416 432 16
cert_test_block_3 7040 27 432 448 16
cert_test_block_3 7040 28 448 464 16
cert_test_block_3 7040 29 464 480 16
cert_test_block_3 7040 30 480 496 16
cert_test_block_3 7040 31 496 512 16
cert_test_block_3 7040 32 512 528 16
cert_test_block_3 7040 33 528 544 16
cert_test_block_3 7040 34 544 560 16
cert_test_block_3 7040 35 560 576 16
cert_test_block_3 7040 36 576 592 16
cert_test_block_3 7040 37 592 608 16
cert_test_block_3 7040 38 608 624 16
cert_test_block_3 7040 39 624 640 16
theorem test7040_complete : Interval test7040 0 640 :=
  (interval_append test7040 0 320 640
  (interval_append test7040 0 160 320
  (interval_append test7040 0 80 160
  (interval_append test7040 0 32 80
  (interval_append test7040 0 16 32
  test7040_block_0
  test7040_block_1)
  (interval_append test7040 32 48 80
  test7040_block_2
  (interval_append test7040 48 64 80
  test7040_block_3
  test7040_block_4)))
  (interval_append test7040 80 112 160
  (interval_append test7040 80 96 112
  test7040_block_5
  test7040_block_6)
  (interval_append test7040 112 128 160
  test7040_block_7
  (interval_append test7040 128 144 160
  test7040_block_8
  test7040_block_9))))
  (interval_append test7040 160 240 320
  (interval_append test7040 160 192 240
  (interval_append test7040 160 176 192
  test7040_block_10
  test7040_block_11)
  (interval_append test7040 192 208 240
  test7040_block_12
  (interval_append test7040 208 224 240
  test7040_block_13
  test7040_block_14)))
  (interval_append test7040 240 272 320
  (interval_append test7040 240 256 272
  test7040_block_15
  test7040_block_16)
  (interval_append test7040 272 288 320
  test7040_block_17
  (interval_append test7040 288 304 320
  test7040_block_18
  test7040_block_19)))))
  (interval_append test7040 320 480 640
  (interval_append test7040 320 400 480
  (interval_append test7040 320 352 400
  (interval_append test7040 320 336 352
  test7040_block_20
  test7040_block_21)
  (interval_append test7040 352 368 400
  test7040_block_22
  (interval_append test7040 368 384 400
  test7040_block_23
  test7040_block_24)))
  (interval_append test7040 400 432 480
  (interval_append test7040 400 416 432
  test7040_block_25
  test7040_block_26)
  (interval_append test7040 432 448 480
  test7040_block_27
  (interval_append test7040 448 464 480
  test7040_block_28
  test7040_block_29))))
  (interval_append test7040 480 560 640
  (interval_append test7040 480 512 560
  (interval_append test7040 480 496 512
  test7040_block_30
  test7040_block_31)
  (interval_append test7040 512 528 560
  test7040_block_32
  (interval_append test7040 528 544 560
  test7040_block_33
  test7040_block_34)))
  (interval_append test7040 560 592 640
  (interval_append test7040 560 576 592
  test7040_block_35
  test7040_block_36)
  (interval_append test7040 592 608 640
  test7040_block_37
  (interval_append test7040 608 624 640
  test7040_block_38
  test7040_block_39))))))
cert_nodeInterval_3 7040 7680
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 8960
cert_test_block_3 8960 0 0 16 16
cert_test_block_3 8960 1 16 32 16
cert_test_block_3 8960 2 32 43 11
theorem test8960_complete : Interval test8960 0 43 :=
  (interval_append test8960 0 16 43
  test8960_block_0
  (interval_append test8960 16 32 43
  test8960_block_1
  test8960_block_2))
cert_nodeInterval_3 8960 9003
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
end
end
