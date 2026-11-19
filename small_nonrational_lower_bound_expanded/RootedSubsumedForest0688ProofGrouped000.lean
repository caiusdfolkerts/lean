module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0688Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
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
cert_test_block_3 1920 16 256 269 13
theorem test1920_complete : Interval test1920 0 269 :=
  (interval_append test1920 0 128 269
  (interval_append test1920 0 64 128
  (interval_append test1920 0 32 64
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 64
  test1920_block_2
  test1920_block_3))
  (interval_append test1920 64 96 128
  (interval_append test1920 64 80 96
  test1920_block_4
  test1920_block_5)
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7)))
  (interval_append test1920 128 192 269
  (interval_append test1920 128 160 192
  (interval_append test1920 128 144 160
  test1920_block_8
  test1920_block_9)
  (interval_append test1920 160 176 192
  test1920_block_10
  test1920_block_11))
  (interval_append test1920 192 224 269
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13)
  (interval_append test1920 224 240 269
  test1920_block_14
  (interval_append test1920 240 256 269
  test1920_block_15
  test1920_block_16)))))
cert_nodeInterval_3 1920 2189
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
end
end
