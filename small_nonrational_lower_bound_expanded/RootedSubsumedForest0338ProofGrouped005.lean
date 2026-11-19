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
cert_test_11 32000
cert_test_block_3 32000 0 0 16 16
cert_test_block_3 32000 1 16 32 16
cert_test_block_3 32000 2 32 48 16
cert_test_block_3 32000 3 48 64 16
cert_test_block_3 32000 4 64 80 16
cert_test_block_3 32000 5 80 96 16
cert_test_block_3 32000 6 96 112 16
cert_test_block_3 32000 7 112 128 16
cert_test_block_3 32000 8 128 144 16
cert_test_block_3 32000 9 144 160 16
cert_test_block_3 32000 10 160 176 16
cert_test_block_3 32000 11 176 192 16
cert_test_block_3 32000 12 192 208 16
cert_test_block_3 32000 13 208 224 16
cert_test_block_3 32000 14 224 240 16
cert_test_block_3 32000 15 240 256 16
cert_test_block_3 32000 16 256 272 16
cert_test_block_3 32000 17 272 288 16
cert_test_block_3 32000 18 288 304 16
cert_test_block_3 32000 19 304 320 16
cert_test_block_3 32000 20 320 336 16
cert_test_block_3 32000 21 336 352 16
cert_test_block_3 32000 22 352 368 16
cert_test_block_3 32000 23 368 384 16
cert_test_block_3 32000 24 384 400 16
cert_test_block_3 32000 25 400 416 16
cert_test_block_3 32000 26 416 432 16
cert_test_block_3 32000 27 432 448 16
cert_test_block_3 32000 28 448 464 16
cert_test_block_3 32000 29 464 480 16
cert_test_block_3 32000 30 480 496 16
cert_test_block_3 32000 31 496 512 16
cert_test_block_3 32000 32 512 528 16
cert_test_block_3 32000 33 528 544 16
cert_test_block_3 32000 34 544 560 16
cert_test_block_3 32000 35 560 576 16
cert_test_block_3 32000 36 576 592 16
cert_test_block_3 32000 37 592 608 16
cert_test_block_3 32000 38 608 624 16
cert_test_block_3 32000 39 624 640 16
theorem test32000_complete : Interval test32000 0 640 :=
  (interval_append test32000 0 320 640
  (interval_append test32000 0 160 320
  (interval_append test32000 0 80 160
  (interval_append test32000 0 32 80
  (interval_append test32000 0 16 32
  test32000_block_0
  test32000_block_1)
  (interval_append test32000 32 48 80
  test32000_block_2
  (interval_append test32000 48 64 80
  test32000_block_3
  test32000_block_4)))
  (interval_append test32000 80 112 160
  (interval_append test32000 80 96 112
  test32000_block_5
  test32000_block_6)
  (interval_append test32000 112 128 160
  test32000_block_7
  (interval_append test32000 128 144 160
  test32000_block_8
  test32000_block_9))))
  (interval_append test32000 160 240 320
  (interval_append test32000 160 192 240
  (interval_append test32000 160 176 192
  test32000_block_10
  test32000_block_11)
  (interval_append test32000 192 208 240
  test32000_block_12
  (interval_append test32000 208 224 240
  test32000_block_13
  test32000_block_14)))
  (interval_append test32000 240 272 320
  (interval_append test32000 240 256 272
  test32000_block_15
  test32000_block_16)
  (interval_append test32000 272 288 320
  test32000_block_17
  (interval_append test32000 288 304 320
  test32000_block_18
  test32000_block_19)))))
  (interval_append test32000 320 480 640
  (interval_append test32000 320 400 480
  (interval_append test32000 320 352 400
  (interval_append test32000 320 336 352
  test32000_block_20
  test32000_block_21)
  (interval_append test32000 352 368 400
  test32000_block_22
  (interval_append test32000 368 384 400
  test32000_block_23
  test32000_block_24)))
  (interval_append test32000 400 432 480
  (interval_append test32000 400 416 432
  test32000_block_25
  test32000_block_26)
  (interval_append test32000 432 448 480
  test32000_block_27
  (interval_append test32000 448 464 480
  test32000_block_28
  test32000_block_29))))
  (interval_append test32000 480 560 640
  (interval_append test32000 480 512 560
  (interval_append test32000 480 496 512
  test32000_block_30
  test32000_block_31)
  (interval_append test32000 512 528 560
  test32000_block_32
  (interval_append test32000 528 544 560
  test32000_block_33
  test32000_block_34)))
  (interval_append test32000 560 592 640
  (interval_append test32000 560 576 592
  test32000_block_35
  test32000_block_36)
  (interval_append test32000 592 608 640
  test32000_block_37
  (interval_append test32000 608 624 640
  test32000_block_38
  test32000_block_39))))))
cert_nodeInterval_3 32000 32640
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
cert_test_11 32640
cert_test_block_3 32640 0 0 16 16
cert_test_block_3 32640 1 16 32 16
cert_test_block_3 32640 2 32 48 16
cert_test_block_3 32640 3 48 64 16
cert_test_block_3 32640 4 64 80 16
cert_test_block_3 32640 5 80 96 16
cert_test_block_3 32640 6 96 112 16
cert_test_block_3 32640 7 112 128 16
cert_test_block_3 32640 8 128 144 16
cert_test_block_3 32640 9 144 160 16
cert_test_block_3 32640 10 160 176 16
cert_test_block_3 32640 11 176 192 16
cert_test_block_3 32640 12 192 208 16
cert_test_block_3 32640 13 208 224 16
cert_test_block_3 32640 14 224 240 16
cert_test_block_3 32640 15 240 256 16
cert_test_block_3 32640 16 256 272 16
cert_test_block_3 32640 17 272 288 16
cert_test_block_3 32640 18 288 304 16
cert_test_block_3 32640 19 304 320 16
cert_test_block_3 32640 20 320 336 16
cert_test_block_3 32640 21 336 352 16
cert_test_block_3 32640 22 352 368 16
cert_test_block_3 32640 23 368 384 16
cert_test_block_3 32640 24 384 400 16
cert_test_block_3 32640 25 400 416 16
cert_test_block_3 32640 26 416 432 16
cert_test_block_3 32640 27 432 448 16
cert_test_block_3 32640 28 448 464 16
cert_test_block_3 32640 29 464 480 16
cert_test_block_3 32640 30 480 496 16
cert_test_block_3 32640 31 496 512 16
cert_test_block_3 32640 32 512 528 16
cert_test_block_3 32640 33 528 544 16
cert_test_block_3 32640 34 544 560 16
cert_test_block_3 32640 35 560 576 16
cert_test_block_3 32640 36 576 592 16
cert_test_block_3 32640 37 592 608 16
cert_test_block_3 32640 38 608 624 16
cert_test_block_3 32640 39 624 640 16
theorem test32640_complete : Interval test32640 0 640 :=
  (interval_append test32640 0 320 640
  (interval_append test32640 0 160 320
  (interval_append test32640 0 80 160
  (interval_append test32640 0 32 80
  (interval_append test32640 0 16 32
  test32640_block_0
  test32640_block_1)
  (interval_append test32640 32 48 80
  test32640_block_2
  (interval_append test32640 48 64 80
  test32640_block_3
  test32640_block_4)))
  (interval_append test32640 80 112 160
  (interval_append test32640 80 96 112
  test32640_block_5
  test32640_block_6)
  (interval_append test32640 112 128 160
  test32640_block_7
  (interval_append test32640 128 144 160
  test32640_block_8
  test32640_block_9))))
  (interval_append test32640 160 240 320
  (interval_append test32640 160 192 240
  (interval_append test32640 160 176 192
  test32640_block_10
  test32640_block_11)
  (interval_append test32640 192 208 240
  test32640_block_12
  (interval_append test32640 208 224 240
  test32640_block_13
  test32640_block_14)))
  (interval_append test32640 240 272 320
  (interval_append test32640 240 256 272
  test32640_block_15
  test32640_block_16)
  (interval_append test32640 272 288 320
  test32640_block_17
  (interval_append test32640 288 304 320
  test32640_block_18
  test32640_block_19)))))
  (interval_append test32640 320 480 640
  (interval_append test32640 320 400 480
  (interval_append test32640 320 352 400
  (interval_append test32640 320 336 352
  test32640_block_20
  test32640_block_21)
  (interval_append test32640 352 368 400
  test32640_block_22
  (interval_append test32640 368 384 400
  test32640_block_23
  test32640_block_24)))
  (interval_append test32640 400 432 480
  (interval_append test32640 400 416 432
  test32640_block_25
  test32640_block_26)
  (interval_append test32640 432 448 480
  test32640_block_27
  (interval_append test32640 448 464 480
  test32640_block_28
  test32640_block_29))))
  (interval_append test32640 480 560 640
  (interval_append test32640 480 512 560
  (interval_append test32640 480 496 512
  test32640_block_30
  test32640_block_31)
  (interval_append test32640 512 528 560
  test32640_block_32
  (interval_append test32640 528 544 560
  test32640_block_33
  test32640_block_34)))
  (interval_append test32640 560 592 640
  (interval_append test32640 560 576 592
  test32640_block_35
  test32640_block_36)
  (interval_append test32640 592 608 640
  test32640_block_37
  (interval_append test32640 608 624 640
  test32640_block_38
  test32640_block_39))))))
cert_nodeInterval_3 32640 33280
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
cert_test_11 33280
cert_test_block_3 33280 0 0 16 16
cert_test_block_3 33280 1 16 32 16
cert_test_block_3 33280 2 32 48 16
cert_test_block_3 33280 3 48 64 16
cert_test_block_3 33280 4 64 80 16
cert_test_block_3 33280 5 80 96 16
cert_test_block_3 33280 6 96 112 16
cert_test_block_3 33280 7 112 128 16
cert_test_block_3 33280 8 128 144 16
cert_test_block_3 33280 9 144 160 16
cert_test_block_3 33280 10 160 176 16
cert_test_block_3 33280 11 176 192 16
cert_test_block_3 33280 12 192 208 16
cert_test_block_3 33280 13 208 224 16
cert_test_block_3 33280 14 224 240 16
cert_test_block_3 33280 15 240 256 16
cert_test_block_3 33280 16 256 272 16
cert_test_block_3 33280 17 272 288 16
cert_test_block_3 33280 18 288 304 16
cert_test_block_3 33280 19 304 320 16
cert_test_block_3 33280 20 320 336 16
cert_test_block_3 33280 21 336 352 16
cert_test_block_3 33280 22 352 368 16
cert_test_block_3 33280 23 368 384 16
cert_test_block_3 33280 24 384 400 16
cert_test_block_3 33280 25 400 416 16
cert_test_block_3 33280 26 416 432 16
cert_test_block_3 33280 27 432 448 16
cert_test_block_3 33280 28 448 464 16
cert_test_block_3 33280 29 464 480 16
cert_test_block_3 33280 30 480 496 16
cert_test_block_3 33280 31 496 512 16
cert_test_block_3 33280 32 512 528 16
cert_test_block_3 33280 33 528 544 16
cert_test_block_3 33280 34 544 560 16
cert_test_block_3 33280 35 560 576 16
cert_test_block_3 33280 36 576 592 16
cert_test_block_3 33280 37 592 608 16
cert_test_block_3 33280 38 608 624 16
cert_test_block_3 33280 39 624 640 16
theorem test33280_complete : Interval test33280 0 640 :=
  (interval_append test33280 0 320 640
  (interval_append test33280 0 160 320
  (interval_append test33280 0 80 160
  (interval_append test33280 0 32 80
  (interval_append test33280 0 16 32
  test33280_block_0
  test33280_block_1)
  (interval_append test33280 32 48 80
  test33280_block_2
  (interval_append test33280 48 64 80
  test33280_block_3
  test33280_block_4)))
  (interval_append test33280 80 112 160
  (interval_append test33280 80 96 112
  test33280_block_5
  test33280_block_6)
  (interval_append test33280 112 128 160
  test33280_block_7
  (interval_append test33280 128 144 160
  test33280_block_8
  test33280_block_9))))
  (interval_append test33280 160 240 320
  (interval_append test33280 160 192 240
  (interval_append test33280 160 176 192
  test33280_block_10
  test33280_block_11)
  (interval_append test33280 192 208 240
  test33280_block_12
  (interval_append test33280 208 224 240
  test33280_block_13
  test33280_block_14)))
  (interval_append test33280 240 272 320
  (interval_append test33280 240 256 272
  test33280_block_15
  test33280_block_16)
  (interval_append test33280 272 288 320
  test33280_block_17
  (interval_append test33280 288 304 320
  test33280_block_18
  test33280_block_19)))))
  (interval_append test33280 320 480 640
  (interval_append test33280 320 400 480
  (interval_append test33280 320 352 400
  (interval_append test33280 320 336 352
  test33280_block_20
  test33280_block_21)
  (interval_append test33280 352 368 400
  test33280_block_22
  (interval_append test33280 368 384 400
  test33280_block_23
  test33280_block_24)))
  (interval_append test33280 400 432 480
  (interval_append test33280 400 416 432
  test33280_block_25
  test33280_block_26)
  (interval_append test33280 432 448 480
  test33280_block_27
  (interval_append test33280 448 464 480
  test33280_block_28
  test33280_block_29))))
  (interval_append test33280 480 560 640
  (interval_append test33280 480 512 560
  (interval_append test33280 480 496 512
  test33280_block_30
  test33280_block_31)
  (interval_append test33280 512 528 560
  test33280_block_32
  (interval_append test33280 528 544 560
  test33280_block_33
  test33280_block_34)))
  (interval_append test33280 560 592 640
  (interval_append test33280 560 576 592
  test33280_block_35
  test33280_block_36)
  (interval_append test33280 592 608 640
  test33280_block_37
  (interval_append test33280 608 624 640
  test33280_block_38
  test33280_block_39))))))
cert_nodeInterval_3 33280 33920
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
cert_test_11 33920
cert_test_block_3 33920 0 0 16 16
cert_test_block_3 33920 1 16 32 16
cert_test_block_3 33920 2 32 48 16
cert_test_block_3 33920 3 48 64 16
cert_test_block_3 33920 4 64 80 16
cert_test_block_3 33920 5 80 96 16
cert_test_block_3 33920 6 96 112 16
cert_test_block_3 33920 7 112 128 16
cert_test_block_3 33920 8 128 144 16
cert_test_block_3 33920 9 144 160 16
cert_test_block_3 33920 10 160 176 16
cert_test_block_3 33920 11 176 192 16
cert_test_block_3 33920 12 192 208 16
cert_test_block_3 33920 13 208 224 16
cert_test_block_3 33920 14 224 240 16
cert_test_block_3 33920 15 240 256 16
cert_test_block_3 33920 16 256 272 16
cert_test_block_3 33920 17 272 288 16
cert_test_block_3 33920 18 288 304 16
cert_test_block_3 33920 19 304 320 16
cert_test_block_3 33920 20 320 336 16
cert_test_block_3 33920 21 336 352 16
cert_test_block_3 33920 22 352 368 16
cert_test_block_3 33920 23 368 384 16
cert_test_block_3 33920 24 384 400 16
cert_test_block_3 33920 25 400 416 16
cert_test_block_3 33920 26 416 432 16
cert_test_block_3 33920 27 432 448 16
cert_test_block_3 33920 28 448 464 16
cert_test_block_3 33920 29 464 480 16
cert_test_block_3 33920 30 480 496 16
cert_test_block_3 33920 31 496 512 16
cert_test_block_3 33920 32 512 528 16
cert_test_block_3 33920 33 528 544 16
cert_test_block_3 33920 34 544 560 16
cert_test_block_3 33920 35 560 576 16
cert_test_block_3 33920 36 576 592 16
cert_test_block_3 33920 37 592 608 16
cert_test_block_3 33920 38 608 624 16
cert_test_block_3 33920 39 624 640 16
theorem test33920_complete : Interval test33920 0 640 :=
  (interval_append test33920 0 320 640
  (interval_append test33920 0 160 320
  (interval_append test33920 0 80 160
  (interval_append test33920 0 32 80
  (interval_append test33920 0 16 32
  test33920_block_0
  test33920_block_1)
  (interval_append test33920 32 48 80
  test33920_block_2
  (interval_append test33920 48 64 80
  test33920_block_3
  test33920_block_4)))
  (interval_append test33920 80 112 160
  (interval_append test33920 80 96 112
  test33920_block_5
  test33920_block_6)
  (interval_append test33920 112 128 160
  test33920_block_7
  (interval_append test33920 128 144 160
  test33920_block_8
  test33920_block_9))))
  (interval_append test33920 160 240 320
  (interval_append test33920 160 192 240
  (interval_append test33920 160 176 192
  test33920_block_10
  test33920_block_11)
  (interval_append test33920 192 208 240
  test33920_block_12
  (interval_append test33920 208 224 240
  test33920_block_13
  test33920_block_14)))
  (interval_append test33920 240 272 320
  (interval_append test33920 240 256 272
  test33920_block_15
  test33920_block_16)
  (interval_append test33920 272 288 320
  test33920_block_17
  (interval_append test33920 288 304 320
  test33920_block_18
  test33920_block_19)))))
  (interval_append test33920 320 480 640
  (interval_append test33920 320 400 480
  (interval_append test33920 320 352 400
  (interval_append test33920 320 336 352
  test33920_block_20
  test33920_block_21)
  (interval_append test33920 352 368 400
  test33920_block_22
  (interval_append test33920 368 384 400
  test33920_block_23
  test33920_block_24)))
  (interval_append test33920 400 432 480
  (interval_append test33920 400 416 432
  test33920_block_25
  test33920_block_26)
  (interval_append test33920 432 448 480
  test33920_block_27
  (interval_append test33920 448 464 480
  test33920_block_28
  test33920_block_29))))
  (interval_append test33920 480 560 640
  (interval_append test33920 480 512 560
  (interval_append test33920 480 496 512
  test33920_block_30
  test33920_block_31)
  (interval_append test33920 512 528 560
  test33920_block_32
  (interval_append test33920 528 544 560
  test33920_block_33
  test33920_block_34)))
  (interval_append test33920 560 592 640
  (interval_append test33920 560 576 592
  test33920_block_35
  test33920_block_36)
  (interval_append test33920 592 608 640
  test33920_block_37
  (interval_append test33920 608 624 640
  test33920_block_38
  test33920_block_39))))))
cert_nodeInterval_3 33920 34560
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
cert_test_11 34560
cert_test_block_3 34560 0 0 16 16
cert_test_block_3 34560 1 16 32 16
cert_test_block_3 34560 2 32 48 16
cert_test_block_3 34560 3 48 64 16
cert_test_block_3 34560 4 64 80 16
cert_test_block_3 34560 5 80 96 16
cert_test_block_3 34560 6 96 112 16
cert_test_block_3 34560 7 112 128 16
cert_test_block_3 34560 8 128 144 16
cert_test_block_3 34560 9 144 160 16
cert_test_block_3 34560 10 160 176 16
cert_test_block_3 34560 11 176 192 16
cert_test_block_3 34560 12 192 208 16
cert_test_block_3 34560 13 208 224 16
cert_test_block_3 34560 14 224 240 16
cert_test_block_3 34560 15 240 256 16
cert_test_block_3 34560 16 256 272 16
cert_test_block_3 34560 17 272 288 16
cert_test_block_3 34560 18 288 304 16
cert_test_block_3 34560 19 304 320 16
cert_test_block_3 34560 20 320 336 16
cert_test_block_3 34560 21 336 352 16
cert_test_block_3 34560 22 352 368 16
cert_test_block_3 34560 23 368 384 16
cert_test_block_3 34560 24 384 400 16
cert_test_block_3 34560 25 400 416 16
cert_test_block_3 34560 26 416 432 16
cert_test_block_3 34560 27 432 448 16
cert_test_block_3 34560 28 448 464 16
cert_test_block_3 34560 29 464 480 16
cert_test_block_3 34560 30 480 496 16
cert_test_block_3 34560 31 496 512 16
cert_test_block_3 34560 32 512 528 16
cert_test_block_3 34560 33 528 544 16
cert_test_block_3 34560 34 544 560 16
cert_test_block_3 34560 35 560 576 16
cert_test_block_3 34560 36 576 592 16
cert_test_block_3 34560 37 592 608 16
cert_test_block_3 34560 38 608 624 16
cert_test_block_3 34560 39 624 640 16
theorem test34560_complete : Interval test34560 0 640 :=
  (interval_append test34560 0 320 640
  (interval_append test34560 0 160 320
  (interval_append test34560 0 80 160
  (interval_append test34560 0 32 80
  (interval_append test34560 0 16 32
  test34560_block_0
  test34560_block_1)
  (interval_append test34560 32 48 80
  test34560_block_2
  (interval_append test34560 48 64 80
  test34560_block_3
  test34560_block_4)))
  (interval_append test34560 80 112 160
  (interval_append test34560 80 96 112
  test34560_block_5
  test34560_block_6)
  (interval_append test34560 112 128 160
  test34560_block_7
  (interval_append test34560 128 144 160
  test34560_block_8
  test34560_block_9))))
  (interval_append test34560 160 240 320
  (interval_append test34560 160 192 240
  (interval_append test34560 160 176 192
  test34560_block_10
  test34560_block_11)
  (interval_append test34560 192 208 240
  test34560_block_12
  (interval_append test34560 208 224 240
  test34560_block_13
  test34560_block_14)))
  (interval_append test34560 240 272 320
  (interval_append test34560 240 256 272
  test34560_block_15
  test34560_block_16)
  (interval_append test34560 272 288 320
  test34560_block_17
  (interval_append test34560 288 304 320
  test34560_block_18
  test34560_block_19)))))
  (interval_append test34560 320 480 640
  (interval_append test34560 320 400 480
  (interval_append test34560 320 352 400
  (interval_append test34560 320 336 352
  test34560_block_20
  test34560_block_21)
  (interval_append test34560 352 368 400
  test34560_block_22
  (interval_append test34560 368 384 400
  test34560_block_23
  test34560_block_24)))
  (interval_append test34560 400 432 480
  (interval_append test34560 400 416 432
  test34560_block_25
  test34560_block_26)
  (interval_append test34560 432 448 480
  test34560_block_27
  (interval_append test34560 448 464 480
  test34560_block_28
  test34560_block_29))))
  (interval_append test34560 480 560 640
  (interval_append test34560 480 512 560
  (interval_append test34560 480 496 512
  test34560_block_30
  test34560_block_31)
  (interval_append test34560 512 528 560
  test34560_block_32
  (interval_append test34560 528 544 560
  test34560_block_33
  test34560_block_34)))
  (interval_append test34560 560 592 640
  (interval_append test34560 560 576 592
  test34560_block_35
  test34560_block_36)
  (interval_append test34560 592 608 640
  test34560_block_37
  (interval_append test34560 608 624 640
  test34560_block_38
  test34560_block_39))))))
cert_nodeInterval_3 34560 35200
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
cert_test_11 35200
cert_test_block_3 35200 0 0 16 16
cert_test_block_3 35200 1 16 32 16
cert_test_block_3 35200 2 32 48 16
cert_test_block_3 35200 3 48 64 16
cert_test_block_3 35200 4 64 80 16
cert_test_block_3 35200 5 80 96 16
cert_test_block_3 35200 6 96 112 16
cert_test_block_3 35200 7 112 128 16
cert_test_block_3 35200 8 128 144 16
cert_test_block_3 35200 9 144 160 16
cert_test_block_3 35200 10 160 176 16
cert_test_block_3 35200 11 176 192 16
cert_test_block_3 35200 12 192 208 16
cert_test_block_3 35200 13 208 224 16
cert_test_block_3 35200 14 224 240 16
cert_test_block_3 35200 15 240 256 16
cert_test_block_3 35200 16 256 272 16
cert_test_block_3 35200 17 272 288 16
cert_test_block_3 35200 18 288 304 16
cert_test_block_3 35200 19 304 320 16
cert_test_block_3 35200 20 320 336 16
cert_test_block_3 35200 21 336 352 16
cert_test_block_3 35200 22 352 368 16
cert_test_block_3 35200 23 368 384 16
cert_test_block_3 35200 24 384 400 16
cert_test_block_3 35200 25 400 416 16
cert_test_block_3 35200 26 416 432 16
cert_test_block_3 35200 27 432 448 16
cert_test_block_3 35200 28 448 464 16
cert_test_block_3 35200 29 464 480 16
cert_test_block_3 35200 30 480 496 16
cert_test_block_3 35200 31 496 512 16
cert_test_block_3 35200 32 512 528 16
cert_test_block_3 35200 33 528 544 16
cert_test_block_3 35200 34 544 560 16
cert_test_block_3 35200 35 560 576 16
cert_test_block_3 35200 36 576 592 16
cert_test_block_3 35200 37 592 608 16
cert_test_block_3 35200 38 608 624 16
cert_test_block_3 35200 39 624 640 16
theorem test35200_complete : Interval test35200 0 640 :=
  (interval_append test35200 0 320 640
  (interval_append test35200 0 160 320
  (interval_append test35200 0 80 160
  (interval_append test35200 0 32 80
  (interval_append test35200 0 16 32
  test35200_block_0
  test35200_block_1)
  (interval_append test35200 32 48 80
  test35200_block_2
  (interval_append test35200 48 64 80
  test35200_block_3
  test35200_block_4)))
  (interval_append test35200 80 112 160
  (interval_append test35200 80 96 112
  test35200_block_5
  test35200_block_6)
  (interval_append test35200 112 128 160
  test35200_block_7
  (interval_append test35200 128 144 160
  test35200_block_8
  test35200_block_9))))
  (interval_append test35200 160 240 320
  (interval_append test35200 160 192 240
  (interval_append test35200 160 176 192
  test35200_block_10
  test35200_block_11)
  (interval_append test35200 192 208 240
  test35200_block_12
  (interval_append test35200 208 224 240
  test35200_block_13
  test35200_block_14)))
  (interval_append test35200 240 272 320
  (interval_append test35200 240 256 272
  test35200_block_15
  test35200_block_16)
  (interval_append test35200 272 288 320
  test35200_block_17
  (interval_append test35200 288 304 320
  test35200_block_18
  test35200_block_19)))))
  (interval_append test35200 320 480 640
  (interval_append test35200 320 400 480
  (interval_append test35200 320 352 400
  (interval_append test35200 320 336 352
  test35200_block_20
  test35200_block_21)
  (interval_append test35200 352 368 400
  test35200_block_22
  (interval_append test35200 368 384 400
  test35200_block_23
  test35200_block_24)))
  (interval_append test35200 400 432 480
  (interval_append test35200 400 416 432
  test35200_block_25
  test35200_block_26)
  (interval_append test35200 432 448 480
  test35200_block_27
  (interval_append test35200 448 464 480
  test35200_block_28
  test35200_block_29))))
  (interval_append test35200 480 560 640
  (interval_append test35200 480 512 560
  (interval_append test35200 480 496 512
  test35200_block_30
  test35200_block_31)
  (interval_append test35200 512 528 560
  test35200_block_32
  (interval_append test35200 528 544 560
  test35200_block_33
  test35200_block_34)))
  (interval_append test35200 560 592 640
  (interval_append test35200 560 576 592
  test35200_block_35
  test35200_block_36)
  (interval_append test35200 592 608 640
  test35200_block_37
  (interval_append test35200 608 624 640
  test35200_block_38
  test35200_block_39))))))
cert_nodeInterval_3 35200 35840
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
cert_test_11 35840
cert_test_block_3 35840 0 0 16 16
cert_test_block_3 35840 1 16 32 16
cert_test_block_3 35840 2 32 48 16
cert_test_block_3 35840 3 48 64 16
cert_test_block_3 35840 4 64 80 16
cert_test_block_3 35840 5 80 96 16
cert_test_block_3 35840 6 96 112 16
cert_test_block_3 35840 7 112 128 16
cert_test_block_3 35840 8 128 144 16
cert_test_block_3 35840 9 144 160 16
cert_test_block_3 35840 10 160 176 16
cert_test_block_3 35840 11 176 192 16
cert_test_block_3 35840 12 192 208 16
cert_test_block_3 35840 13 208 224 16
cert_test_block_3 35840 14 224 240 16
cert_test_block_3 35840 15 240 256 16
cert_test_block_3 35840 16 256 272 16
cert_test_block_3 35840 17 272 288 16
cert_test_block_3 35840 18 288 304 16
cert_test_block_3 35840 19 304 320 16
cert_test_block_3 35840 20 320 336 16
cert_test_block_3 35840 21 336 352 16
cert_test_block_3 35840 22 352 368 16
cert_test_block_3 35840 23 368 384 16
cert_test_block_3 35840 24 384 400 16
cert_test_block_3 35840 25 400 416 16
cert_test_block_3 35840 26 416 432 16
cert_test_block_3 35840 27 432 448 16
cert_test_block_3 35840 28 448 464 16
cert_test_block_3 35840 29 464 480 16
cert_test_block_3 35840 30 480 496 16
cert_test_block_3 35840 31 496 512 16
cert_test_block_3 35840 32 512 528 16
cert_test_block_3 35840 33 528 544 16
cert_test_block_3 35840 34 544 560 16
cert_test_block_3 35840 35 560 576 16
cert_test_block_3 35840 36 576 592 16
cert_test_block_3 35840 37 592 608 16
cert_test_block_3 35840 38 608 624 16
cert_test_block_3 35840 39 624 640 16
theorem test35840_complete : Interval test35840 0 640 :=
  (interval_append test35840 0 320 640
  (interval_append test35840 0 160 320
  (interval_append test35840 0 80 160
  (interval_append test35840 0 32 80
  (interval_append test35840 0 16 32
  test35840_block_0
  test35840_block_1)
  (interval_append test35840 32 48 80
  test35840_block_2
  (interval_append test35840 48 64 80
  test35840_block_3
  test35840_block_4)))
  (interval_append test35840 80 112 160
  (interval_append test35840 80 96 112
  test35840_block_5
  test35840_block_6)
  (interval_append test35840 112 128 160
  test35840_block_7
  (interval_append test35840 128 144 160
  test35840_block_8
  test35840_block_9))))
  (interval_append test35840 160 240 320
  (interval_append test35840 160 192 240
  (interval_append test35840 160 176 192
  test35840_block_10
  test35840_block_11)
  (interval_append test35840 192 208 240
  test35840_block_12
  (interval_append test35840 208 224 240
  test35840_block_13
  test35840_block_14)))
  (interval_append test35840 240 272 320
  (interval_append test35840 240 256 272
  test35840_block_15
  test35840_block_16)
  (interval_append test35840 272 288 320
  test35840_block_17
  (interval_append test35840 288 304 320
  test35840_block_18
  test35840_block_19)))))
  (interval_append test35840 320 480 640
  (interval_append test35840 320 400 480
  (interval_append test35840 320 352 400
  (interval_append test35840 320 336 352
  test35840_block_20
  test35840_block_21)
  (interval_append test35840 352 368 400
  test35840_block_22
  (interval_append test35840 368 384 400
  test35840_block_23
  test35840_block_24)))
  (interval_append test35840 400 432 480
  (interval_append test35840 400 416 432
  test35840_block_25
  test35840_block_26)
  (interval_append test35840 432 448 480
  test35840_block_27
  (interval_append test35840 448 464 480
  test35840_block_28
  test35840_block_29))))
  (interval_append test35840 480 560 640
  (interval_append test35840 480 512 560
  (interval_append test35840 480 496 512
  test35840_block_30
  test35840_block_31)
  (interval_append test35840 512 528 560
  test35840_block_32
  (interval_append test35840 528 544 560
  test35840_block_33
  test35840_block_34)))
  (interval_append test35840 560 592 640
  (interval_append test35840 560 576 592
  test35840_block_35
  test35840_block_36)
  (interval_append test35840 592 608 640
  test35840_block_37
  (interval_append test35840 608 624 640
  test35840_block_38
  test35840_block_39))))))
cert_nodeInterval_3 35840 36480
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
cert_test_11 36480
cert_test_block_3 36480 0 0 16 16
cert_test_block_3 36480 1 16 32 16
cert_test_block_3 36480 2 32 48 16
cert_test_block_3 36480 3 48 64 16
cert_test_block_3 36480 4 64 80 16
cert_test_block_3 36480 5 80 96 16
cert_test_block_3 36480 6 96 112 16
cert_test_block_3 36480 7 112 128 16
cert_test_block_3 36480 8 128 144 16
cert_test_block_3 36480 9 144 160 16
cert_test_block_3 36480 10 160 176 16
cert_test_block_3 36480 11 176 192 16
cert_test_block_3 36480 12 192 208 16
cert_test_block_3 36480 13 208 224 16
cert_test_block_3 36480 14 224 240 16
cert_test_block_3 36480 15 240 256 16
cert_test_block_3 36480 16 256 272 16
cert_test_block_3 36480 17 272 288 16
cert_test_block_3 36480 18 288 304 16
cert_test_block_3 36480 19 304 320 16
cert_test_block_3 36480 20 320 336 16
cert_test_block_3 36480 21 336 352 16
cert_test_block_3 36480 22 352 368 16
cert_test_block_3 36480 23 368 384 16
cert_test_block_3 36480 24 384 400 16
cert_test_block_3 36480 25 400 416 16
cert_test_block_3 36480 26 416 432 16
cert_test_block_3 36480 27 432 448 16
cert_test_block_3 36480 28 448 464 16
cert_test_block_3 36480 29 464 480 16
cert_test_block_3 36480 30 480 496 16
cert_test_block_3 36480 31 496 512 16
cert_test_block_3 36480 32 512 528 16
cert_test_block_3 36480 33 528 544 16
cert_test_block_3 36480 34 544 560 16
cert_test_block_3 36480 35 560 576 16
cert_test_block_3 36480 36 576 592 16
cert_test_block_3 36480 37 592 608 16
cert_test_block_3 36480 38 608 624 16
cert_test_block_3 36480 39 624 640 16
theorem test36480_complete : Interval test36480 0 640 :=
  (interval_append test36480 0 320 640
  (interval_append test36480 0 160 320
  (interval_append test36480 0 80 160
  (interval_append test36480 0 32 80
  (interval_append test36480 0 16 32
  test36480_block_0
  test36480_block_1)
  (interval_append test36480 32 48 80
  test36480_block_2
  (interval_append test36480 48 64 80
  test36480_block_3
  test36480_block_4)))
  (interval_append test36480 80 112 160
  (interval_append test36480 80 96 112
  test36480_block_5
  test36480_block_6)
  (interval_append test36480 112 128 160
  test36480_block_7
  (interval_append test36480 128 144 160
  test36480_block_8
  test36480_block_9))))
  (interval_append test36480 160 240 320
  (interval_append test36480 160 192 240
  (interval_append test36480 160 176 192
  test36480_block_10
  test36480_block_11)
  (interval_append test36480 192 208 240
  test36480_block_12
  (interval_append test36480 208 224 240
  test36480_block_13
  test36480_block_14)))
  (interval_append test36480 240 272 320
  (interval_append test36480 240 256 272
  test36480_block_15
  test36480_block_16)
  (interval_append test36480 272 288 320
  test36480_block_17
  (interval_append test36480 288 304 320
  test36480_block_18
  test36480_block_19)))))
  (interval_append test36480 320 480 640
  (interval_append test36480 320 400 480
  (interval_append test36480 320 352 400
  (interval_append test36480 320 336 352
  test36480_block_20
  test36480_block_21)
  (interval_append test36480 352 368 400
  test36480_block_22
  (interval_append test36480 368 384 400
  test36480_block_23
  test36480_block_24)))
  (interval_append test36480 400 432 480
  (interval_append test36480 400 416 432
  test36480_block_25
  test36480_block_26)
  (interval_append test36480 432 448 480
  test36480_block_27
  (interval_append test36480 448 464 480
  test36480_block_28
  test36480_block_29))))
  (interval_append test36480 480 560 640
  (interval_append test36480 480 512 560
  (interval_append test36480 480 496 512
  test36480_block_30
  test36480_block_31)
  (interval_append test36480 512 528 560
  test36480_block_32
  (interval_append test36480 528 544 560
  test36480_block_33
  test36480_block_34)))
  (interval_append test36480 560 592 640
  (interval_append test36480 560 576 592
  test36480_block_35
  test36480_block_36)
  (interval_append test36480 592 608 640
  test36480_block_37
  (interval_append test36480 608 624 640
  test36480_block_38
  test36480_block_39))))))
cert_nodeInterval_3 36480 37120
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
cert_test_11 37120
cert_test_block_3 37120 0 0 16 16
cert_test_block_3 37120 1 16 32 16
cert_test_block_3 37120 2 32 48 16
cert_test_block_3 37120 3 48 64 16
cert_test_block_3 37120 4 64 80 16
cert_test_block_3 37120 5 80 96 16
cert_test_block_3 37120 6 96 112 16
cert_test_block_3 37120 7 112 128 16
cert_test_block_3 37120 8 128 144 16
cert_test_block_3 37120 9 144 160 16
cert_test_block_3 37120 10 160 176 16
cert_test_block_3 37120 11 176 192 16
cert_test_block_3 37120 12 192 208 16
cert_test_block_3 37120 13 208 224 16
cert_test_block_3 37120 14 224 240 16
cert_test_block_3 37120 15 240 256 16
cert_test_block_3 37120 16 256 272 16
cert_test_block_3 37120 17 272 288 16
cert_test_block_3 37120 18 288 304 16
cert_test_block_3 37120 19 304 320 16
cert_test_block_3 37120 20 320 336 16
cert_test_block_3 37120 21 336 352 16
cert_test_block_3 37120 22 352 368 16
cert_test_block_3 37120 23 368 384 16
cert_test_block_3 37120 24 384 400 16
cert_test_block_3 37120 25 400 416 16
cert_test_block_3 37120 26 416 432 16
cert_test_block_3 37120 27 432 448 16
cert_test_block_3 37120 28 448 464 16
cert_test_block_3 37120 29 464 480 16
cert_test_block_3 37120 30 480 496 16
cert_test_block_3 37120 31 496 512 16
cert_test_block_3 37120 32 512 528 16
cert_test_block_3 37120 33 528 544 16
cert_test_block_3 37120 34 544 560 16
cert_test_block_3 37120 35 560 576 16
cert_test_block_3 37120 36 576 592 16
cert_test_block_3 37120 37 592 608 16
cert_test_block_3 37120 38 608 624 16
cert_test_block_3 37120 39 624 640 16
theorem test37120_complete : Interval test37120 0 640 :=
  (interval_append test37120 0 320 640
  (interval_append test37120 0 160 320
  (interval_append test37120 0 80 160
  (interval_append test37120 0 32 80
  (interval_append test37120 0 16 32
  test37120_block_0
  test37120_block_1)
  (interval_append test37120 32 48 80
  test37120_block_2
  (interval_append test37120 48 64 80
  test37120_block_3
  test37120_block_4)))
  (interval_append test37120 80 112 160
  (interval_append test37120 80 96 112
  test37120_block_5
  test37120_block_6)
  (interval_append test37120 112 128 160
  test37120_block_7
  (interval_append test37120 128 144 160
  test37120_block_8
  test37120_block_9))))
  (interval_append test37120 160 240 320
  (interval_append test37120 160 192 240
  (interval_append test37120 160 176 192
  test37120_block_10
  test37120_block_11)
  (interval_append test37120 192 208 240
  test37120_block_12
  (interval_append test37120 208 224 240
  test37120_block_13
  test37120_block_14)))
  (interval_append test37120 240 272 320
  (interval_append test37120 240 256 272
  test37120_block_15
  test37120_block_16)
  (interval_append test37120 272 288 320
  test37120_block_17
  (interval_append test37120 288 304 320
  test37120_block_18
  test37120_block_19)))))
  (interval_append test37120 320 480 640
  (interval_append test37120 320 400 480
  (interval_append test37120 320 352 400
  (interval_append test37120 320 336 352
  test37120_block_20
  test37120_block_21)
  (interval_append test37120 352 368 400
  test37120_block_22
  (interval_append test37120 368 384 400
  test37120_block_23
  test37120_block_24)))
  (interval_append test37120 400 432 480
  (interval_append test37120 400 416 432
  test37120_block_25
  test37120_block_26)
  (interval_append test37120 432 448 480
  test37120_block_27
  (interval_append test37120 448 464 480
  test37120_block_28
  test37120_block_29))))
  (interval_append test37120 480 560 640
  (interval_append test37120 480 512 560
  (interval_append test37120 480 496 512
  test37120_block_30
  test37120_block_31)
  (interval_append test37120 512 528 560
  test37120_block_32
  (interval_append test37120 528 544 560
  test37120_block_33
  test37120_block_34)))
  (interval_append test37120 560 592 640
  (interval_append test37120 560 576 592
  test37120_block_35
  test37120_block_36)
  (interval_append test37120 592 608 640
  test37120_block_37
  (interval_append test37120 608 624 640
  test37120_block_38
  test37120_block_39))))))
cert_nodeInterval_3 37120 37760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end
