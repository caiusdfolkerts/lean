module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0298Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 15360
cert_test_block_3 15360 0 0 16 16
cert_test_block_3 15360 1 16 32 16
cert_test_block_3 15360 2 32 48 16
cert_test_block_3 15360 3 48 64 16
cert_test_block_3 15360 4 64 80 16
cert_test_block_3 15360 5 80 96 16
cert_test_block_3 15360 6 96 112 16
cert_test_block_3 15360 7 112 128 16
cert_test_block_3 15360 8 128 144 16
cert_test_block_3 15360 9 144 160 16
cert_test_block_3 15360 10 160 176 16
cert_test_block_3 15360 11 176 192 16
cert_test_block_3 15360 12 192 208 16
cert_test_block_3 15360 13 208 224 16
cert_test_block_3 15360 14 224 240 16
cert_test_block_3 15360 15 240 256 16
cert_test_block_3 15360 16 256 272 16
cert_test_block_3 15360 17 272 288 16
cert_test_block_3 15360 18 288 304 16
cert_test_block_3 15360 19 304 320 16
cert_test_block_3 15360 20 320 336 16
cert_test_block_3 15360 21 336 352 16
cert_test_block_3 15360 22 352 368 16
cert_test_block_3 15360 23 368 384 16
cert_test_block_3 15360 24 384 400 16
cert_test_block_3 15360 25 400 416 16
cert_test_block_3 15360 26 416 432 16
cert_test_block_3 15360 27 432 448 16
cert_test_block_3 15360 28 448 464 16
cert_test_block_3 15360 29 464 480 16
cert_test_block_3 15360 30 480 496 16
cert_test_block_3 15360 31 496 512 16
cert_test_block_3 15360 32 512 528 16
cert_test_block_3 15360 33 528 544 16
cert_test_block_3 15360 34 544 560 16
cert_test_block_3 15360 35 560 576 16
cert_test_block_3 15360 36 576 592 16
cert_test_block_3 15360 37 592 608 16
cert_test_block_3 15360 38 608 624 16
cert_test_block_3 15360 39 624 640 16
theorem test15360_complete : Interval test15360 0 640 :=
  (interval_append test15360 0 320 640
  (interval_append test15360 0 160 320
  (interval_append test15360 0 80 160
  (interval_append test15360 0 32 80
  (interval_append test15360 0 16 32
  test15360_block_0
  test15360_block_1)
  (interval_append test15360 32 48 80
  test15360_block_2
  (interval_append test15360 48 64 80
  test15360_block_3
  test15360_block_4)))
  (interval_append test15360 80 112 160
  (interval_append test15360 80 96 112
  test15360_block_5
  test15360_block_6)
  (interval_append test15360 112 128 160
  test15360_block_7
  (interval_append test15360 128 144 160
  test15360_block_8
  test15360_block_9))))
  (interval_append test15360 160 240 320
  (interval_append test15360 160 192 240
  (interval_append test15360 160 176 192
  test15360_block_10
  test15360_block_11)
  (interval_append test15360 192 208 240
  test15360_block_12
  (interval_append test15360 208 224 240
  test15360_block_13
  test15360_block_14)))
  (interval_append test15360 240 272 320
  (interval_append test15360 240 256 272
  test15360_block_15
  test15360_block_16)
  (interval_append test15360 272 288 320
  test15360_block_17
  (interval_append test15360 288 304 320
  test15360_block_18
  test15360_block_19)))))
  (interval_append test15360 320 480 640
  (interval_append test15360 320 400 480
  (interval_append test15360 320 352 400
  (interval_append test15360 320 336 352
  test15360_block_20
  test15360_block_21)
  (interval_append test15360 352 368 400
  test15360_block_22
  (interval_append test15360 368 384 400
  test15360_block_23
  test15360_block_24)))
  (interval_append test15360 400 432 480
  (interval_append test15360 400 416 432
  test15360_block_25
  test15360_block_26)
  (interval_append test15360 432 448 480
  test15360_block_27
  (interval_append test15360 448 464 480
  test15360_block_28
  test15360_block_29))))
  (interval_append test15360 480 560 640
  (interval_append test15360 480 512 560
  (interval_append test15360 480 496 512
  test15360_block_30
  test15360_block_31)
  (interval_append test15360 512 528 560
  test15360_block_32
  (interval_append test15360 528 544 560
  test15360_block_33
  test15360_block_34)))
  (interval_append test15360 560 592 640
  (interval_append test15360 560 576 592
  test15360_block_35
  test15360_block_36)
  (interval_append test15360 592 608 640
  test15360_block_37
  (interval_append test15360 608 624 640
  test15360_block_38
  test15360_block_39))))))
cert_nodeInterval_3 15360 16000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 16000
cert_test_block_3 16000 0 0 16 16
cert_test_block_3 16000 1 16 32 16
cert_test_block_3 16000 2 32 48 16
cert_test_block_3 16000 3 48 64 16
cert_test_block_3 16000 4 64 80 16
cert_test_block_3 16000 5 80 96 16
cert_test_block_3 16000 6 96 112 16
cert_test_block_3 16000 7 112 128 16
cert_test_block_3 16000 8 128 144 16
cert_test_block_3 16000 9 144 160 16
cert_test_block_3 16000 10 160 176 16
cert_test_block_3 16000 11 176 192 16
cert_test_block_3 16000 12 192 208 16
cert_test_block_3 16000 13 208 224 16
cert_test_block_3 16000 14 224 240 16
cert_test_block_3 16000 15 240 256 16
cert_test_block_3 16000 16 256 272 16
cert_test_block_3 16000 17 272 288 16
cert_test_block_3 16000 18 288 304 16
cert_test_block_3 16000 19 304 320 16
cert_test_block_3 16000 20 320 336 16
cert_test_block_3 16000 21 336 352 16
cert_test_block_3 16000 22 352 368 16
cert_test_block_3 16000 23 368 384 16
cert_test_block_3 16000 24 384 400 16
cert_test_block_3 16000 25 400 416 16
cert_test_block_3 16000 26 416 432 16
cert_test_block_3 16000 27 432 448 16
cert_test_block_3 16000 28 448 464 16
cert_test_block_3 16000 29 464 480 16
cert_test_block_3 16000 30 480 496 16
cert_test_block_3 16000 31 496 512 16
cert_test_block_3 16000 32 512 528 16
cert_test_block_3 16000 33 528 544 16
cert_test_block_3 16000 34 544 560 16
cert_test_block_3 16000 35 560 576 16
cert_test_block_3 16000 36 576 592 16
cert_test_block_3 16000 37 592 608 16
cert_test_block_3 16000 38 608 624 16
cert_test_block_3 16000 39 624 640 16
theorem test16000_complete : Interval test16000 0 640 :=
  (interval_append test16000 0 320 640
  (interval_append test16000 0 160 320
  (interval_append test16000 0 80 160
  (interval_append test16000 0 32 80
  (interval_append test16000 0 16 32
  test16000_block_0
  test16000_block_1)
  (interval_append test16000 32 48 80
  test16000_block_2
  (interval_append test16000 48 64 80
  test16000_block_3
  test16000_block_4)))
  (interval_append test16000 80 112 160
  (interval_append test16000 80 96 112
  test16000_block_5
  test16000_block_6)
  (interval_append test16000 112 128 160
  test16000_block_7
  (interval_append test16000 128 144 160
  test16000_block_8
  test16000_block_9))))
  (interval_append test16000 160 240 320
  (interval_append test16000 160 192 240
  (interval_append test16000 160 176 192
  test16000_block_10
  test16000_block_11)
  (interval_append test16000 192 208 240
  test16000_block_12
  (interval_append test16000 208 224 240
  test16000_block_13
  test16000_block_14)))
  (interval_append test16000 240 272 320
  (interval_append test16000 240 256 272
  test16000_block_15
  test16000_block_16)
  (interval_append test16000 272 288 320
  test16000_block_17
  (interval_append test16000 288 304 320
  test16000_block_18
  test16000_block_19)))))
  (interval_append test16000 320 480 640
  (interval_append test16000 320 400 480
  (interval_append test16000 320 352 400
  (interval_append test16000 320 336 352
  test16000_block_20
  test16000_block_21)
  (interval_append test16000 352 368 400
  test16000_block_22
  (interval_append test16000 368 384 400
  test16000_block_23
  test16000_block_24)))
  (interval_append test16000 400 432 480
  (interval_append test16000 400 416 432
  test16000_block_25
  test16000_block_26)
  (interval_append test16000 432 448 480
  test16000_block_27
  (interval_append test16000 448 464 480
  test16000_block_28
  test16000_block_29))))
  (interval_append test16000 480 560 640
  (interval_append test16000 480 512 560
  (interval_append test16000 480 496 512
  test16000_block_30
  test16000_block_31)
  (interval_append test16000 512 528 560
  test16000_block_32
  (interval_append test16000 528 544 560
  test16000_block_33
  test16000_block_34)))
  (interval_append test16000 560 592 640
  (interval_append test16000 560 576 592
  test16000_block_35
  test16000_block_36)
  (interval_append test16000 592 608 640
  test16000_block_37
  (interval_append test16000 608 624 640
  test16000_block_38
  test16000_block_39))))))
cert_nodeInterval_3 16000 16640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 16640
cert_test_block_3 16640 0 0 16 16
cert_test_block_3 16640 1 16 32 16
cert_test_block_3 16640 2 32 48 16
cert_test_block_3 16640 3 48 64 16
cert_test_block_3 16640 4 64 80 16
cert_test_block_3 16640 5 80 96 16
cert_test_block_3 16640 6 96 112 16
cert_test_block_3 16640 7 112 128 16
cert_test_block_3 16640 8 128 144 16
cert_test_block_3 16640 9 144 160 16
cert_test_block_3 16640 10 160 176 16
cert_test_block_3 16640 11 176 192 16
cert_test_block_3 16640 12 192 208 16
cert_test_block_3 16640 13 208 224 16
cert_test_block_3 16640 14 224 240 16
cert_test_block_3 16640 15 240 256 16
cert_test_block_3 16640 16 256 272 16
cert_test_block_3 16640 17 272 288 16
cert_test_block_3 16640 18 288 304 16
cert_test_block_3 16640 19 304 320 16
cert_test_block_3 16640 20 320 336 16
cert_test_block_3 16640 21 336 352 16
cert_test_block_3 16640 22 352 368 16
cert_test_block_3 16640 23 368 384 16
cert_test_block_3 16640 24 384 400 16
cert_test_block_3 16640 25 400 416 16
cert_test_block_3 16640 26 416 432 16
cert_test_block_3 16640 27 432 448 16
cert_test_block_3 16640 28 448 464 16
cert_test_block_3 16640 29 464 480 16
cert_test_block_3 16640 30 480 496 16
cert_test_block_3 16640 31 496 512 16
cert_test_block_3 16640 32 512 528 16
cert_test_block_3 16640 33 528 544 16
cert_test_block_3 16640 34 544 560 16
cert_test_block_3 16640 35 560 576 16
cert_test_block_3 16640 36 576 592 16
cert_test_block_3 16640 37 592 608 16
cert_test_block_3 16640 38 608 624 16
cert_test_block_3 16640 39 624 640 16
theorem test16640_complete : Interval test16640 0 640 :=
  (interval_append test16640 0 320 640
  (interval_append test16640 0 160 320
  (interval_append test16640 0 80 160
  (interval_append test16640 0 32 80
  (interval_append test16640 0 16 32
  test16640_block_0
  test16640_block_1)
  (interval_append test16640 32 48 80
  test16640_block_2
  (interval_append test16640 48 64 80
  test16640_block_3
  test16640_block_4)))
  (interval_append test16640 80 112 160
  (interval_append test16640 80 96 112
  test16640_block_5
  test16640_block_6)
  (interval_append test16640 112 128 160
  test16640_block_7
  (interval_append test16640 128 144 160
  test16640_block_8
  test16640_block_9))))
  (interval_append test16640 160 240 320
  (interval_append test16640 160 192 240
  (interval_append test16640 160 176 192
  test16640_block_10
  test16640_block_11)
  (interval_append test16640 192 208 240
  test16640_block_12
  (interval_append test16640 208 224 240
  test16640_block_13
  test16640_block_14)))
  (interval_append test16640 240 272 320
  (interval_append test16640 240 256 272
  test16640_block_15
  test16640_block_16)
  (interval_append test16640 272 288 320
  test16640_block_17
  (interval_append test16640 288 304 320
  test16640_block_18
  test16640_block_19)))))
  (interval_append test16640 320 480 640
  (interval_append test16640 320 400 480
  (interval_append test16640 320 352 400
  (interval_append test16640 320 336 352
  test16640_block_20
  test16640_block_21)
  (interval_append test16640 352 368 400
  test16640_block_22
  (interval_append test16640 368 384 400
  test16640_block_23
  test16640_block_24)))
  (interval_append test16640 400 432 480
  (interval_append test16640 400 416 432
  test16640_block_25
  test16640_block_26)
  (interval_append test16640 432 448 480
  test16640_block_27
  (interval_append test16640 448 464 480
  test16640_block_28
  test16640_block_29))))
  (interval_append test16640 480 560 640
  (interval_append test16640 480 512 560
  (interval_append test16640 480 496 512
  test16640_block_30
  test16640_block_31)
  (interval_append test16640 512 528 560
  test16640_block_32
  (interval_append test16640 528 544 560
  test16640_block_33
  test16640_block_34)))
  (interval_append test16640 560 592 640
  (interval_append test16640 560 576 592
  test16640_block_35
  test16640_block_36)
  (interval_append test16640 592 608 640
  test16640_block_37
  (interval_append test16640 608 624 640
  test16640_block_38
  test16640_block_39))))))
cert_nodeInterval_3 16640 17280
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 17280
cert_test_block_3 17280 0 0 16 16
cert_test_block_3 17280 1 16 32 16
cert_test_block_3 17280 2 32 48 16
cert_test_block_3 17280 3 48 64 16
cert_test_block_3 17280 4 64 80 16
cert_test_block_3 17280 5 80 96 16
cert_test_block_3 17280 6 96 112 16
cert_test_block_3 17280 7 112 128 16
cert_test_block_3 17280 8 128 144 16
cert_test_block_3 17280 9 144 160 16
cert_test_block_3 17280 10 160 176 16
cert_test_block_3 17280 11 176 192 16
cert_test_block_3 17280 12 192 208 16
cert_test_block_3 17280 13 208 224 16
cert_test_block_3 17280 14 224 240 16
cert_test_block_3 17280 15 240 256 16
cert_test_block_3 17280 16 256 272 16
cert_test_block_3 17280 17 272 288 16
cert_test_block_3 17280 18 288 304 16
cert_test_block_3 17280 19 304 320 16
cert_test_block_3 17280 20 320 336 16
cert_test_block_3 17280 21 336 352 16
cert_test_block_3 17280 22 352 368 16
cert_test_block_3 17280 23 368 384 16
cert_test_block_3 17280 24 384 400 16
cert_test_block_3 17280 25 400 416 16
cert_test_block_3 17280 26 416 432 16
cert_test_block_3 17280 27 432 448 16
cert_test_block_3 17280 28 448 464 16
cert_test_block_3 17280 29 464 480 16
cert_test_block_3 17280 30 480 496 16
cert_test_block_3 17280 31 496 512 16
cert_test_block_3 17280 32 512 528 16
cert_test_block_3 17280 33 528 544 16
cert_test_block_3 17280 34 544 560 16
cert_test_block_3 17280 35 560 576 16
cert_test_block_3 17280 36 576 592 16
cert_test_block_3 17280 37 592 608 16
cert_test_block_3 17280 38 608 624 16
cert_test_block_3 17280 39 624 640 16
theorem test17280_complete : Interval test17280 0 640 :=
  (interval_append test17280 0 320 640
  (interval_append test17280 0 160 320
  (interval_append test17280 0 80 160
  (interval_append test17280 0 32 80
  (interval_append test17280 0 16 32
  test17280_block_0
  test17280_block_1)
  (interval_append test17280 32 48 80
  test17280_block_2
  (interval_append test17280 48 64 80
  test17280_block_3
  test17280_block_4)))
  (interval_append test17280 80 112 160
  (interval_append test17280 80 96 112
  test17280_block_5
  test17280_block_6)
  (interval_append test17280 112 128 160
  test17280_block_7
  (interval_append test17280 128 144 160
  test17280_block_8
  test17280_block_9))))
  (interval_append test17280 160 240 320
  (interval_append test17280 160 192 240
  (interval_append test17280 160 176 192
  test17280_block_10
  test17280_block_11)
  (interval_append test17280 192 208 240
  test17280_block_12
  (interval_append test17280 208 224 240
  test17280_block_13
  test17280_block_14)))
  (interval_append test17280 240 272 320
  (interval_append test17280 240 256 272
  test17280_block_15
  test17280_block_16)
  (interval_append test17280 272 288 320
  test17280_block_17
  (interval_append test17280 288 304 320
  test17280_block_18
  test17280_block_19)))))
  (interval_append test17280 320 480 640
  (interval_append test17280 320 400 480
  (interval_append test17280 320 352 400
  (interval_append test17280 320 336 352
  test17280_block_20
  test17280_block_21)
  (interval_append test17280 352 368 400
  test17280_block_22
  (interval_append test17280 368 384 400
  test17280_block_23
  test17280_block_24)))
  (interval_append test17280 400 432 480
  (interval_append test17280 400 416 432
  test17280_block_25
  test17280_block_26)
  (interval_append test17280 432 448 480
  test17280_block_27
  (interval_append test17280 448 464 480
  test17280_block_28
  test17280_block_29))))
  (interval_append test17280 480 560 640
  (interval_append test17280 480 512 560
  (interval_append test17280 480 496 512
  test17280_block_30
  test17280_block_31)
  (interval_append test17280 512 528 560
  test17280_block_32
  (interval_append test17280 528 544 560
  test17280_block_33
  test17280_block_34)))
  (interval_append test17280 560 592 640
  (interval_append test17280 560 576 592
  test17280_block_35
  test17280_block_36)
  (interval_append test17280 592 608 640
  test17280_block_37
  (interval_append test17280 608 624 640
  test17280_block_38
  test17280_block_39))))))
cert_nodeInterval_3 17280 17920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 17920
cert_test_block_3 17920 0 0 16 16
cert_test_block_3 17920 1 16 32 16
cert_test_block_3 17920 2 32 48 16
cert_test_block_3 17920 3 48 64 16
cert_test_block_3 17920 4 64 80 16
cert_test_block_3 17920 5 80 96 16
cert_test_block_3 17920 6 96 112 16
cert_test_block_3 17920 7 112 128 16
cert_test_block_3 17920 8 128 144 16
cert_test_block_3 17920 9 144 160 16
cert_test_block_3 17920 10 160 176 16
cert_test_block_3 17920 11 176 192 16
cert_test_block_3 17920 12 192 208 16
cert_test_block_3 17920 13 208 224 16
cert_test_block_3 17920 14 224 240 16
cert_test_block_3 17920 15 240 256 16
cert_test_block_3 17920 16 256 272 16
cert_test_block_3 17920 17 272 288 16
cert_test_block_3 17920 18 288 304 16
cert_test_block_3 17920 19 304 320 16
cert_test_block_3 17920 20 320 336 16
cert_test_block_3 17920 21 336 352 16
cert_test_block_3 17920 22 352 368 16
cert_test_block_3 17920 23 368 384 16
cert_test_block_3 17920 24 384 400 16
cert_test_block_3 17920 25 400 416 16
cert_test_block_3 17920 26 416 432 16
cert_test_block_3 17920 27 432 448 16
cert_test_block_3 17920 28 448 464 16
cert_test_block_3 17920 29 464 480 16
cert_test_block_3 17920 30 480 496 16
cert_test_block_3 17920 31 496 512 16
cert_test_block_3 17920 32 512 528 16
cert_test_block_3 17920 33 528 544 16
cert_test_block_3 17920 34 544 560 16
cert_test_block_3 17920 35 560 576 16
cert_test_block_3 17920 36 576 592 16
cert_test_block_3 17920 37 592 608 16
cert_test_block_3 17920 38 608 624 16
cert_test_block_3 17920 39 624 640 16
theorem test17920_complete : Interval test17920 0 640 :=
  (interval_append test17920 0 320 640
  (interval_append test17920 0 160 320
  (interval_append test17920 0 80 160
  (interval_append test17920 0 32 80
  (interval_append test17920 0 16 32
  test17920_block_0
  test17920_block_1)
  (interval_append test17920 32 48 80
  test17920_block_2
  (interval_append test17920 48 64 80
  test17920_block_3
  test17920_block_4)))
  (interval_append test17920 80 112 160
  (interval_append test17920 80 96 112
  test17920_block_5
  test17920_block_6)
  (interval_append test17920 112 128 160
  test17920_block_7
  (interval_append test17920 128 144 160
  test17920_block_8
  test17920_block_9))))
  (interval_append test17920 160 240 320
  (interval_append test17920 160 192 240
  (interval_append test17920 160 176 192
  test17920_block_10
  test17920_block_11)
  (interval_append test17920 192 208 240
  test17920_block_12
  (interval_append test17920 208 224 240
  test17920_block_13
  test17920_block_14)))
  (interval_append test17920 240 272 320
  (interval_append test17920 240 256 272
  test17920_block_15
  test17920_block_16)
  (interval_append test17920 272 288 320
  test17920_block_17
  (interval_append test17920 288 304 320
  test17920_block_18
  test17920_block_19)))))
  (interval_append test17920 320 480 640
  (interval_append test17920 320 400 480
  (interval_append test17920 320 352 400
  (interval_append test17920 320 336 352
  test17920_block_20
  test17920_block_21)
  (interval_append test17920 352 368 400
  test17920_block_22
  (interval_append test17920 368 384 400
  test17920_block_23
  test17920_block_24)))
  (interval_append test17920 400 432 480
  (interval_append test17920 400 416 432
  test17920_block_25
  test17920_block_26)
  (interval_append test17920 432 448 480
  test17920_block_27
  (interval_append test17920 448 464 480
  test17920_block_28
  test17920_block_29))))
  (interval_append test17920 480 560 640
  (interval_append test17920 480 512 560
  (interval_append test17920 480 496 512
  test17920_block_30
  test17920_block_31)
  (interval_append test17920 512 528 560
  test17920_block_32
  (interval_append test17920 528 544 560
  test17920_block_33
  test17920_block_34)))
  (interval_append test17920 560 592 640
  (interval_append test17920 560 576 592
  test17920_block_35
  test17920_block_36)
  (interval_append test17920 592 608 640
  test17920_block_37
  (interval_append test17920 608 624 640
  test17920_block_38
  test17920_block_39))))))
cert_nodeInterval_3 17920 18560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 18560
cert_test_block_3 18560 0 0 16 16
cert_test_block_3 18560 1 16 32 16
cert_test_block_3 18560 2 32 48 16
cert_test_block_3 18560 3 48 64 16
cert_test_block_3 18560 4 64 80 16
cert_test_block_3 18560 5 80 96 16
cert_test_block_3 18560 6 96 112 16
cert_test_block_3 18560 7 112 128 16
cert_test_block_3 18560 8 128 144 16
cert_test_block_3 18560 9 144 160 16
cert_test_block_3 18560 10 160 176 16
cert_test_block_3 18560 11 176 192 16
cert_test_block_3 18560 12 192 208 16
cert_test_block_3 18560 13 208 224 16
cert_test_block_3 18560 14 224 240 16
cert_test_block_3 18560 15 240 256 16
cert_test_block_3 18560 16 256 272 16
cert_test_block_3 18560 17 272 288 16
cert_test_block_3 18560 18 288 304 16
cert_test_block_3 18560 19 304 320 16
cert_test_block_3 18560 20 320 336 16
cert_test_block_3 18560 21 336 352 16
cert_test_block_3 18560 22 352 368 16
cert_test_block_3 18560 23 368 384 16
cert_test_block_3 18560 24 384 400 16
cert_test_block_3 18560 25 400 416 16
cert_test_block_3 18560 26 416 432 16
cert_test_block_3 18560 27 432 448 16
cert_test_block_3 18560 28 448 464 16
cert_test_block_3 18560 29 464 480 16
cert_test_block_3 18560 30 480 496 16
cert_test_block_3 18560 31 496 512 16
cert_test_block_3 18560 32 512 528 16
cert_test_block_3 18560 33 528 544 16
cert_test_block_3 18560 34 544 560 16
cert_test_block_3 18560 35 560 576 16
cert_test_block_3 18560 36 576 592 16
cert_test_block_3 18560 37 592 608 16
cert_test_block_3 18560 38 608 624 16
cert_test_block_3 18560 39 624 640 16
theorem test18560_complete : Interval test18560 0 640 :=
  (interval_append test18560 0 320 640
  (interval_append test18560 0 160 320
  (interval_append test18560 0 80 160
  (interval_append test18560 0 32 80
  (interval_append test18560 0 16 32
  test18560_block_0
  test18560_block_1)
  (interval_append test18560 32 48 80
  test18560_block_2
  (interval_append test18560 48 64 80
  test18560_block_3
  test18560_block_4)))
  (interval_append test18560 80 112 160
  (interval_append test18560 80 96 112
  test18560_block_5
  test18560_block_6)
  (interval_append test18560 112 128 160
  test18560_block_7
  (interval_append test18560 128 144 160
  test18560_block_8
  test18560_block_9))))
  (interval_append test18560 160 240 320
  (interval_append test18560 160 192 240
  (interval_append test18560 160 176 192
  test18560_block_10
  test18560_block_11)
  (interval_append test18560 192 208 240
  test18560_block_12
  (interval_append test18560 208 224 240
  test18560_block_13
  test18560_block_14)))
  (interval_append test18560 240 272 320
  (interval_append test18560 240 256 272
  test18560_block_15
  test18560_block_16)
  (interval_append test18560 272 288 320
  test18560_block_17
  (interval_append test18560 288 304 320
  test18560_block_18
  test18560_block_19)))))
  (interval_append test18560 320 480 640
  (interval_append test18560 320 400 480
  (interval_append test18560 320 352 400
  (interval_append test18560 320 336 352
  test18560_block_20
  test18560_block_21)
  (interval_append test18560 352 368 400
  test18560_block_22
  (interval_append test18560 368 384 400
  test18560_block_23
  test18560_block_24)))
  (interval_append test18560 400 432 480
  (interval_append test18560 400 416 432
  test18560_block_25
  test18560_block_26)
  (interval_append test18560 432 448 480
  test18560_block_27
  (interval_append test18560 448 464 480
  test18560_block_28
  test18560_block_29))))
  (interval_append test18560 480 560 640
  (interval_append test18560 480 512 560
  (interval_append test18560 480 496 512
  test18560_block_30
  test18560_block_31)
  (interval_append test18560 512 528 560
  test18560_block_32
  (interval_append test18560 528 544 560
  test18560_block_33
  test18560_block_34)))
  (interval_append test18560 560 592 640
  (interval_append test18560 560 576 592
  test18560_block_35
  test18560_block_36)
  (interval_append test18560 592 608 640
  test18560_block_37
  (interval_append test18560 608 624 640
  test18560_block_38
  test18560_block_39))))))
cert_nodeInterval_3 18560 19200
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 19200
cert_test_block_3 19200 0 0 16 16
cert_test_block_3 19200 1 16 32 16
cert_test_block_3 19200 2 32 48 16
cert_test_block_3 19200 3 48 64 16
cert_test_block_3 19200 4 64 80 16
cert_test_block_3 19200 5 80 96 16
cert_test_block_3 19200 6 96 112 16
cert_test_block_3 19200 7 112 128 16
cert_test_block_3 19200 8 128 144 16
cert_test_block_3 19200 9 144 160 16
cert_test_block_3 19200 10 160 176 16
cert_test_block_3 19200 11 176 192 16
cert_test_block_3 19200 12 192 208 16
cert_test_block_3 19200 13 208 223 15
theorem test19200_complete : Interval test19200 0 223 :=
  (interval_append test19200 0 112 223
  (interval_append test19200 0 48 112
  (interval_append test19200 0 16 48
  test19200_block_0
  (interval_append test19200 16 32 48
  test19200_block_1
  test19200_block_2))
  (interval_append test19200 48 80 112
  (interval_append test19200 48 64 80
  test19200_block_3
  test19200_block_4)
  (interval_append test19200 80 96 112
  test19200_block_5
  test19200_block_6)))
  (interval_append test19200 112 160 223
  (interval_append test19200 112 128 160
  test19200_block_7
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9))
  (interval_append test19200 160 192 223
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11)
  (interval_append test19200 192 208 223
  test19200_block_12
  test19200_block_13))))
cert_nodeInterval_3 19200 19423
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
end
end
