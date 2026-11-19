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
cert_test_11 57600
cert_test_block_3 57600 0 0 16 16
cert_test_block_3 57600 1 16 32 16
cert_test_block_3 57600 2 32 48 16
cert_test_block_3 57600 3 48 64 16
cert_test_block_3 57600 4 64 80 16
cert_test_block_3 57600 5 80 96 16
cert_test_block_3 57600 6 96 112 16
cert_test_block_3 57600 7 112 128 16
cert_test_block_3 57600 8 128 144 16
cert_test_block_3 57600 9 144 160 16
cert_test_block_3 57600 10 160 176 16
cert_test_block_3 57600 11 176 192 16
cert_test_block_3 57600 12 192 208 16
cert_test_block_3 57600 13 208 224 16
cert_test_block_3 57600 14 224 240 16
cert_test_block_3 57600 15 240 256 16
cert_test_block_3 57600 16 256 272 16
cert_test_block_3 57600 17 272 288 16
cert_test_block_3 57600 18 288 304 16
cert_test_block_3 57600 19 304 320 16
cert_test_block_3 57600 20 320 336 16
cert_test_block_3 57600 21 336 352 16
cert_test_block_3 57600 22 352 368 16
cert_test_block_3 57600 23 368 384 16
cert_test_block_3 57600 24 384 400 16
cert_test_block_3 57600 25 400 416 16
cert_test_block_3 57600 26 416 432 16
cert_test_block_3 57600 27 432 448 16
cert_test_block_3 57600 28 448 464 16
cert_test_block_3 57600 29 464 480 16
cert_test_block_3 57600 30 480 496 16
cert_test_block_3 57600 31 496 512 16
cert_test_block_3 57600 32 512 528 16
cert_test_block_3 57600 33 528 544 16
cert_test_block_3 57600 34 544 560 16
cert_test_block_3 57600 35 560 576 16
cert_test_block_3 57600 36 576 592 16
cert_test_block_3 57600 37 592 608 16
cert_test_block_3 57600 38 608 624 16
cert_test_block_3 57600 39 624 640 16
theorem test57600_complete : Interval test57600 0 640 :=
  (interval_append test57600 0 320 640
  (interval_append test57600 0 160 320
  (interval_append test57600 0 80 160
  (interval_append test57600 0 32 80
  (interval_append test57600 0 16 32
  test57600_block_0
  test57600_block_1)
  (interval_append test57600 32 48 80
  test57600_block_2
  (interval_append test57600 48 64 80
  test57600_block_3
  test57600_block_4)))
  (interval_append test57600 80 112 160
  (interval_append test57600 80 96 112
  test57600_block_5
  test57600_block_6)
  (interval_append test57600 112 128 160
  test57600_block_7
  (interval_append test57600 128 144 160
  test57600_block_8
  test57600_block_9))))
  (interval_append test57600 160 240 320
  (interval_append test57600 160 192 240
  (interval_append test57600 160 176 192
  test57600_block_10
  test57600_block_11)
  (interval_append test57600 192 208 240
  test57600_block_12
  (interval_append test57600 208 224 240
  test57600_block_13
  test57600_block_14)))
  (interval_append test57600 240 272 320
  (interval_append test57600 240 256 272
  test57600_block_15
  test57600_block_16)
  (interval_append test57600 272 288 320
  test57600_block_17
  (interval_append test57600 288 304 320
  test57600_block_18
  test57600_block_19)))))
  (interval_append test57600 320 480 640
  (interval_append test57600 320 400 480
  (interval_append test57600 320 352 400
  (interval_append test57600 320 336 352
  test57600_block_20
  test57600_block_21)
  (interval_append test57600 352 368 400
  test57600_block_22
  (interval_append test57600 368 384 400
  test57600_block_23
  test57600_block_24)))
  (interval_append test57600 400 432 480
  (interval_append test57600 400 416 432
  test57600_block_25
  test57600_block_26)
  (interval_append test57600 432 448 480
  test57600_block_27
  (interval_append test57600 448 464 480
  test57600_block_28
  test57600_block_29))))
  (interval_append test57600 480 560 640
  (interval_append test57600 480 512 560
  (interval_append test57600 480 496 512
  test57600_block_30
  test57600_block_31)
  (interval_append test57600 512 528 560
  test57600_block_32
  (interval_append test57600 528 544 560
  test57600_block_33
  test57600_block_34)))
  (interval_append test57600 560 592 640
  (interval_append test57600 560 576 592
  test57600_block_35
  test57600_block_36)
  (interval_append test57600 592 608 640
  test57600_block_37
  (interval_append test57600 608 624 640
  test57600_block_38
  test57600_block_39))))))
cert_nodeInterval_3 57600 58240
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
cert_test_11 58240
cert_test_block_3 58240 0 0 16 16
cert_test_block_3 58240 1 16 32 16
cert_test_block_3 58240 2 32 48 16
cert_test_block_3 58240 3 48 64 16
cert_test_block_3 58240 4 64 80 16
cert_test_block_3 58240 5 80 96 16
cert_test_block_3 58240 6 96 112 16
cert_test_block_3 58240 7 112 128 16
cert_test_block_3 58240 8 128 144 16
cert_test_block_3 58240 9 144 160 16
cert_test_block_3 58240 10 160 176 16
cert_test_block_3 58240 11 176 192 16
cert_test_block_3 58240 12 192 208 16
cert_test_block_3 58240 13 208 224 16
cert_test_block_3 58240 14 224 240 16
cert_test_block_3 58240 15 240 256 16
cert_test_block_3 58240 16 256 272 16
cert_test_block_3 58240 17 272 288 16
cert_test_block_3 58240 18 288 304 16
cert_test_block_3 58240 19 304 320 16
cert_test_block_3 58240 20 320 336 16
cert_test_block_3 58240 21 336 352 16
cert_test_block_3 58240 22 352 368 16
cert_test_block_3 58240 23 368 384 16
cert_test_block_3 58240 24 384 400 16
cert_test_block_3 58240 25 400 416 16
cert_test_block_3 58240 26 416 432 16
cert_test_block_3 58240 27 432 448 16
cert_test_block_3 58240 28 448 464 16
cert_test_block_3 58240 29 464 480 16
cert_test_block_3 58240 30 480 496 16
cert_test_block_3 58240 31 496 512 16
cert_test_block_3 58240 32 512 528 16
cert_test_block_3 58240 33 528 544 16
cert_test_block_3 58240 34 544 560 16
cert_test_block_3 58240 35 560 576 16
cert_test_block_3 58240 36 576 592 16
cert_test_block_3 58240 37 592 608 16
cert_test_block_3 58240 38 608 624 16
cert_test_block_3 58240 39 624 640 16
theorem test58240_complete : Interval test58240 0 640 :=
  (interval_append test58240 0 320 640
  (interval_append test58240 0 160 320
  (interval_append test58240 0 80 160
  (interval_append test58240 0 32 80
  (interval_append test58240 0 16 32
  test58240_block_0
  test58240_block_1)
  (interval_append test58240 32 48 80
  test58240_block_2
  (interval_append test58240 48 64 80
  test58240_block_3
  test58240_block_4)))
  (interval_append test58240 80 112 160
  (interval_append test58240 80 96 112
  test58240_block_5
  test58240_block_6)
  (interval_append test58240 112 128 160
  test58240_block_7
  (interval_append test58240 128 144 160
  test58240_block_8
  test58240_block_9))))
  (interval_append test58240 160 240 320
  (interval_append test58240 160 192 240
  (interval_append test58240 160 176 192
  test58240_block_10
  test58240_block_11)
  (interval_append test58240 192 208 240
  test58240_block_12
  (interval_append test58240 208 224 240
  test58240_block_13
  test58240_block_14)))
  (interval_append test58240 240 272 320
  (interval_append test58240 240 256 272
  test58240_block_15
  test58240_block_16)
  (interval_append test58240 272 288 320
  test58240_block_17
  (interval_append test58240 288 304 320
  test58240_block_18
  test58240_block_19)))))
  (interval_append test58240 320 480 640
  (interval_append test58240 320 400 480
  (interval_append test58240 320 352 400
  (interval_append test58240 320 336 352
  test58240_block_20
  test58240_block_21)
  (interval_append test58240 352 368 400
  test58240_block_22
  (interval_append test58240 368 384 400
  test58240_block_23
  test58240_block_24)))
  (interval_append test58240 400 432 480
  (interval_append test58240 400 416 432
  test58240_block_25
  test58240_block_26)
  (interval_append test58240 432 448 480
  test58240_block_27
  (interval_append test58240 448 464 480
  test58240_block_28
  test58240_block_29))))
  (interval_append test58240 480 560 640
  (interval_append test58240 480 512 560
  (interval_append test58240 480 496 512
  test58240_block_30
  test58240_block_31)
  (interval_append test58240 512 528 560
  test58240_block_32
  (interval_append test58240 528 544 560
  test58240_block_33
  test58240_block_34)))
  (interval_append test58240 560 592 640
  (interval_append test58240 560 576 592
  test58240_block_35
  test58240_block_36)
  (interval_append test58240 592 608 640
  test58240_block_37
  (interval_append test58240 608 624 640
  test58240_block_38
  test58240_block_39))))))
cert_nodeInterval_3 58240 58880
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
cert_test_11 58880
cert_test_block_3 58880 0 0 16 16
cert_test_block_3 58880 1 16 32 16
cert_test_block_3 58880 2 32 48 16
cert_test_block_3 58880 3 48 64 16
cert_test_block_3 58880 4 64 80 16
cert_test_block_3 58880 5 80 96 16
cert_test_block_3 58880 6 96 112 16
cert_test_block_3 58880 7 112 128 16
cert_test_block_3 58880 8 128 144 16
cert_test_block_3 58880 9 144 160 16
cert_test_block_3 58880 10 160 176 16
cert_test_block_3 58880 11 176 192 16
cert_test_block_3 58880 12 192 208 16
cert_test_block_3 58880 13 208 224 16
cert_test_block_3 58880 14 224 240 16
cert_test_block_3 58880 15 240 256 16
cert_test_block_3 58880 16 256 272 16
cert_test_block_3 58880 17 272 288 16
cert_test_block_3 58880 18 288 304 16
cert_test_block_3 58880 19 304 320 16
cert_test_block_3 58880 20 320 336 16
cert_test_block_3 58880 21 336 352 16
cert_test_block_3 58880 22 352 368 16
cert_test_block_3 58880 23 368 384 16
cert_test_block_3 58880 24 384 400 16
cert_test_block_3 58880 25 400 416 16
cert_test_block_3 58880 26 416 432 16
cert_test_block_3 58880 27 432 448 16
cert_test_block_3 58880 28 448 464 16
cert_test_block_3 58880 29 464 480 16
cert_test_block_3 58880 30 480 496 16
cert_test_block_3 58880 31 496 512 16
cert_test_block_3 58880 32 512 528 16
cert_test_block_3 58880 33 528 544 16
cert_test_block_3 58880 34 544 560 16
cert_test_block_3 58880 35 560 576 16
cert_test_block_3 58880 36 576 592 16
cert_test_block_3 58880 37 592 608 16
cert_test_block_3 58880 38 608 624 16
cert_test_block_3 58880 39 624 640 16
theorem test58880_complete : Interval test58880 0 640 :=
  (interval_append test58880 0 320 640
  (interval_append test58880 0 160 320
  (interval_append test58880 0 80 160
  (interval_append test58880 0 32 80
  (interval_append test58880 0 16 32
  test58880_block_0
  test58880_block_1)
  (interval_append test58880 32 48 80
  test58880_block_2
  (interval_append test58880 48 64 80
  test58880_block_3
  test58880_block_4)))
  (interval_append test58880 80 112 160
  (interval_append test58880 80 96 112
  test58880_block_5
  test58880_block_6)
  (interval_append test58880 112 128 160
  test58880_block_7
  (interval_append test58880 128 144 160
  test58880_block_8
  test58880_block_9))))
  (interval_append test58880 160 240 320
  (interval_append test58880 160 192 240
  (interval_append test58880 160 176 192
  test58880_block_10
  test58880_block_11)
  (interval_append test58880 192 208 240
  test58880_block_12
  (interval_append test58880 208 224 240
  test58880_block_13
  test58880_block_14)))
  (interval_append test58880 240 272 320
  (interval_append test58880 240 256 272
  test58880_block_15
  test58880_block_16)
  (interval_append test58880 272 288 320
  test58880_block_17
  (interval_append test58880 288 304 320
  test58880_block_18
  test58880_block_19)))))
  (interval_append test58880 320 480 640
  (interval_append test58880 320 400 480
  (interval_append test58880 320 352 400
  (interval_append test58880 320 336 352
  test58880_block_20
  test58880_block_21)
  (interval_append test58880 352 368 400
  test58880_block_22
  (interval_append test58880 368 384 400
  test58880_block_23
  test58880_block_24)))
  (interval_append test58880 400 432 480
  (interval_append test58880 400 416 432
  test58880_block_25
  test58880_block_26)
  (interval_append test58880 432 448 480
  test58880_block_27
  (interval_append test58880 448 464 480
  test58880_block_28
  test58880_block_29))))
  (interval_append test58880 480 560 640
  (interval_append test58880 480 512 560
  (interval_append test58880 480 496 512
  test58880_block_30
  test58880_block_31)
  (interval_append test58880 512 528 560
  test58880_block_32
  (interval_append test58880 528 544 560
  test58880_block_33
  test58880_block_34)))
  (interval_append test58880 560 592 640
  (interval_append test58880 560 576 592
  test58880_block_35
  test58880_block_36)
  (interval_append test58880 592 608 640
  test58880_block_37
  (interval_append test58880 608 624 640
  test58880_block_38
  test58880_block_39))))))
cert_nodeInterval_3 58880 59520
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
cert_test_11 59520
cert_test_block_3 59520 0 0 16 16
cert_test_block_3 59520 1 16 32 16
cert_test_block_3 59520 2 32 48 16
cert_test_block_3 59520 3 48 64 16
cert_test_block_3 59520 4 64 80 16
cert_test_block_3 59520 5 80 96 16
cert_test_block_3 59520 6 96 112 16
cert_test_block_3 59520 7 112 128 16
cert_test_block_3 59520 8 128 144 16
cert_test_block_3 59520 9 144 160 16
cert_test_block_3 59520 10 160 176 16
cert_test_block_3 59520 11 176 192 16
cert_test_block_3 59520 12 192 208 16
cert_test_block_3 59520 13 208 224 16
cert_test_block_3 59520 14 224 240 16
cert_test_block_3 59520 15 240 256 16
cert_test_block_3 59520 16 256 272 16
cert_test_block_3 59520 17 272 288 16
cert_test_block_3 59520 18 288 304 16
cert_test_block_3 59520 19 304 320 16
cert_test_block_3 59520 20 320 336 16
cert_test_block_3 59520 21 336 352 16
cert_test_block_3 59520 22 352 368 16
cert_test_block_3 59520 23 368 384 16
cert_test_block_3 59520 24 384 400 16
cert_test_block_3 59520 25 400 416 16
cert_test_block_3 59520 26 416 432 16
cert_test_block_3 59520 27 432 448 16
cert_test_block_3 59520 28 448 464 16
cert_test_block_3 59520 29 464 480 16
cert_test_block_3 59520 30 480 496 16
cert_test_block_3 59520 31 496 512 16
cert_test_block_3 59520 32 512 528 16
cert_test_block_3 59520 33 528 544 16
cert_test_block_3 59520 34 544 560 16
cert_test_block_3 59520 35 560 576 16
cert_test_block_3 59520 36 576 592 16
cert_test_block_3 59520 37 592 608 16
cert_test_block_3 59520 38 608 624 16
cert_test_block_3 59520 39 624 640 16
theorem test59520_complete : Interval test59520 0 640 :=
  (interval_append test59520 0 320 640
  (interval_append test59520 0 160 320
  (interval_append test59520 0 80 160
  (interval_append test59520 0 32 80
  (interval_append test59520 0 16 32
  test59520_block_0
  test59520_block_1)
  (interval_append test59520 32 48 80
  test59520_block_2
  (interval_append test59520 48 64 80
  test59520_block_3
  test59520_block_4)))
  (interval_append test59520 80 112 160
  (interval_append test59520 80 96 112
  test59520_block_5
  test59520_block_6)
  (interval_append test59520 112 128 160
  test59520_block_7
  (interval_append test59520 128 144 160
  test59520_block_8
  test59520_block_9))))
  (interval_append test59520 160 240 320
  (interval_append test59520 160 192 240
  (interval_append test59520 160 176 192
  test59520_block_10
  test59520_block_11)
  (interval_append test59520 192 208 240
  test59520_block_12
  (interval_append test59520 208 224 240
  test59520_block_13
  test59520_block_14)))
  (interval_append test59520 240 272 320
  (interval_append test59520 240 256 272
  test59520_block_15
  test59520_block_16)
  (interval_append test59520 272 288 320
  test59520_block_17
  (interval_append test59520 288 304 320
  test59520_block_18
  test59520_block_19)))))
  (interval_append test59520 320 480 640
  (interval_append test59520 320 400 480
  (interval_append test59520 320 352 400
  (interval_append test59520 320 336 352
  test59520_block_20
  test59520_block_21)
  (interval_append test59520 352 368 400
  test59520_block_22
  (interval_append test59520 368 384 400
  test59520_block_23
  test59520_block_24)))
  (interval_append test59520 400 432 480
  (interval_append test59520 400 416 432
  test59520_block_25
  test59520_block_26)
  (interval_append test59520 432 448 480
  test59520_block_27
  (interval_append test59520 448 464 480
  test59520_block_28
  test59520_block_29))))
  (interval_append test59520 480 560 640
  (interval_append test59520 480 512 560
  (interval_append test59520 480 496 512
  test59520_block_30
  test59520_block_31)
  (interval_append test59520 512 528 560
  test59520_block_32
  (interval_append test59520 528 544 560
  test59520_block_33
  test59520_block_34)))
  (interval_append test59520 560 592 640
  (interval_append test59520 560 576 592
  test59520_block_35
  test59520_block_36)
  (interval_append test59520 592 608 640
  test59520_block_37
  (interval_append test59520 608 624 640
  test59520_block_38
  test59520_block_39))))))
cert_nodeInterval_3 59520 60160
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
cert_test_11 60160
cert_test_block_3 60160 0 0 16 16
cert_test_block_3 60160 1 16 32 16
cert_test_block_3 60160 2 32 48 16
cert_test_block_3 60160 3 48 64 16
cert_test_block_3 60160 4 64 80 16
cert_test_block_3 60160 5 80 96 16
cert_test_block_3 60160 6 96 112 16
cert_test_block_3 60160 7 112 128 16
cert_test_block_3 60160 8 128 144 16
cert_test_block_3 60160 9 144 160 16
cert_test_block_3 60160 10 160 176 16
cert_test_block_3 60160 11 176 192 16
cert_test_block_3 60160 12 192 208 16
cert_test_block_3 60160 13 208 224 16
cert_test_block_3 60160 14 224 240 16
cert_test_block_3 60160 15 240 256 16
cert_test_block_3 60160 16 256 272 16
cert_test_block_3 60160 17 272 288 16
cert_test_block_3 60160 18 288 304 16
cert_test_block_3 60160 19 304 320 16
cert_test_block_3 60160 20 320 336 16
cert_test_block_3 60160 21 336 352 16
cert_test_block_3 60160 22 352 368 16
cert_test_block_3 60160 23 368 384 16
cert_test_block_3 60160 24 384 400 16
cert_test_block_3 60160 25 400 416 16
cert_test_block_3 60160 26 416 432 16
cert_test_block_3 60160 27 432 448 16
cert_test_block_3 60160 28 448 464 16
cert_test_block_3 60160 29 464 480 16
cert_test_block_3 60160 30 480 496 16
cert_test_block_3 60160 31 496 512 16
cert_test_block_3 60160 32 512 528 16
cert_test_block_3 60160 33 528 544 16
cert_test_block_3 60160 34 544 560 16
cert_test_block_3 60160 35 560 576 16
cert_test_block_3 60160 36 576 592 16
cert_test_block_3 60160 37 592 608 16
cert_test_block_3 60160 38 608 624 16
cert_test_block_3 60160 39 624 640 16
theorem test60160_complete : Interval test60160 0 640 :=
  (interval_append test60160 0 320 640
  (interval_append test60160 0 160 320
  (interval_append test60160 0 80 160
  (interval_append test60160 0 32 80
  (interval_append test60160 0 16 32
  test60160_block_0
  test60160_block_1)
  (interval_append test60160 32 48 80
  test60160_block_2
  (interval_append test60160 48 64 80
  test60160_block_3
  test60160_block_4)))
  (interval_append test60160 80 112 160
  (interval_append test60160 80 96 112
  test60160_block_5
  test60160_block_6)
  (interval_append test60160 112 128 160
  test60160_block_7
  (interval_append test60160 128 144 160
  test60160_block_8
  test60160_block_9))))
  (interval_append test60160 160 240 320
  (interval_append test60160 160 192 240
  (interval_append test60160 160 176 192
  test60160_block_10
  test60160_block_11)
  (interval_append test60160 192 208 240
  test60160_block_12
  (interval_append test60160 208 224 240
  test60160_block_13
  test60160_block_14)))
  (interval_append test60160 240 272 320
  (interval_append test60160 240 256 272
  test60160_block_15
  test60160_block_16)
  (interval_append test60160 272 288 320
  test60160_block_17
  (interval_append test60160 288 304 320
  test60160_block_18
  test60160_block_19)))))
  (interval_append test60160 320 480 640
  (interval_append test60160 320 400 480
  (interval_append test60160 320 352 400
  (interval_append test60160 320 336 352
  test60160_block_20
  test60160_block_21)
  (interval_append test60160 352 368 400
  test60160_block_22
  (interval_append test60160 368 384 400
  test60160_block_23
  test60160_block_24)))
  (interval_append test60160 400 432 480
  (interval_append test60160 400 416 432
  test60160_block_25
  test60160_block_26)
  (interval_append test60160 432 448 480
  test60160_block_27
  (interval_append test60160 448 464 480
  test60160_block_28
  test60160_block_29))))
  (interval_append test60160 480 560 640
  (interval_append test60160 480 512 560
  (interval_append test60160 480 496 512
  test60160_block_30
  test60160_block_31)
  (interval_append test60160 512 528 560
  test60160_block_32
  (interval_append test60160 528 544 560
  test60160_block_33
  test60160_block_34)))
  (interval_append test60160 560 592 640
  (interval_append test60160 560 576 592
  test60160_block_35
  test60160_block_36)
  (interval_append test60160 592 608 640
  test60160_block_37
  (interval_append test60160 608 624 640
  test60160_block_38
  test60160_block_39))))))
cert_nodeInterval_3 60160 60800
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
cert_test_11 60800
cert_test_block_3 60800 0 0 16 16
cert_test_block_3 60800 1 16 32 16
cert_test_block_3 60800 2 32 48 16
cert_test_block_3 60800 3 48 64 16
cert_test_block_3 60800 4 64 80 16
cert_test_block_3 60800 5 80 96 16
cert_test_block_3 60800 6 96 112 16
cert_test_block_3 60800 7 112 128 16
cert_test_block_3 60800 8 128 144 16
cert_test_block_3 60800 9 144 160 16
cert_test_block_3 60800 10 160 176 16
cert_test_block_3 60800 11 176 192 16
cert_test_block_3 60800 12 192 208 16
cert_test_block_3 60800 13 208 224 16
cert_test_block_3 60800 14 224 240 16
cert_test_block_3 60800 15 240 256 16
cert_test_block_3 60800 16 256 272 16
cert_test_block_3 60800 17 272 288 16
cert_test_block_3 60800 18 288 304 16
cert_test_block_3 60800 19 304 320 16
cert_test_block_3 60800 20 320 336 16
cert_test_block_3 60800 21 336 352 16
cert_test_block_3 60800 22 352 368 16
cert_test_block_3 60800 23 368 384 16
cert_test_block_3 60800 24 384 400 16
cert_test_block_3 60800 25 400 416 16
cert_test_block_3 60800 26 416 432 16
cert_test_block_3 60800 27 432 448 16
cert_test_block_3 60800 28 448 464 16
cert_test_block_3 60800 29 464 480 16
cert_test_block_3 60800 30 480 496 16
cert_test_block_3 60800 31 496 512 16
cert_test_block_3 60800 32 512 528 16
cert_test_block_3 60800 33 528 544 16
cert_test_block_3 60800 34 544 560 16
cert_test_block_3 60800 35 560 576 16
cert_test_block_3 60800 36 576 592 16
cert_test_block_3 60800 37 592 608 16
cert_test_block_3 60800 38 608 624 16
cert_test_block_3 60800 39 624 640 16
theorem test60800_complete : Interval test60800 0 640 :=
  (interval_append test60800 0 320 640
  (interval_append test60800 0 160 320
  (interval_append test60800 0 80 160
  (interval_append test60800 0 32 80
  (interval_append test60800 0 16 32
  test60800_block_0
  test60800_block_1)
  (interval_append test60800 32 48 80
  test60800_block_2
  (interval_append test60800 48 64 80
  test60800_block_3
  test60800_block_4)))
  (interval_append test60800 80 112 160
  (interval_append test60800 80 96 112
  test60800_block_5
  test60800_block_6)
  (interval_append test60800 112 128 160
  test60800_block_7
  (interval_append test60800 128 144 160
  test60800_block_8
  test60800_block_9))))
  (interval_append test60800 160 240 320
  (interval_append test60800 160 192 240
  (interval_append test60800 160 176 192
  test60800_block_10
  test60800_block_11)
  (interval_append test60800 192 208 240
  test60800_block_12
  (interval_append test60800 208 224 240
  test60800_block_13
  test60800_block_14)))
  (interval_append test60800 240 272 320
  (interval_append test60800 240 256 272
  test60800_block_15
  test60800_block_16)
  (interval_append test60800 272 288 320
  test60800_block_17
  (interval_append test60800 288 304 320
  test60800_block_18
  test60800_block_19)))))
  (interval_append test60800 320 480 640
  (interval_append test60800 320 400 480
  (interval_append test60800 320 352 400
  (interval_append test60800 320 336 352
  test60800_block_20
  test60800_block_21)
  (interval_append test60800 352 368 400
  test60800_block_22
  (interval_append test60800 368 384 400
  test60800_block_23
  test60800_block_24)))
  (interval_append test60800 400 432 480
  (interval_append test60800 400 416 432
  test60800_block_25
  test60800_block_26)
  (interval_append test60800 432 448 480
  test60800_block_27
  (interval_append test60800 448 464 480
  test60800_block_28
  test60800_block_29))))
  (interval_append test60800 480 560 640
  (interval_append test60800 480 512 560
  (interval_append test60800 480 496 512
  test60800_block_30
  test60800_block_31)
  (interval_append test60800 512 528 560
  test60800_block_32
  (interval_append test60800 528 544 560
  test60800_block_33
  test60800_block_34)))
  (interval_append test60800 560 592 640
  (interval_append test60800 560 576 592
  test60800_block_35
  test60800_block_36)
  (interval_append test60800 592 608 640
  test60800_block_37
  (interval_append test60800 608 624 640
  test60800_block_38
  test60800_block_39))))))
cert_nodeInterval_3 60800 61440
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
cert_test_11 61440
cert_test_block_3 61440 0 0 16 16
cert_test_block_3 61440 1 16 32 16
cert_test_block_3 61440 2 32 48 16
cert_test_block_3 61440 3 48 64 16
cert_test_block_3 61440 4 64 80 16
cert_test_block_3 61440 5 80 96 16
cert_test_block_3 61440 6 96 112 16
cert_test_block_3 61440 7 112 128 16
cert_test_block_3 61440 8 128 144 16
cert_test_block_3 61440 9 144 160 16
cert_test_block_3 61440 10 160 176 16
cert_test_block_3 61440 11 176 192 16
cert_test_block_3 61440 12 192 208 16
cert_test_block_3 61440 13 208 224 16
cert_test_block_3 61440 14 224 240 16
cert_test_block_3 61440 15 240 256 16
cert_test_block_3 61440 16 256 272 16
cert_test_block_3 61440 17 272 288 16
cert_test_block_3 61440 18 288 304 16
cert_test_block_3 61440 19 304 320 16
cert_test_block_3 61440 20 320 336 16
cert_test_block_3 61440 21 336 352 16
cert_test_block_3 61440 22 352 368 16
cert_test_block_3 61440 23 368 384 16
cert_test_block_3 61440 24 384 400 16
cert_test_block_3 61440 25 400 416 16
cert_test_block_3 61440 26 416 432 16
cert_test_block_3 61440 27 432 448 16
cert_test_block_3 61440 28 448 464 16
cert_test_block_3 61440 29 464 480 16
cert_test_block_3 61440 30 480 496 16
cert_test_block_3 61440 31 496 512 16
cert_test_block_3 61440 32 512 528 16
cert_test_block_3 61440 33 528 544 16
cert_test_block_3 61440 34 544 560 16
cert_test_block_3 61440 35 560 576 16
cert_test_block_3 61440 36 576 592 16
cert_test_block_3 61440 37 592 608 16
cert_test_block_3 61440 38 608 624 16
cert_test_block_3 61440 39 624 640 16
theorem test61440_complete : Interval test61440 0 640 :=
  (interval_append test61440 0 320 640
  (interval_append test61440 0 160 320
  (interval_append test61440 0 80 160
  (interval_append test61440 0 32 80
  (interval_append test61440 0 16 32
  test61440_block_0
  test61440_block_1)
  (interval_append test61440 32 48 80
  test61440_block_2
  (interval_append test61440 48 64 80
  test61440_block_3
  test61440_block_4)))
  (interval_append test61440 80 112 160
  (interval_append test61440 80 96 112
  test61440_block_5
  test61440_block_6)
  (interval_append test61440 112 128 160
  test61440_block_7
  (interval_append test61440 128 144 160
  test61440_block_8
  test61440_block_9))))
  (interval_append test61440 160 240 320
  (interval_append test61440 160 192 240
  (interval_append test61440 160 176 192
  test61440_block_10
  test61440_block_11)
  (interval_append test61440 192 208 240
  test61440_block_12
  (interval_append test61440 208 224 240
  test61440_block_13
  test61440_block_14)))
  (interval_append test61440 240 272 320
  (interval_append test61440 240 256 272
  test61440_block_15
  test61440_block_16)
  (interval_append test61440 272 288 320
  test61440_block_17
  (interval_append test61440 288 304 320
  test61440_block_18
  test61440_block_19)))))
  (interval_append test61440 320 480 640
  (interval_append test61440 320 400 480
  (interval_append test61440 320 352 400
  (interval_append test61440 320 336 352
  test61440_block_20
  test61440_block_21)
  (interval_append test61440 352 368 400
  test61440_block_22
  (interval_append test61440 368 384 400
  test61440_block_23
  test61440_block_24)))
  (interval_append test61440 400 432 480
  (interval_append test61440 400 416 432
  test61440_block_25
  test61440_block_26)
  (interval_append test61440 432 448 480
  test61440_block_27
  (interval_append test61440 448 464 480
  test61440_block_28
  test61440_block_29))))
  (interval_append test61440 480 560 640
  (interval_append test61440 480 512 560
  (interval_append test61440 480 496 512
  test61440_block_30
  test61440_block_31)
  (interval_append test61440 512 528 560
  test61440_block_32
  (interval_append test61440 528 544 560
  test61440_block_33
  test61440_block_34)))
  (interval_append test61440 560 592 640
  (interval_append test61440 560 576 592
  test61440_block_35
  test61440_block_36)
  (interval_append test61440 592 608 640
  test61440_block_37
  (interval_append test61440 608 624 640
  test61440_block_38
  test61440_block_39))))))
cert_nodeInterval_3 61440 62080
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
cert_test_11 62080
cert_test_block_3 62080 0 0 16 16
cert_test_block_3 62080 1 16 32 16
cert_test_block_3 62080 2 32 48 16
cert_test_block_3 62080 3 48 64 16
cert_test_block_3 62080 4 64 80 16
cert_test_block_3 62080 5 80 96 16
cert_test_block_3 62080 6 96 112 16
cert_test_block_3 62080 7 112 128 16
cert_test_block_3 62080 8 128 144 16
cert_test_block_3 62080 9 144 160 16
cert_test_block_3 62080 10 160 176 16
cert_test_block_3 62080 11 176 192 16
cert_test_block_3 62080 12 192 208 16
cert_test_block_3 62080 13 208 224 16
cert_test_block_3 62080 14 224 240 16
cert_test_block_3 62080 15 240 256 16
cert_test_block_3 62080 16 256 272 16
cert_test_block_3 62080 17 272 288 16
cert_test_block_3 62080 18 288 304 16
cert_test_block_3 62080 19 304 320 16
cert_test_block_3 62080 20 320 336 16
cert_test_block_3 62080 21 336 352 16
cert_test_block_3 62080 22 352 368 16
cert_test_block_3 62080 23 368 384 16
cert_test_block_3 62080 24 384 400 16
cert_test_block_3 62080 25 400 416 16
cert_test_block_3 62080 26 416 432 16
cert_test_block_3 62080 27 432 448 16
cert_test_block_3 62080 28 448 464 16
cert_test_block_3 62080 29 464 480 16
cert_test_block_3 62080 30 480 496 16
cert_test_block_3 62080 31 496 512 16
cert_test_block_3 62080 32 512 528 16
cert_test_block_3 62080 33 528 544 16
cert_test_block_3 62080 34 544 560 16
cert_test_block_3 62080 35 560 576 16
cert_test_block_3 62080 36 576 592 16
cert_test_block_3 62080 37 592 608 16
cert_test_block_3 62080 38 608 624 16
cert_test_block_3 62080 39 624 640 16
theorem test62080_complete : Interval test62080 0 640 :=
  (interval_append test62080 0 320 640
  (interval_append test62080 0 160 320
  (interval_append test62080 0 80 160
  (interval_append test62080 0 32 80
  (interval_append test62080 0 16 32
  test62080_block_0
  test62080_block_1)
  (interval_append test62080 32 48 80
  test62080_block_2
  (interval_append test62080 48 64 80
  test62080_block_3
  test62080_block_4)))
  (interval_append test62080 80 112 160
  (interval_append test62080 80 96 112
  test62080_block_5
  test62080_block_6)
  (interval_append test62080 112 128 160
  test62080_block_7
  (interval_append test62080 128 144 160
  test62080_block_8
  test62080_block_9))))
  (interval_append test62080 160 240 320
  (interval_append test62080 160 192 240
  (interval_append test62080 160 176 192
  test62080_block_10
  test62080_block_11)
  (interval_append test62080 192 208 240
  test62080_block_12
  (interval_append test62080 208 224 240
  test62080_block_13
  test62080_block_14)))
  (interval_append test62080 240 272 320
  (interval_append test62080 240 256 272
  test62080_block_15
  test62080_block_16)
  (interval_append test62080 272 288 320
  test62080_block_17
  (interval_append test62080 288 304 320
  test62080_block_18
  test62080_block_19)))))
  (interval_append test62080 320 480 640
  (interval_append test62080 320 400 480
  (interval_append test62080 320 352 400
  (interval_append test62080 320 336 352
  test62080_block_20
  test62080_block_21)
  (interval_append test62080 352 368 400
  test62080_block_22
  (interval_append test62080 368 384 400
  test62080_block_23
  test62080_block_24)))
  (interval_append test62080 400 432 480
  (interval_append test62080 400 416 432
  test62080_block_25
  test62080_block_26)
  (interval_append test62080 432 448 480
  test62080_block_27
  (interval_append test62080 448 464 480
  test62080_block_28
  test62080_block_29))))
  (interval_append test62080 480 560 640
  (interval_append test62080 480 512 560
  (interval_append test62080 480 496 512
  test62080_block_30
  test62080_block_31)
  (interval_append test62080 512 528 560
  test62080_block_32
  (interval_append test62080 528 544 560
  test62080_block_33
  test62080_block_34)))
  (interval_append test62080 560 592 640
  (interval_append test62080 560 576 592
  test62080_block_35
  test62080_block_36)
  (interval_append test62080 592 608 640
  test62080_block_37
  (interval_append test62080 608 624 640
  test62080_block_38
  test62080_block_39))))))
cert_nodeInterval_3 62080 62720
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
cert_test_11 62720
cert_test_block_3 62720 0 0 16 16
cert_test_block_3 62720 1 16 32 16
cert_test_block_3 62720 2 32 48 16
cert_test_block_3 62720 3 48 64 16
cert_test_block_3 62720 4 64 80 16
cert_test_block_3 62720 5 80 96 16
cert_test_block_3 62720 6 96 112 16
cert_test_block_3 62720 7 112 128 16
cert_test_block_3 62720 8 128 144 16
cert_test_block_3 62720 9 144 160 16
cert_test_block_3 62720 10 160 176 16
cert_test_block_3 62720 11 176 192 16
cert_test_block_3 62720 12 192 208 16
cert_test_block_3 62720 13 208 224 16
cert_test_block_3 62720 14 224 240 16
cert_test_block_3 62720 15 240 256 16
cert_test_block_3 62720 16 256 272 16
cert_test_block_3 62720 17 272 288 16
cert_test_block_3 62720 18 288 304 16
cert_test_block_3 62720 19 304 320 16
cert_test_block_3 62720 20 320 336 16
cert_test_block_3 62720 21 336 352 16
cert_test_block_3 62720 22 352 368 16
cert_test_block_3 62720 23 368 384 16
cert_test_block_3 62720 24 384 400 16
cert_test_block_3 62720 25 400 416 16
cert_test_block_3 62720 26 416 432 16
cert_test_block_3 62720 27 432 448 16
cert_test_block_3 62720 28 448 464 16
cert_test_block_3 62720 29 464 480 16
cert_test_block_3 62720 30 480 496 16
cert_test_block_3 62720 31 496 512 16
cert_test_block_3 62720 32 512 528 16
cert_test_block_3 62720 33 528 544 16
cert_test_block_3 62720 34 544 560 16
cert_test_block_3 62720 35 560 576 16
cert_test_block_3 62720 36 576 592 16
cert_test_block_3 62720 37 592 608 16
cert_test_block_3 62720 38 608 624 16
cert_test_block_3 62720 39 624 640 16
theorem test62720_complete : Interval test62720 0 640 :=
  (interval_append test62720 0 320 640
  (interval_append test62720 0 160 320
  (interval_append test62720 0 80 160
  (interval_append test62720 0 32 80
  (interval_append test62720 0 16 32
  test62720_block_0
  test62720_block_1)
  (interval_append test62720 32 48 80
  test62720_block_2
  (interval_append test62720 48 64 80
  test62720_block_3
  test62720_block_4)))
  (interval_append test62720 80 112 160
  (interval_append test62720 80 96 112
  test62720_block_5
  test62720_block_6)
  (interval_append test62720 112 128 160
  test62720_block_7
  (interval_append test62720 128 144 160
  test62720_block_8
  test62720_block_9))))
  (interval_append test62720 160 240 320
  (interval_append test62720 160 192 240
  (interval_append test62720 160 176 192
  test62720_block_10
  test62720_block_11)
  (interval_append test62720 192 208 240
  test62720_block_12
  (interval_append test62720 208 224 240
  test62720_block_13
  test62720_block_14)))
  (interval_append test62720 240 272 320
  (interval_append test62720 240 256 272
  test62720_block_15
  test62720_block_16)
  (interval_append test62720 272 288 320
  test62720_block_17
  (interval_append test62720 288 304 320
  test62720_block_18
  test62720_block_19)))))
  (interval_append test62720 320 480 640
  (interval_append test62720 320 400 480
  (interval_append test62720 320 352 400
  (interval_append test62720 320 336 352
  test62720_block_20
  test62720_block_21)
  (interval_append test62720 352 368 400
  test62720_block_22
  (interval_append test62720 368 384 400
  test62720_block_23
  test62720_block_24)))
  (interval_append test62720 400 432 480
  (interval_append test62720 400 416 432
  test62720_block_25
  test62720_block_26)
  (interval_append test62720 432 448 480
  test62720_block_27
  (interval_append test62720 448 464 480
  test62720_block_28
  test62720_block_29))))
  (interval_append test62720 480 560 640
  (interval_append test62720 480 512 560
  (interval_append test62720 480 496 512
  test62720_block_30
  test62720_block_31)
  (interval_append test62720 512 528 560
  test62720_block_32
  (interval_append test62720 528 544 560
  test62720_block_33
  test62720_block_34)))
  (interval_append test62720 560 592 640
  (interval_append test62720 560 576 592
  test62720_block_35
  test62720_block_36)
  (interval_append test62720 592 608 640
  test62720_block_37
  (interval_append test62720 608 624 640
  test62720_block_38
  test62720_block_39))))))
cert_nodeInterval_3 62720 63360
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
cert_test_11 63360
cert_test_block_3 63360 0 0 16 16
cert_test_block_3 63360 1 16 32 16
cert_test_block_3 63360 2 32 48 16
cert_test_block_3 63360 3 48 64 16
cert_test_block_3 63360 4 64 80 16
cert_test_block_3 63360 5 80 96 16
cert_test_block_3 63360 6 96 112 16
cert_test_block_3 63360 7 112 128 16
cert_test_block_3 63360 8 128 144 16
cert_test_block_3 63360 9 144 160 16
cert_test_block_3 63360 10 160 176 16
cert_test_block_3 63360 11 176 192 16
cert_test_block_3 63360 12 192 208 16
cert_test_block_3 63360 13 208 224 16
cert_test_block_3 63360 14 224 240 16
cert_test_block_3 63360 15 240 256 16
cert_test_block_3 63360 16 256 272 16
cert_test_block_3 63360 17 272 288 16
cert_test_block_3 63360 18 288 304 16
cert_test_block_3 63360 19 304 320 16
cert_test_block_3 63360 20 320 336 16
cert_test_block_3 63360 21 336 352 16
cert_test_block_3 63360 22 352 368 16
cert_test_block_3 63360 23 368 384 16
cert_test_block_3 63360 24 384 400 16
cert_test_block_3 63360 25 400 416 16
cert_test_block_3 63360 26 416 432 16
cert_test_block_3 63360 27 432 448 16
cert_test_block_3 63360 28 448 464 16
cert_test_block_3 63360 29 464 480 16
cert_test_block_3 63360 30 480 496 16
cert_test_block_3 63360 31 496 512 16
cert_test_block_3 63360 32 512 528 16
cert_test_block_3 63360 33 528 544 16
cert_test_block_3 63360 34 544 560 16
cert_test_block_3 63360 35 560 576 16
cert_test_block_3 63360 36 576 592 16
cert_test_block_3 63360 37 592 608 16
cert_test_block_3 63360 38 608 624 16
cert_test_block_3 63360 39 624 640 16
theorem test63360_complete : Interval test63360 0 640 :=
  (interval_append test63360 0 320 640
  (interval_append test63360 0 160 320
  (interval_append test63360 0 80 160
  (interval_append test63360 0 32 80
  (interval_append test63360 0 16 32
  test63360_block_0
  test63360_block_1)
  (interval_append test63360 32 48 80
  test63360_block_2
  (interval_append test63360 48 64 80
  test63360_block_3
  test63360_block_4)))
  (interval_append test63360 80 112 160
  (interval_append test63360 80 96 112
  test63360_block_5
  test63360_block_6)
  (interval_append test63360 112 128 160
  test63360_block_7
  (interval_append test63360 128 144 160
  test63360_block_8
  test63360_block_9))))
  (interval_append test63360 160 240 320
  (interval_append test63360 160 192 240
  (interval_append test63360 160 176 192
  test63360_block_10
  test63360_block_11)
  (interval_append test63360 192 208 240
  test63360_block_12
  (interval_append test63360 208 224 240
  test63360_block_13
  test63360_block_14)))
  (interval_append test63360 240 272 320
  (interval_append test63360 240 256 272
  test63360_block_15
  test63360_block_16)
  (interval_append test63360 272 288 320
  test63360_block_17
  (interval_append test63360 288 304 320
  test63360_block_18
  test63360_block_19)))))
  (interval_append test63360 320 480 640
  (interval_append test63360 320 400 480
  (interval_append test63360 320 352 400
  (interval_append test63360 320 336 352
  test63360_block_20
  test63360_block_21)
  (interval_append test63360 352 368 400
  test63360_block_22
  (interval_append test63360 368 384 400
  test63360_block_23
  test63360_block_24)))
  (interval_append test63360 400 432 480
  (interval_append test63360 400 416 432
  test63360_block_25
  test63360_block_26)
  (interval_append test63360 432 448 480
  test63360_block_27
  (interval_append test63360 448 464 480
  test63360_block_28
  test63360_block_29))))
  (interval_append test63360 480 560 640
  (interval_append test63360 480 512 560
  (interval_append test63360 480 496 512
  test63360_block_30
  test63360_block_31)
  (interval_append test63360 512 528 560
  test63360_block_32
  (interval_append test63360 528 544 560
  test63360_block_33
  test63360_block_34)))
  (interval_append test63360 560 592 640
  (interval_append test63360 560 576 592
  test63360_block_35
  test63360_block_36)
  (interval_append test63360 592 608 640
  test63360_block_37
  (interval_append test63360 608 624 640
  test63360_block_38
  test63360_block_39))))))
cert_nodeInterval_3 63360 64000
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
cert_test_11 64000
cert_test_block_3 64000 0 0 16 16
cert_test_block_3 64000 1 16 32 16
cert_test_block_3 64000 2 32 48 16
cert_test_block_3 64000 3 48 64 16
cert_test_block_3 64000 4 64 80 16
cert_test_block_3 64000 5 80 96 16
cert_test_block_3 64000 6 96 112 16
cert_test_block_3 64000 7 112 128 16
cert_test_block_3 64000 8 128 144 16
cert_test_block_3 64000 9 144 160 16
cert_test_block_3 64000 10 160 176 16
cert_test_block_3 64000 11 176 192 16
cert_test_block_3 64000 12 192 208 16
cert_test_block_3 64000 13 208 224 16
cert_test_block_3 64000 14 224 240 16
cert_test_block_3 64000 15 240 256 16
cert_test_block_3 64000 16 256 272 16
cert_test_block_3 64000 17 272 288 16
cert_test_block_3 64000 18 288 304 16
cert_test_block_3 64000 19 304 320 16
cert_test_block_3 64000 20 320 336 16
cert_test_block_3 64000 21 336 352 16
cert_test_block_3 64000 22 352 368 16
cert_test_block_3 64000 23 368 384 16
cert_test_block_3 64000 24 384 400 16
cert_test_block_3 64000 25 400 416 16
cert_test_block_3 64000 26 416 432 16
cert_test_block_3 64000 27 432 448 16
cert_test_block_3 64000 28 448 464 16
cert_test_block_3 64000 29 464 480 16
cert_test_block_3 64000 30 480 496 16
cert_test_block_3 64000 31 496 512 16
cert_test_block_3 64000 32 512 528 16
cert_test_block_3 64000 33 528 544 16
cert_test_block_3 64000 34 544 560 16
cert_test_block_3 64000 35 560 576 16
cert_test_block_3 64000 36 576 592 16
cert_test_block_3 64000 37 592 608 16
cert_test_block_3 64000 38 608 624 16
cert_test_block_3 64000 39 624 640 16
theorem test64000_complete : Interval test64000 0 640 :=
  (interval_append test64000 0 320 640
  (interval_append test64000 0 160 320
  (interval_append test64000 0 80 160
  (interval_append test64000 0 32 80
  (interval_append test64000 0 16 32
  test64000_block_0
  test64000_block_1)
  (interval_append test64000 32 48 80
  test64000_block_2
  (interval_append test64000 48 64 80
  test64000_block_3
  test64000_block_4)))
  (interval_append test64000 80 112 160
  (interval_append test64000 80 96 112
  test64000_block_5
  test64000_block_6)
  (interval_append test64000 112 128 160
  test64000_block_7
  (interval_append test64000 128 144 160
  test64000_block_8
  test64000_block_9))))
  (interval_append test64000 160 240 320
  (interval_append test64000 160 192 240
  (interval_append test64000 160 176 192
  test64000_block_10
  test64000_block_11)
  (interval_append test64000 192 208 240
  test64000_block_12
  (interval_append test64000 208 224 240
  test64000_block_13
  test64000_block_14)))
  (interval_append test64000 240 272 320
  (interval_append test64000 240 256 272
  test64000_block_15
  test64000_block_16)
  (interval_append test64000 272 288 320
  test64000_block_17
  (interval_append test64000 288 304 320
  test64000_block_18
  test64000_block_19)))))
  (interval_append test64000 320 480 640
  (interval_append test64000 320 400 480
  (interval_append test64000 320 352 400
  (interval_append test64000 320 336 352
  test64000_block_20
  test64000_block_21)
  (interval_append test64000 352 368 400
  test64000_block_22
  (interval_append test64000 368 384 400
  test64000_block_23
  test64000_block_24)))
  (interval_append test64000 400 432 480
  (interval_append test64000 400 416 432
  test64000_block_25
  test64000_block_26)
  (interval_append test64000 432 448 480
  test64000_block_27
  (interval_append test64000 448 464 480
  test64000_block_28
  test64000_block_29))))
  (interval_append test64000 480 560 640
  (interval_append test64000 480 512 560
  (interval_append test64000 480 496 512
  test64000_block_30
  test64000_block_31)
  (interval_append test64000 512 528 560
  test64000_block_32
  (interval_append test64000 528 544 560
  test64000_block_33
  test64000_block_34)))
  (interval_append test64000 560 592 640
  (interval_append test64000 560 576 592
  test64000_block_35
  test64000_block_36)
  (interval_append test64000 592 608 640
  test64000_block_37
  (interval_append test64000 608 624 640
  test64000_block_38
  test64000_block_39))))))
cert_nodeInterval_3 64000 64640
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
cert_test_11 64640
cert_test_block_3 64640 0 0 16 16
cert_test_block_3 64640 1 16 32 16
cert_test_block_3 64640 2 32 48 16
cert_test_block_3 64640 3 48 64 16
cert_test_block_3 64640 4 64 80 16
cert_test_block_3 64640 5 80 96 16
cert_test_block_3 64640 6 96 112 16
cert_test_block_3 64640 7 112 128 16
cert_test_block_3 64640 8 128 144 16
cert_test_block_3 64640 9 144 160 16
cert_test_block_3 64640 10 160 176 16
cert_test_block_3 64640 11 176 192 16
cert_test_block_3 64640 12 192 208 16
cert_test_block_3 64640 13 208 224 16
cert_test_block_3 64640 14 224 240 16
cert_test_block_3 64640 15 240 256 16
cert_test_block_3 64640 16 256 272 16
cert_test_block_3 64640 17 272 288 16
cert_test_block_3 64640 18 288 304 16
cert_test_block_3 64640 19 304 320 16
cert_test_block_3 64640 20 320 336 16
cert_test_block_3 64640 21 336 352 16
cert_test_block_3 64640 22 352 368 16
cert_test_block_3 64640 23 368 384 16
cert_test_block_3 64640 24 384 400 16
cert_test_block_3 64640 25 400 416 16
cert_test_block_3 64640 26 416 432 16
cert_test_block_3 64640 27 432 448 16
cert_test_block_3 64640 28 448 464 16
cert_test_block_3 64640 29 464 480 16
cert_test_block_3 64640 30 480 496 16
cert_test_block_3 64640 31 496 512 16
cert_test_block_3 64640 32 512 528 16
cert_test_block_3 64640 33 528 544 16
cert_test_block_3 64640 34 544 560 16
cert_test_block_3 64640 35 560 576 16
cert_test_block_3 64640 36 576 592 16
cert_test_block_3 64640 37 592 608 16
cert_test_block_3 64640 38 608 624 16
cert_test_block_3 64640 39 624 640 16
theorem test64640_complete : Interval test64640 0 640 :=
  (interval_append test64640 0 320 640
  (interval_append test64640 0 160 320
  (interval_append test64640 0 80 160
  (interval_append test64640 0 32 80
  (interval_append test64640 0 16 32
  test64640_block_0
  test64640_block_1)
  (interval_append test64640 32 48 80
  test64640_block_2
  (interval_append test64640 48 64 80
  test64640_block_3
  test64640_block_4)))
  (interval_append test64640 80 112 160
  (interval_append test64640 80 96 112
  test64640_block_5
  test64640_block_6)
  (interval_append test64640 112 128 160
  test64640_block_7
  (interval_append test64640 128 144 160
  test64640_block_8
  test64640_block_9))))
  (interval_append test64640 160 240 320
  (interval_append test64640 160 192 240
  (interval_append test64640 160 176 192
  test64640_block_10
  test64640_block_11)
  (interval_append test64640 192 208 240
  test64640_block_12
  (interval_append test64640 208 224 240
  test64640_block_13
  test64640_block_14)))
  (interval_append test64640 240 272 320
  (interval_append test64640 240 256 272
  test64640_block_15
  test64640_block_16)
  (interval_append test64640 272 288 320
  test64640_block_17
  (interval_append test64640 288 304 320
  test64640_block_18
  test64640_block_19)))))
  (interval_append test64640 320 480 640
  (interval_append test64640 320 400 480
  (interval_append test64640 320 352 400
  (interval_append test64640 320 336 352
  test64640_block_20
  test64640_block_21)
  (interval_append test64640 352 368 400
  test64640_block_22
  (interval_append test64640 368 384 400
  test64640_block_23
  test64640_block_24)))
  (interval_append test64640 400 432 480
  (interval_append test64640 400 416 432
  test64640_block_25
  test64640_block_26)
  (interval_append test64640 432 448 480
  test64640_block_27
  (interval_append test64640 448 464 480
  test64640_block_28
  test64640_block_29))))
  (interval_append test64640 480 560 640
  (interval_append test64640 480 512 560
  (interval_append test64640 480 496 512
  test64640_block_30
  test64640_block_31)
  (interval_append test64640 512 528 560
  test64640_block_32
  (interval_append test64640 528 544 560
  test64640_block_33
  test64640_block_34)))
  (interval_append test64640 560 592 640
  (interval_append test64640 560 576 592
  test64640_block_35
  test64640_block_36)
  (interval_append test64640 592 608 640
  test64640_block_37
  (interval_append test64640 608 624 640
  test64640_block_38
  test64640_block_39))))))
cert_nodeInterval_3 64640 65280
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
cert_test_11 65280
cert_test_block_3 65280 0 0 16 16
cert_test_block_3 65280 1 16 32 16
cert_test_block_3 65280 2 32 48 16
cert_test_block_3 65280 3 48 64 16
cert_test_block_3 65280 4 64 80 16
cert_test_block_3 65280 5 80 96 16
cert_test_block_3 65280 6 96 112 16
cert_test_block_3 65280 7 112 128 16
cert_test_block_3 65280 8 128 144 16
cert_test_block_3 65280 9 144 160 16
cert_test_block_3 65280 10 160 176 16
cert_test_block_3 65280 11 176 192 16
cert_test_block_3 65280 12 192 208 16
cert_test_block_3 65280 13 208 224 16
cert_test_block_3 65280 14 224 240 16
cert_test_block_3 65280 15 240 256 16
cert_test_block_3 65280 16 256 272 16
cert_test_block_3 65280 17 272 288 16
cert_test_block_3 65280 18 288 304 16
cert_test_block_3 65280 19 304 320 16
cert_test_block_3 65280 20 320 336 16
cert_test_block_3 65280 21 336 352 16
cert_test_block_3 65280 22 352 368 16
cert_test_block_3 65280 23 368 384 16
cert_test_block_3 65280 24 384 400 16
cert_test_block_3 65280 25 400 416 16
cert_test_block_3 65280 26 416 432 16
cert_test_block_3 65280 27 432 448 16
cert_test_block_3 65280 28 448 464 16
cert_test_block_3 65280 29 464 480 16
cert_test_block_3 65280 30 480 496 16
cert_test_block_3 65280 31 496 512 16
cert_test_block_3 65280 32 512 528 16
cert_test_block_3 65280 33 528 544 16
cert_test_block_3 65280 34 544 560 16
cert_test_block_3 65280 35 560 576 16
cert_test_block_3 65280 36 576 592 16
cert_test_block_3 65280 37 592 608 16
cert_test_block_3 65280 38 608 624 16
cert_test_block_3 65280 39 624 640 16
theorem test65280_complete : Interval test65280 0 640 :=
  (interval_append test65280 0 320 640
  (interval_append test65280 0 160 320
  (interval_append test65280 0 80 160
  (interval_append test65280 0 32 80
  (interval_append test65280 0 16 32
  test65280_block_0
  test65280_block_1)
  (interval_append test65280 32 48 80
  test65280_block_2
  (interval_append test65280 48 64 80
  test65280_block_3
  test65280_block_4)))
  (interval_append test65280 80 112 160
  (interval_append test65280 80 96 112
  test65280_block_5
  test65280_block_6)
  (interval_append test65280 112 128 160
  test65280_block_7
  (interval_append test65280 128 144 160
  test65280_block_8
  test65280_block_9))))
  (interval_append test65280 160 240 320
  (interval_append test65280 160 192 240
  (interval_append test65280 160 176 192
  test65280_block_10
  test65280_block_11)
  (interval_append test65280 192 208 240
  test65280_block_12
  (interval_append test65280 208 224 240
  test65280_block_13
  test65280_block_14)))
  (interval_append test65280 240 272 320
  (interval_append test65280 240 256 272
  test65280_block_15
  test65280_block_16)
  (interval_append test65280 272 288 320
  test65280_block_17
  (interval_append test65280 288 304 320
  test65280_block_18
  test65280_block_19)))))
  (interval_append test65280 320 480 640
  (interval_append test65280 320 400 480
  (interval_append test65280 320 352 400
  (interval_append test65280 320 336 352
  test65280_block_20
  test65280_block_21)
  (interval_append test65280 352 368 400
  test65280_block_22
  (interval_append test65280 368 384 400
  test65280_block_23
  test65280_block_24)))
  (interval_append test65280 400 432 480
  (interval_append test65280 400 416 432
  test65280_block_25
  test65280_block_26)
  (interval_append test65280 432 448 480
  test65280_block_27
  (interval_append test65280 448 464 480
  test65280_block_28
  test65280_block_29))))
  (interval_append test65280 480 560 640
  (interval_append test65280 480 512 560
  (interval_append test65280 480 496 512
  test65280_block_30
  test65280_block_31)
  (interval_append test65280 512 528 560
  test65280_block_32
  (interval_append test65280 528 544 560
  test65280_block_33
  test65280_block_34)))
  (interval_append test65280 560 592 640
  (interval_append test65280 560 576 592
  test65280_block_35
  test65280_block_36)
  (interval_append test65280 592 608 640
  test65280_block_37
  (interval_append test65280 608 624 640
  test65280_block_38
  test65280_block_39))))))
cert_nodeInterval_3 65280 65920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
