module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
cert_test_block_3 11520 36 576 592 16
cert_test_block_3 11520 37 592 608 16
cert_test_block_3 11520 38 608 624 16
cert_test_block_3 11520 39 624 640 16
theorem test11520_complete : Interval test11520 0 640 :=
  (interval_append test11520 0 320 640
  (interval_append test11520 0 160 320
  (interval_append test11520 0 80 160
  (interval_append test11520 0 32 80
  (interval_append test11520 0 16 32
  test11520_block_0
  test11520_block_1)
  (interval_append test11520 32 48 80
  test11520_block_2
  (interval_append test11520 48 64 80
  test11520_block_3
  test11520_block_4)))
  (interval_append test11520 80 112 160
  (interval_append test11520 80 96 112
  test11520_block_5
  test11520_block_6)
  (interval_append test11520 112 128 160
  test11520_block_7
  (interval_append test11520 128 144 160
  test11520_block_8
  test11520_block_9))))
  (interval_append test11520 160 240 320
  (interval_append test11520 160 192 240
  (interval_append test11520 160 176 192
  test11520_block_10
  test11520_block_11)
  (interval_append test11520 192 208 240
  test11520_block_12
  (interval_append test11520 208 224 240
  test11520_block_13
  test11520_block_14)))
  (interval_append test11520 240 272 320
  (interval_append test11520 240 256 272
  test11520_block_15
  test11520_block_16)
  (interval_append test11520 272 288 320
  test11520_block_17
  (interval_append test11520 288 304 320
  test11520_block_18
  test11520_block_19)))))
  (interval_append test11520 320 480 640
  (interval_append test11520 320 400 480
  (interval_append test11520 320 352 400
  (interval_append test11520 320 336 352
  test11520_block_20
  test11520_block_21)
  (interval_append test11520 352 368 400
  test11520_block_22
  (interval_append test11520 368 384 400
  test11520_block_23
  test11520_block_24)))
  (interval_append test11520 400 432 480
  (interval_append test11520 400 416 432
  test11520_block_25
  test11520_block_26)
  (interval_append test11520 432 448 480
  test11520_block_27
  (interval_append test11520 448 464 480
  test11520_block_28
  test11520_block_29))))
  (interval_append test11520 480 560 640
  (interval_append test11520 480 512 560
  (interval_append test11520 480 496 512
  test11520_block_30
  test11520_block_31)
  (interval_append test11520 512 528 560
  test11520_block_32
  (interval_append test11520 528 544 560
  test11520_block_33
  test11520_block_34)))
  (interval_append test11520 560 592 640
  (interval_append test11520 560 576 592
  test11520_block_35
  test11520_block_36)
  (interval_append test11520 592 608 640
  test11520_block_37
  (interval_append test11520 608 624 640
  test11520_block_38
  test11520_block_39))))))
cert_nodeInterval_3 11520 12160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 12160
cert_test_block_3 12160 0 0 16 16
cert_test_block_3 12160 1 16 32 16
cert_test_block_3 12160 2 32 48 16
cert_test_block_3 12160 3 48 64 16
cert_test_block_3 12160 4 64 80 16
cert_test_block_3 12160 5 80 96 16
cert_test_block_3 12160 6 96 112 16
cert_test_block_3 12160 7 112 128 16
cert_test_block_3 12160 8 128 144 16
cert_test_block_3 12160 9 144 160 16
cert_test_block_3 12160 10 160 176 16
cert_test_block_3 12160 11 176 192 16
cert_test_block_3 12160 12 192 208 16
cert_test_block_3 12160 13 208 224 16
cert_test_block_3 12160 14 224 240 16
cert_test_block_3 12160 15 240 256 16
cert_test_block_3 12160 16 256 272 16
cert_test_block_3 12160 17 272 288 16
cert_test_block_3 12160 18 288 304 16
cert_test_block_3 12160 19 304 320 16
cert_test_block_3 12160 20 320 336 16
cert_test_block_3 12160 21 336 352 16
cert_test_block_3 12160 22 352 368 16
cert_test_block_3 12160 23 368 384 16
cert_test_block_3 12160 24 384 400 16
cert_test_block_3 12160 25 400 416 16
cert_test_block_3 12160 26 416 432 16
cert_test_block_3 12160 27 432 448 16
cert_test_block_3 12160 28 448 464 16
cert_test_block_3 12160 29 464 480 16
cert_test_block_3 12160 30 480 496 16
cert_test_block_3 12160 31 496 512 16
cert_test_block_3 12160 32 512 528 16
cert_test_block_3 12160 33 528 544 16
cert_test_block_3 12160 34 544 560 16
cert_test_block_3 12160 35 560 576 16
cert_test_block_3 12160 36 576 592 16
cert_test_block_3 12160 37 592 608 16
cert_test_block_3 12160 38 608 624 16
cert_test_block_3 12160 39 624 640 16
theorem test12160_complete : Interval test12160 0 640 :=
  (interval_append test12160 0 320 640
  (interval_append test12160 0 160 320
  (interval_append test12160 0 80 160
  (interval_append test12160 0 32 80
  (interval_append test12160 0 16 32
  test12160_block_0
  test12160_block_1)
  (interval_append test12160 32 48 80
  test12160_block_2
  (interval_append test12160 48 64 80
  test12160_block_3
  test12160_block_4)))
  (interval_append test12160 80 112 160
  (interval_append test12160 80 96 112
  test12160_block_5
  test12160_block_6)
  (interval_append test12160 112 128 160
  test12160_block_7
  (interval_append test12160 128 144 160
  test12160_block_8
  test12160_block_9))))
  (interval_append test12160 160 240 320
  (interval_append test12160 160 192 240
  (interval_append test12160 160 176 192
  test12160_block_10
  test12160_block_11)
  (interval_append test12160 192 208 240
  test12160_block_12
  (interval_append test12160 208 224 240
  test12160_block_13
  test12160_block_14)))
  (interval_append test12160 240 272 320
  (interval_append test12160 240 256 272
  test12160_block_15
  test12160_block_16)
  (interval_append test12160 272 288 320
  test12160_block_17
  (interval_append test12160 288 304 320
  test12160_block_18
  test12160_block_19)))))
  (interval_append test12160 320 480 640
  (interval_append test12160 320 400 480
  (interval_append test12160 320 352 400
  (interval_append test12160 320 336 352
  test12160_block_20
  test12160_block_21)
  (interval_append test12160 352 368 400
  test12160_block_22
  (interval_append test12160 368 384 400
  test12160_block_23
  test12160_block_24)))
  (interval_append test12160 400 432 480
  (interval_append test12160 400 416 432
  test12160_block_25
  test12160_block_26)
  (interval_append test12160 432 448 480
  test12160_block_27
  (interval_append test12160 448 464 480
  test12160_block_28
  test12160_block_29))))
  (interval_append test12160 480 560 640
  (interval_append test12160 480 512 560
  (interval_append test12160 480 496 512
  test12160_block_30
  test12160_block_31)
  (interval_append test12160 512 528 560
  test12160_block_32
  (interval_append test12160 528 544 560
  test12160_block_33
  test12160_block_34)))
  (interval_append test12160 560 592 640
  (interval_append test12160 560 576 592
  test12160_block_35
  test12160_block_36)
  (interval_append test12160 592 608 640
  test12160_block_37
  (interval_append test12160 608 624 640
  test12160_block_38
  test12160_block_39))))))
cert_nodeInterval_3 12160 12800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 12800
cert_test_block_3 12800 0 0 16 16
cert_test_block_3 12800 1 16 32 16
cert_test_block_3 12800 2 32 48 16
cert_test_block_3 12800 3 48 64 16
cert_test_block_3 12800 4 64 80 16
cert_test_block_3 12800 5 80 96 16
cert_test_block_3 12800 6 96 112 16
cert_test_block_3 12800 7 112 128 16
cert_test_block_3 12800 8 128 144 16
cert_test_block_3 12800 9 144 160 16
cert_test_block_3 12800 10 160 176 16
cert_test_block_3 12800 11 176 192 16
cert_test_block_3 12800 12 192 208 16
cert_test_block_3 12800 13 208 224 16
cert_test_block_3 12800 14 224 240 16
cert_test_block_3 12800 15 240 256 16
cert_test_block_3 12800 16 256 272 16
cert_test_block_3 12800 17 272 288 16
cert_test_block_3 12800 18 288 304 16
cert_test_block_3 12800 19 304 320 16
cert_test_block_3 12800 20 320 336 16
cert_test_block_3 12800 21 336 352 16
cert_test_block_3 12800 22 352 368 16
cert_test_block_3 12800 23 368 384 16
cert_test_block_3 12800 24 384 400 16
cert_test_block_3 12800 25 400 416 16
cert_test_block_3 12800 26 416 432 16
cert_test_block_3 12800 27 432 448 16
cert_test_block_3 12800 28 448 464 16
cert_test_block_3 12800 29 464 480 16
cert_test_block_3 12800 30 480 496 16
cert_test_block_3 12800 31 496 512 16
cert_test_block_3 12800 32 512 528 16
cert_test_block_3 12800 33 528 544 16
cert_test_block_3 12800 34 544 560 16
cert_test_block_3 12800 35 560 576 16
cert_test_block_3 12800 36 576 592 16
cert_test_block_3 12800 37 592 608 16
cert_test_block_3 12800 38 608 624 16
cert_test_block_3 12800 39 624 640 16
theorem test12800_complete : Interval test12800 0 640 :=
  (interval_append test12800 0 320 640
  (interval_append test12800 0 160 320
  (interval_append test12800 0 80 160
  (interval_append test12800 0 32 80
  (interval_append test12800 0 16 32
  test12800_block_0
  test12800_block_1)
  (interval_append test12800 32 48 80
  test12800_block_2
  (interval_append test12800 48 64 80
  test12800_block_3
  test12800_block_4)))
  (interval_append test12800 80 112 160
  (interval_append test12800 80 96 112
  test12800_block_5
  test12800_block_6)
  (interval_append test12800 112 128 160
  test12800_block_7
  (interval_append test12800 128 144 160
  test12800_block_8
  test12800_block_9))))
  (interval_append test12800 160 240 320
  (interval_append test12800 160 192 240
  (interval_append test12800 160 176 192
  test12800_block_10
  test12800_block_11)
  (interval_append test12800 192 208 240
  test12800_block_12
  (interval_append test12800 208 224 240
  test12800_block_13
  test12800_block_14)))
  (interval_append test12800 240 272 320
  (interval_append test12800 240 256 272
  test12800_block_15
  test12800_block_16)
  (interval_append test12800 272 288 320
  test12800_block_17
  (interval_append test12800 288 304 320
  test12800_block_18
  test12800_block_19)))))
  (interval_append test12800 320 480 640
  (interval_append test12800 320 400 480
  (interval_append test12800 320 352 400
  (interval_append test12800 320 336 352
  test12800_block_20
  test12800_block_21)
  (interval_append test12800 352 368 400
  test12800_block_22
  (interval_append test12800 368 384 400
  test12800_block_23
  test12800_block_24)))
  (interval_append test12800 400 432 480
  (interval_append test12800 400 416 432
  test12800_block_25
  test12800_block_26)
  (interval_append test12800 432 448 480
  test12800_block_27
  (interval_append test12800 448 464 480
  test12800_block_28
  test12800_block_29))))
  (interval_append test12800 480 560 640
  (interval_append test12800 480 512 560
  (interval_append test12800 480 496 512
  test12800_block_30
  test12800_block_31)
  (interval_append test12800 512 528 560
  test12800_block_32
  (interval_append test12800 528 544 560
  test12800_block_33
  test12800_block_34)))
  (interval_append test12800 560 592 640
  (interval_append test12800 560 576 592
  test12800_block_35
  test12800_block_36)
  (interval_append test12800 592 608 640
  test12800_block_37
  (interval_append test12800 608 624 640
  test12800_block_38
  test12800_block_39))))))
cert_nodeInterval_3 12800 13440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 13440
cert_test_block_3 13440 0 0 16 16
cert_test_block_3 13440 1 16 32 16
cert_test_block_3 13440 2 32 48 16
cert_test_block_3 13440 3 48 64 16
cert_test_block_3 13440 4 64 80 16
cert_test_block_3 13440 5 80 96 16
cert_test_block_3 13440 6 96 112 16
cert_test_block_3 13440 7 112 128 16
cert_test_block_3 13440 8 128 144 16
cert_test_block_3 13440 9 144 160 16
cert_test_block_3 13440 10 160 176 16
cert_test_block_3 13440 11 176 192 16
cert_test_block_3 13440 12 192 208 16
cert_test_block_3 13440 13 208 224 16
cert_test_block_3 13440 14 224 240 16
cert_test_block_3 13440 15 240 256 16
cert_test_block_3 13440 16 256 272 16
cert_test_block_3 13440 17 272 288 16
cert_test_block_3 13440 18 288 304 16
cert_test_block_3 13440 19 304 320 16
cert_test_block_3 13440 20 320 336 16
cert_test_block_3 13440 21 336 352 16
cert_test_block_3 13440 22 352 368 16
cert_test_block_3 13440 23 368 384 16
cert_test_block_3 13440 24 384 400 16
cert_test_block_3 13440 25 400 416 16
cert_test_block_3 13440 26 416 432 16
cert_test_block_3 13440 27 432 448 16
cert_test_block_3 13440 28 448 464 16
cert_test_block_3 13440 29 464 480 16
cert_test_block_3 13440 30 480 496 16
cert_test_block_3 13440 31 496 512 16
cert_test_block_3 13440 32 512 528 16
cert_test_block_3 13440 33 528 544 16
cert_test_block_3 13440 34 544 560 16
cert_test_block_3 13440 35 560 576 16
cert_test_block_3 13440 36 576 592 16
cert_test_block_3 13440 37 592 608 16
cert_test_block_3 13440 38 608 624 16
cert_test_block_3 13440 39 624 640 16
theorem test13440_complete : Interval test13440 0 640 :=
  (interval_append test13440 0 320 640
  (interval_append test13440 0 160 320
  (interval_append test13440 0 80 160
  (interval_append test13440 0 32 80
  (interval_append test13440 0 16 32
  test13440_block_0
  test13440_block_1)
  (interval_append test13440 32 48 80
  test13440_block_2
  (interval_append test13440 48 64 80
  test13440_block_3
  test13440_block_4)))
  (interval_append test13440 80 112 160
  (interval_append test13440 80 96 112
  test13440_block_5
  test13440_block_6)
  (interval_append test13440 112 128 160
  test13440_block_7
  (interval_append test13440 128 144 160
  test13440_block_8
  test13440_block_9))))
  (interval_append test13440 160 240 320
  (interval_append test13440 160 192 240
  (interval_append test13440 160 176 192
  test13440_block_10
  test13440_block_11)
  (interval_append test13440 192 208 240
  test13440_block_12
  (interval_append test13440 208 224 240
  test13440_block_13
  test13440_block_14)))
  (interval_append test13440 240 272 320
  (interval_append test13440 240 256 272
  test13440_block_15
  test13440_block_16)
  (interval_append test13440 272 288 320
  test13440_block_17
  (interval_append test13440 288 304 320
  test13440_block_18
  test13440_block_19)))))
  (interval_append test13440 320 480 640
  (interval_append test13440 320 400 480
  (interval_append test13440 320 352 400
  (interval_append test13440 320 336 352
  test13440_block_20
  test13440_block_21)
  (interval_append test13440 352 368 400
  test13440_block_22
  (interval_append test13440 368 384 400
  test13440_block_23
  test13440_block_24)))
  (interval_append test13440 400 432 480
  (interval_append test13440 400 416 432
  test13440_block_25
  test13440_block_26)
  (interval_append test13440 432 448 480
  test13440_block_27
  (interval_append test13440 448 464 480
  test13440_block_28
  test13440_block_29))))
  (interval_append test13440 480 560 640
  (interval_append test13440 480 512 560
  (interval_append test13440 480 496 512
  test13440_block_30
  test13440_block_31)
  (interval_append test13440 512 528 560
  test13440_block_32
  (interval_append test13440 528 544 560
  test13440_block_33
  test13440_block_34)))
  (interval_append test13440 560 592 640
  (interval_append test13440 560 576 592
  test13440_block_35
  test13440_block_36)
  (interval_append test13440 592 608 640
  test13440_block_37
  (interval_append test13440 608 624 640
  test13440_block_38
  test13440_block_39))))))
cert_nodeInterval_3 13440 14080
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 14080
cert_test_block_3 14080 0 0 16 16
cert_test_block_3 14080 1 16 32 16
cert_test_block_3 14080 2 32 48 16
cert_test_block_3 14080 3 48 64 16
cert_test_block_3 14080 4 64 80 16
cert_test_block_3 14080 5 80 96 16
cert_test_block_3 14080 6 96 112 16
cert_test_block_3 14080 7 112 128 16
cert_test_block_3 14080 8 128 144 16
cert_test_block_3 14080 9 144 160 16
cert_test_block_3 14080 10 160 176 16
cert_test_block_3 14080 11 176 192 16
cert_test_block_3 14080 12 192 208 16
cert_test_block_3 14080 13 208 224 16
cert_test_block_3 14080 14 224 240 16
cert_test_block_3 14080 15 240 256 16
cert_test_block_3 14080 16 256 272 16
cert_test_block_3 14080 17 272 288 16
cert_test_block_3 14080 18 288 304 16
cert_test_block_3 14080 19 304 320 16
cert_test_block_3 14080 20 320 336 16
cert_test_block_3 14080 21 336 352 16
cert_test_block_3 14080 22 352 368 16
cert_test_block_3 14080 23 368 384 16
cert_test_block_3 14080 24 384 400 16
cert_test_block_3 14080 25 400 416 16
cert_test_block_3 14080 26 416 432 16
cert_test_block_3 14080 27 432 448 16
cert_test_block_3 14080 28 448 464 16
cert_test_block_3 14080 29 464 480 16
cert_test_block_3 14080 30 480 496 16
cert_test_block_3 14080 31 496 512 16
cert_test_block_3 14080 32 512 528 16
cert_test_block_3 14080 33 528 544 16
cert_test_block_3 14080 34 544 560 16
cert_test_block_3 14080 35 560 576 16
cert_test_block_3 14080 36 576 592 16
cert_test_block_3 14080 37 592 608 16
cert_test_block_3 14080 38 608 624 16
cert_test_block_3 14080 39 624 640 16
theorem test14080_complete : Interval test14080 0 640 :=
  (interval_append test14080 0 320 640
  (interval_append test14080 0 160 320
  (interval_append test14080 0 80 160
  (interval_append test14080 0 32 80
  (interval_append test14080 0 16 32
  test14080_block_0
  test14080_block_1)
  (interval_append test14080 32 48 80
  test14080_block_2
  (interval_append test14080 48 64 80
  test14080_block_3
  test14080_block_4)))
  (interval_append test14080 80 112 160
  (interval_append test14080 80 96 112
  test14080_block_5
  test14080_block_6)
  (interval_append test14080 112 128 160
  test14080_block_7
  (interval_append test14080 128 144 160
  test14080_block_8
  test14080_block_9))))
  (interval_append test14080 160 240 320
  (interval_append test14080 160 192 240
  (interval_append test14080 160 176 192
  test14080_block_10
  test14080_block_11)
  (interval_append test14080 192 208 240
  test14080_block_12
  (interval_append test14080 208 224 240
  test14080_block_13
  test14080_block_14)))
  (interval_append test14080 240 272 320
  (interval_append test14080 240 256 272
  test14080_block_15
  test14080_block_16)
  (interval_append test14080 272 288 320
  test14080_block_17
  (interval_append test14080 288 304 320
  test14080_block_18
  test14080_block_19)))))
  (interval_append test14080 320 480 640
  (interval_append test14080 320 400 480
  (interval_append test14080 320 352 400
  (interval_append test14080 320 336 352
  test14080_block_20
  test14080_block_21)
  (interval_append test14080 352 368 400
  test14080_block_22
  (interval_append test14080 368 384 400
  test14080_block_23
  test14080_block_24)))
  (interval_append test14080 400 432 480
  (interval_append test14080 400 416 432
  test14080_block_25
  test14080_block_26)
  (interval_append test14080 432 448 480
  test14080_block_27
  (interval_append test14080 448 464 480
  test14080_block_28
  test14080_block_29))))
  (interval_append test14080 480 560 640
  (interval_append test14080 480 512 560
  (interval_append test14080 480 496 512
  test14080_block_30
  test14080_block_31)
  (interval_append test14080 512 528 560
  test14080_block_32
  (interval_append test14080 528 544 560
  test14080_block_33
  test14080_block_34)))
  (interval_append test14080 560 592 640
  (interval_append test14080 560 576 592
  test14080_block_35
  test14080_block_36)
  (interval_append test14080 592 608 640
  test14080_block_37
  (interval_append test14080 608 624 640
  test14080_block_38
  test14080_block_39))))))
cert_nodeInterval_3 14080 14720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 14720
cert_test_block_3 14720 0 0 16 16
cert_test_block_3 14720 1 16 32 16
cert_test_block_3 14720 2 32 48 16
cert_test_block_3 14720 3 48 64 16
cert_test_block_3 14720 4 64 80 16
cert_test_block_3 14720 5 80 96 16
cert_test_block_3 14720 6 96 112 16
cert_test_block_3 14720 7 112 128 16
cert_test_block_3 14720 8 128 144 16
cert_test_block_3 14720 9 144 160 16
cert_test_block_3 14720 10 160 176 16
cert_test_block_3 14720 11 176 192 16
cert_test_block_3 14720 12 192 208 16
cert_test_block_3 14720 13 208 224 16
cert_test_block_3 14720 14 224 240 16
cert_test_block_3 14720 15 240 256 16
cert_test_block_3 14720 16 256 272 16
cert_test_block_3 14720 17 272 288 16
cert_test_block_3 14720 18 288 304 16
cert_test_block_3 14720 19 304 320 16
cert_test_block_3 14720 20 320 336 16
cert_test_block_3 14720 21 336 352 16
cert_test_block_3 14720 22 352 368 16
cert_test_block_3 14720 23 368 384 16
cert_test_block_3 14720 24 384 400 16
cert_test_block_3 14720 25 400 416 16
cert_test_block_3 14720 26 416 432 16
cert_test_block_3 14720 27 432 448 16
cert_test_block_3 14720 28 448 464 16
cert_test_block_3 14720 29 464 480 16
cert_test_block_3 14720 30 480 496 16
cert_test_block_3 14720 31 496 512 16
cert_test_block_3 14720 32 512 528 16
cert_test_block_3 14720 33 528 544 16
cert_test_block_3 14720 34 544 560 16
cert_test_block_3 14720 35 560 576 16
cert_test_block_3 14720 36 576 592 16
cert_test_block_3 14720 37 592 608 16
cert_test_block_3 14720 38 608 624 16
cert_test_block_3 14720 39 624 640 16
theorem test14720_complete : Interval test14720 0 640 :=
  (interval_append test14720 0 320 640
  (interval_append test14720 0 160 320
  (interval_append test14720 0 80 160
  (interval_append test14720 0 32 80
  (interval_append test14720 0 16 32
  test14720_block_0
  test14720_block_1)
  (interval_append test14720 32 48 80
  test14720_block_2
  (interval_append test14720 48 64 80
  test14720_block_3
  test14720_block_4)))
  (interval_append test14720 80 112 160
  (interval_append test14720 80 96 112
  test14720_block_5
  test14720_block_6)
  (interval_append test14720 112 128 160
  test14720_block_7
  (interval_append test14720 128 144 160
  test14720_block_8
  test14720_block_9))))
  (interval_append test14720 160 240 320
  (interval_append test14720 160 192 240
  (interval_append test14720 160 176 192
  test14720_block_10
  test14720_block_11)
  (interval_append test14720 192 208 240
  test14720_block_12
  (interval_append test14720 208 224 240
  test14720_block_13
  test14720_block_14)))
  (interval_append test14720 240 272 320
  (interval_append test14720 240 256 272
  test14720_block_15
  test14720_block_16)
  (interval_append test14720 272 288 320
  test14720_block_17
  (interval_append test14720 288 304 320
  test14720_block_18
  test14720_block_19)))))
  (interval_append test14720 320 480 640
  (interval_append test14720 320 400 480
  (interval_append test14720 320 352 400
  (interval_append test14720 320 336 352
  test14720_block_20
  test14720_block_21)
  (interval_append test14720 352 368 400
  test14720_block_22
  (interval_append test14720 368 384 400
  test14720_block_23
  test14720_block_24)))
  (interval_append test14720 400 432 480
  (interval_append test14720 400 416 432
  test14720_block_25
  test14720_block_26)
  (interval_append test14720 432 448 480
  test14720_block_27
  (interval_append test14720 448 464 480
  test14720_block_28
  test14720_block_29))))
  (interval_append test14720 480 560 640
  (interval_append test14720 480 512 560
  (interval_append test14720 480 496 512
  test14720_block_30
  test14720_block_31)
  (interval_append test14720 512 528 560
  test14720_block_32
  (interval_append test14720 528 544 560
  test14720_block_33
  test14720_block_34)))
  (interval_append test14720 560 592 640
  (interval_append test14720 560 576 592
  test14720_block_35
  test14720_block_36)
  (interval_append test14720 592 608 640
  test14720_block_37
  (interval_append test14720 608 624 640
  test14720_block_38
  test14720_block_39))))))
cert_nodeInterval_3 14720 15360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
end
end
