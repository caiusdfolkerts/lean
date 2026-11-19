module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0365Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
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
cert_test_block_3 12160 37 592 607 15
theorem test12160_complete : Interval test12160 0 607 :=
  (interval_append test12160 0 304 607
  (interval_append test12160 0 144 304
  (interval_append test12160 0 64 144
  (interval_append test12160 0 32 64
  (interval_append test12160 0 16 32
  test12160_block_0
  test12160_block_1)
  (interval_append test12160 32 48 64
  test12160_block_2
  test12160_block_3))
  (interval_append test12160 64 96 144
  (interval_append test12160 64 80 96
  test12160_block_4
  test12160_block_5)
  (interval_append test12160 96 112 144
  test12160_block_6
  (interval_append test12160 112 128 144
  test12160_block_7
  test12160_block_8))))
  (interval_append test12160 144 224 304
  (interval_append test12160 144 176 224
  (interval_append test12160 144 160 176
  test12160_block_9
  test12160_block_10)
  (interval_append test12160 176 192 224
  test12160_block_11
  (interval_append test12160 192 208 224
  test12160_block_12
  test12160_block_13)))
  (interval_append test12160 224 256 304
  (interval_append test12160 224 240 256
  test12160_block_14
  test12160_block_15)
  (interval_append test12160 256 272 304
  test12160_block_16
  (interval_append test12160 272 288 304
  test12160_block_17
  test12160_block_18)))))
  (interval_append test12160 304 448 607
  (interval_append test12160 304 368 448
  (interval_append test12160 304 336 368
  (interval_append test12160 304 320 336
  test12160_block_19
  test12160_block_20)
  (interval_append test12160 336 352 368
  test12160_block_21
  test12160_block_22))
  (interval_append test12160 368 400 448
  (interval_append test12160 368 384 400
  test12160_block_23
  test12160_block_24)
  (interval_append test12160 400 416 448
  test12160_block_25
  (interval_append test12160 416 432 448
  test12160_block_26
  test12160_block_27))))
  (interval_append test12160 448 528 607
  (interval_append test12160 448 480 528
  (interval_append test12160 448 464 480
  test12160_block_28
  test12160_block_29)
  (interval_append test12160 480 496 528
  test12160_block_30
  (interval_append test12160 496 512 528
  test12160_block_31
  test12160_block_32)))
  (interval_append test12160 528 560 607
  (interval_append test12160 528 544 560
  test12160_block_33
  test12160_block_34)
  (interval_append test12160 560 576 607
  test12160_block_35
  (interval_append test12160 576 592 607
  test12160_block_36
  test12160_block_37))))))
cert_nodeInterval_3 12160 12767
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0365
end
end
