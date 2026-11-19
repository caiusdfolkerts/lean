module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0319Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 21120
cert_test_block_3 21120 0 0 16 16
cert_test_block_3 21120 1 16 32 16
cert_test_block_3 21120 2 32 48 16
cert_test_block_3 21120 3 48 64 16
cert_test_block_3 21120 4 64 80 16
cert_test_block_3 21120 5 80 96 16
cert_test_block_3 21120 6 96 112 16
cert_test_block_3 21120 7 112 128 16
cert_test_block_3 21120 8 128 144 16
cert_test_block_3 21120 9 144 160 16
cert_test_block_3 21120 10 160 176 16
cert_test_block_3 21120 11 176 192 16
cert_test_block_3 21120 12 192 208 16
cert_test_block_3 21120 13 208 224 16
cert_test_block_3 21120 14 224 240 16
cert_test_block_3 21120 15 240 256 16
cert_test_block_3 21120 16 256 272 16
cert_test_block_3 21120 17 272 288 16
cert_test_block_3 21120 18 288 304 16
cert_test_block_3 21120 19 304 320 16
cert_test_block_3 21120 20 320 336 16
cert_test_block_3 21120 21 336 352 16
cert_test_block_3 21120 22 352 368 16
cert_test_block_3 21120 23 368 384 16
cert_test_block_3 21120 24 384 400 16
cert_test_block_3 21120 25 400 416 16
cert_test_block_3 21120 26 416 432 16
cert_test_block_3 21120 27 432 448 16
cert_test_block_3 21120 28 448 464 16
cert_test_block_3 21120 29 464 480 16
cert_test_block_3 21120 30 480 496 16
cert_test_block_3 21120 31 496 512 16
cert_test_block_3 21120 32 512 528 16
cert_test_block_3 21120 33 528 544 16
cert_test_block_3 21120 34 544 560 16
cert_test_block_3 21120 35 560 576 16
cert_test_block_3 21120 36 576 592 16
cert_test_block_3 21120 37 592 608 16
cert_test_block_3 21120 38 608 624 16
cert_test_block_3 21120 39 624 640 16
theorem test21120_complete : Interval test21120 0 640 :=
  (interval_append test21120 0 320 640
  (interval_append test21120 0 160 320
  (interval_append test21120 0 80 160
  (interval_append test21120 0 32 80
  (interval_append test21120 0 16 32
  test21120_block_0
  test21120_block_1)
  (interval_append test21120 32 48 80
  test21120_block_2
  (interval_append test21120 48 64 80
  test21120_block_3
  test21120_block_4)))
  (interval_append test21120 80 112 160
  (interval_append test21120 80 96 112
  test21120_block_5
  test21120_block_6)
  (interval_append test21120 112 128 160
  test21120_block_7
  (interval_append test21120 128 144 160
  test21120_block_8
  test21120_block_9))))
  (interval_append test21120 160 240 320
  (interval_append test21120 160 192 240
  (interval_append test21120 160 176 192
  test21120_block_10
  test21120_block_11)
  (interval_append test21120 192 208 240
  test21120_block_12
  (interval_append test21120 208 224 240
  test21120_block_13
  test21120_block_14)))
  (interval_append test21120 240 272 320
  (interval_append test21120 240 256 272
  test21120_block_15
  test21120_block_16)
  (interval_append test21120 272 288 320
  test21120_block_17
  (interval_append test21120 288 304 320
  test21120_block_18
  test21120_block_19)))))
  (interval_append test21120 320 480 640
  (interval_append test21120 320 400 480
  (interval_append test21120 320 352 400
  (interval_append test21120 320 336 352
  test21120_block_20
  test21120_block_21)
  (interval_append test21120 352 368 400
  test21120_block_22
  (interval_append test21120 368 384 400
  test21120_block_23
  test21120_block_24)))
  (interval_append test21120 400 432 480
  (interval_append test21120 400 416 432
  test21120_block_25
  test21120_block_26)
  (interval_append test21120 432 448 480
  test21120_block_27
  (interval_append test21120 448 464 480
  test21120_block_28
  test21120_block_29))))
  (interval_append test21120 480 560 640
  (interval_append test21120 480 512 560
  (interval_append test21120 480 496 512
  test21120_block_30
  test21120_block_31)
  (interval_append test21120 512 528 560
  test21120_block_32
  (interval_append test21120 528 544 560
  test21120_block_33
  test21120_block_34)))
  (interval_append test21120 560 592 640
  (interval_append test21120 560 576 592
  test21120_block_35
  test21120_block_36)
  (interval_append test21120 592 608 640
  test21120_block_37
  (interval_append test21120 608 624 640
  test21120_block_38
  test21120_block_39))))))
cert_nodeInterval_3 21120 21760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 21760
cert_test_block_3 21760 0 0 16 16
cert_test_block_3 21760 1 16 32 16
cert_test_block_3 21760 2 32 48 16
cert_test_block_3 21760 3 48 64 16
cert_test_block_3 21760 4 64 80 16
cert_test_block_3 21760 5 80 96 16
cert_test_block_3 21760 6 96 112 16
cert_test_block_3 21760 7 112 128 16
cert_test_block_3 21760 8 128 144 16
cert_test_block_3 21760 9 144 160 16
cert_test_block_3 21760 10 160 176 16
cert_test_block_3 21760 11 176 192 16
cert_test_block_3 21760 12 192 208 16
cert_test_block_3 21760 13 208 224 16
cert_test_block_3 21760 14 224 240 16
cert_test_block_3 21760 15 240 256 16
cert_test_block_3 21760 16 256 272 16
cert_test_block_3 21760 17 272 288 16
cert_test_block_3 21760 18 288 304 16
cert_test_block_3 21760 19 304 320 16
cert_test_block_3 21760 20 320 336 16
cert_test_block_3 21760 21 336 352 16
cert_test_block_3 21760 22 352 368 16
cert_test_block_3 21760 23 368 384 16
cert_test_block_3 21760 24 384 400 16
cert_test_block_3 21760 25 400 416 16
cert_test_block_3 21760 26 416 432 16
cert_test_block_3 21760 27 432 448 16
cert_test_block_3 21760 28 448 464 16
cert_test_block_3 21760 29 464 480 16
cert_test_block_3 21760 30 480 496 16
cert_test_block_3 21760 31 496 512 16
cert_test_block_3 21760 32 512 528 16
cert_test_block_3 21760 33 528 544 16
cert_test_block_3 21760 34 544 560 16
cert_test_block_3 21760 35 560 576 16
cert_test_block_3 21760 36 576 592 16
cert_test_block_3 21760 37 592 608 16
cert_test_block_3 21760 38 608 624 16
cert_test_block_3 21760 39 624 640 16
theorem test21760_complete : Interval test21760 0 640 :=
  (interval_append test21760 0 320 640
  (interval_append test21760 0 160 320
  (interval_append test21760 0 80 160
  (interval_append test21760 0 32 80
  (interval_append test21760 0 16 32
  test21760_block_0
  test21760_block_1)
  (interval_append test21760 32 48 80
  test21760_block_2
  (interval_append test21760 48 64 80
  test21760_block_3
  test21760_block_4)))
  (interval_append test21760 80 112 160
  (interval_append test21760 80 96 112
  test21760_block_5
  test21760_block_6)
  (interval_append test21760 112 128 160
  test21760_block_7
  (interval_append test21760 128 144 160
  test21760_block_8
  test21760_block_9))))
  (interval_append test21760 160 240 320
  (interval_append test21760 160 192 240
  (interval_append test21760 160 176 192
  test21760_block_10
  test21760_block_11)
  (interval_append test21760 192 208 240
  test21760_block_12
  (interval_append test21760 208 224 240
  test21760_block_13
  test21760_block_14)))
  (interval_append test21760 240 272 320
  (interval_append test21760 240 256 272
  test21760_block_15
  test21760_block_16)
  (interval_append test21760 272 288 320
  test21760_block_17
  (interval_append test21760 288 304 320
  test21760_block_18
  test21760_block_19)))))
  (interval_append test21760 320 480 640
  (interval_append test21760 320 400 480
  (interval_append test21760 320 352 400
  (interval_append test21760 320 336 352
  test21760_block_20
  test21760_block_21)
  (interval_append test21760 352 368 400
  test21760_block_22
  (interval_append test21760 368 384 400
  test21760_block_23
  test21760_block_24)))
  (interval_append test21760 400 432 480
  (interval_append test21760 400 416 432
  test21760_block_25
  test21760_block_26)
  (interval_append test21760 432 448 480
  test21760_block_27
  (interval_append test21760 448 464 480
  test21760_block_28
  test21760_block_29))))
  (interval_append test21760 480 560 640
  (interval_append test21760 480 512 560
  (interval_append test21760 480 496 512
  test21760_block_30
  test21760_block_31)
  (interval_append test21760 512 528 560
  test21760_block_32
  (interval_append test21760 528 544 560
  test21760_block_33
  test21760_block_34)))
  (interval_append test21760 560 592 640
  (interval_append test21760 560 576 592
  test21760_block_35
  test21760_block_36)
  (interval_append test21760 592 608 640
  test21760_block_37
  (interval_append test21760 608 624 640
  test21760_block_38
  test21760_block_39))))))
cert_nodeInterval_3 21760 22400
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 22400
cert_test_block_3 22400 0 0 16 16
cert_test_block_3 22400 1 16 32 16
cert_test_block_3 22400 2 32 48 16
cert_test_block_3 22400 3 48 64 16
cert_test_block_3 22400 4 64 80 16
cert_test_block_3 22400 5 80 96 16
cert_test_block_3 22400 6 96 112 16
cert_test_block_3 22400 7 112 128 16
cert_test_block_3 22400 8 128 144 16
cert_test_block_3 22400 9 144 160 16
cert_test_block_3 22400 10 160 176 16
cert_test_block_3 22400 11 176 192 16
cert_test_block_3 22400 12 192 208 16
cert_test_block_3 22400 13 208 224 16
cert_test_block_3 22400 14 224 240 16
cert_test_block_3 22400 15 240 256 16
cert_test_block_3 22400 16 256 272 16
cert_test_block_3 22400 17 272 288 16
cert_test_block_3 22400 18 288 304 16
cert_test_block_3 22400 19 304 320 16
cert_test_block_3 22400 20 320 336 16
cert_test_block_3 22400 21 336 352 16
cert_test_block_3 22400 22 352 368 16
cert_test_block_3 22400 23 368 384 16
cert_test_block_3 22400 24 384 400 16
cert_test_block_3 22400 25 400 416 16
cert_test_block_3 22400 26 416 432 16
cert_test_block_3 22400 27 432 448 16
cert_test_block_3 22400 28 448 464 16
cert_test_block_3 22400 29 464 480 16
cert_test_block_3 22400 30 480 496 16
cert_test_block_3 22400 31 496 512 16
cert_test_block_3 22400 32 512 528 16
cert_test_block_3 22400 33 528 544 16
cert_test_block_3 22400 34 544 560 16
cert_test_block_3 22400 35 560 576 16
cert_test_block_3 22400 36 576 592 16
cert_test_block_3 22400 37 592 608 16
cert_test_block_3 22400 38 608 624 16
cert_test_block_3 22400 39 624 640 16
theorem test22400_complete : Interval test22400 0 640 :=
  (interval_append test22400 0 320 640
  (interval_append test22400 0 160 320
  (interval_append test22400 0 80 160
  (interval_append test22400 0 32 80
  (interval_append test22400 0 16 32
  test22400_block_0
  test22400_block_1)
  (interval_append test22400 32 48 80
  test22400_block_2
  (interval_append test22400 48 64 80
  test22400_block_3
  test22400_block_4)))
  (interval_append test22400 80 112 160
  (interval_append test22400 80 96 112
  test22400_block_5
  test22400_block_6)
  (interval_append test22400 112 128 160
  test22400_block_7
  (interval_append test22400 128 144 160
  test22400_block_8
  test22400_block_9))))
  (interval_append test22400 160 240 320
  (interval_append test22400 160 192 240
  (interval_append test22400 160 176 192
  test22400_block_10
  test22400_block_11)
  (interval_append test22400 192 208 240
  test22400_block_12
  (interval_append test22400 208 224 240
  test22400_block_13
  test22400_block_14)))
  (interval_append test22400 240 272 320
  (interval_append test22400 240 256 272
  test22400_block_15
  test22400_block_16)
  (interval_append test22400 272 288 320
  test22400_block_17
  (interval_append test22400 288 304 320
  test22400_block_18
  test22400_block_19)))))
  (interval_append test22400 320 480 640
  (interval_append test22400 320 400 480
  (interval_append test22400 320 352 400
  (interval_append test22400 320 336 352
  test22400_block_20
  test22400_block_21)
  (interval_append test22400 352 368 400
  test22400_block_22
  (interval_append test22400 368 384 400
  test22400_block_23
  test22400_block_24)))
  (interval_append test22400 400 432 480
  (interval_append test22400 400 416 432
  test22400_block_25
  test22400_block_26)
  (interval_append test22400 432 448 480
  test22400_block_27
  (interval_append test22400 448 464 480
  test22400_block_28
  test22400_block_29))))
  (interval_append test22400 480 560 640
  (interval_append test22400 480 512 560
  (interval_append test22400 480 496 512
  test22400_block_30
  test22400_block_31)
  (interval_append test22400 512 528 560
  test22400_block_32
  (interval_append test22400 528 544 560
  test22400_block_33
  test22400_block_34)))
  (interval_append test22400 560 592 640
  (interval_append test22400 560 576 592
  test22400_block_35
  test22400_block_36)
  (interval_append test22400 592 608 640
  test22400_block_37
  (interval_append test22400 608 624 640
  test22400_block_38
  test22400_block_39))))))
cert_nodeInterval_3 22400 23040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 23040
cert_test_block_3 23040 0 0 16 16
cert_test_block_3 23040 1 16 32 16
cert_test_block_3 23040 2 32 48 16
cert_test_block_3 23040 3 48 64 16
cert_test_block_3 23040 4 64 80 16
cert_test_block_3 23040 5 80 96 16
cert_test_block_3 23040 6 96 112 16
cert_test_block_3 23040 7 112 128 16
cert_test_block_3 23040 8 128 144 16
cert_test_block_3 23040 9 144 160 16
cert_test_block_3 23040 10 160 176 16
cert_test_block_3 23040 11 176 192 16
cert_test_block_3 23040 12 192 208 16
cert_test_block_3 23040 13 208 224 16
cert_test_block_3 23040 14 224 240 16
cert_test_block_3 23040 15 240 256 16
cert_test_block_3 23040 16 256 272 16
cert_test_block_3 23040 17 272 288 16
cert_test_block_3 23040 18 288 304 16
cert_test_block_3 23040 19 304 320 16
cert_test_block_3 23040 20 320 336 16
cert_test_block_3 23040 21 336 352 16
cert_test_block_3 23040 22 352 368 16
cert_test_block_3 23040 23 368 384 16
cert_test_block_3 23040 24 384 400 16
cert_test_block_3 23040 25 400 416 16
cert_test_block_3 23040 26 416 432 16
cert_test_block_3 23040 27 432 448 16
cert_test_block_3 23040 28 448 464 16
cert_test_block_3 23040 29 464 480 16
cert_test_block_3 23040 30 480 496 16
cert_test_block_3 23040 31 496 512 16
cert_test_block_3 23040 32 512 528 16
cert_test_block_3 23040 33 528 544 16
cert_test_block_3 23040 34 544 560 16
cert_test_block_3 23040 35 560 576 16
cert_test_block_3 23040 36 576 592 16
cert_test_block_3 23040 37 592 608 16
cert_test_block_3 23040 38 608 624 16
cert_test_block_3 23040 39 624 640 16
theorem test23040_complete : Interval test23040 0 640 :=
  (interval_append test23040 0 320 640
  (interval_append test23040 0 160 320
  (interval_append test23040 0 80 160
  (interval_append test23040 0 32 80
  (interval_append test23040 0 16 32
  test23040_block_0
  test23040_block_1)
  (interval_append test23040 32 48 80
  test23040_block_2
  (interval_append test23040 48 64 80
  test23040_block_3
  test23040_block_4)))
  (interval_append test23040 80 112 160
  (interval_append test23040 80 96 112
  test23040_block_5
  test23040_block_6)
  (interval_append test23040 112 128 160
  test23040_block_7
  (interval_append test23040 128 144 160
  test23040_block_8
  test23040_block_9))))
  (interval_append test23040 160 240 320
  (interval_append test23040 160 192 240
  (interval_append test23040 160 176 192
  test23040_block_10
  test23040_block_11)
  (interval_append test23040 192 208 240
  test23040_block_12
  (interval_append test23040 208 224 240
  test23040_block_13
  test23040_block_14)))
  (interval_append test23040 240 272 320
  (interval_append test23040 240 256 272
  test23040_block_15
  test23040_block_16)
  (interval_append test23040 272 288 320
  test23040_block_17
  (interval_append test23040 288 304 320
  test23040_block_18
  test23040_block_19)))))
  (interval_append test23040 320 480 640
  (interval_append test23040 320 400 480
  (interval_append test23040 320 352 400
  (interval_append test23040 320 336 352
  test23040_block_20
  test23040_block_21)
  (interval_append test23040 352 368 400
  test23040_block_22
  (interval_append test23040 368 384 400
  test23040_block_23
  test23040_block_24)))
  (interval_append test23040 400 432 480
  (interval_append test23040 400 416 432
  test23040_block_25
  test23040_block_26)
  (interval_append test23040 432 448 480
  test23040_block_27
  (interval_append test23040 448 464 480
  test23040_block_28
  test23040_block_29))))
  (interval_append test23040 480 560 640
  (interval_append test23040 480 512 560
  (interval_append test23040 480 496 512
  test23040_block_30
  test23040_block_31)
  (interval_append test23040 512 528 560
  test23040_block_32
  (interval_append test23040 528 544 560
  test23040_block_33
  test23040_block_34)))
  (interval_append test23040 560 592 640
  (interval_append test23040 560 576 592
  test23040_block_35
  test23040_block_36)
  (interval_append test23040 592 608 640
  test23040_block_37
  (interval_append test23040 608 624 640
  test23040_block_38
  test23040_block_39))))))
cert_nodeInterval_3 23040 23680
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 23680
cert_test_block_3 23680 0 0 16 16
cert_test_block_3 23680 1 16 32 16
cert_test_block_3 23680 2 32 48 16
cert_test_block_3 23680 3 48 64 16
cert_test_block_3 23680 4 64 80 16
cert_test_block_3 23680 5 80 96 16
cert_test_block_3 23680 6 96 112 16
cert_test_block_3 23680 7 112 128 16
cert_test_block_3 23680 8 128 144 16
cert_test_block_3 23680 9 144 160 16
cert_test_block_3 23680 10 160 176 16
cert_test_block_3 23680 11 176 192 16
cert_test_block_3 23680 12 192 208 16
cert_test_block_3 23680 13 208 224 16
cert_test_block_3 23680 14 224 240 16
cert_test_block_3 23680 15 240 256 16
cert_test_block_3 23680 16 256 272 16
cert_test_block_3 23680 17 272 288 16
cert_test_block_3 23680 18 288 304 16
cert_test_block_3 23680 19 304 320 16
cert_test_block_3 23680 20 320 336 16
cert_test_block_3 23680 21 336 352 16
cert_test_block_3 23680 22 352 368 16
cert_test_block_3 23680 23 368 384 16
cert_test_block_3 23680 24 384 400 16
cert_test_block_3 23680 25 400 416 16
cert_test_block_3 23680 26 416 432 16
cert_test_block_3 23680 27 432 448 16
cert_test_block_3 23680 28 448 464 16
cert_test_block_3 23680 29 464 480 16
cert_test_block_3 23680 30 480 496 16
cert_test_block_3 23680 31 496 512 16
cert_test_block_3 23680 32 512 528 16
cert_test_block_3 23680 33 528 544 16
cert_test_block_3 23680 34 544 560 16
cert_test_block_3 23680 35 560 576 16
cert_test_block_3 23680 36 576 592 16
cert_test_block_3 23680 37 592 608 16
cert_test_block_3 23680 38 608 624 16
cert_test_block_3 23680 39 624 640 16
theorem test23680_complete : Interval test23680 0 640 :=
  (interval_append test23680 0 320 640
  (interval_append test23680 0 160 320
  (interval_append test23680 0 80 160
  (interval_append test23680 0 32 80
  (interval_append test23680 0 16 32
  test23680_block_0
  test23680_block_1)
  (interval_append test23680 32 48 80
  test23680_block_2
  (interval_append test23680 48 64 80
  test23680_block_3
  test23680_block_4)))
  (interval_append test23680 80 112 160
  (interval_append test23680 80 96 112
  test23680_block_5
  test23680_block_6)
  (interval_append test23680 112 128 160
  test23680_block_7
  (interval_append test23680 128 144 160
  test23680_block_8
  test23680_block_9))))
  (interval_append test23680 160 240 320
  (interval_append test23680 160 192 240
  (interval_append test23680 160 176 192
  test23680_block_10
  test23680_block_11)
  (interval_append test23680 192 208 240
  test23680_block_12
  (interval_append test23680 208 224 240
  test23680_block_13
  test23680_block_14)))
  (interval_append test23680 240 272 320
  (interval_append test23680 240 256 272
  test23680_block_15
  test23680_block_16)
  (interval_append test23680 272 288 320
  test23680_block_17
  (interval_append test23680 288 304 320
  test23680_block_18
  test23680_block_19)))))
  (interval_append test23680 320 480 640
  (interval_append test23680 320 400 480
  (interval_append test23680 320 352 400
  (interval_append test23680 320 336 352
  test23680_block_20
  test23680_block_21)
  (interval_append test23680 352 368 400
  test23680_block_22
  (interval_append test23680 368 384 400
  test23680_block_23
  test23680_block_24)))
  (interval_append test23680 400 432 480
  (interval_append test23680 400 416 432
  test23680_block_25
  test23680_block_26)
  (interval_append test23680 432 448 480
  test23680_block_27
  (interval_append test23680 448 464 480
  test23680_block_28
  test23680_block_29))))
  (interval_append test23680 480 560 640
  (interval_append test23680 480 512 560
  (interval_append test23680 480 496 512
  test23680_block_30
  test23680_block_31)
  (interval_append test23680 512 528 560
  test23680_block_32
  (interval_append test23680 528 544 560
  test23680_block_33
  test23680_block_34)))
  (interval_append test23680 560 592 640
  (interval_append test23680 560 576 592
  test23680_block_35
  test23680_block_36)
  (interval_append test23680 592 608 640
  test23680_block_37
  (interval_append test23680 608 624 640
  test23680_block_38
  test23680_block_39))))))
cert_nodeInterval_3 23680 24320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 24320
cert_test_block_3 24320 0 0 16 16
cert_test_block_3 24320 1 16 32 16
cert_test_block_3 24320 2 32 48 16
cert_test_block_3 24320 3 48 64 16
cert_test_block_3 24320 4 64 80 16
cert_test_block_3 24320 5 80 96 16
cert_test_block_3 24320 6 96 112 16
cert_test_block_3 24320 7 112 128 16
cert_test_block_3 24320 8 128 144 16
cert_test_block_3 24320 9 144 160 16
cert_test_block_3 24320 10 160 176 16
cert_test_block_3 24320 11 176 192 16
cert_test_block_3 24320 12 192 208 16
cert_test_block_3 24320 13 208 224 16
cert_test_block_3 24320 14 224 240 16
cert_test_block_3 24320 15 240 256 16
cert_test_block_3 24320 16 256 272 16
cert_test_block_3 24320 17 272 288 16
cert_test_block_3 24320 18 288 304 16
cert_test_block_3 24320 19 304 320 16
cert_test_block_3 24320 20 320 336 16
cert_test_block_3 24320 21 336 352 16
cert_test_block_3 24320 22 352 368 16
cert_test_block_3 24320 23 368 384 16
cert_test_block_3 24320 24 384 400 16
cert_test_block_3 24320 25 400 416 16
cert_test_block_3 24320 26 416 432 16
cert_test_block_3 24320 27 432 448 16
cert_test_block_3 24320 28 448 464 16
cert_test_block_3 24320 29 464 480 16
cert_test_block_3 24320 30 480 496 16
cert_test_block_3 24320 31 496 512 16
cert_test_block_3 24320 32 512 528 16
cert_test_block_3 24320 33 528 544 16
cert_test_block_3 24320 34 544 560 16
cert_test_block_3 24320 35 560 576 16
cert_test_block_3 24320 36 576 592 16
cert_test_block_3 24320 37 592 608 16
cert_test_block_3 24320 38 608 624 16
cert_test_block_3 24320 39 624 640 16
theorem test24320_complete : Interval test24320 0 640 :=
  (interval_append test24320 0 320 640
  (interval_append test24320 0 160 320
  (interval_append test24320 0 80 160
  (interval_append test24320 0 32 80
  (interval_append test24320 0 16 32
  test24320_block_0
  test24320_block_1)
  (interval_append test24320 32 48 80
  test24320_block_2
  (interval_append test24320 48 64 80
  test24320_block_3
  test24320_block_4)))
  (interval_append test24320 80 112 160
  (interval_append test24320 80 96 112
  test24320_block_5
  test24320_block_6)
  (interval_append test24320 112 128 160
  test24320_block_7
  (interval_append test24320 128 144 160
  test24320_block_8
  test24320_block_9))))
  (interval_append test24320 160 240 320
  (interval_append test24320 160 192 240
  (interval_append test24320 160 176 192
  test24320_block_10
  test24320_block_11)
  (interval_append test24320 192 208 240
  test24320_block_12
  (interval_append test24320 208 224 240
  test24320_block_13
  test24320_block_14)))
  (interval_append test24320 240 272 320
  (interval_append test24320 240 256 272
  test24320_block_15
  test24320_block_16)
  (interval_append test24320 272 288 320
  test24320_block_17
  (interval_append test24320 288 304 320
  test24320_block_18
  test24320_block_19)))))
  (interval_append test24320 320 480 640
  (interval_append test24320 320 400 480
  (interval_append test24320 320 352 400
  (interval_append test24320 320 336 352
  test24320_block_20
  test24320_block_21)
  (interval_append test24320 352 368 400
  test24320_block_22
  (interval_append test24320 368 384 400
  test24320_block_23
  test24320_block_24)))
  (interval_append test24320 400 432 480
  (interval_append test24320 400 416 432
  test24320_block_25
  test24320_block_26)
  (interval_append test24320 432 448 480
  test24320_block_27
  (interval_append test24320 448 464 480
  test24320_block_28
  test24320_block_29))))
  (interval_append test24320 480 560 640
  (interval_append test24320 480 512 560
  (interval_append test24320 480 496 512
  test24320_block_30
  test24320_block_31)
  (interval_append test24320 512 528 560
  test24320_block_32
  (interval_append test24320 528 544 560
  test24320_block_33
  test24320_block_34)))
  (interval_append test24320 560 592 640
  (interval_append test24320 560 576 592
  test24320_block_35
  test24320_block_36)
  (interval_append test24320 592 608 640
  test24320_block_37
  (interval_append test24320 608 624 640
  test24320_block_38
  test24320_block_39))))))
cert_nodeInterval_3 24320 24960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 24960
cert_test_block_3 24960 0 0 16 16
cert_test_block_3 24960 1 16 32 16
cert_test_block_3 24960 2 32 48 16
cert_test_block_3 24960 3 48 64 16
cert_test_block_3 24960 4 64 80 16
cert_test_block_3 24960 5 80 96 16
cert_test_block_3 24960 6 96 112 16
cert_test_block_3 24960 7 112 128 16
cert_test_block_3 24960 8 128 144 16
cert_test_block_3 24960 9 144 160 16
cert_test_block_3 24960 10 160 176 16
cert_test_block_3 24960 11 176 192 16
cert_test_block_3 24960 12 192 208 16
cert_test_block_3 24960 13 208 224 16
cert_test_block_3 24960 14 224 240 16
cert_test_block_3 24960 15 240 256 16
cert_test_block_3 24960 16 256 272 16
cert_test_block_3 24960 17 272 288 16
cert_test_block_3 24960 18 288 304 16
cert_test_block_3 24960 19 304 320 16
cert_test_block_3 24960 20 320 336 16
cert_test_block_3 24960 21 336 352 16
cert_test_block_3 24960 22 352 368 16
cert_test_block_3 24960 23 368 384 16
cert_test_block_3 24960 24 384 400 16
cert_test_block_3 24960 25 400 416 16
cert_test_block_3 24960 26 416 432 16
cert_test_block_3 24960 27 432 448 16
cert_test_block_3 24960 28 448 464 16
cert_test_block_3 24960 29 464 480 16
cert_test_block_3 24960 30 480 496 16
cert_test_block_3 24960 31 496 512 16
cert_test_block_3 24960 32 512 528 16
cert_test_block_3 24960 33 528 544 16
cert_test_block_3 24960 34 544 560 16
cert_test_block_3 24960 35 560 576 16
cert_test_block_3 24960 36 576 592 16
cert_test_block_3 24960 37 592 608 16
cert_test_block_3 24960 38 608 624 16
cert_test_block_3 24960 39 624 640 16
theorem test24960_complete : Interval test24960 0 640 :=
  (interval_append test24960 0 320 640
  (interval_append test24960 0 160 320
  (interval_append test24960 0 80 160
  (interval_append test24960 0 32 80
  (interval_append test24960 0 16 32
  test24960_block_0
  test24960_block_1)
  (interval_append test24960 32 48 80
  test24960_block_2
  (interval_append test24960 48 64 80
  test24960_block_3
  test24960_block_4)))
  (interval_append test24960 80 112 160
  (interval_append test24960 80 96 112
  test24960_block_5
  test24960_block_6)
  (interval_append test24960 112 128 160
  test24960_block_7
  (interval_append test24960 128 144 160
  test24960_block_8
  test24960_block_9))))
  (interval_append test24960 160 240 320
  (interval_append test24960 160 192 240
  (interval_append test24960 160 176 192
  test24960_block_10
  test24960_block_11)
  (interval_append test24960 192 208 240
  test24960_block_12
  (interval_append test24960 208 224 240
  test24960_block_13
  test24960_block_14)))
  (interval_append test24960 240 272 320
  (interval_append test24960 240 256 272
  test24960_block_15
  test24960_block_16)
  (interval_append test24960 272 288 320
  test24960_block_17
  (interval_append test24960 288 304 320
  test24960_block_18
  test24960_block_19)))))
  (interval_append test24960 320 480 640
  (interval_append test24960 320 400 480
  (interval_append test24960 320 352 400
  (interval_append test24960 320 336 352
  test24960_block_20
  test24960_block_21)
  (interval_append test24960 352 368 400
  test24960_block_22
  (interval_append test24960 368 384 400
  test24960_block_23
  test24960_block_24)))
  (interval_append test24960 400 432 480
  (interval_append test24960 400 416 432
  test24960_block_25
  test24960_block_26)
  (interval_append test24960 432 448 480
  test24960_block_27
  (interval_append test24960 448 464 480
  test24960_block_28
  test24960_block_29))))
  (interval_append test24960 480 560 640
  (interval_append test24960 480 512 560
  (interval_append test24960 480 496 512
  test24960_block_30
  test24960_block_31)
  (interval_append test24960 512 528 560
  test24960_block_32
  (interval_append test24960 528 544 560
  test24960_block_33
  test24960_block_34)))
  (interval_append test24960 560 592 640
  (interval_append test24960 560 576 592
  test24960_block_35
  test24960_block_36)
  (interval_append test24960 592 608 640
  test24960_block_37
  (interval_append test24960 608 624 640
  test24960_block_38
  test24960_block_39))))))
cert_nodeInterval_3 24960 25600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 25600
cert_test_block_3 25600 0 0 16 16
cert_test_block_3 25600 1 16 32 16
cert_test_block_3 25600 2 32 48 16
cert_test_block_3 25600 3 48 64 16
cert_test_block_3 25600 4 64 80 16
cert_test_block_3 25600 5 80 96 16
cert_test_block_3 25600 6 96 112 16
cert_test_block_3 25600 7 112 128 16
cert_test_block_3 25600 8 128 144 16
cert_test_block_3 25600 9 144 160 16
cert_test_block_3 25600 10 160 176 16
cert_test_block_3 25600 11 176 192 16
cert_test_block_3 25600 12 192 208 16
cert_test_block_3 25600 13 208 224 16
cert_test_block_3 25600 14 224 240 16
cert_test_block_3 25600 15 240 256 16
cert_test_block_3 25600 16 256 272 16
cert_test_block_3 25600 17 272 288 16
cert_test_block_3 25600 18 288 304 16
cert_test_block_3 25600 19 304 320 16
cert_test_block_3 25600 20 320 336 16
cert_test_block_3 25600 21 336 352 16
cert_test_block_3 25600 22 352 368 16
cert_test_block_3 25600 23 368 384 16
cert_test_block_3 25600 24 384 400 16
cert_test_block_3 25600 25 400 416 16
cert_test_block_3 25600 26 416 432 16
cert_test_block_3 25600 27 432 448 16
cert_test_block_3 25600 28 448 464 16
cert_test_block_3 25600 29 464 480 16
cert_test_block_3 25600 30 480 496 16
cert_test_block_3 25600 31 496 512 16
cert_test_block_3 25600 32 512 528 16
cert_test_block_3 25600 33 528 544 16
cert_test_block_3 25600 34 544 560 16
cert_test_block_3 25600 35 560 576 16
cert_test_block_3 25600 36 576 592 16
cert_test_block_3 25600 37 592 608 16
cert_test_block_3 25600 38 608 624 16
cert_test_block_3 25600 39 624 640 16
theorem test25600_complete : Interval test25600 0 640 :=
  (interval_append test25600 0 320 640
  (interval_append test25600 0 160 320
  (interval_append test25600 0 80 160
  (interval_append test25600 0 32 80
  (interval_append test25600 0 16 32
  test25600_block_0
  test25600_block_1)
  (interval_append test25600 32 48 80
  test25600_block_2
  (interval_append test25600 48 64 80
  test25600_block_3
  test25600_block_4)))
  (interval_append test25600 80 112 160
  (interval_append test25600 80 96 112
  test25600_block_5
  test25600_block_6)
  (interval_append test25600 112 128 160
  test25600_block_7
  (interval_append test25600 128 144 160
  test25600_block_8
  test25600_block_9))))
  (interval_append test25600 160 240 320
  (interval_append test25600 160 192 240
  (interval_append test25600 160 176 192
  test25600_block_10
  test25600_block_11)
  (interval_append test25600 192 208 240
  test25600_block_12
  (interval_append test25600 208 224 240
  test25600_block_13
  test25600_block_14)))
  (interval_append test25600 240 272 320
  (interval_append test25600 240 256 272
  test25600_block_15
  test25600_block_16)
  (interval_append test25600 272 288 320
  test25600_block_17
  (interval_append test25600 288 304 320
  test25600_block_18
  test25600_block_19)))))
  (interval_append test25600 320 480 640
  (interval_append test25600 320 400 480
  (interval_append test25600 320 352 400
  (interval_append test25600 320 336 352
  test25600_block_20
  test25600_block_21)
  (interval_append test25600 352 368 400
  test25600_block_22
  (interval_append test25600 368 384 400
  test25600_block_23
  test25600_block_24)))
  (interval_append test25600 400 432 480
  (interval_append test25600 400 416 432
  test25600_block_25
  test25600_block_26)
  (interval_append test25600 432 448 480
  test25600_block_27
  (interval_append test25600 448 464 480
  test25600_block_28
  test25600_block_29))))
  (interval_append test25600 480 560 640
  (interval_append test25600 480 512 560
  (interval_append test25600 480 496 512
  test25600_block_30
  test25600_block_31)
  (interval_append test25600 512 528 560
  test25600_block_32
  (interval_append test25600 528 544 560
  test25600_block_33
  test25600_block_34)))
  (interval_append test25600 560 592 640
  (interval_append test25600 560 576 592
  test25600_block_35
  test25600_block_36)
  (interval_append test25600 592 608 640
  test25600_block_37
  (interval_append test25600 608 624 640
  test25600_block_38
  test25600_block_39))))))
cert_nodeInterval_3 25600 26240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 26240
cert_test_block_3 26240 0 0 16 16
cert_test_block_3 26240 1 16 32 16
cert_test_block_3 26240 2 32 48 16
cert_test_block_3 26240 3 48 64 16
cert_test_block_3 26240 4 64 80 16
cert_test_block_3 26240 5 80 96 16
cert_test_block_3 26240 6 96 112 16
cert_test_block_3 26240 7 112 128 16
cert_test_block_3 26240 8 128 144 16
cert_test_block_3 26240 9 144 160 16
cert_test_block_3 26240 10 160 176 16
cert_test_block_3 26240 11 176 192 16
cert_test_block_3 26240 12 192 208 16
cert_test_block_3 26240 13 208 224 16
cert_test_block_3 26240 14 224 240 16
cert_test_block_3 26240 15 240 256 16
cert_test_block_3 26240 16 256 272 16
cert_test_block_3 26240 17 272 288 16
cert_test_block_3 26240 18 288 304 16
cert_test_block_3 26240 19 304 320 16
cert_test_block_3 26240 20 320 336 16
cert_test_block_3 26240 21 336 352 16
cert_test_block_3 26240 22 352 368 16
cert_test_block_3 26240 23 368 384 16
cert_test_block_3 26240 24 384 400 16
cert_test_block_3 26240 25 400 416 16
cert_test_block_3 26240 26 416 432 16
cert_test_block_3 26240 27 432 448 16
cert_test_block_3 26240 28 448 464 16
cert_test_block_3 26240 29 464 480 16
cert_test_block_3 26240 30 480 496 16
cert_test_block_3 26240 31 496 512 16
cert_test_block_3 26240 32 512 528 16
cert_test_block_3 26240 33 528 544 16
cert_test_block_3 26240 34 544 560 16
cert_test_block_3 26240 35 560 576 16
cert_test_block_3 26240 36 576 592 16
cert_test_block_3 26240 37 592 608 16
cert_test_block_3 26240 38 608 624 16
cert_test_block_3 26240 39 624 640 16
theorem test26240_complete : Interval test26240 0 640 :=
  (interval_append test26240 0 320 640
  (interval_append test26240 0 160 320
  (interval_append test26240 0 80 160
  (interval_append test26240 0 32 80
  (interval_append test26240 0 16 32
  test26240_block_0
  test26240_block_1)
  (interval_append test26240 32 48 80
  test26240_block_2
  (interval_append test26240 48 64 80
  test26240_block_3
  test26240_block_4)))
  (interval_append test26240 80 112 160
  (interval_append test26240 80 96 112
  test26240_block_5
  test26240_block_6)
  (interval_append test26240 112 128 160
  test26240_block_7
  (interval_append test26240 128 144 160
  test26240_block_8
  test26240_block_9))))
  (interval_append test26240 160 240 320
  (interval_append test26240 160 192 240
  (interval_append test26240 160 176 192
  test26240_block_10
  test26240_block_11)
  (interval_append test26240 192 208 240
  test26240_block_12
  (interval_append test26240 208 224 240
  test26240_block_13
  test26240_block_14)))
  (interval_append test26240 240 272 320
  (interval_append test26240 240 256 272
  test26240_block_15
  test26240_block_16)
  (interval_append test26240 272 288 320
  test26240_block_17
  (interval_append test26240 288 304 320
  test26240_block_18
  test26240_block_19)))))
  (interval_append test26240 320 480 640
  (interval_append test26240 320 400 480
  (interval_append test26240 320 352 400
  (interval_append test26240 320 336 352
  test26240_block_20
  test26240_block_21)
  (interval_append test26240 352 368 400
  test26240_block_22
  (interval_append test26240 368 384 400
  test26240_block_23
  test26240_block_24)))
  (interval_append test26240 400 432 480
  (interval_append test26240 400 416 432
  test26240_block_25
  test26240_block_26)
  (interval_append test26240 432 448 480
  test26240_block_27
  (interval_append test26240 448 464 480
  test26240_block_28
  test26240_block_29))))
  (interval_append test26240 480 560 640
  (interval_append test26240 480 512 560
  (interval_append test26240 480 496 512
  test26240_block_30
  test26240_block_31)
  (interval_append test26240 512 528 560
  test26240_block_32
  (interval_append test26240 528 544 560
  test26240_block_33
  test26240_block_34)))
  (interval_append test26240 560 592 640
  (interval_append test26240 560 576 592
  test26240_block_35
  test26240_block_36)
  (interval_append test26240 592 608 640
  test26240_block_37
  (interval_append test26240 608 624 640
  test26240_block_38
  test26240_block_39))))))
cert_nodeInterval_3 26240 26880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 26880
cert_test_block_3 26880 0 0 16 16
cert_test_block_3 26880 1 16 32 16
cert_test_block_3 26880 2 32 48 16
cert_test_block_3 26880 3 48 64 16
cert_test_block_3 26880 4 64 80 16
cert_test_block_3 26880 5 80 96 16
cert_test_block_3 26880 6 96 112 16
cert_test_block_3 26880 7 112 128 16
cert_test_block_3 26880 8 128 144 16
cert_test_block_3 26880 9 144 160 16
cert_test_block_3 26880 10 160 176 16
cert_test_block_3 26880 11 176 192 16
cert_test_block_3 26880 12 192 208 16
cert_test_block_3 26880 13 208 224 16
cert_test_block_3 26880 14 224 240 16
cert_test_block_3 26880 15 240 256 16
cert_test_block_3 26880 16 256 272 16
cert_test_block_3 26880 17 272 288 16
cert_test_block_3 26880 18 288 304 16
cert_test_block_3 26880 19 304 320 16
cert_test_block_3 26880 20 320 336 16
cert_test_block_3 26880 21 336 352 16
cert_test_block_3 26880 22 352 368 16
cert_test_block_3 26880 23 368 384 16
cert_test_block_3 26880 24 384 400 16
cert_test_block_3 26880 25 400 416 16
cert_test_block_3 26880 26 416 432 16
cert_test_block_3 26880 27 432 448 16
cert_test_block_3 26880 28 448 464 16
cert_test_block_3 26880 29 464 480 16
cert_test_block_3 26880 30 480 496 16
cert_test_block_3 26880 31 496 512 16
cert_test_block_3 26880 32 512 528 16
cert_test_block_3 26880 33 528 544 16
cert_test_block_3 26880 34 544 560 16
cert_test_block_3 26880 35 560 576 16
cert_test_block_3 26880 36 576 592 16
cert_test_block_3 26880 37 592 608 16
cert_test_block_3 26880 38 608 624 16
cert_test_block_3 26880 39 624 640 16
theorem test26880_complete : Interval test26880 0 640 :=
  (interval_append test26880 0 320 640
  (interval_append test26880 0 160 320
  (interval_append test26880 0 80 160
  (interval_append test26880 0 32 80
  (interval_append test26880 0 16 32
  test26880_block_0
  test26880_block_1)
  (interval_append test26880 32 48 80
  test26880_block_2
  (interval_append test26880 48 64 80
  test26880_block_3
  test26880_block_4)))
  (interval_append test26880 80 112 160
  (interval_append test26880 80 96 112
  test26880_block_5
  test26880_block_6)
  (interval_append test26880 112 128 160
  test26880_block_7
  (interval_append test26880 128 144 160
  test26880_block_8
  test26880_block_9))))
  (interval_append test26880 160 240 320
  (interval_append test26880 160 192 240
  (interval_append test26880 160 176 192
  test26880_block_10
  test26880_block_11)
  (interval_append test26880 192 208 240
  test26880_block_12
  (interval_append test26880 208 224 240
  test26880_block_13
  test26880_block_14)))
  (interval_append test26880 240 272 320
  (interval_append test26880 240 256 272
  test26880_block_15
  test26880_block_16)
  (interval_append test26880 272 288 320
  test26880_block_17
  (interval_append test26880 288 304 320
  test26880_block_18
  test26880_block_19)))))
  (interval_append test26880 320 480 640
  (interval_append test26880 320 400 480
  (interval_append test26880 320 352 400
  (interval_append test26880 320 336 352
  test26880_block_20
  test26880_block_21)
  (interval_append test26880 352 368 400
  test26880_block_22
  (interval_append test26880 368 384 400
  test26880_block_23
  test26880_block_24)))
  (interval_append test26880 400 432 480
  (interval_append test26880 400 416 432
  test26880_block_25
  test26880_block_26)
  (interval_append test26880 432 448 480
  test26880_block_27
  (interval_append test26880 448 464 480
  test26880_block_28
  test26880_block_29))))
  (interval_append test26880 480 560 640
  (interval_append test26880 480 512 560
  (interval_append test26880 480 496 512
  test26880_block_30
  test26880_block_31)
  (interval_append test26880 512 528 560
  test26880_block_32
  (interval_append test26880 528 544 560
  test26880_block_33
  test26880_block_34)))
  (interval_append test26880 560 592 640
  (interval_append test26880 560 576 592
  test26880_block_35
  test26880_block_36)
  (interval_append test26880 592 608 640
  test26880_block_37
  (interval_append test26880 608 624 640
  test26880_block_38
  test26880_block_39))))))
cert_nodeInterval_3 26880 27520
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 27520
cert_test_block_3 27520 0 0 16 16
cert_test_block_3 27520 1 16 32 16
cert_test_block_3 27520 2 32 48 16
cert_test_block_3 27520 3 48 64 16
cert_test_block_3 27520 4 64 80 16
cert_test_block_3 27520 5 80 96 16
cert_test_block_3 27520 6 96 112 16
cert_test_block_3 27520 7 112 128 16
cert_test_block_3 27520 8 128 144 16
cert_test_block_3 27520 9 144 160 16
cert_test_block_3 27520 10 160 176 16
cert_test_block_3 27520 11 176 192 16
cert_test_block_3 27520 12 192 208 16
cert_test_block_3 27520 13 208 224 16
cert_test_block_3 27520 14 224 240 16
cert_test_block_3 27520 15 240 256 16
cert_test_block_3 27520 16 256 272 16
cert_test_block_3 27520 17 272 288 16
cert_test_block_3 27520 18 288 304 16
cert_test_block_3 27520 19 304 320 16
cert_test_block_3 27520 20 320 336 16
cert_test_block_3 27520 21 336 352 16
cert_test_block_3 27520 22 352 368 16
cert_test_block_3 27520 23 368 384 16
cert_test_block_3 27520 24 384 400 16
cert_test_block_3 27520 25 400 416 16
cert_test_block_3 27520 26 416 432 16
cert_test_block_3 27520 27 432 448 16
cert_test_block_3 27520 28 448 464 16
cert_test_block_3 27520 29 464 480 16
cert_test_block_3 27520 30 480 496 16
cert_test_block_3 27520 31 496 512 16
cert_test_block_3 27520 32 512 528 16
cert_test_block_3 27520 33 528 544 16
cert_test_block_3 27520 34 544 560 16
cert_test_block_3 27520 35 560 576 16
cert_test_block_3 27520 36 576 592 16
cert_test_block_3 27520 37 592 608 16
cert_test_block_3 27520 38 608 624 16
cert_test_block_3 27520 39 624 640 16
theorem test27520_complete : Interval test27520 0 640 :=
  (interval_append test27520 0 320 640
  (interval_append test27520 0 160 320
  (interval_append test27520 0 80 160
  (interval_append test27520 0 32 80
  (interval_append test27520 0 16 32
  test27520_block_0
  test27520_block_1)
  (interval_append test27520 32 48 80
  test27520_block_2
  (interval_append test27520 48 64 80
  test27520_block_3
  test27520_block_4)))
  (interval_append test27520 80 112 160
  (interval_append test27520 80 96 112
  test27520_block_5
  test27520_block_6)
  (interval_append test27520 112 128 160
  test27520_block_7
  (interval_append test27520 128 144 160
  test27520_block_8
  test27520_block_9))))
  (interval_append test27520 160 240 320
  (interval_append test27520 160 192 240
  (interval_append test27520 160 176 192
  test27520_block_10
  test27520_block_11)
  (interval_append test27520 192 208 240
  test27520_block_12
  (interval_append test27520 208 224 240
  test27520_block_13
  test27520_block_14)))
  (interval_append test27520 240 272 320
  (interval_append test27520 240 256 272
  test27520_block_15
  test27520_block_16)
  (interval_append test27520 272 288 320
  test27520_block_17
  (interval_append test27520 288 304 320
  test27520_block_18
  test27520_block_19)))))
  (interval_append test27520 320 480 640
  (interval_append test27520 320 400 480
  (interval_append test27520 320 352 400
  (interval_append test27520 320 336 352
  test27520_block_20
  test27520_block_21)
  (interval_append test27520 352 368 400
  test27520_block_22
  (interval_append test27520 368 384 400
  test27520_block_23
  test27520_block_24)))
  (interval_append test27520 400 432 480
  (interval_append test27520 400 416 432
  test27520_block_25
  test27520_block_26)
  (interval_append test27520 432 448 480
  test27520_block_27
  (interval_append test27520 448 464 480
  test27520_block_28
  test27520_block_29))))
  (interval_append test27520 480 560 640
  (interval_append test27520 480 512 560
  (interval_append test27520 480 496 512
  test27520_block_30
  test27520_block_31)
  (interval_append test27520 512 528 560
  test27520_block_32
  (interval_append test27520 528 544 560
  test27520_block_33
  test27520_block_34)))
  (interval_append test27520 560 592 640
  (interval_append test27520 560 576 592
  test27520_block_35
  test27520_block_36)
  (interval_append test27520 592 608 640
  test27520_block_37
  (interval_append test27520 608 624 640
  test27520_block_38
  test27520_block_39))))))
cert_nodeInterval_3 27520 28160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
end
end
