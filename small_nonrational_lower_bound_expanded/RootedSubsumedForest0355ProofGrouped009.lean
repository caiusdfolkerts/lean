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
cert_test_11 69120
cert_test_block_3 69120 0 0 16 16
cert_test_block_3 69120 1 16 32 16
cert_test_block_3 69120 2 32 48 16
cert_test_block_3 69120 3 48 64 16
cert_test_block_3 69120 4 64 80 16
cert_test_block_3 69120 5 80 96 16
cert_test_block_3 69120 6 96 112 16
cert_test_block_3 69120 7 112 128 16
cert_test_block_3 69120 8 128 144 16
cert_test_block_3 69120 9 144 160 16
cert_test_block_3 69120 10 160 176 16
cert_test_block_3 69120 11 176 192 16
cert_test_block_3 69120 12 192 208 16
cert_test_block_3 69120 13 208 224 16
cert_test_block_3 69120 14 224 240 16
cert_test_block_3 69120 15 240 256 16
cert_test_block_3 69120 16 256 272 16
cert_test_block_3 69120 17 272 288 16
cert_test_block_3 69120 18 288 304 16
cert_test_block_3 69120 19 304 320 16
cert_test_block_3 69120 20 320 336 16
cert_test_block_3 69120 21 336 352 16
cert_test_block_3 69120 22 352 368 16
cert_test_block_3 69120 23 368 384 16
cert_test_block_3 69120 24 384 400 16
cert_test_block_3 69120 25 400 416 16
cert_test_block_3 69120 26 416 432 16
cert_test_block_3 69120 27 432 448 16
cert_test_block_3 69120 28 448 464 16
cert_test_block_3 69120 29 464 480 16
cert_test_block_3 69120 30 480 496 16
cert_test_block_3 69120 31 496 512 16
cert_test_block_3 69120 32 512 528 16
cert_test_block_3 69120 33 528 544 16
cert_test_block_3 69120 34 544 560 16
cert_test_block_3 69120 35 560 576 16
cert_test_block_3 69120 36 576 592 16
cert_test_block_3 69120 37 592 608 16
cert_test_block_3 69120 38 608 624 16
cert_test_block_3 69120 39 624 640 16
theorem test69120_complete : Interval test69120 0 640 :=
  (interval_append test69120 0 320 640
  (interval_append test69120 0 160 320
  (interval_append test69120 0 80 160
  (interval_append test69120 0 32 80
  (interval_append test69120 0 16 32
  test69120_block_0
  test69120_block_1)
  (interval_append test69120 32 48 80
  test69120_block_2
  (interval_append test69120 48 64 80
  test69120_block_3
  test69120_block_4)))
  (interval_append test69120 80 112 160
  (interval_append test69120 80 96 112
  test69120_block_5
  test69120_block_6)
  (interval_append test69120 112 128 160
  test69120_block_7
  (interval_append test69120 128 144 160
  test69120_block_8
  test69120_block_9))))
  (interval_append test69120 160 240 320
  (interval_append test69120 160 192 240
  (interval_append test69120 160 176 192
  test69120_block_10
  test69120_block_11)
  (interval_append test69120 192 208 240
  test69120_block_12
  (interval_append test69120 208 224 240
  test69120_block_13
  test69120_block_14)))
  (interval_append test69120 240 272 320
  (interval_append test69120 240 256 272
  test69120_block_15
  test69120_block_16)
  (interval_append test69120 272 288 320
  test69120_block_17
  (interval_append test69120 288 304 320
  test69120_block_18
  test69120_block_19)))))
  (interval_append test69120 320 480 640
  (interval_append test69120 320 400 480
  (interval_append test69120 320 352 400
  (interval_append test69120 320 336 352
  test69120_block_20
  test69120_block_21)
  (interval_append test69120 352 368 400
  test69120_block_22
  (interval_append test69120 368 384 400
  test69120_block_23
  test69120_block_24)))
  (interval_append test69120 400 432 480
  (interval_append test69120 400 416 432
  test69120_block_25
  test69120_block_26)
  (interval_append test69120 432 448 480
  test69120_block_27
  (interval_append test69120 448 464 480
  test69120_block_28
  test69120_block_29))))
  (interval_append test69120 480 560 640
  (interval_append test69120 480 512 560
  (interval_append test69120 480 496 512
  test69120_block_30
  test69120_block_31)
  (interval_append test69120 512 528 560
  test69120_block_32
  (interval_append test69120 528 544 560
  test69120_block_33
  test69120_block_34)))
  (interval_append test69120 560 592 640
  (interval_append test69120 560 576 592
  test69120_block_35
  test69120_block_36)
  (interval_append test69120 592 608 640
  test69120_block_37
  (interval_append test69120 608 624 640
  test69120_block_38
  test69120_block_39))))))
cert_nodeInterval_3 69120 69760
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
cert_test_11 69760
cert_test_block_3 69760 0 0 16 16
cert_test_block_3 69760 1 16 32 16
cert_test_block_3 69760 2 32 48 16
cert_test_block_3 69760 3 48 64 16
cert_test_block_3 69760 4 64 80 16
cert_test_block_3 69760 5 80 96 16
cert_test_block_3 69760 6 96 112 16
cert_test_block_3 69760 7 112 128 16
cert_test_block_3 69760 8 128 144 16
cert_test_block_3 69760 9 144 160 16
cert_test_block_3 69760 10 160 176 16
cert_test_block_3 69760 11 176 192 16
cert_test_block_3 69760 12 192 208 16
cert_test_block_3 69760 13 208 224 16
cert_test_block_3 69760 14 224 240 16
cert_test_block_3 69760 15 240 256 16
cert_test_block_3 69760 16 256 272 16
cert_test_block_3 69760 17 272 288 16
cert_test_block_3 69760 18 288 304 16
cert_test_block_3 69760 19 304 320 16
cert_test_block_3 69760 20 320 336 16
cert_test_block_3 69760 21 336 352 16
cert_test_block_3 69760 22 352 368 16
cert_test_block_3 69760 23 368 384 16
cert_test_block_3 69760 24 384 400 16
cert_test_block_3 69760 25 400 416 16
cert_test_block_3 69760 26 416 432 16
cert_test_block_3 69760 27 432 448 16
cert_test_block_3 69760 28 448 464 16
cert_test_block_3 69760 29 464 480 16
cert_test_block_3 69760 30 480 496 16
cert_test_block_3 69760 31 496 512 16
cert_test_block_3 69760 32 512 528 16
cert_test_block_3 69760 33 528 544 16
cert_test_block_3 69760 34 544 560 16
cert_test_block_3 69760 35 560 576 16
cert_test_block_3 69760 36 576 592 16
cert_test_block_3 69760 37 592 608 16
cert_test_block_3 69760 38 608 624 16
cert_test_block_3 69760 39 624 640 16
theorem test69760_complete : Interval test69760 0 640 :=
  (interval_append test69760 0 320 640
  (interval_append test69760 0 160 320
  (interval_append test69760 0 80 160
  (interval_append test69760 0 32 80
  (interval_append test69760 0 16 32
  test69760_block_0
  test69760_block_1)
  (interval_append test69760 32 48 80
  test69760_block_2
  (interval_append test69760 48 64 80
  test69760_block_3
  test69760_block_4)))
  (interval_append test69760 80 112 160
  (interval_append test69760 80 96 112
  test69760_block_5
  test69760_block_6)
  (interval_append test69760 112 128 160
  test69760_block_7
  (interval_append test69760 128 144 160
  test69760_block_8
  test69760_block_9))))
  (interval_append test69760 160 240 320
  (interval_append test69760 160 192 240
  (interval_append test69760 160 176 192
  test69760_block_10
  test69760_block_11)
  (interval_append test69760 192 208 240
  test69760_block_12
  (interval_append test69760 208 224 240
  test69760_block_13
  test69760_block_14)))
  (interval_append test69760 240 272 320
  (interval_append test69760 240 256 272
  test69760_block_15
  test69760_block_16)
  (interval_append test69760 272 288 320
  test69760_block_17
  (interval_append test69760 288 304 320
  test69760_block_18
  test69760_block_19)))))
  (interval_append test69760 320 480 640
  (interval_append test69760 320 400 480
  (interval_append test69760 320 352 400
  (interval_append test69760 320 336 352
  test69760_block_20
  test69760_block_21)
  (interval_append test69760 352 368 400
  test69760_block_22
  (interval_append test69760 368 384 400
  test69760_block_23
  test69760_block_24)))
  (interval_append test69760 400 432 480
  (interval_append test69760 400 416 432
  test69760_block_25
  test69760_block_26)
  (interval_append test69760 432 448 480
  test69760_block_27
  (interval_append test69760 448 464 480
  test69760_block_28
  test69760_block_29))))
  (interval_append test69760 480 560 640
  (interval_append test69760 480 512 560
  (interval_append test69760 480 496 512
  test69760_block_30
  test69760_block_31)
  (interval_append test69760 512 528 560
  test69760_block_32
  (interval_append test69760 528 544 560
  test69760_block_33
  test69760_block_34)))
  (interval_append test69760 560 592 640
  (interval_append test69760 560 576 592
  test69760_block_35
  test69760_block_36)
  (interval_append test69760 592 608 640
  test69760_block_37
  (interval_append test69760 608 624 640
  test69760_block_38
  test69760_block_39))))))
cert_nodeInterval_3 69760 70400
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
cert_test_11 70400
cert_test_block_3 70400 0 0 16 16
cert_test_block_3 70400 1 16 32 16
cert_test_block_3 70400 2 32 48 16
cert_test_block_3 70400 3 48 64 16
cert_test_block_3 70400 4 64 80 16
cert_test_block_3 70400 5 80 96 16
cert_test_block_3 70400 6 96 112 16
cert_test_block_3 70400 7 112 128 16
cert_test_block_3 70400 8 128 144 16
cert_test_block_3 70400 9 144 160 16
cert_test_block_3 70400 10 160 176 16
cert_test_block_3 70400 11 176 192 16
cert_test_block_3 70400 12 192 208 16
cert_test_block_3 70400 13 208 224 16
cert_test_block_3 70400 14 224 240 16
cert_test_block_3 70400 15 240 256 16
cert_test_block_3 70400 16 256 272 16
cert_test_block_3 70400 17 272 288 16
cert_test_block_3 70400 18 288 304 16
cert_test_block_3 70400 19 304 320 16
cert_test_block_3 70400 20 320 336 16
cert_test_block_3 70400 21 336 352 16
cert_test_block_3 70400 22 352 368 16
cert_test_block_3 70400 23 368 384 16
cert_test_block_3 70400 24 384 400 16
cert_test_block_3 70400 25 400 416 16
cert_test_block_3 70400 26 416 432 16
cert_test_block_3 70400 27 432 448 16
cert_test_block_3 70400 28 448 464 16
cert_test_block_3 70400 29 464 480 16
cert_test_block_3 70400 30 480 496 16
cert_test_block_3 70400 31 496 512 16
cert_test_block_3 70400 32 512 528 16
cert_test_block_3 70400 33 528 544 16
cert_test_block_3 70400 34 544 560 16
cert_test_block_3 70400 35 560 576 16
cert_test_block_3 70400 36 576 592 16
cert_test_block_3 70400 37 592 608 16
cert_test_block_3 70400 38 608 624 16
cert_test_block_3 70400 39 624 640 16
theorem test70400_complete : Interval test70400 0 640 :=
  (interval_append test70400 0 320 640
  (interval_append test70400 0 160 320
  (interval_append test70400 0 80 160
  (interval_append test70400 0 32 80
  (interval_append test70400 0 16 32
  test70400_block_0
  test70400_block_1)
  (interval_append test70400 32 48 80
  test70400_block_2
  (interval_append test70400 48 64 80
  test70400_block_3
  test70400_block_4)))
  (interval_append test70400 80 112 160
  (interval_append test70400 80 96 112
  test70400_block_5
  test70400_block_6)
  (interval_append test70400 112 128 160
  test70400_block_7
  (interval_append test70400 128 144 160
  test70400_block_8
  test70400_block_9))))
  (interval_append test70400 160 240 320
  (interval_append test70400 160 192 240
  (interval_append test70400 160 176 192
  test70400_block_10
  test70400_block_11)
  (interval_append test70400 192 208 240
  test70400_block_12
  (interval_append test70400 208 224 240
  test70400_block_13
  test70400_block_14)))
  (interval_append test70400 240 272 320
  (interval_append test70400 240 256 272
  test70400_block_15
  test70400_block_16)
  (interval_append test70400 272 288 320
  test70400_block_17
  (interval_append test70400 288 304 320
  test70400_block_18
  test70400_block_19)))))
  (interval_append test70400 320 480 640
  (interval_append test70400 320 400 480
  (interval_append test70400 320 352 400
  (interval_append test70400 320 336 352
  test70400_block_20
  test70400_block_21)
  (interval_append test70400 352 368 400
  test70400_block_22
  (interval_append test70400 368 384 400
  test70400_block_23
  test70400_block_24)))
  (interval_append test70400 400 432 480
  (interval_append test70400 400 416 432
  test70400_block_25
  test70400_block_26)
  (interval_append test70400 432 448 480
  test70400_block_27
  (interval_append test70400 448 464 480
  test70400_block_28
  test70400_block_29))))
  (interval_append test70400 480 560 640
  (interval_append test70400 480 512 560
  (interval_append test70400 480 496 512
  test70400_block_30
  test70400_block_31)
  (interval_append test70400 512 528 560
  test70400_block_32
  (interval_append test70400 528 544 560
  test70400_block_33
  test70400_block_34)))
  (interval_append test70400 560 592 640
  (interval_append test70400 560 576 592
  test70400_block_35
  test70400_block_36)
  (interval_append test70400 592 608 640
  test70400_block_37
  (interval_append test70400 608 624 640
  test70400_block_38
  test70400_block_39))))))
cert_nodeInterval_3 70400 71040
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
cert_test_11 71040
cert_test_block_3 71040 0 0 16 16
cert_test_block_3 71040 1 16 32 16
cert_test_block_3 71040 2 32 48 16
cert_test_block_3 71040 3 48 64 16
cert_test_block_3 71040 4 64 80 16
cert_test_block_3 71040 5 80 96 16
cert_test_block_3 71040 6 96 112 16
cert_test_block_3 71040 7 112 128 16
cert_test_block_3 71040 8 128 144 16
cert_test_block_3 71040 9 144 160 16
cert_test_block_3 71040 10 160 176 16
cert_test_block_3 71040 11 176 192 16
cert_test_block_3 71040 12 192 208 16
cert_test_block_3 71040 13 208 224 16
cert_test_block_3 71040 14 224 240 16
cert_test_block_3 71040 15 240 256 16
cert_test_block_3 71040 16 256 272 16
cert_test_block_3 71040 17 272 288 16
cert_test_block_3 71040 18 288 304 16
cert_test_block_3 71040 19 304 320 16
cert_test_block_3 71040 20 320 336 16
cert_test_block_3 71040 21 336 352 16
cert_test_block_3 71040 22 352 368 16
cert_test_block_3 71040 23 368 384 16
cert_test_block_3 71040 24 384 400 16
cert_test_block_3 71040 25 400 416 16
cert_test_block_3 71040 26 416 432 16
cert_test_block_3 71040 27 432 448 16
cert_test_block_3 71040 28 448 464 16
cert_test_block_3 71040 29 464 480 16
cert_test_block_3 71040 30 480 496 16
cert_test_block_3 71040 31 496 512 16
cert_test_block_3 71040 32 512 528 16
cert_test_block_3 71040 33 528 544 16
cert_test_block_3 71040 34 544 560 16
cert_test_block_3 71040 35 560 576 16
cert_test_block_3 71040 36 576 592 16
cert_test_block_3 71040 37 592 608 16
cert_test_block_3 71040 38 608 624 16
cert_test_block_3 71040 39 624 640 16
theorem test71040_complete : Interval test71040 0 640 :=
  (interval_append test71040 0 320 640
  (interval_append test71040 0 160 320
  (interval_append test71040 0 80 160
  (interval_append test71040 0 32 80
  (interval_append test71040 0 16 32
  test71040_block_0
  test71040_block_1)
  (interval_append test71040 32 48 80
  test71040_block_2
  (interval_append test71040 48 64 80
  test71040_block_3
  test71040_block_4)))
  (interval_append test71040 80 112 160
  (interval_append test71040 80 96 112
  test71040_block_5
  test71040_block_6)
  (interval_append test71040 112 128 160
  test71040_block_7
  (interval_append test71040 128 144 160
  test71040_block_8
  test71040_block_9))))
  (interval_append test71040 160 240 320
  (interval_append test71040 160 192 240
  (interval_append test71040 160 176 192
  test71040_block_10
  test71040_block_11)
  (interval_append test71040 192 208 240
  test71040_block_12
  (interval_append test71040 208 224 240
  test71040_block_13
  test71040_block_14)))
  (interval_append test71040 240 272 320
  (interval_append test71040 240 256 272
  test71040_block_15
  test71040_block_16)
  (interval_append test71040 272 288 320
  test71040_block_17
  (interval_append test71040 288 304 320
  test71040_block_18
  test71040_block_19)))))
  (interval_append test71040 320 480 640
  (interval_append test71040 320 400 480
  (interval_append test71040 320 352 400
  (interval_append test71040 320 336 352
  test71040_block_20
  test71040_block_21)
  (interval_append test71040 352 368 400
  test71040_block_22
  (interval_append test71040 368 384 400
  test71040_block_23
  test71040_block_24)))
  (interval_append test71040 400 432 480
  (interval_append test71040 400 416 432
  test71040_block_25
  test71040_block_26)
  (interval_append test71040 432 448 480
  test71040_block_27
  (interval_append test71040 448 464 480
  test71040_block_28
  test71040_block_29))))
  (interval_append test71040 480 560 640
  (interval_append test71040 480 512 560
  (interval_append test71040 480 496 512
  test71040_block_30
  test71040_block_31)
  (interval_append test71040 512 528 560
  test71040_block_32
  (interval_append test71040 528 544 560
  test71040_block_33
  test71040_block_34)))
  (interval_append test71040 560 592 640
  (interval_append test71040 560 576 592
  test71040_block_35
  test71040_block_36)
  (interval_append test71040 592 608 640
  test71040_block_37
  (interval_append test71040 608 624 640
  test71040_block_38
  test71040_block_39))))))
cert_nodeInterval_3 71040 71680
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
cert_test_11 71680
cert_test_block_3 71680 0 0 16 16
cert_test_block_3 71680 1 16 32 16
cert_test_block_3 71680 2 32 48 16
cert_test_block_3 71680 3 48 64 16
cert_test_block_3 71680 4 64 80 16
cert_test_block_3 71680 5 80 96 16
cert_test_block_3 71680 6 96 112 16
cert_test_block_3 71680 7 112 128 16
cert_test_block_3 71680 8 128 144 16
cert_test_block_3 71680 9 144 160 16
cert_test_block_3 71680 10 160 176 16
cert_test_block_3 71680 11 176 192 16
cert_test_block_3 71680 12 192 208 16
cert_test_block_3 71680 13 208 224 16
cert_test_block_3 71680 14 224 240 16
cert_test_block_3 71680 15 240 256 16
cert_test_block_3 71680 16 256 272 16
cert_test_block_3 71680 17 272 288 16
cert_test_block_3 71680 18 288 304 16
cert_test_block_3 71680 19 304 320 16
cert_test_block_3 71680 20 320 336 16
cert_test_block_3 71680 21 336 352 16
cert_test_block_3 71680 22 352 368 16
cert_test_block_3 71680 23 368 384 16
cert_test_block_3 71680 24 384 400 16
cert_test_block_3 71680 25 400 416 16
cert_test_block_3 71680 26 416 432 16
cert_test_block_3 71680 27 432 448 16
cert_test_block_3 71680 28 448 464 16
cert_test_block_3 71680 29 464 480 16
cert_test_block_3 71680 30 480 496 16
cert_test_block_3 71680 31 496 512 16
cert_test_block_3 71680 32 512 528 16
cert_test_block_3 71680 33 528 544 16
cert_test_block_3 71680 34 544 560 16
cert_test_block_3 71680 35 560 576 16
cert_test_block_3 71680 36 576 592 16
cert_test_block_3 71680 37 592 608 16
cert_test_block_3 71680 38 608 624 16
cert_test_block_3 71680 39 624 640 16
theorem test71680_complete : Interval test71680 0 640 :=
  (interval_append test71680 0 320 640
  (interval_append test71680 0 160 320
  (interval_append test71680 0 80 160
  (interval_append test71680 0 32 80
  (interval_append test71680 0 16 32
  test71680_block_0
  test71680_block_1)
  (interval_append test71680 32 48 80
  test71680_block_2
  (interval_append test71680 48 64 80
  test71680_block_3
  test71680_block_4)))
  (interval_append test71680 80 112 160
  (interval_append test71680 80 96 112
  test71680_block_5
  test71680_block_6)
  (interval_append test71680 112 128 160
  test71680_block_7
  (interval_append test71680 128 144 160
  test71680_block_8
  test71680_block_9))))
  (interval_append test71680 160 240 320
  (interval_append test71680 160 192 240
  (interval_append test71680 160 176 192
  test71680_block_10
  test71680_block_11)
  (interval_append test71680 192 208 240
  test71680_block_12
  (interval_append test71680 208 224 240
  test71680_block_13
  test71680_block_14)))
  (interval_append test71680 240 272 320
  (interval_append test71680 240 256 272
  test71680_block_15
  test71680_block_16)
  (interval_append test71680 272 288 320
  test71680_block_17
  (interval_append test71680 288 304 320
  test71680_block_18
  test71680_block_19)))))
  (interval_append test71680 320 480 640
  (interval_append test71680 320 400 480
  (interval_append test71680 320 352 400
  (interval_append test71680 320 336 352
  test71680_block_20
  test71680_block_21)
  (interval_append test71680 352 368 400
  test71680_block_22
  (interval_append test71680 368 384 400
  test71680_block_23
  test71680_block_24)))
  (interval_append test71680 400 432 480
  (interval_append test71680 400 416 432
  test71680_block_25
  test71680_block_26)
  (interval_append test71680 432 448 480
  test71680_block_27
  (interval_append test71680 448 464 480
  test71680_block_28
  test71680_block_29))))
  (interval_append test71680 480 560 640
  (interval_append test71680 480 512 560
  (interval_append test71680 480 496 512
  test71680_block_30
  test71680_block_31)
  (interval_append test71680 512 528 560
  test71680_block_32
  (interval_append test71680 528 544 560
  test71680_block_33
  test71680_block_34)))
  (interval_append test71680 560 592 640
  (interval_append test71680 560 576 592
  test71680_block_35
  test71680_block_36)
  (interval_append test71680 592 608 640
  test71680_block_37
  (interval_append test71680 608 624 640
  test71680_block_38
  test71680_block_39))))))
cert_nodeInterval_3 71680 72320
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
cert_test_11 72320
cert_test_block_3 72320 0 0 16 16
cert_test_block_3 72320 1 16 32 16
cert_test_block_3 72320 2 32 48 16
cert_test_block_3 72320 3 48 64 16
cert_test_block_3 72320 4 64 80 16
cert_test_block_3 72320 5 80 96 16
cert_test_block_3 72320 6 96 112 16
cert_test_block_3 72320 7 112 128 16
cert_test_block_3 72320 8 128 144 16
cert_test_block_3 72320 9 144 160 16
cert_test_block_3 72320 10 160 176 16
cert_test_block_3 72320 11 176 192 16
cert_test_block_3 72320 12 192 208 16
cert_test_block_3 72320 13 208 224 16
cert_test_block_3 72320 14 224 240 16
cert_test_block_3 72320 15 240 256 16
cert_test_block_3 72320 16 256 272 16
cert_test_block_3 72320 17 272 288 16
cert_test_block_3 72320 18 288 304 16
cert_test_block_3 72320 19 304 320 16
cert_test_block_3 72320 20 320 336 16
cert_test_block_3 72320 21 336 352 16
cert_test_block_3 72320 22 352 368 16
cert_test_block_3 72320 23 368 384 16
cert_test_block_3 72320 24 384 400 16
cert_test_block_3 72320 25 400 416 16
cert_test_block_3 72320 26 416 432 16
cert_test_block_3 72320 27 432 448 16
cert_test_block_3 72320 28 448 464 16
cert_test_block_3 72320 29 464 480 16
cert_test_block_3 72320 30 480 496 16
cert_test_block_3 72320 31 496 512 16
cert_test_block_3 72320 32 512 528 16
cert_test_block_3 72320 33 528 544 16
cert_test_block_3 72320 34 544 560 16
cert_test_block_3 72320 35 560 576 16
cert_test_block_3 72320 36 576 592 16
cert_test_block_3 72320 37 592 608 16
cert_test_block_3 72320 38 608 624 16
cert_test_block_3 72320 39 624 640 16
theorem test72320_complete : Interval test72320 0 640 :=
  (interval_append test72320 0 320 640
  (interval_append test72320 0 160 320
  (interval_append test72320 0 80 160
  (interval_append test72320 0 32 80
  (interval_append test72320 0 16 32
  test72320_block_0
  test72320_block_1)
  (interval_append test72320 32 48 80
  test72320_block_2
  (interval_append test72320 48 64 80
  test72320_block_3
  test72320_block_4)))
  (interval_append test72320 80 112 160
  (interval_append test72320 80 96 112
  test72320_block_5
  test72320_block_6)
  (interval_append test72320 112 128 160
  test72320_block_7
  (interval_append test72320 128 144 160
  test72320_block_8
  test72320_block_9))))
  (interval_append test72320 160 240 320
  (interval_append test72320 160 192 240
  (interval_append test72320 160 176 192
  test72320_block_10
  test72320_block_11)
  (interval_append test72320 192 208 240
  test72320_block_12
  (interval_append test72320 208 224 240
  test72320_block_13
  test72320_block_14)))
  (interval_append test72320 240 272 320
  (interval_append test72320 240 256 272
  test72320_block_15
  test72320_block_16)
  (interval_append test72320 272 288 320
  test72320_block_17
  (interval_append test72320 288 304 320
  test72320_block_18
  test72320_block_19)))))
  (interval_append test72320 320 480 640
  (interval_append test72320 320 400 480
  (interval_append test72320 320 352 400
  (interval_append test72320 320 336 352
  test72320_block_20
  test72320_block_21)
  (interval_append test72320 352 368 400
  test72320_block_22
  (interval_append test72320 368 384 400
  test72320_block_23
  test72320_block_24)))
  (interval_append test72320 400 432 480
  (interval_append test72320 400 416 432
  test72320_block_25
  test72320_block_26)
  (interval_append test72320 432 448 480
  test72320_block_27
  (interval_append test72320 448 464 480
  test72320_block_28
  test72320_block_29))))
  (interval_append test72320 480 560 640
  (interval_append test72320 480 512 560
  (interval_append test72320 480 496 512
  test72320_block_30
  test72320_block_31)
  (interval_append test72320 512 528 560
  test72320_block_32
  (interval_append test72320 528 544 560
  test72320_block_33
  test72320_block_34)))
  (interval_append test72320 560 592 640
  (interval_append test72320 560 576 592
  test72320_block_35
  test72320_block_36)
  (interval_append test72320 592 608 640
  test72320_block_37
  (interval_append test72320 608 624 640
  test72320_block_38
  test72320_block_39))))))
cert_nodeInterval_3 72320 72960
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
cert_test_11 72960
cert_test_block_3 72960 0 0 16 16
cert_test_block_3 72960 1 16 32 16
cert_test_block_3 72960 2 32 48 16
cert_test_block_3 72960 3 48 64 16
cert_test_block_3 72960 4 64 80 16
cert_test_block_3 72960 5 80 96 16
cert_test_block_3 72960 6 96 112 16
cert_test_block_3 72960 7 112 128 16
cert_test_block_3 72960 8 128 144 16
cert_test_block_3 72960 9 144 160 16
cert_test_block_3 72960 10 160 176 16
cert_test_block_3 72960 11 176 192 16
cert_test_block_3 72960 12 192 208 16
cert_test_block_3 72960 13 208 224 16
cert_test_block_3 72960 14 224 240 16
cert_test_block_3 72960 15 240 256 16
cert_test_block_3 72960 16 256 272 16
cert_test_block_3 72960 17 272 288 16
cert_test_block_3 72960 18 288 304 16
cert_test_block_3 72960 19 304 320 16
cert_test_block_3 72960 20 320 336 16
cert_test_block_3 72960 21 336 352 16
cert_test_block_3 72960 22 352 368 16
cert_test_block_3 72960 23 368 384 16
cert_test_block_3 72960 24 384 400 16
cert_test_block_3 72960 25 400 416 16
cert_test_block_3 72960 26 416 432 16
cert_test_block_3 72960 27 432 448 16
cert_test_block_3 72960 28 448 464 16
cert_test_block_3 72960 29 464 480 16
cert_test_block_3 72960 30 480 496 16
cert_test_block_3 72960 31 496 512 16
cert_test_block_3 72960 32 512 528 16
cert_test_block_3 72960 33 528 544 16
cert_test_block_3 72960 34 544 560 16
cert_test_block_3 72960 35 560 576 16
cert_test_block_3 72960 36 576 592 16
cert_test_block_3 72960 37 592 608 16
cert_test_block_3 72960 38 608 624 16
cert_test_block_3 72960 39 624 640 16
theorem test72960_complete : Interval test72960 0 640 :=
  (interval_append test72960 0 320 640
  (interval_append test72960 0 160 320
  (interval_append test72960 0 80 160
  (interval_append test72960 0 32 80
  (interval_append test72960 0 16 32
  test72960_block_0
  test72960_block_1)
  (interval_append test72960 32 48 80
  test72960_block_2
  (interval_append test72960 48 64 80
  test72960_block_3
  test72960_block_4)))
  (interval_append test72960 80 112 160
  (interval_append test72960 80 96 112
  test72960_block_5
  test72960_block_6)
  (interval_append test72960 112 128 160
  test72960_block_7
  (interval_append test72960 128 144 160
  test72960_block_8
  test72960_block_9))))
  (interval_append test72960 160 240 320
  (interval_append test72960 160 192 240
  (interval_append test72960 160 176 192
  test72960_block_10
  test72960_block_11)
  (interval_append test72960 192 208 240
  test72960_block_12
  (interval_append test72960 208 224 240
  test72960_block_13
  test72960_block_14)))
  (interval_append test72960 240 272 320
  (interval_append test72960 240 256 272
  test72960_block_15
  test72960_block_16)
  (interval_append test72960 272 288 320
  test72960_block_17
  (interval_append test72960 288 304 320
  test72960_block_18
  test72960_block_19)))))
  (interval_append test72960 320 480 640
  (interval_append test72960 320 400 480
  (interval_append test72960 320 352 400
  (interval_append test72960 320 336 352
  test72960_block_20
  test72960_block_21)
  (interval_append test72960 352 368 400
  test72960_block_22
  (interval_append test72960 368 384 400
  test72960_block_23
  test72960_block_24)))
  (interval_append test72960 400 432 480
  (interval_append test72960 400 416 432
  test72960_block_25
  test72960_block_26)
  (interval_append test72960 432 448 480
  test72960_block_27
  (interval_append test72960 448 464 480
  test72960_block_28
  test72960_block_29))))
  (interval_append test72960 480 560 640
  (interval_append test72960 480 512 560
  (interval_append test72960 480 496 512
  test72960_block_30
  test72960_block_31)
  (interval_append test72960 512 528 560
  test72960_block_32
  (interval_append test72960 528 544 560
  test72960_block_33
  test72960_block_34)))
  (interval_append test72960 560 592 640
  (interval_append test72960 560 576 592
  test72960_block_35
  test72960_block_36)
  (interval_append test72960 592 608 640
  test72960_block_37
  (interval_append test72960 608 624 640
  test72960_block_38
  test72960_block_39))))))
cert_nodeInterval_3 72960 73600
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
cert_test_11 73600
cert_test_block_3 73600 0 0 16 16
cert_test_block_3 73600 1 16 32 16
cert_test_block_3 73600 2 32 48 16
cert_test_block_3 73600 3 48 64 16
cert_test_block_3 73600 4 64 80 16
cert_test_block_3 73600 5 80 96 16
cert_test_block_3 73600 6 96 112 16
cert_test_block_3 73600 7 112 128 16
cert_test_block_3 73600 8 128 144 16
cert_test_block_3 73600 9 144 160 16
cert_test_block_3 73600 10 160 176 16
cert_test_block_3 73600 11 176 192 16
cert_test_block_3 73600 12 192 208 16
cert_test_block_3 73600 13 208 224 16
cert_test_block_3 73600 14 224 240 16
cert_test_block_3 73600 15 240 256 16
cert_test_block_3 73600 16 256 272 16
cert_test_block_3 73600 17 272 288 16
cert_test_block_3 73600 18 288 304 16
cert_test_block_3 73600 19 304 320 16
cert_test_block_3 73600 20 320 336 16
cert_test_block_3 73600 21 336 352 16
cert_test_block_3 73600 22 352 368 16
cert_test_block_3 73600 23 368 384 16
cert_test_block_3 73600 24 384 400 16
cert_test_block_3 73600 25 400 416 16
cert_test_block_3 73600 26 416 432 16
cert_test_block_3 73600 27 432 448 16
cert_test_block_3 73600 28 448 464 16
cert_test_block_3 73600 29 464 480 16
cert_test_block_3 73600 30 480 496 16
cert_test_block_3 73600 31 496 512 16
cert_test_block_3 73600 32 512 528 16
cert_test_block_3 73600 33 528 544 16
cert_test_block_3 73600 34 544 560 16
cert_test_block_3 73600 35 560 576 16
cert_test_block_3 73600 36 576 592 16
cert_test_block_3 73600 37 592 608 16
cert_test_block_3 73600 38 608 624 16
cert_test_block_3 73600 39 624 640 16
theorem test73600_complete : Interval test73600 0 640 :=
  (interval_append test73600 0 320 640
  (interval_append test73600 0 160 320
  (interval_append test73600 0 80 160
  (interval_append test73600 0 32 80
  (interval_append test73600 0 16 32
  test73600_block_0
  test73600_block_1)
  (interval_append test73600 32 48 80
  test73600_block_2
  (interval_append test73600 48 64 80
  test73600_block_3
  test73600_block_4)))
  (interval_append test73600 80 112 160
  (interval_append test73600 80 96 112
  test73600_block_5
  test73600_block_6)
  (interval_append test73600 112 128 160
  test73600_block_7
  (interval_append test73600 128 144 160
  test73600_block_8
  test73600_block_9))))
  (interval_append test73600 160 240 320
  (interval_append test73600 160 192 240
  (interval_append test73600 160 176 192
  test73600_block_10
  test73600_block_11)
  (interval_append test73600 192 208 240
  test73600_block_12
  (interval_append test73600 208 224 240
  test73600_block_13
  test73600_block_14)))
  (interval_append test73600 240 272 320
  (interval_append test73600 240 256 272
  test73600_block_15
  test73600_block_16)
  (interval_append test73600 272 288 320
  test73600_block_17
  (interval_append test73600 288 304 320
  test73600_block_18
  test73600_block_19)))))
  (interval_append test73600 320 480 640
  (interval_append test73600 320 400 480
  (interval_append test73600 320 352 400
  (interval_append test73600 320 336 352
  test73600_block_20
  test73600_block_21)
  (interval_append test73600 352 368 400
  test73600_block_22
  (interval_append test73600 368 384 400
  test73600_block_23
  test73600_block_24)))
  (interval_append test73600 400 432 480
  (interval_append test73600 400 416 432
  test73600_block_25
  test73600_block_26)
  (interval_append test73600 432 448 480
  test73600_block_27
  (interval_append test73600 448 464 480
  test73600_block_28
  test73600_block_29))))
  (interval_append test73600 480 560 640
  (interval_append test73600 480 512 560
  (interval_append test73600 480 496 512
  test73600_block_30
  test73600_block_31)
  (interval_append test73600 512 528 560
  test73600_block_32
  (interval_append test73600 528 544 560
  test73600_block_33
  test73600_block_34)))
  (interval_append test73600 560 592 640
  (interval_append test73600 560 576 592
  test73600_block_35
  test73600_block_36)
  (interval_append test73600 592 608 640
  test73600_block_37
  (interval_append test73600 608 624 640
  test73600_block_38
  test73600_block_39))))))
cert_nodeInterval_3 73600 74240
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
cert_test_11 74240
cert_test_block_3 74240 0 0 16 16
cert_test_block_3 74240 1 16 32 16
cert_test_block_3 74240 2 32 48 16
cert_test_block_3 74240 3 48 64 16
cert_test_block_3 74240 4 64 80 16
cert_test_block_3 74240 5 80 96 16
cert_test_block_3 74240 6 96 112 16
cert_test_block_3 74240 7 112 128 16
cert_test_block_3 74240 8 128 144 16
cert_test_block_3 74240 9 144 160 16
cert_test_block_3 74240 10 160 176 16
cert_test_block_3 74240 11 176 192 16
cert_test_block_3 74240 12 192 208 16
cert_test_block_3 74240 13 208 224 16
cert_test_block_3 74240 14 224 240 16
cert_test_block_3 74240 15 240 256 16
cert_test_block_3 74240 16 256 272 16
cert_test_block_3 74240 17 272 288 16
cert_test_block_3 74240 18 288 304 16
cert_test_block_3 74240 19 304 320 16
cert_test_block_3 74240 20 320 336 16
cert_test_block_3 74240 21 336 352 16
cert_test_block_3 74240 22 352 368 16
cert_test_block_3 74240 23 368 384 16
cert_test_block_3 74240 24 384 400 16
cert_test_block_3 74240 25 400 416 16
cert_test_block_3 74240 26 416 432 16
cert_test_block_3 74240 27 432 448 16
cert_test_block_3 74240 28 448 464 16
cert_test_block_3 74240 29 464 480 16
cert_test_block_3 74240 30 480 496 16
cert_test_block_3 74240 31 496 512 16
cert_test_block_3 74240 32 512 528 16
cert_test_block_3 74240 33 528 544 16
cert_test_block_3 74240 34 544 560 16
cert_test_block_3 74240 35 560 576 16
cert_test_block_3 74240 36 576 592 16
cert_test_block_3 74240 37 592 608 16
cert_test_block_3 74240 38 608 624 16
cert_test_block_3 74240 39 624 640 16
theorem test74240_complete : Interval test74240 0 640 :=
  (interval_append test74240 0 320 640
  (interval_append test74240 0 160 320
  (interval_append test74240 0 80 160
  (interval_append test74240 0 32 80
  (interval_append test74240 0 16 32
  test74240_block_0
  test74240_block_1)
  (interval_append test74240 32 48 80
  test74240_block_2
  (interval_append test74240 48 64 80
  test74240_block_3
  test74240_block_4)))
  (interval_append test74240 80 112 160
  (interval_append test74240 80 96 112
  test74240_block_5
  test74240_block_6)
  (interval_append test74240 112 128 160
  test74240_block_7
  (interval_append test74240 128 144 160
  test74240_block_8
  test74240_block_9))))
  (interval_append test74240 160 240 320
  (interval_append test74240 160 192 240
  (interval_append test74240 160 176 192
  test74240_block_10
  test74240_block_11)
  (interval_append test74240 192 208 240
  test74240_block_12
  (interval_append test74240 208 224 240
  test74240_block_13
  test74240_block_14)))
  (interval_append test74240 240 272 320
  (interval_append test74240 240 256 272
  test74240_block_15
  test74240_block_16)
  (interval_append test74240 272 288 320
  test74240_block_17
  (interval_append test74240 288 304 320
  test74240_block_18
  test74240_block_19)))))
  (interval_append test74240 320 480 640
  (interval_append test74240 320 400 480
  (interval_append test74240 320 352 400
  (interval_append test74240 320 336 352
  test74240_block_20
  test74240_block_21)
  (interval_append test74240 352 368 400
  test74240_block_22
  (interval_append test74240 368 384 400
  test74240_block_23
  test74240_block_24)))
  (interval_append test74240 400 432 480
  (interval_append test74240 400 416 432
  test74240_block_25
  test74240_block_26)
  (interval_append test74240 432 448 480
  test74240_block_27
  (interval_append test74240 448 464 480
  test74240_block_28
  test74240_block_29))))
  (interval_append test74240 480 560 640
  (interval_append test74240 480 512 560
  (interval_append test74240 480 496 512
  test74240_block_30
  test74240_block_31)
  (interval_append test74240 512 528 560
  test74240_block_32
  (interval_append test74240 528 544 560
  test74240_block_33
  test74240_block_34)))
  (interval_append test74240 560 592 640
  (interval_append test74240 560 576 592
  test74240_block_35
  test74240_block_36)
  (interval_append test74240 592 608 640
  test74240_block_37
  (interval_append test74240 608 624 640
  test74240_block_38
  test74240_block_39))))))
cert_nodeInterval_3 74240 74880
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
cert_test_11 74880
cert_test_block_3 74880 0 0 16 16
cert_test_block_3 74880 1 16 32 16
cert_test_block_3 74880 2 32 48 16
cert_test_block_3 74880 3 48 64 16
cert_test_block_3 74880 4 64 80 16
cert_test_block_3 74880 5 80 96 16
cert_test_block_3 74880 6 96 112 16
cert_test_block_3 74880 7 112 128 16
cert_test_block_3 74880 8 128 144 16
cert_test_block_3 74880 9 144 160 16
cert_test_block_3 74880 10 160 176 16
cert_test_block_3 74880 11 176 192 16
cert_test_block_3 74880 12 192 208 16
cert_test_block_3 74880 13 208 224 16
cert_test_block_3 74880 14 224 240 16
cert_test_block_3 74880 15 240 256 16
cert_test_block_3 74880 16 256 272 16
cert_test_block_3 74880 17 272 288 16
cert_test_block_3 74880 18 288 304 16
cert_test_block_3 74880 19 304 320 16
cert_test_block_3 74880 20 320 336 16
cert_test_block_3 74880 21 336 352 16
cert_test_block_3 74880 22 352 368 16
cert_test_block_3 74880 23 368 384 16
cert_test_block_3 74880 24 384 400 16
cert_test_block_3 74880 25 400 416 16
cert_test_block_3 74880 26 416 432 16
cert_test_block_3 74880 27 432 448 16
cert_test_block_3 74880 28 448 464 16
cert_test_block_3 74880 29 464 480 16
cert_test_block_3 74880 30 480 496 16
cert_test_block_3 74880 31 496 512 16
cert_test_block_3 74880 32 512 528 16
cert_test_block_3 74880 33 528 544 16
cert_test_block_3 74880 34 544 560 16
cert_test_block_3 74880 35 560 576 16
cert_test_block_3 74880 36 576 592 16
cert_test_block_3 74880 37 592 608 16
cert_test_block_3 74880 38 608 624 16
cert_test_block_3 74880 39 624 640 16
theorem test74880_complete : Interval test74880 0 640 :=
  (interval_append test74880 0 320 640
  (interval_append test74880 0 160 320
  (interval_append test74880 0 80 160
  (interval_append test74880 0 32 80
  (interval_append test74880 0 16 32
  test74880_block_0
  test74880_block_1)
  (interval_append test74880 32 48 80
  test74880_block_2
  (interval_append test74880 48 64 80
  test74880_block_3
  test74880_block_4)))
  (interval_append test74880 80 112 160
  (interval_append test74880 80 96 112
  test74880_block_5
  test74880_block_6)
  (interval_append test74880 112 128 160
  test74880_block_7
  (interval_append test74880 128 144 160
  test74880_block_8
  test74880_block_9))))
  (interval_append test74880 160 240 320
  (interval_append test74880 160 192 240
  (interval_append test74880 160 176 192
  test74880_block_10
  test74880_block_11)
  (interval_append test74880 192 208 240
  test74880_block_12
  (interval_append test74880 208 224 240
  test74880_block_13
  test74880_block_14)))
  (interval_append test74880 240 272 320
  (interval_append test74880 240 256 272
  test74880_block_15
  test74880_block_16)
  (interval_append test74880 272 288 320
  test74880_block_17
  (interval_append test74880 288 304 320
  test74880_block_18
  test74880_block_19)))))
  (interval_append test74880 320 480 640
  (interval_append test74880 320 400 480
  (interval_append test74880 320 352 400
  (interval_append test74880 320 336 352
  test74880_block_20
  test74880_block_21)
  (interval_append test74880 352 368 400
  test74880_block_22
  (interval_append test74880 368 384 400
  test74880_block_23
  test74880_block_24)))
  (interval_append test74880 400 432 480
  (interval_append test74880 400 416 432
  test74880_block_25
  test74880_block_26)
  (interval_append test74880 432 448 480
  test74880_block_27
  (interval_append test74880 448 464 480
  test74880_block_28
  test74880_block_29))))
  (interval_append test74880 480 560 640
  (interval_append test74880 480 512 560
  (interval_append test74880 480 496 512
  test74880_block_30
  test74880_block_31)
  (interval_append test74880 512 528 560
  test74880_block_32
  (interval_append test74880 528 544 560
  test74880_block_33
  test74880_block_34)))
  (interval_append test74880 560 592 640
  (interval_append test74880 560 576 592
  test74880_block_35
  test74880_block_36)
  (interval_append test74880 592 608 640
  test74880_block_37
  (interval_append test74880 608 624 640
  test74880_block_38
  test74880_block_39))))))
cert_nodeInterval_3 74880 75520
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
cert_test_11 75520
cert_test_block_3 75520 0 0 16 16
cert_test_block_3 75520 1 16 32 16
cert_test_block_3 75520 2 32 48 16
cert_test_block_3 75520 3 48 64 16
cert_test_block_3 75520 4 64 80 16
cert_test_block_3 75520 5 80 96 16
cert_test_block_3 75520 6 96 112 16
cert_test_block_3 75520 7 112 128 16
cert_test_block_3 75520 8 128 144 16
cert_test_block_3 75520 9 144 160 16
cert_test_block_3 75520 10 160 176 16
cert_test_block_3 75520 11 176 192 16
cert_test_block_3 75520 12 192 208 16
cert_test_block_3 75520 13 208 224 16
cert_test_block_3 75520 14 224 240 16
cert_test_block_3 75520 15 240 256 16
cert_test_block_3 75520 16 256 272 16
cert_test_block_3 75520 17 272 288 16
cert_test_block_3 75520 18 288 304 16
cert_test_block_3 75520 19 304 320 16
cert_test_block_3 75520 20 320 336 16
cert_test_block_3 75520 21 336 352 16
cert_test_block_3 75520 22 352 368 16
cert_test_block_3 75520 23 368 384 16
cert_test_block_3 75520 24 384 400 16
cert_test_block_3 75520 25 400 416 16
cert_test_block_3 75520 26 416 432 16
cert_test_block_3 75520 27 432 448 16
cert_test_block_3 75520 28 448 464 16
cert_test_block_3 75520 29 464 480 16
cert_test_block_3 75520 30 480 496 16
cert_test_block_3 75520 31 496 512 16
cert_test_block_3 75520 32 512 528 16
cert_test_block_3 75520 33 528 544 16
cert_test_block_3 75520 34 544 560 16
cert_test_block_3 75520 35 560 576 16
cert_test_block_3 75520 36 576 592 16
cert_test_block_3 75520 37 592 608 16
cert_test_block_3 75520 38 608 624 16
cert_test_block_3 75520 39 624 640 16
theorem test75520_complete : Interval test75520 0 640 :=
  (interval_append test75520 0 320 640
  (interval_append test75520 0 160 320
  (interval_append test75520 0 80 160
  (interval_append test75520 0 32 80
  (interval_append test75520 0 16 32
  test75520_block_0
  test75520_block_1)
  (interval_append test75520 32 48 80
  test75520_block_2
  (interval_append test75520 48 64 80
  test75520_block_3
  test75520_block_4)))
  (interval_append test75520 80 112 160
  (interval_append test75520 80 96 112
  test75520_block_5
  test75520_block_6)
  (interval_append test75520 112 128 160
  test75520_block_7
  (interval_append test75520 128 144 160
  test75520_block_8
  test75520_block_9))))
  (interval_append test75520 160 240 320
  (interval_append test75520 160 192 240
  (interval_append test75520 160 176 192
  test75520_block_10
  test75520_block_11)
  (interval_append test75520 192 208 240
  test75520_block_12
  (interval_append test75520 208 224 240
  test75520_block_13
  test75520_block_14)))
  (interval_append test75520 240 272 320
  (interval_append test75520 240 256 272
  test75520_block_15
  test75520_block_16)
  (interval_append test75520 272 288 320
  test75520_block_17
  (interval_append test75520 288 304 320
  test75520_block_18
  test75520_block_19)))))
  (interval_append test75520 320 480 640
  (interval_append test75520 320 400 480
  (interval_append test75520 320 352 400
  (interval_append test75520 320 336 352
  test75520_block_20
  test75520_block_21)
  (interval_append test75520 352 368 400
  test75520_block_22
  (interval_append test75520 368 384 400
  test75520_block_23
  test75520_block_24)))
  (interval_append test75520 400 432 480
  (interval_append test75520 400 416 432
  test75520_block_25
  test75520_block_26)
  (interval_append test75520 432 448 480
  test75520_block_27
  (interval_append test75520 448 464 480
  test75520_block_28
  test75520_block_29))))
  (interval_append test75520 480 560 640
  (interval_append test75520 480 512 560
  (interval_append test75520 480 496 512
  test75520_block_30
  test75520_block_31)
  (interval_append test75520 512 528 560
  test75520_block_32
  (interval_append test75520 528 544 560
  test75520_block_33
  test75520_block_34)))
  (interval_append test75520 560 592 640
  (interval_append test75520 560 576 592
  test75520_block_35
  test75520_block_36)
  (interval_append test75520 592 608 640
  test75520_block_37
  (interval_append test75520 608 624 640
  test75520_block_38
  test75520_block_39))))))
cert_nodeInterval_3 75520 76160
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
cert_test_11 76160
cert_test_block_3 76160 0 0 16 16
cert_test_block_3 76160 1 16 32 16
cert_test_block_3 76160 2 32 48 16
cert_test_block_3 76160 3 48 64 16
cert_test_block_3 76160 4 64 80 16
cert_test_block_3 76160 5 80 96 16
cert_test_block_3 76160 6 96 112 16
cert_test_block_3 76160 7 112 128 16
cert_test_block_3 76160 8 128 144 16
cert_test_block_3 76160 9 144 160 16
cert_test_block_3 76160 10 160 176 16
cert_test_block_3 76160 11 176 192 16
cert_test_block_3 76160 12 192 208 16
cert_test_block_3 76160 13 208 224 16
cert_test_block_3 76160 14 224 240 16
cert_test_block_3 76160 15 240 256 16
cert_test_block_3 76160 16 256 272 16
cert_test_block_3 76160 17 272 288 16
cert_test_block_3 76160 18 288 304 16
cert_test_block_3 76160 19 304 320 16
cert_test_block_3 76160 20 320 336 16
cert_test_block_3 76160 21 336 352 16
cert_test_block_3 76160 22 352 368 16
cert_test_block_3 76160 23 368 384 16
cert_test_block_3 76160 24 384 400 16
cert_test_block_3 76160 25 400 416 16
cert_test_block_3 76160 26 416 432 16
cert_test_block_3 76160 27 432 448 16
cert_test_block_3 76160 28 448 464 16
cert_test_block_3 76160 29 464 480 16
cert_test_block_3 76160 30 480 496 16
cert_test_block_3 76160 31 496 512 16
cert_test_block_3 76160 32 512 528 16
cert_test_block_3 76160 33 528 544 16
cert_test_block_3 76160 34 544 560 16
cert_test_block_3 76160 35 560 576 16
cert_test_block_3 76160 36 576 592 16
cert_test_block_3 76160 37 592 608 16
cert_test_block_3 76160 38 608 624 16
cert_test_block_3 76160 39 624 640 16
theorem test76160_complete : Interval test76160 0 640 :=
  (interval_append test76160 0 320 640
  (interval_append test76160 0 160 320
  (interval_append test76160 0 80 160
  (interval_append test76160 0 32 80
  (interval_append test76160 0 16 32
  test76160_block_0
  test76160_block_1)
  (interval_append test76160 32 48 80
  test76160_block_2
  (interval_append test76160 48 64 80
  test76160_block_3
  test76160_block_4)))
  (interval_append test76160 80 112 160
  (interval_append test76160 80 96 112
  test76160_block_5
  test76160_block_6)
  (interval_append test76160 112 128 160
  test76160_block_7
  (interval_append test76160 128 144 160
  test76160_block_8
  test76160_block_9))))
  (interval_append test76160 160 240 320
  (interval_append test76160 160 192 240
  (interval_append test76160 160 176 192
  test76160_block_10
  test76160_block_11)
  (interval_append test76160 192 208 240
  test76160_block_12
  (interval_append test76160 208 224 240
  test76160_block_13
  test76160_block_14)))
  (interval_append test76160 240 272 320
  (interval_append test76160 240 256 272
  test76160_block_15
  test76160_block_16)
  (interval_append test76160 272 288 320
  test76160_block_17
  (interval_append test76160 288 304 320
  test76160_block_18
  test76160_block_19)))))
  (interval_append test76160 320 480 640
  (interval_append test76160 320 400 480
  (interval_append test76160 320 352 400
  (interval_append test76160 320 336 352
  test76160_block_20
  test76160_block_21)
  (interval_append test76160 352 368 400
  test76160_block_22
  (interval_append test76160 368 384 400
  test76160_block_23
  test76160_block_24)))
  (interval_append test76160 400 432 480
  (interval_append test76160 400 416 432
  test76160_block_25
  test76160_block_26)
  (interval_append test76160 432 448 480
  test76160_block_27
  (interval_append test76160 448 464 480
  test76160_block_28
  test76160_block_29))))
  (interval_append test76160 480 560 640
  (interval_append test76160 480 512 560
  (interval_append test76160 480 496 512
  test76160_block_30
  test76160_block_31)
  (interval_append test76160 512 528 560
  test76160_block_32
  (interval_append test76160 528 544 560
  test76160_block_33
  test76160_block_34)))
  (interval_append test76160 560 592 640
  (interval_append test76160 560 576 592
  test76160_block_35
  test76160_block_36)
  (interval_append test76160 592 608 640
  test76160_block_37
  (interval_append test76160 608 624 640
  test76160_block_38
  test76160_block_39))))))
cert_nodeInterval_3 76160 76800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
