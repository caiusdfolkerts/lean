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
cert_test_11 53760
cert_test_block_3 53760 0 0 16 16
cert_test_block_3 53760 1 16 32 16
cert_test_block_3 53760 2 32 48 16
cert_test_block_3 53760 3 48 64 16
cert_test_block_3 53760 4 64 80 16
cert_test_block_3 53760 5 80 96 16
cert_test_block_3 53760 6 96 112 16
cert_test_block_3 53760 7 112 128 16
cert_test_block_3 53760 8 128 144 16
cert_test_block_3 53760 9 144 160 16
cert_test_block_3 53760 10 160 176 16
cert_test_block_3 53760 11 176 192 16
cert_test_block_3 53760 12 192 208 16
cert_test_block_3 53760 13 208 224 16
cert_test_block_3 53760 14 224 240 16
cert_test_block_3 53760 15 240 256 16
cert_test_block_3 53760 16 256 272 16
cert_test_block_3 53760 17 272 288 16
cert_test_block_3 53760 18 288 304 16
cert_test_block_3 53760 19 304 320 16
cert_test_block_3 53760 20 320 336 16
cert_test_block_3 53760 21 336 352 16
cert_test_block_3 53760 22 352 368 16
cert_test_block_3 53760 23 368 384 16
cert_test_block_3 53760 24 384 400 16
cert_test_block_3 53760 25 400 416 16
cert_test_block_3 53760 26 416 432 16
cert_test_block_3 53760 27 432 448 16
cert_test_block_3 53760 28 448 464 16
cert_test_block_3 53760 29 464 480 16
cert_test_block_3 53760 30 480 496 16
cert_test_block_3 53760 31 496 512 16
cert_test_block_3 53760 32 512 528 16
cert_test_block_3 53760 33 528 544 16
cert_test_block_3 53760 34 544 560 16
cert_test_block_3 53760 35 560 576 16
cert_test_block_3 53760 36 576 592 16
cert_test_block_3 53760 37 592 608 16
cert_test_block_3 53760 38 608 624 16
cert_test_block_3 53760 39 624 640 16
theorem test53760_complete : Interval test53760 0 640 :=
  (interval_append test53760 0 320 640
  (interval_append test53760 0 160 320
  (interval_append test53760 0 80 160
  (interval_append test53760 0 32 80
  (interval_append test53760 0 16 32
  test53760_block_0
  test53760_block_1)
  (interval_append test53760 32 48 80
  test53760_block_2
  (interval_append test53760 48 64 80
  test53760_block_3
  test53760_block_4)))
  (interval_append test53760 80 112 160
  (interval_append test53760 80 96 112
  test53760_block_5
  test53760_block_6)
  (interval_append test53760 112 128 160
  test53760_block_7
  (interval_append test53760 128 144 160
  test53760_block_8
  test53760_block_9))))
  (interval_append test53760 160 240 320
  (interval_append test53760 160 192 240
  (interval_append test53760 160 176 192
  test53760_block_10
  test53760_block_11)
  (interval_append test53760 192 208 240
  test53760_block_12
  (interval_append test53760 208 224 240
  test53760_block_13
  test53760_block_14)))
  (interval_append test53760 240 272 320
  (interval_append test53760 240 256 272
  test53760_block_15
  test53760_block_16)
  (interval_append test53760 272 288 320
  test53760_block_17
  (interval_append test53760 288 304 320
  test53760_block_18
  test53760_block_19)))))
  (interval_append test53760 320 480 640
  (interval_append test53760 320 400 480
  (interval_append test53760 320 352 400
  (interval_append test53760 320 336 352
  test53760_block_20
  test53760_block_21)
  (interval_append test53760 352 368 400
  test53760_block_22
  (interval_append test53760 368 384 400
  test53760_block_23
  test53760_block_24)))
  (interval_append test53760 400 432 480
  (interval_append test53760 400 416 432
  test53760_block_25
  test53760_block_26)
  (interval_append test53760 432 448 480
  test53760_block_27
  (interval_append test53760 448 464 480
  test53760_block_28
  test53760_block_29))))
  (interval_append test53760 480 560 640
  (interval_append test53760 480 512 560
  (interval_append test53760 480 496 512
  test53760_block_30
  test53760_block_31)
  (interval_append test53760 512 528 560
  test53760_block_32
  (interval_append test53760 528 544 560
  test53760_block_33
  test53760_block_34)))
  (interval_append test53760 560 592 640
  (interval_append test53760 560 576 592
  test53760_block_35
  test53760_block_36)
  (interval_append test53760 592 608 640
  test53760_block_37
  (interval_append test53760 608 624 640
  test53760_block_38
  test53760_block_39))))))
cert_nodeInterval_3 53760 54400
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
cert_test_11 54400
cert_test_block_3 54400 0 0 16 16
cert_test_block_3 54400 1 16 32 16
cert_test_block_3 54400 2 32 48 16
cert_test_block_3 54400 3 48 64 16
cert_test_block_3 54400 4 64 80 16
cert_test_block_3 54400 5 80 96 16
cert_test_block_3 54400 6 96 112 16
cert_test_block_3 54400 7 112 128 16
cert_test_block_3 54400 8 128 144 16
cert_test_block_3 54400 9 144 160 16
cert_test_block_3 54400 10 160 176 16
cert_test_block_3 54400 11 176 192 16
cert_test_block_3 54400 12 192 208 16
cert_test_block_3 54400 13 208 224 16
cert_test_block_3 54400 14 224 240 16
cert_test_block_3 54400 15 240 256 16
cert_test_block_3 54400 16 256 272 16
cert_test_block_3 54400 17 272 288 16
cert_test_block_3 54400 18 288 304 16
cert_test_block_3 54400 19 304 320 16
cert_test_block_3 54400 20 320 336 16
cert_test_block_3 54400 21 336 352 16
cert_test_block_3 54400 22 352 368 16
cert_test_block_3 54400 23 368 384 16
cert_test_block_3 54400 24 384 400 16
cert_test_block_3 54400 25 400 416 16
cert_test_block_3 54400 26 416 432 16
cert_test_block_3 54400 27 432 448 16
cert_test_block_3 54400 28 448 464 16
cert_test_block_3 54400 29 464 480 16
cert_test_block_3 54400 30 480 496 16
cert_test_block_3 54400 31 496 512 16
cert_test_block_3 54400 32 512 528 16
cert_test_block_3 54400 33 528 544 16
cert_test_block_3 54400 34 544 560 16
cert_test_block_3 54400 35 560 576 16
cert_test_block_3 54400 36 576 592 16
cert_test_block_3 54400 37 592 608 16
cert_test_block_3 54400 38 608 624 16
cert_test_block_3 54400 39 624 640 16
theorem test54400_complete : Interval test54400 0 640 :=
  (interval_append test54400 0 320 640
  (interval_append test54400 0 160 320
  (interval_append test54400 0 80 160
  (interval_append test54400 0 32 80
  (interval_append test54400 0 16 32
  test54400_block_0
  test54400_block_1)
  (interval_append test54400 32 48 80
  test54400_block_2
  (interval_append test54400 48 64 80
  test54400_block_3
  test54400_block_4)))
  (interval_append test54400 80 112 160
  (interval_append test54400 80 96 112
  test54400_block_5
  test54400_block_6)
  (interval_append test54400 112 128 160
  test54400_block_7
  (interval_append test54400 128 144 160
  test54400_block_8
  test54400_block_9))))
  (interval_append test54400 160 240 320
  (interval_append test54400 160 192 240
  (interval_append test54400 160 176 192
  test54400_block_10
  test54400_block_11)
  (interval_append test54400 192 208 240
  test54400_block_12
  (interval_append test54400 208 224 240
  test54400_block_13
  test54400_block_14)))
  (interval_append test54400 240 272 320
  (interval_append test54400 240 256 272
  test54400_block_15
  test54400_block_16)
  (interval_append test54400 272 288 320
  test54400_block_17
  (interval_append test54400 288 304 320
  test54400_block_18
  test54400_block_19)))))
  (interval_append test54400 320 480 640
  (interval_append test54400 320 400 480
  (interval_append test54400 320 352 400
  (interval_append test54400 320 336 352
  test54400_block_20
  test54400_block_21)
  (interval_append test54400 352 368 400
  test54400_block_22
  (interval_append test54400 368 384 400
  test54400_block_23
  test54400_block_24)))
  (interval_append test54400 400 432 480
  (interval_append test54400 400 416 432
  test54400_block_25
  test54400_block_26)
  (interval_append test54400 432 448 480
  test54400_block_27
  (interval_append test54400 448 464 480
  test54400_block_28
  test54400_block_29))))
  (interval_append test54400 480 560 640
  (interval_append test54400 480 512 560
  (interval_append test54400 480 496 512
  test54400_block_30
  test54400_block_31)
  (interval_append test54400 512 528 560
  test54400_block_32
  (interval_append test54400 528 544 560
  test54400_block_33
  test54400_block_34)))
  (interval_append test54400 560 592 640
  (interval_append test54400 560 576 592
  test54400_block_35
  test54400_block_36)
  (interval_append test54400 592 608 640
  test54400_block_37
  (interval_append test54400 608 624 640
  test54400_block_38
  test54400_block_39))))))
cert_nodeInterval_3 54400 55040
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
cert_test_11 55040
cert_test_block_3 55040 0 0 16 16
cert_test_block_3 55040 1 16 32 16
cert_test_block_3 55040 2 32 48 16
cert_test_block_3 55040 3 48 64 16
cert_test_block_3 55040 4 64 80 16
cert_test_block_3 55040 5 80 96 16
cert_test_block_3 55040 6 96 112 16
cert_test_block_3 55040 7 112 128 16
cert_test_block_3 55040 8 128 144 16
cert_test_block_3 55040 9 144 160 16
cert_test_block_3 55040 10 160 176 16
cert_test_block_3 55040 11 176 192 16
cert_test_block_3 55040 12 192 208 16
cert_test_block_3 55040 13 208 224 16
cert_test_block_3 55040 14 224 240 16
cert_test_block_3 55040 15 240 256 16
cert_test_block_3 55040 16 256 272 16
cert_test_block_3 55040 17 272 288 16
cert_test_block_3 55040 18 288 304 16
cert_test_block_3 55040 19 304 320 16
cert_test_block_3 55040 20 320 336 16
cert_test_block_3 55040 21 336 352 16
cert_test_block_3 55040 22 352 368 16
cert_test_block_3 55040 23 368 384 16
cert_test_block_3 55040 24 384 400 16
cert_test_block_3 55040 25 400 416 16
cert_test_block_3 55040 26 416 432 16
cert_test_block_3 55040 27 432 448 16
cert_test_block_3 55040 28 448 464 16
cert_test_block_3 55040 29 464 480 16
cert_test_block_3 55040 30 480 496 16
cert_test_block_3 55040 31 496 512 16
cert_test_block_3 55040 32 512 528 16
cert_test_block_3 55040 33 528 544 16
cert_test_block_3 55040 34 544 560 16
cert_test_block_3 55040 35 560 576 16
cert_test_block_3 55040 36 576 592 16
cert_test_block_3 55040 37 592 608 16
cert_test_block_3 55040 38 608 624 16
cert_test_block_3 55040 39 624 640 16
theorem test55040_complete : Interval test55040 0 640 :=
  (interval_append test55040 0 320 640
  (interval_append test55040 0 160 320
  (interval_append test55040 0 80 160
  (interval_append test55040 0 32 80
  (interval_append test55040 0 16 32
  test55040_block_0
  test55040_block_1)
  (interval_append test55040 32 48 80
  test55040_block_2
  (interval_append test55040 48 64 80
  test55040_block_3
  test55040_block_4)))
  (interval_append test55040 80 112 160
  (interval_append test55040 80 96 112
  test55040_block_5
  test55040_block_6)
  (interval_append test55040 112 128 160
  test55040_block_7
  (interval_append test55040 128 144 160
  test55040_block_8
  test55040_block_9))))
  (interval_append test55040 160 240 320
  (interval_append test55040 160 192 240
  (interval_append test55040 160 176 192
  test55040_block_10
  test55040_block_11)
  (interval_append test55040 192 208 240
  test55040_block_12
  (interval_append test55040 208 224 240
  test55040_block_13
  test55040_block_14)))
  (interval_append test55040 240 272 320
  (interval_append test55040 240 256 272
  test55040_block_15
  test55040_block_16)
  (interval_append test55040 272 288 320
  test55040_block_17
  (interval_append test55040 288 304 320
  test55040_block_18
  test55040_block_19)))))
  (interval_append test55040 320 480 640
  (interval_append test55040 320 400 480
  (interval_append test55040 320 352 400
  (interval_append test55040 320 336 352
  test55040_block_20
  test55040_block_21)
  (interval_append test55040 352 368 400
  test55040_block_22
  (interval_append test55040 368 384 400
  test55040_block_23
  test55040_block_24)))
  (interval_append test55040 400 432 480
  (interval_append test55040 400 416 432
  test55040_block_25
  test55040_block_26)
  (interval_append test55040 432 448 480
  test55040_block_27
  (interval_append test55040 448 464 480
  test55040_block_28
  test55040_block_29))))
  (interval_append test55040 480 560 640
  (interval_append test55040 480 512 560
  (interval_append test55040 480 496 512
  test55040_block_30
  test55040_block_31)
  (interval_append test55040 512 528 560
  test55040_block_32
  (interval_append test55040 528 544 560
  test55040_block_33
  test55040_block_34)))
  (interval_append test55040 560 592 640
  (interval_append test55040 560 576 592
  test55040_block_35
  test55040_block_36)
  (interval_append test55040 592 608 640
  test55040_block_37
  (interval_append test55040 608 624 640
  test55040_block_38
  test55040_block_39))))))
cert_nodeInterval_3 55040 55680
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
cert_test_11 55680
cert_test_block_3 55680 0 0 16 16
cert_test_block_3 55680 1 16 32 16
cert_test_block_3 55680 2 32 48 16
cert_test_block_3 55680 3 48 64 16
cert_test_block_3 55680 4 64 80 16
cert_test_block_3 55680 5 80 96 16
cert_test_block_3 55680 6 96 112 16
cert_test_block_3 55680 7 112 128 16
cert_test_block_3 55680 8 128 144 16
cert_test_block_3 55680 9 144 160 16
cert_test_block_3 55680 10 160 176 16
cert_test_block_3 55680 11 176 192 16
cert_test_block_3 55680 12 192 208 16
cert_test_block_3 55680 13 208 224 16
cert_test_block_3 55680 14 224 240 16
cert_test_block_3 55680 15 240 256 16
cert_test_block_3 55680 16 256 272 16
cert_test_block_3 55680 17 272 288 16
cert_test_block_3 55680 18 288 304 16
cert_test_block_3 55680 19 304 320 16
cert_test_block_3 55680 20 320 336 16
cert_test_block_3 55680 21 336 352 16
cert_test_block_3 55680 22 352 368 16
cert_test_block_3 55680 23 368 384 16
cert_test_block_3 55680 24 384 400 16
cert_test_block_3 55680 25 400 416 16
cert_test_block_3 55680 26 416 432 16
cert_test_block_3 55680 27 432 448 16
cert_test_block_3 55680 28 448 464 16
cert_test_block_3 55680 29 464 480 16
cert_test_block_3 55680 30 480 496 16
cert_test_block_3 55680 31 496 512 16
cert_test_block_3 55680 32 512 528 16
cert_test_block_3 55680 33 528 544 16
cert_test_block_3 55680 34 544 560 16
cert_test_block_3 55680 35 560 576 16
cert_test_block_3 55680 36 576 592 16
cert_test_block_3 55680 37 592 608 16
cert_test_block_3 55680 38 608 624 16
cert_test_block_3 55680 39 624 640 16
theorem test55680_complete : Interval test55680 0 640 :=
  (interval_append test55680 0 320 640
  (interval_append test55680 0 160 320
  (interval_append test55680 0 80 160
  (interval_append test55680 0 32 80
  (interval_append test55680 0 16 32
  test55680_block_0
  test55680_block_1)
  (interval_append test55680 32 48 80
  test55680_block_2
  (interval_append test55680 48 64 80
  test55680_block_3
  test55680_block_4)))
  (interval_append test55680 80 112 160
  (interval_append test55680 80 96 112
  test55680_block_5
  test55680_block_6)
  (interval_append test55680 112 128 160
  test55680_block_7
  (interval_append test55680 128 144 160
  test55680_block_8
  test55680_block_9))))
  (interval_append test55680 160 240 320
  (interval_append test55680 160 192 240
  (interval_append test55680 160 176 192
  test55680_block_10
  test55680_block_11)
  (interval_append test55680 192 208 240
  test55680_block_12
  (interval_append test55680 208 224 240
  test55680_block_13
  test55680_block_14)))
  (interval_append test55680 240 272 320
  (interval_append test55680 240 256 272
  test55680_block_15
  test55680_block_16)
  (interval_append test55680 272 288 320
  test55680_block_17
  (interval_append test55680 288 304 320
  test55680_block_18
  test55680_block_19)))))
  (interval_append test55680 320 480 640
  (interval_append test55680 320 400 480
  (interval_append test55680 320 352 400
  (interval_append test55680 320 336 352
  test55680_block_20
  test55680_block_21)
  (interval_append test55680 352 368 400
  test55680_block_22
  (interval_append test55680 368 384 400
  test55680_block_23
  test55680_block_24)))
  (interval_append test55680 400 432 480
  (interval_append test55680 400 416 432
  test55680_block_25
  test55680_block_26)
  (interval_append test55680 432 448 480
  test55680_block_27
  (interval_append test55680 448 464 480
  test55680_block_28
  test55680_block_29))))
  (interval_append test55680 480 560 640
  (interval_append test55680 480 512 560
  (interval_append test55680 480 496 512
  test55680_block_30
  test55680_block_31)
  (interval_append test55680 512 528 560
  test55680_block_32
  (interval_append test55680 528 544 560
  test55680_block_33
  test55680_block_34)))
  (interval_append test55680 560 592 640
  (interval_append test55680 560 576 592
  test55680_block_35
  test55680_block_36)
  (interval_append test55680 592 608 640
  test55680_block_37
  (interval_append test55680 608 624 640
  test55680_block_38
  test55680_block_39))))))
cert_nodeInterval_3 55680 56320
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
cert_test_11 56320
cert_test_block_3 56320 0 0 16 16
cert_test_block_3 56320 1 16 32 16
cert_test_block_3 56320 2 32 48 16
cert_test_block_3 56320 3 48 64 16
cert_test_block_3 56320 4 64 80 16
cert_test_block_3 56320 5 80 96 16
cert_test_block_3 56320 6 96 112 16
cert_test_block_3 56320 7 112 128 16
cert_test_block_3 56320 8 128 144 16
cert_test_block_3 56320 9 144 160 16
cert_test_block_3 56320 10 160 176 16
cert_test_block_3 56320 11 176 192 16
cert_test_block_3 56320 12 192 208 16
cert_test_block_3 56320 13 208 224 16
cert_test_block_3 56320 14 224 240 16
cert_test_block_3 56320 15 240 256 16
cert_test_block_3 56320 16 256 272 16
cert_test_block_3 56320 17 272 288 16
cert_test_block_3 56320 18 288 304 16
cert_test_block_3 56320 19 304 320 16
cert_test_block_3 56320 20 320 336 16
cert_test_block_3 56320 21 336 352 16
cert_test_block_3 56320 22 352 368 16
cert_test_block_3 56320 23 368 384 16
cert_test_block_3 56320 24 384 400 16
cert_test_block_3 56320 25 400 416 16
cert_test_block_3 56320 26 416 432 16
cert_test_block_3 56320 27 432 448 16
cert_test_block_3 56320 28 448 464 16
cert_test_block_3 56320 29 464 480 16
cert_test_block_3 56320 30 480 496 16
cert_test_block_3 56320 31 496 512 16
cert_test_block_3 56320 32 512 528 16
cert_test_block_3 56320 33 528 544 16
cert_test_block_3 56320 34 544 560 16
cert_test_block_3 56320 35 560 576 16
cert_test_block_3 56320 36 576 592 16
cert_test_block_3 56320 37 592 608 16
cert_test_block_3 56320 38 608 624 16
cert_test_block_3 56320 39 624 640 16
theorem test56320_complete : Interval test56320 0 640 :=
  (interval_append test56320 0 320 640
  (interval_append test56320 0 160 320
  (interval_append test56320 0 80 160
  (interval_append test56320 0 32 80
  (interval_append test56320 0 16 32
  test56320_block_0
  test56320_block_1)
  (interval_append test56320 32 48 80
  test56320_block_2
  (interval_append test56320 48 64 80
  test56320_block_3
  test56320_block_4)))
  (interval_append test56320 80 112 160
  (interval_append test56320 80 96 112
  test56320_block_5
  test56320_block_6)
  (interval_append test56320 112 128 160
  test56320_block_7
  (interval_append test56320 128 144 160
  test56320_block_8
  test56320_block_9))))
  (interval_append test56320 160 240 320
  (interval_append test56320 160 192 240
  (interval_append test56320 160 176 192
  test56320_block_10
  test56320_block_11)
  (interval_append test56320 192 208 240
  test56320_block_12
  (interval_append test56320 208 224 240
  test56320_block_13
  test56320_block_14)))
  (interval_append test56320 240 272 320
  (interval_append test56320 240 256 272
  test56320_block_15
  test56320_block_16)
  (interval_append test56320 272 288 320
  test56320_block_17
  (interval_append test56320 288 304 320
  test56320_block_18
  test56320_block_19)))))
  (interval_append test56320 320 480 640
  (interval_append test56320 320 400 480
  (interval_append test56320 320 352 400
  (interval_append test56320 320 336 352
  test56320_block_20
  test56320_block_21)
  (interval_append test56320 352 368 400
  test56320_block_22
  (interval_append test56320 368 384 400
  test56320_block_23
  test56320_block_24)))
  (interval_append test56320 400 432 480
  (interval_append test56320 400 416 432
  test56320_block_25
  test56320_block_26)
  (interval_append test56320 432 448 480
  test56320_block_27
  (interval_append test56320 448 464 480
  test56320_block_28
  test56320_block_29))))
  (interval_append test56320 480 560 640
  (interval_append test56320 480 512 560
  (interval_append test56320 480 496 512
  test56320_block_30
  test56320_block_31)
  (interval_append test56320 512 528 560
  test56320_block_32
  (interval_append test56320 528 544 560
  test56320_block_33
  test56320_block_34)))
  (interval_append test56320 560 592 640
  (interval_append test56320 560 576 592
  test56320_block_35
  test56320_block_36)
  (interval_append test56320 592 608 640
  test56320_block_37
  (interval_append test56320 608 624 640
  test56320_block_38
  test56320_block_39))))))
cert_nodeInterval_3 56320 56960
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
cert_test_11 56960
cert_test_block_3 56960 0 0 16 16
cert_test_block_3 56960 1 16 32 16
cert_test_block_3 56960 2 32 48 16
cert_test_block_3 56960 3 48 64 16
cert_test_block_3 56960 4 64 80 16
cert_test_block_3 56960 5 80 96 16
cert_test_block_3 56960 6 96 112 16
cert_test_block_3 56960 7 112 128 16
cert_test_block_3 56960 8 128 144 16
cert_test_block_3 56960 9 144 160 16
cert_test_block_3 56960 10 160 176 16
cert_test_block_3 56960 11 176 192 16
cert_test_block_3 56960 12 192 208 16
cert_test_block_3 56960 13 208 224 16
cert_test_block_3 56960 14 224 240 16
cert_test_block_3 56960 15 240 256 16
cert_test_block_3 56960 16 256 272 16
cert_test_block_3 56960 17 272 288 16
cert_test_block_3 56960 18 288 304 16
cert_test_block_3 56960 19 304 320 16
cert_test_block_3 56960 20 320 336 16
cert_test_block_3 56960 21 336 352 16
cert_test_block_3 56960 22 352 368 16
cert_test_block_3 56960 23 368 384 16
cert_test_block_3 56960 24 384 400 16
cert_test_block_3 56960 25 400 416 16
cert_test_block_3 56960 26 416 432 16
cert_test_block_3 56960 27 432 448 16
cert_test_block_3 56960 28 448 464 16
cert_test_block_3 56960 29 464 480 16
cert_test_block_3 56960 30 480 496 16
cert_test_block_3 56960 31 496 512 16
cert_test_block_3 56960 32 512 528 16
cert_test_block_3 56960 33 528 544 16
cert_test_block_3 56960 34 544 560 16
cert_test_block_3 56960 35 560 576 16
cert_test_block_3 56960 36 576 592 16
cert_test_block_3 56960 37 592 608 16
cert_test_block_3 56960 38 608 624 16
cert_test_block_3 56960 39 624 640 16
theorem test56960_complete : Interval test56960 0 640 :=
  (interval_append test56960 0 320 640
  (interval_append test56960 0 160 320
  (interval_append test56960 0 80 160
  (interval_append test56960 0 32 80
  (interval_append test56960 0 16 32
  test56960_block_0
  test56960_block_1)
  (interval_append test56960 32 48 80
  test56960_block_2
  (interval_append test56960 48 64 80
  test56960_block_3
  test56960_block_4)))
  (interval_append test56960 80 112 160
  (interval_append test56960 80 96 112
  test56960_block_5
  test56960_block_6)
  (interval_append test56960 112 128 160
  test56960_block_7
  (interval_append test56960 128 144 160
  test56960_block_8
  test56960_block_9))))
  (interval_append test56960 160 240 320
  (interval_append test56960 160 192 240
  (interval_append test56960 160 176 192
  test56960_block_10
  test56960_block_11)
  (interval_append test56960 192 208 240
  test56960_block_12
  (interval_append test56960 208 224 240
  test56960_block_13
  test56960_block_14)))
  (interval_append test56960 240 272 320
  (interval_append test56960 240 256 272
  test56960_block_15
  test56960_block_16)
  (interval_append test56960 272 288 320
  test56960_block_17
  (interval_append test56960 288 304 320
  test56960_block_18
  test56960_block_19)))))
  (interval_append test56960 320 480 640
  (interval_append test56960 320 400 480
  (interval_append test56960 320 352 400
  (interval_append test56960 320 336 352
  test56960_block_20
  test56960_block_21)
  (interval_append test56960 352 368 400
  test56960_block_22
  (interval_append test56960 368 384 400
  test56960_block_23
  test56960_block_24)))
  (interval_append test56960 400 432 480
  (interval_append test56960 400 416 432
  test56960_block_25
  test56960_block_26)
  (interval_append test56960 432 448 480
  test56960_block_27
  (interval_append test56960 448 464 480
  test56960_block_28
  test56960_block_29))))
  (interval_append test56960 480 560 640
  (interval_append test56960 480 512 560
  (interval_append test56960 480 496 512
  test56960_block_30
  test56960_block_31)
  (interval_append test56960 512 528 560
  test56960_block_32
  (interval_append test56960 528 544 560
  test56960_block_33
  test56960_block_34)))
  (interval_append test56960 560 592 640
  (interval_append test56960 560 576 592
  test56960_block_35
  test56960_block_36)
  (interval_append test56960 592 608 640
  test56960_block_37
  (interval_append test56960 608 624 640
  test56960_block_38
  test56960_block_39))))))
cert_nodeInterval_3 56960 57600
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
