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
cert_test_block_3 57600 38 608 609 1
theorem test57600_complete : Interval test57600 0 609 :=
  (interval_append test57600 0 304 609
  (interval_append test57600 0 144 304
  (interval_append test57600 0 64 144
  (interval_append test57600 0 32 64
  (interval_append test57600 0 16 32
  test57600_block_0
  test57600_block_1)
  (interval_append test57600 32 48 64
  test57600_block_2
  test57600_block_3))
  (interval_append test57600 64 96 144
  (interval_append test57600 64 80 96
  test57600_block_4
  test57600_block_5)
  (interval_append test57600 96 112 144
  test57600_block_6
  (interval_append test57600 112 128 144
  test57600_block_7
  test57600_block_8))))
  (interval_append test57600 144 224 304
  (interval_append test57600 144 176 224
  (interval_append test57600 144 160 176
  test57600_block_9
  test57600_block_10)
  (interval_append test57600 176 192 224
  test57600_block_11
  (interval_append test57600 192 208 224
  test57600_block_12
  test57600_block_13)))
  (interval_append test57600 224 256 304
  (interval_append test57600 224 240 256
  test57600_block_14
  test57600_block_15)
  (interval_append test57600 256 272 304
  test57600_block_16
  (interval_append test57600 272 288 304
  test57600_block_17
  test57600_block_18)))))
  (interval_append test57600 304 464 609
  (interval_append test57600 304 384 464
  (interval_append test57600 304 336 384
  (interval_append test57600 304 320 336
  test57600_block_19
  test57600_block_20)
  (interval_append test57600 336 352 384
  test57600_block_21
  (interval_append test57600 352 368 384
  test57600_block_22
  test57600_block_23)))
  (interval_append test57600 384 416 464
  (interval_append test57600 384 400 416
  test57600_block_24
  test57600_block_25)
  (interval_append test57600 416 432 464
  test57600_block_26
  (interval_append test57600 432 448 464
  test57600_block_27
  test57600_block_28))))
  (interval_append test57600 464 544 609
  (interval_append test57600 464 496 544
  (interval_append test57600 464 480 496
  test57600_block_29
  test57600_block_30)
  (interval_append test57600 496 512 544
  test57600_block_31
  (interval_append test57600 512 528 544
  test57600_block_32
  test57600_block_33)))
  (interval_append test57600 544 576 609
  (interval_append test57600 544 560 576
  test57600_block_34
  test57600_block_35)
  (interval_append test57600 576 592 609
  test57600_block_36
  (interval_append test57600 592 608 609
  test57600_block_37
  test57600_block_38))))))
cert_nodeInterval_3 57600 58209
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end
