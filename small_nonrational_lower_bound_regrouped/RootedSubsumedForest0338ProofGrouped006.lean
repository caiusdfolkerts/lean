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
cert_test_11 37760
cert_test_block_3 37760 0 0 16 16
cert_test_block_3 37760 1 16 32 16
cert_test_block_3 37760 2 32 48 16
cert_test_block_3 37760 3 48 64 16
cert_test_block_3 37760 4 64 80 16
cert_test_block_3 37760 5 80 96 16
cert_test_block_3 37760 6 96 112 16
cert_test_block_3 37760 7 112 128 16
cert_test_block_3 37760 8 128 144 16
cert_test_block_3 37760 9 144 160 16
cert_test_block_3 37760 10 160 176 16
cert_test_block_3 37760 11 176 192 16
cert_test_block_3 37760 12 192 208 16
cert_test_block_3 37760 13 208 224 16
cert_test_block_3 37760 14 224 240 16
cert_test_block_3 37760 15 240 256 16
cert_test_block_3 37760 16 256 272 16
cert_test_block_3 37760 17 272 288 16
cert_test_block_3 37760 18 288 304 16
cert_test_block_3 37760 19 304 320 16
cert_test_block_3 37760 20 320 336 16
cert_test_block_3 37760 21 336 352 16
cert_test_block_3 37760 22 352 368 16
cert_test_block_3 37760 23 368 384 16
cert_test_block_3 37760 24 384 400 16
cert_test_block_3 37760 25 400 416 16
cert_test_block_3 37760 26 416 432 16
cert_test_block_3 37760 27 432 448 16
cert_test_block_3 37760 28 448 464 16
cert_test_block_3 37760 29 464 480 16
cert_test_block_3 37760 30 480 496 16
cert_test_block_3 37760 31 496 512 16
cert_test_block_3 37760 32 512 528 16
cert_test_block_3 37760 33 528 544 16
cert_test_block_3 37760 34 544 560 16
cert_test_block_3 37760 35 560 576 16
cert_test_block_3 37760 36 576 592 16
cert_test_block_3 37760 37 592 608 16
cert_test_block_3 37760 38 608 624 16
cert_test_block_3 37760 39 624 640 16
theorem test37760_complete : Interval test37760 0 640 :=
  (interval_append test37760 0 320 640
  (interval_append test37760 0 160 320
  (interval_append test37760 0 80 160
  (interval_append test37760 0 32 80
  (interval_append test37760 0 16 32
  test37760_block_0
  test37760_block_1)
  (interval_append test37760 32 48 80
  test37760_block_2
  (interval_append test37760 48 64 80
  test37760_block_3
  test37760_block_4)))
  (interval_append test37760 80 112 160
  (interval_append test37760 80 96 112
  test37760_block_5
  test37760_block_6)
  (interval_append test37760 112 128 160
  test37760_block_7
  (interval_append test37760 128 144 160
  test37760_block_8
  test37760_block_9))))
  (interval_append test37760 160 240 320
  (interval_append test37760 160 192 240
  (interval_append test37760 160 176 192
  test37760_block_10
  test37760_block_11)
  (interval_append test37760 192 208 240
  test37760_block_12
  (interval_append test37760 208 224 240
  test37760_block_13
  test37760_block_14)))
  (interval_append test37760 240 272 320
  (interval_append test37760 240 256 272
  test37760_block_15
  test37760_block_16)
  (interval_append test37760 272 288 320
  test37760_block_17
  (interval_append test37760 288 304 320
  test37760_block_18
  test37760_block_19)))))
  (interval_append test37760 320 480 640
  (interval_append test37760 320 400 480
  (interval_append test37760 320 352 400
  (interval_append test37760 320 336 352
  test37760_block_20
  test37760_block_21)
  (interval_append test37760 352 368 400
  test37760_block_22
  (interval_append test37760 368 384 400
  test37760_block_23
  test37760_block_24)))
  (interval_append test37760 400 432 480
  (interval_append test37760 400 416 432
  test37760_block_25
  test37760_block_26)
  (interval_append test37760 432 448 480
  test37760_block_27
  (interval_append test37760 448 464 480
  test37760_block_28
  test37760_block_29))))
  (interval_append test37760 480 560 640
  (interval_append test37760 480 512 560
  (interval_append test37760 480 496 512
  test37760_block_30
  test37760_block_31)
  (interval_append test37760 512 528 560
  test37760_block_32
  (interval_append test37760 528 544 560
  test37760_block_33
  test37760_block_34)))
  (interval_append test37760 560 592 640
  (interval_append test37760 560 576 592
  test37760_block_35
  test37760_block_36)
  (interval_append test37760 592 608 640
  test37760_block_37
  (interval_append test37760 608 624 640
  test37760_block_38
  test37760_block_39))))))
cert_nodeInterval_3 37760 38400
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
cert_test_11 38400
cert_test_block_3 38400 0 0 16 16
cert_test_block_3 38400 1 16 32 16
cert_test_block_3 38400 2 32 48 16
cert_test_block_3 38400 3 48 64 16
cert_test_block_3 38400 4 64 80 16
cert_test_block_3 38400 5 80 96 16
cert_test_block_3 38400 6 96 112 16
cert_test_block_3 38400 7 112 128 16
cert_test_block_3 38400 8 128 144 16
cert_test_block_3 38400 9 144 160 16
cert_test_block_3 38400 10 160 176 16
cert_test_block_3 38400 11 176 192 16
cert_test_block_3 38400 12 192 208 16
cert_test_block_3 38400 13 208 224 16
cert_test_block_3 38400 14 224 240 16
cert_test_block_3 38400 15 240 256 16
cert_test_block_3 38400 16 256 272 16
cert_test_block_3 38400 17 272 288 16
cert_test_block_3 38400 18 288 304 16
cert_test_block_3 38400 19 304 320 16
cert_test_block_3 38400 20 320 336 16
cert_test_block_3 38400 21 336 352 16
cert_test_block_3 38400 22 352 368 16
cert_test_block_3 38400 23 368 384 16
cert_test_block_3 38400 24 384 400 16
cert_test_block_3 38400 25 400 416 16
cert_test_block_3 38400 26 416 432 16
cert_test_block_3 38400 27 432 448 16
cert_test_block_3 38400 28 448 464 16
cert_test_block_3 38400 29 464 480 16
cert_test_block_3 38400 30 480 496 16
cert_test_block_3 38400 31 496 512 16
cert_test_block_3 38400 32 512 528 16
cert_test_block_3 38400 33 528 544 16
cert_test_block_3 38400 34 544 560 16
cert_test_block_3 38400 35 560 576 16
cert_test_block_3 38400 36 576 592 16
cert_test_block_3 38400 37 592 608 16
cert_test_block_3 38400 38 608 624 16
cert_test_block_3 38400 39 624 640 16
theorem test38400_complete : Interval test38400 0 640 :=
  (interval_append test38400 0 320 640
  (interval_append test38400 0 160 320
  (interval_append test38400 0 80 160
  (interval_append test38400 0 32 80
  (interval_append test38400 0 16 32
  test38400_block_0
  test38400_block_1)
  (interval_append test38400 32 48 80
  test38400_block_2
  (interval_append test38400 48 64 80
  test38400_block_3
  test38400_block_4)))
  (interval_append test38400 80 112 160
  (interval_append test38400 80 96 112
  test38400_block_5
  test38400_block_6)
  (interval_append test38400 112 128 160
  test38400_block_7
  (interval_append test38400 128 144 160
  test38400_block_8
  test38400_block_9))))
  (interval_append test38400 160 240 320
  (interval_append test38400 160 192 240
  (interval_append test38400 160 176 192
  test38400_block_10
  test38400_block_11)
  (interval_append test38400 192 208 240
  test38400_block_12
  (interval_append test38400 208 224 240
  test38400_block_13
  test38400_block_14)))
  (interval_append test38400 240 272 320
  (interval_append test38400 240 256 272
  test38400_block_15
  test38400_block_16)
  (interval_append test38400 272 288 320
  test38400_block_17
  (interval_append test38400 288 304 320
  test38400_block_18
  test38400_block_19)))))
  (interval_append test38400 320 480 640
  (interval_append test38400 320 400 480
  (interval_append test38400 320 352 400
  (interval_append test38400 320 336 352
  test38400_block_20
  test38400_block_21)
  (interval_append test38400 352 368 400
  test38400_block_22
  (interval_append test38400 368 384 400
  test38400_block_23
  test38400_block_24)))
  (interval_append test38400 400 432 480
  (interval_append test38400 400 416 432
  test38400_block_25
  test38400_block_26)
  (interval_append test38400 432 448 480
  test38400_block_27
  (interval_append test38400 448 464 480
  test38400_block_28
  test38400_block_29))))
  (interval_append test38400 480 560 640
  (interval_append test38400 480 512 560
  (interval_append test38400 480 496 512
  test38400_block_30
  test38400_block_31)
  (interval_append test38400 512 528 560
  test38400_block_32
  (interval_append test38400 528 544 560
  test38400_block_33
  test38400_block_34)))
  (interval_append test38400 560 592 640
  (interval_append test38400 560 576 592
  test38400_block_35
  test38400_block_36)
  (interval_append test38400 592 608 640
  test38400_block_37
  (interval_append test38400 608 624 640
  test38400_block_38
  test38400_block_39))))))
cert_nodeInterval_3 38400 39040
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
cert_test_11 39040
cert_test_block_3 39040 0 0 16 16
cert_test_block_3 39040 1 16 32 16
cert_test_block_3 39040 2 32 48 16
cert_test_block_3 39040 3 48 64 16
cert_test_block_3 39040 4 64 80 16
cert_test_block_3 39040 5 80 96 16
cert_test_block_3 39040 6 96 112 16
cert_test_block_3 39040 7 112 128 16
cert_test_block_3 39040 8 128 144 16
cert_test_block_3 39040 9 144 160 16
cert_test_block_3 39040 10 160 176 16
cert_test_block_3 39040 11 176 192 16
cert_test_block_3 39040 12 192 208 16
cert_test_block_3 39040 13 208 224 16
cert_test_block_3 39040 14 224 240 16
cert_test_block_3 39040 15 240 256 16
cert_test_block_3 39040 16 256 272 16
cert_test_block_3 39040 17 272 288 16
cert_test_block_3 39040 18 288 304 16
cert_test_block_3 39040 19 304 320 16
cert_test_block_3 39040 20 320 336 16
cert_test_block_3 39040 21 336 352 16
cert_test_block_3 39040 22 352 368 16
cert_test_block_3 39040 23 368 384 16
cert_test_block_3 39040 24 384 400 16
cert_test_block_3 39040 25 400 416 16
cert_test_block_3 39040 26 416 432 16
cert_test_block_3 39040 27 432 448 16
cert_test_block_3 39040 28 448 464 16
cert_test_block_3 39040 29 464 480 16
cert_test_block_3 39040 30 480 496 16
cert_test_block_3 39040 31 496 512 16
cert_test_block_3 39040 32 512 528 16
cert_test_block_3 39040 33 528 544 16
cert_test_block_3 39040 34 544 560 16
cert_test_block_3 39040 35 560 576 16
cert_test_block_3 39040 36 576 592 16
cert_test_block_3 39040 37 592 608 16
cert_test_block_3 39040 38 608 624 16
cert_test_block_3 39040 39 624 640 16
theorem test39040_complete : Interval test39040 0 640 :=
  (interval_append test39040 0 320 640
  (interval_append test39040 0 160 320
  (interval_append test39040 0 80 160
  (interval_append test39040 0 32 80
  (interval_append test39040 0 16 32
  test39040_block_0
  test39040_block_1)
  (interval_append test39040 32 48 80
  test39040_block_2
  (interval_append test39040 48 64 80
  test39040_block_3
  test39040_block_4)))
  (interval_append test39040 80 112 160
  (interval_append test39040 80 96 112
  test39040_block_5
  test39040_block_6)
  (interval_append test39040 112 128 160
  test39040_block_7
  (interval_append test39040 128 144 160
  test39040_block_8
  test39040_block_9))))
  (interval_append test39040 160 240 320
  (interval_append test39040 160 192 240
  (interval_append test39040 160 176 192
  test39040_block_10
  test39040_block_11)
  (interval_append test39040 192 208 240
  test39040_block_12
  (interval_append test39040 208 224 240
  test39040_block_13
  test39040_block_14)))
  (interval_append test39040 240 272 320
  (interval_append test39040 240 256 272
  test39040_block_15
  test39040_block_16)
  (interval_append test39040 272 288 320
  test39040_block_17
  (interval_append test39040 288 304 320
  test39040_block_18
  test39040_block_19)))))
  (interval_append test39040 320 480 640
  (interval_append test39040 320 400 480
  (interval_append test39040 320 352 400
  (interval_append test39040 320 336 352
  test39040_block_20
  test39040_block_21)
  (interval_append test39040 352 368 400
  test39040_block_22
  (interval_append test39040 368 384 400
  test39040_block_23
  test39040_block_24)))
  (interval_append test39040 400 432 480
  (interval_append test39040 400 416 432
  test39040_block_25
  test39040_block_26)
  (interval_append test39040 432 448 480
  test39040_block_27
  (interval_append test39040 448 464 480
  test39040_block_28
  test39040_block_29))))
  (interval_append test39040 480 560 640
  (interval_append test39040 480 512 560
  (interval_append test39040 480 496 512
  test39040_block_30
  test39040_block_31)
  (interval_append test39040 512 528 560
  test39040_block_32
  (interval_append test39040 528 544 560
  test39040_block_33
  test39040_block_34)))
  (interval_append test39040 560 592 640
  (interval_append test39040 560 576 592
  test39040_block_35
  test39040_block_36)
  (interval_append test39040 592 608 640
  test39040_block_37
  (interval_append test39040 608 624 640
  test39040_block_38
  test39040_block_39))))))
cert_nodeInterval_3 39040 39680
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
cert_test_11 39680
cert_test_block_3 39680 0 0 16 16
cert_test_block_3 39680 1 16 32 16
cert_test_block_3 39680 2 32 48 16
cert_test_block_3 39680 3 48 64 16
cert_test_block_3 39680 4 64 80 16
cert_test_block_3 39680 5 80 96 16
cert_test_block_3 39680 6 96 112 16
cert_test_block_3 39680 7 112 128 16
cert_test_block_3 39680 8 128 144 16
cert_test_block_3 39680 9 144 160 16
cert_test_block_3 39680 10 160 176 16
cert_test_block_3 39680 11 176 192 16
cert_test_block_3 39680 12 192 208 16
cert_test_block_3 39680 13 208 224 16
cert_test_block_3 39680 14 224 240 16
cert_test_block_3 39680 15 240 256 16
cert_test_block_3 39680 16 256 272 16
cert_test_block_3 39680 17 272 288 16
cert_test_block_3 39680 18 288 304 16
cert_test_block_3 39680 19 304 320 16
cert_test_block_3 39680 20 320 336 16
cert_test_block_3 39680 21 336 352 16
cert_test_block_3 39680 22 352 368 16
cert_test_block_3 39680 23 368 384 16
cert_test_block_3 39680 24 384 400 16
cert_test_block_3 39680 25 400 416 16
cert_test_block_3 39680 26 416 432 16
cert_test_block_3 39680 27 432 448 16
cert_test_block_3 39680 28 448 464 16
cert_test_block_3 39680 29 464 480 16
cert_test_block_3 39680 30 480 496 16
cert_test_block_3 39680 31 496 512 16
cert_test_block_3 39680 32 512 528 16
cert_test_block_3 39680 33 528 544 16
cert_test_block_3 39680 34 544 560 16
cert_test_block_3 39680 35 560 576 16
cert_test_block_3 39680 36 576 592 16
cert_test_block_3 39680 37 592 608 16
cert_test_block_3 39680 38 608 624 16
cert_test_block_3 39680 39 624 640 16
theorem test39680_complete : Interval test39680 0 640 :=
  (interval_append test39680 0 320 640
  (interval_append test39680 0 160 320
  (interval_append test39680 0 80 160
  (interval_append test39680 0 32 80
  (interval_append test39680 0 16 32
  test39680_block_0
  test39680_block_1)
  (interval_append test39680 32 48 80
  test39680_block_2
  (interval_append test39680 48 64 80
  test39680_block_3
  test39680_block_4)))
  (interval_append test39680 80 112 160
  (interval_append test39680 80 96 112
  test39680_block_5
  test39680_block_6)
  (interval_append test39680 112 128 160
  test39680_block_7
  (interval_append test39680 128 144 160
  test39680_block_8
  test39680_block_9))))
  (interval_append test39680 160 240 320
  (interval_append test39680 160 192 240
  (interval_append test39680 160 176 192
  test39680_block_10
  test39680_block_11)
  (interval_append test39680 192 208 240
  test39680_block_12
  (interval_append test39680 208 224 240
  test39680_block_13
  test39680_block_14)))
  (interval_append test39680 240 272 320
  (interval_append test39680 240 256 272
  test39680_block_15
  test39680_block_16)
  (interval_append test39680 272 288 320
  test39680_block_17
  (interval_append test39680 288 304 320
  test39680_block_18
  test39680_block_19)))))
  (interval_append test39680 320 480 640
  (interval_append test39680 320 400 480
  (interval_append test39680 320 352 400
  (interval_append test39680 320 336 352
  test39680_block_20
  test39680_block_21)
  (interval_append test39680 352 368 400
  test39680_block_22
  (interval_append test39680 368 384 400
  test39680_block_23
  test39680_block_24)))
  (interval_append test39680 400 432 480
  (interval_append test39680 400 416 432
  test39680_block_25
  test39680_block_26)
  (interval_append test39680 432 448 480
  test39680_block_27
  (interval_append test39680 448 464 480
  test39680_block_28
  test39680_block_29))))
  (interval_append test39680 480 560 640
  (interval_append test39680 480 512 560
  (interval_append test39680 480 496 512
  test39680_block_30
  test39680_block_31)
  (interval_append test39680 512 528 560
  test39680_block_32
  (interval_append test39680 528 544 560
  test39680_block_33
  test39680_block_34)))
  (interval_append test39680 560 592 640
  (interval_append test39680 560 576 592
  test39680_block_35
  test39680_block_36)
  (interval_append test39680 592 608 640
  test39680_block_37
  (interval_append test39680 608 624 640
  test39680_block_38
  test39680_block_39))))))
cert_nodeInterval_3 39680 40320
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
cert_test_11 40320
cert_test_block_3 40320 0 0 16 16
cert_test_block_3 40320 1 16 32 16
cert_test_block_3 40320 2 32 48 16
cert_test_block_3 40320 3 48 64 16
cert_test_block_3 40320 4 64 80 16
cert_test_block_3 40320 5 80 96 16
cert_test_block_3 40320 6 96 112 16
cert_test_block_3 40320 7 112 128 16
cert_test_block_3 40320 8 128 144 16
cert_test_block_3 40320 9 144 160 16
cert_test_block_3 40320 10 160 176 16
cert_test_block_3 40320 11 176 192 16
cert_test_block_3 40320 12 192 208 16
cert_test_block_3 40320 13 208 224 16
cert_test_block_3 40320 14 224 240 16
cert_test_block_3 40320 15 240 256 16
cert_test_block_3 40320 16 256 272 16
cert_test_block_3 40320 17 272 288 16
cert_test_block_3 40320 18 288 304 16
cert_test_block_3 40320 19 304 320 16
cert_test_block_3 40320 20 320 336 16
cert_test_block_3 40320 21 336 352 16
cert_test_block_3 40320 22 352 368 16
cert_test_block_3 40320 23 368 384 16
cert_test_block_3 40320 24 384 400 16
cert_test_block_3 40320 25 400 416 16
cert_test_block_3 40320 26 416 432 16
cert_test_block_3 40320 27 432 448 16
cert_test_block_3 40320 28 448 464 16
cert_test_block_3 40320 29 464 480 16
cert_test_block_3 40320 30 480 496 16
cert_test_block_3 40320 31 496 512 16
cert_test_block_3 40320 32 512 528 16
cert_test_block_3 40320 33 528 544 16
cert_test_block_3 40320 34 544 560 16
cert_test_block_3 40320 35 560 576 16
cert_test_block_3 40320 36 576 592 16
cert_test_block_3 40320 37 592 608 16
cert_test_block_3 40320 38 608 624 16
cert_test_block_3 40320 39 624 640 16
theorem test40320_complete : Interval test40320 0 640 :=
  (interval_append test40320 0 320 640
  (interval_append test40320 0 160 320
  (interval_append test40320 0 80 160
  (interval_append test40320 0 32 80
  (interval_append test40320 0 16 32
  test40320_block_0
  test40320_block_1)
  (interval_append test40320 32 48 80
  test40320_block_2
  (interval_append test40320 48 64 80
  test40320_block_3
  test40320_block_4)))
  (interval_append test40320 80 112 160
  (interval_append test40320 80 96 112
  test40320_block_5
  test40320_block_6)
  (interval_append test40320 112 128 160
  test40320_block_7
  (interval_append test40320 128 144 160
  test40320_block_8
  test40320_block_9))))
  (interval_append test40320 160 240 320
  (interval_append test40320 160 192 240
  (interval_append test40320 160 176 192
  test40320_block_10
  test40320_block_11)
  (interval_append test40320 192 208 240
  test40320_block_12
  (interval_append test40320 208 224 240
  test40320_block_13
  test40320_block_14)))
  (interval_append test40320 240 272 320
  (interval_append test40320 240 256 272
  test40320_block_15
  test40320_block_16)
  (interval_append test40320 272 288 320
  test40320_block_17
  (interval_append test40320 288 304 320
  test40320_block_18
  test40320_block_19)))))
  (interval_append test40320 320 480 640
  (interval_append test40320 320 400 480
  (interval_append test40320 320 352 400
  (interval_append test40320 320 336 352
  test40320_block_20
  test40320_block_21)
  (interval_append test40320 352 368 400
  test40320_block_22
  (interval_append test40320 368 384 400
  test40320_block_23
  test40320_block_24)))
  (interval_append test40320 400 432 480
  (interval_append test40320 400 416 432
  test40320_block_25
  test40320_block_26)
  (interval_append test40320 432 448 480
  test40320_block_27
  (interval_append test40320 448 464 480
  test40320_block_28
  test40320_block_29))))
  (interval_append test40320 480 560 640
  (interval_append test40320 480 512 560
  (interval_append test40320 480 496 512
  test40320_block_30
  test40320_block_31)
  (interval_append test40320 512 528 560
  test40320_block_32
  (interval_append test40320 528 544 560
  test40320_block_33
  test40320_block_34)))
  (interval_append test40320 560 592 640
  (interval_append test40320 560 576 592
  test40320_block_35
  test40320_block_36)
  (interval_append test40320 592 608 640
  test40320_block_37
  (interval_append test40320 608 624 640
  test40320_block_38
  test40320_block_39))))))
cert_nodeInterval_3 40320 40960
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
cert_test_11 40960
cert_test_block_3 40960 0 0 16 16
cert_test_block_3 40960 1 16 32 16
cert_test_block_3 40960 2 32 48 16
cert_test_block_3 40960 3 48 64 16
cert_test_block_3 40960 4 64 80 16
cert_test_block_3 40960 5 80 96 16
cert_test_block_3 40960 6 96 112 16
cert_test_block_3 40960 7 112 128 16
cert_test_block_3 40960 8 128 144 16
cert_test_block_3 40960 9 144 160 16
cert_test_block_3 40960 10 160 176 16
cert_test_block_3 40960 11 176 192 16
cert_test_block_3 40960 12 192 208 16
cert_test_block_3 40960 13 208 224 16
cert_test_block_3 40960 14 224 240 16
cert_test_block_3 40960 15 240 256 16
cert_test_block_3 40960 16 256 272 16
cert_test_block_3 40960 17 272 288 16
cert_test_block_3 40960 18 288 304 16
cert_test_block_3 40960 19 304 320 16
cert_test_block_3 40960 20 320 336 16
cert_test_block_3 40960 21 336 352 16
cert_test_block_3 40960 22 352 368 16
cert_test_block_3 40960 23 368 384 16
cert_test_block_3 40960 24 384 400 16
cert_test_block_3 40960 25 400 416 16
cert_test_block_3 40960 26 416 432 16
cert_test_block_3 40960 27 432 448 16
cert_test_block_3 40960 28 448 464 16
cert_test_block_3 40960 29 464 480 16
cert_test_block_3 40960 30 480 496 16
cert_test_block_3 40960 31 496 512 16
cert_test_block_3 40960 32 512 528 16
cert_test_block_3 40960 33 528 544 16
cert_test_block_3 40960 34 544 560 16
cert_test_block_3 40960 35 560 576 16
cert_test_block_3 40960 36 576 592 16
cert_test_block_3 40960 37 592 608 16
cert_test_block_3 40960 38 608 624 16
cert_test_block_3 40960 39 624 640 16
theorem test40960_complete : Interval test40960 0 640 :=
  (interval_append test40960 0 320 640
  (interval_append test40960 0 160 320
  (interval_append test40960 0 80 160
  (interval_append test40960 0 32 80
  (interval_append test40960 0 16 32
  test40960_block_0
  test40960_block_1)
  (interval_append test40960 32 48 80
  test40960_block_2
  (interval_append test40960 48 64 80
  test40960_block_3
  test40960_block_4)))
  (interval_append test40960 80 112 160
  (interval_append test40960 80 96 112
  test40960_block_5
  test40960_block_6)
  (interval_append test40960 112 128 160
  test40960_block_7
  (interval_append test40960 128 144 160
  test40960_block_8
  test40960_block_9))))
  (interval_append test40960 160 240 320
  (interval_append test40960 160 192 240
  (interval_append test40960 160 176 192
  test40960_block_10
  test40960_block_11)
  (interval_append test40960 192 208 240
  test40960_block_12
  (interval_append test40960 208 224 240
  test40960_block_13
  test40960_block_14)))
  (interval_append test40960 240 272 320
  (interval_append test40960 240 256 272
  test40960_block_15
  test40960_block_16)
  (interval_append test40960 272 288 320
  test40960_block_17
  (interval_append test40960 288 304 320
  test40960_block_18
  test40960_block_19)))))
  (interval_append test40960 320 480 640
  (interval_append test40960 320 400 480
  (interval_append test40960 320 352 400
  (interval_append test40960 320 336 352
  test40960_block_20
  test40960_block_21)
  (interval_append test40960 352 368 400
  test40960_block_22
  (interval_append test40960 368 384 400
  test40960_block_23
  test40960_block_24)))
  (interval_append test40960 400 432 480
  (interval_append test40960 400 416 432
  test40960_block_25
  test40960_block_26)
  (interval_append test40960 432 448 480
  test40960_block_27
  (interval_append test40960 448 464 480
  test40960_block_28
  test40960_block_29))))
  (interval_append test40960 480 560 640
  (interval_append test40960 480 512 560
  (interval_append test40960 480 496 512
  test40960_block_30
  test40960_block_31)
  (interval_append test40960 512 528 560
  test40960_block_32
  (interval_append test40960 528 544 560
  test40960_block_33
  test40960_block_34)))
  (interval_append test40960 560 592 640
  (interval_append test40960 560 576 592
  test40960_block_35
  test40960_block_36)
  (interval_append test40960 592 608 640
  test40960_block_37
  (interval_append test40960 608 624 640
  test40960_block_38
  test40960_block_39))))))
cert_nodeInterval_3 40960 41600
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
cert_test_11 41600
cert_test_block_3 41600 0 0 16 16
cert_test_block_3 41600 1 16 32 16
cert_test_block_3 41600 2 32 48 16
cert_test_block_3 41600 3 48 64 16
cert_test_block_3 41600 4 64 80 16
cert_test_block_3 41600 5 80 96 16
cert_test_block_3 41600 6 96 112 16
cert_test_block_3 41600 7 112 128 16
cert_test_block_3 41600 8 128 144 16
cert_test_block_3 41600 9 144 160 16
cert_test_block_3 41600 10 160 176 16
cert_test_block_3 41600 11 176 192 16
cert_test_block_3 41600 12 192 208 16
cert_test_block_3 41600 13 208 224 16
cert_test_block_3 41600 14 224 240 16
cert_test_block_3 41600 15 240 256 16
cert_test_block_3 41600 16 256 272 16
cert_test_block_3 41600 17 272 288 16
cert_test_block_3 41600 18 288 304 16
cert_test_block_3 41600 19 304 320 16
cert_test_block_3 41600 20 320 336 16
cert_test_block_3 41600 21 336 352 16
cert_test_block_3 41600 22 352 368 16
cert_test_block_3 41600 23 368 384 16
cert_test_block_3 41600 24 384 400 16
cert_test_block_3 41600 25 400 416 16
cert_test_block_3 41600 26 416 432 16
cert_test_block_3 41600 27 432 448 16
cert_test_block_3 41600 28 448 464 16
cert_test_block_3 41600 29 464 480 16
cert_test_block_3 41600 30 480 496 16
cert_test_block_3 41600 31 496 512 16
cert_test_block_3 41600 32 512 528 16
cert_test_block_3 41600 33 528 544 16
cert_test_block_3 41600 34 544 560 16
cert_test_block_3 41600 35 560 576 16
cert_test_block_3 41600 36 576 592 16
cert_test_block_3 41600 37 592 608 16
cert_test_block_3 41600 38 608 624 16
cert_test_block_3 41600 39 624 640 16
theorem test41600_complete : Interval test41600 0 640 :=
  (interval_append test41600 0 320 640
  (interval_append test41600 0 160 320
  (interval_append test41600 0 80 160
  (interval_append test41600 0 32 80
  (interval_append test41600 0 16 32
  test41600_block_0
  test41600_block_1)
  (interval_append test41600 32 48 80
  test41600_block_2
  (interval_append test41600 48 64 80
  test41600_block_3
  test41600_block_4)))
  (interval_append test41600 80 112 160
  (interval_append test41600 80 96 112
  test41600_block_5
  test41600_block_6)
  (interval_append test41600 112 128 160
  test41600_block_7
  (interval_append test41600 128 144 160
  test41600_block_8
  test41600_block_9))))
  (interval_append test41600 160 240 320
  (interval_append test41600 160 192 240
  (interval_append test41600 160 176 192
  test41600_block_10
  test41600_block_11)
  (interval_append test41600 192 208 240
  test41600_block_12
  (interval_append test41600 208 224 240
  test41600_block_13
  test41600_block_14)))
  (interval_append test41600 240 272 320
  (interval_append test41600 240 256 272
  test41600_block_15
  test41600_block_16)
  (interval_append test41600 272 288 320
  test41600_block_17
  (interval_append test41600 288 304 320
  test41600_block_18
  test41600_block_19)))))
  (interval_append test41600 320 480 640
  (interval_append test41600 320 400 480
  (interval_append test41600 320 352 400
  (interval_append test41600 320 336 352
  test41600_block_20
  test41600_block_21)
  (interval_append test41600 352 368 400
  test41600_block_22
  (interval_append test41600 368 384 400
  test41600_block_23
  test41600_block_24)))
  (interval_append test41600 400 432 480
  (interval_append test41600 400 416 432
  test41600_block_25
  test41600_block_26)
  (interval_append test41600 432 448 480
  test41600_block_27
  (interval_append test41600 448 464 480
  test41600_block_28
  test41600_block_29))))
  (interval_append test41600 480 560 640
  (interval_append test41600 480 512 560
  (interval_append test41600 480 496 512
  test41600_block_30
  test41600_block_31)
  (interval_append test41600 512 528 560
  test41600_block_32
  (interval_append test41600 528 544 560
  test41600_block_33
  test41600_block_34)))
  (interval_append test41600 560 592 640
  (interval_append test41600 560 576 592
  test41600_block_35
  test41600_block_36)
  (interval_append test41600 592 608 640
  test41600_block_37
  (interval_append test41600 608 624 640
  test41600_block_38
  test41600_block_39))))))
cert_nodeInterval_3 41600 42240
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
cert_test_11 42240
cert_test_block_3 42240 0 0 16 16
cert_test_block_3 42240 1 16 32 16
cert_test_block_3 42240 2 32 48 16
cert_test_block_3 42240 3 48 64 16
cert_test_block_3 42240 4 64 80 16
cert_test_block_3 42240 5 80 96 16
cert_test_block_3 42240 6 96 112 16
cert_test_block_3 42240 7 112 128 16
cert_test_block_3 42240 8 128 144 16
cert_test_block_3 42240 9 144 160 16
cert_test_block_3 42240 10 160 176 16
cert_test_block_3 42240 11 176 192 16
cert_test_block_3 42240 12 192 208 16
cert_test_block_3 42240 13 208 224 16
cert_test_block_3 42240 14 224 240 16
cert_test_block_3 42240 15 240 256 16
cert_test_block_3 42240 16 256 272 16
cert_test_block_3 42240 17 272 288 16
cert_test_block_3 42240 18 288 304 16
cert_test_block_3 42240 19 304 320 16
cert_test_block_3 42240 20 320 336 16
cert_test_block_3 42240 21 336 352 16
cert_test_block_3 42240 22 352 368 16
cert_test_block_3 42240 23 368 384 16
cert_test_block_3 42240 24 384 400 16
cert_test_block_3 42240 25 400 416 16
cert_test_block_3 42240 26 416 432 16
cert_test_block_3 42240 27 432 448 16
cert_test_block_3 42240 28 448 464 16
cert_test_block_3 42240 29 464 480 16
cert_test_block_3 42240 30 480 496 16
cert_test_block_3 42240 31 496 512 16
cert_test_block_3 42240 32 512 528 16
cert_test_block_3 42240 33 528 544 16
cert_test_block_3 42240 34 544 560 16
cert_test_block_3 42240 35 560 576 16
cert_test_block_3 42240 36 576 592 16
cert_test_block_3 42240 37 592 608 16
cert_test_block_3 42240 38 608 624 16
cert_test_block_3 42240 39 624 640 16
theorem test42240_complete : Interval test42240 0 640 :=
  (interval_append test42240 0 320 640
  (interval_append test42240 0 160 320
  (interval_append test42240 0 80 160
  (interval_append test42240 0 32 80
  (interval_append test42240 0 16 32
  test42240_block_0
  test42240_block_1)
  (interval_append test42240 32 48 80
  test42240_block_2
  (interval_append test42240 48 64 80
  test42240_block_3
  test42240_block_4)))
  (interval_append test42240 80 112 160
  (interval_append test42240 80 96 112
  test42240_block_5
  test42240_block_6)
  (interval_append test42240 112 128 160
  test42240_block_7
  (interval_append test42240 128 144 160
  test42240_block_8
  test42240_block_9))))
  (interval_append test42240 160 240 320
  (interval_append test42240 160 192 240
  (interval_append test42240 160 176 192
  test42240_block_10
  test42240_block_11)
  (interval_append test42240 192 208 240
  test42240_block_12
  (interval_append test42240 208 224 240
  test42240_block_13
  test42240_block_14)))
  (interval_append test42240 240 272 320
  (interval_append test42240 240 256 272
  test42240_block_15
  test42240_block_16)
  (interval_append test42240 272 288 320
  test42240_block_17
  (interval_append test42240 288 304 320
  test42240_block_18
  test42240_block_19)))))
  (interval_append test42240 320 480 640
  (interval_append test42240 320 400 480
  (interval_append test42240 320 352 400
  (interval_append test42240 320 336 352
  test42240_block_20
  test42240_block_21)
  (interval_append test42240 352 368 400
  test42240_block_22
  (interval_append test42240 368 384 400
  test42240_block_23
  test42240_block_24)))
  (interval_append test42240 400 432 480
  (interval_append test42240 400 416 432
  test42240_block_25
  test42240_block_26)
  (interval_append test42240 432 448 480
  test42240_block_27
  (interval_append test42240 448 464 480
  test42240_block_28
  test42240_block_29))))
  (interval_append test42240 480 560 640
  (interval_append test42240 480 512 560
  (interval_append test42240 480 496 512
  test42240_block_30
  test42240_block_31)
  (interval_append test42240 512 528 560
  test42240_block_32
  (interval_append test42240 528 544 560
  test42240_block_33
  test42240_block_34)))
  (interval_append test42240 560 592 640
  (interval_append test42240 560 576 592
  test42240_block_35
  test42240_block_36)
  (interval_append test42240 592 608 640
  test42240_block_37
  (interval_append test42240 608 624 640
  test42240_block_38
  test42240_block_39))))))
cert_nodeInterval_3 42240 42880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end
