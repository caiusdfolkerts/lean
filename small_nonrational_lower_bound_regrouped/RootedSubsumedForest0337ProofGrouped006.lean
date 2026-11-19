module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0337Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
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
cert_test_block_3 41600 18 288 295 7
theorem test41600_complete : Interval test41600 0 295 :=
  (interval_append test41600 0 144 295
  (interval_append test41600 0 64 144
  (interval_append test41600 0 32 64
  (interval_append test41600 0 16 32
  test41600_block_0
  test41600_block_1)
  (interval_append test41600 32 48 64
  test41600_block_2
  test41600_block_3))
  (interval_append test41600 64 96 144
  (interval_append test41600 64 80 96
  test41600_block_4
  test41600_block_5)
  (interval_append test41600 96 112 144
  test41600_block_6
  (interval_append test41600 112 128 144
  test41600_block_7
  test41600_block_8))))
  (interval_append test41600 144 224 295
  (interval_append test41600 144 176 224
  (interval_append test41600 144 160 176
  test41600_block_9
  test41600_block_10)
  (interval_append test41600 176 192 224
  test41600_block_11
  (interval_append test41600 192 208 224
  test41600_block_12
  test41600_block_13)))
  (interval_append test41600 224 256 295
  (interval_append test41600 224 240 256
  test41600_block_14
  test41600_block_15)
  (interval_append test41600 256 272 295
  test41600_block_16
  (interval_append test41600 272 288 295
  test41600_block_17
  test41600_block_18)))))
cert_nodeInterval_3 41600 41895
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
end
end
