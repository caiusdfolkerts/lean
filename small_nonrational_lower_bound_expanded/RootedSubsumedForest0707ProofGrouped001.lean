module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0707Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 8320
cert_test_block_3 8320 0 0 16 16
cert_test_block_3 8320 1 16 32 16
cert_test_block_3 8320 2 32 48 16
cert_test_block_3 8320 3 48 64 16
cert_test_block_3 8320 4 64 80 16
cert_test_block_3 8320 5 80 96 16
cert_test_block_3 8320 6 96 112 16
cert_test_block_3 8320 7 112 128 16
cert_test_block_3 8320 8 128 144 16
cert_test_block_3 8320 9 144 160 16
cert_test_block_3 8320 10 160 176 16
cert_test_block_3 8320 11 176 192 16
cert_test_block_3 8320 12 192 208 16
cert_test_block_3 8320 13 208 224 16
cert_test_block_3 8320 14 224 240 16
cert_test_block_3 8320 15 240 256 16
cert_test_block_3 8320 16 256 272 16
cert_test_block_3 8320 17 272 288 16
cert_test_block_3 8320 18 288 304 16
cert_test_block_3 8320 19 304 320 16
cert_test_block_3 8320 20 320 336 16
cert_test_block_3 8320 21 336 352 16
cert_test_block_3 8320 22 352 368 16
cert_test_block_3 8320 23 368 384 16
cert_test_block_3 8320 24 384 400 16
cert_test_block_3 8320 25 400 416 16
cert_test_block_3 8320 26 416 432 16
cert_test_block_3 8320 27 432 448 16
cert_test_block_3 8320 28 448 464 16
cert_test_block_3 8320 29 464 480 16
cert_test_block_3 8320 30 480 496 16
cert_test_block_3 8320 31 496 512 16
cert_test_block_3 8320 32 512 528 16
cert_test_block_3 8320 33 528 544 16
cert_test_block_3 8320 34 544 560 16
cert_test_block_3 8320 35 560 576 16
cert_test_block_3 8320 36 576 592 16
cert_test_block_3 8320 37 592 608 16
cert_test_block_3 8320 38 608 624 16
cert_test_block_3 8320 39 624 640 16
theorem test8320_complete : Interval test8320 0 640 :=
  (interval_append test8320 0 320 640
  (interval_append test8320 0 160 320
  (interval_append test8320 0 80 160
  (interval_append test8320 0 32 80
  (interval_append test8320 0 16 32
  test8320_block_0
  test8320_block_1)
  (interval_append test8320 32 48 80
  test8320_block_2
  (interval_append test8320 48 64 80
  test8320_block_3
  test8320_block_4)))
  (interval_append test8320 80 112 160
  (interval_append test8320 80 96 112
  test8320_block_5
  test8320_block_6)
  (interval_append test8320 112 128 160
  test8320_block_7
  (interval_append test8320 128 144 160
  test8320_block_8
  test8320_block_9))))
  (interval_append test8320 160 240 320
  (interval_append test8320 160 192 240
  (interval_append test8320 160 176 192
  test8320_block_10
  test8320_block_11)
  (interval_append test8320 192 208 240
  test8320_block_12
  (interval_append test8320 208 224 240
  test8320_block_13
  test8320_block_14)))
  (interval_append test8320 240 272 320
  (interval_append test8320 240 256 272
  test8320_block_15
  test8320_block_16)
  (interval_append test8320 272 288 320
  test8320_block_17
  (interval_append test8320 288 304 320
  test8320_block_18
  test8320_block_19)))))
  (interval_append test8320 320 480 640
  (interval_append test8320 320 400 480
  (interval_append test8320 320 352 400
  (interval_append test8320 320 336 352
  test8320_block_20
  test8320_block_21)
  (interval_append test8320 352 368 400
  test8320_block_22
  (interval_append test8320 368 384 400
  test8320_block_23
  test8320_block_24)))
  (interval_append test8320 400 432 480
  (interval_append test8320 400 416 432
  test8320_block_25
  test8320_block_26)
  (interval_append test8320 432 448 480
  test8320_block_27
  (interval_append test8320 448 464 480
  test8320_block_28
  test8320_block_29))))
  (interval_append test8320 480 560 640
  (interval_append test8320 480 512 560
  (interval_append test8320 480 496 512
  test8320_block_30
  test8320_block_31)
  (interval_append test8320 512 528 560
  test8320_block_32
  (interval_append test8320 528 544 560
  test8320_block_33
  test8320_block_34)))
  (interval_append test8320 560 592 640
  (interval_append test8320 560 576 592
  test8320_block_35
  test8320_block_36)
  (interval_append test8320 592 608 640
  test8320_block_37
  (interval_append test8320 608 624 640
  test8320_block_38
  test8320_block_39))))))
cert_nodeInterval_3 8320 8960
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
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
cert_test_block_3 9600 38 608 623 15
theorem test9600_complete : Interval test9600 0 623 :=
  (interval_append test9600 0 304 623
  (interval_append test9600 0 144 304
  (interval_append test9600 0 64 144
  (interval_append test9600 0 32 64
  (interval_append test9600 0 16 32
  test9600_block_0
  test9600_block_1)
  (interval_append test9600 32 48 64
  test9600_block_2
  test9600_block_3))
  (interval_append test9600 64 96 144
  (interval_append test9600 64 80 96
  test9600_block_4
  test9600_block_5)
  (interval_append test9600 96 112 144
  test9600_block_6
  (interval_append test9600 112 128 144
  test9600_block_7
  test9600_block_8))))
  (interval_append test9600 144 224 304
  (interval_append test9600 144 176 224
  (interval_append test9600 144 160 176
  test9600_block_9
  test9600_block_10)
  (interval_append test9600 176 192 224
  test9600_block_11
  (interval_append test9600 192 208 224
  test9600_block_12
  test9600_block_13)))
  (interval_append test9600 224 256 304
  (interval_append test9600 224 240 256
  test9600_block_14
  test9600_block_15)
  (interval_append test9600 256 272 304
  test9600_block_16
  (interval_append test9600 272 288 304
  test9600_block_17
  test9600_block_18)))))
  (interval_append test9600 304 464 623
  (interval_append test9600 304 384 464
  (interval_append test9600 304 336 384
  (interval_append test9600 304 320 336
  test9600_block_19
  test9600_block_20)
  (interval_append test9600 336 352 384
  test9600_block_21
  (interval_append test9600 352 368 384
  test9600_block_22
  test9600_block_23)))
  (interval_append test9600 384 416 464
  (interval_append test9600 384 400 416
  test9600_block_24
  test9600_block_25)
  (interval_append test9600 416 432 464
  test9600_block_26
  (interval_append test9600 432 448 464
  test9600_block_27
  test9600_block_28))))
  (interval_append test9600 464 544 623
  (interval_append test9600 464 496 544
  (interval_append test9600 464 480 496
  test9600_block_29
  test9600_block_30)
  (interval_append test9600 496 512 544
  test9600_block_31
  (interval_append test9600 512 528 544
  test9600_block_32
  test9600_block_33)))
  (interval_append test9600 544 576 623
  (interval_append test9600 544 560 576
  test9600_block_34
  test9600_block_35)
  (interval_append test9600 576 592 623
  test9600_block_36
  (interval_append test9600 592 608 623
  test9600_block_37
  test9600_block_38))))))
cert_nodeInterval_3 9600 10223
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0707
end
end
