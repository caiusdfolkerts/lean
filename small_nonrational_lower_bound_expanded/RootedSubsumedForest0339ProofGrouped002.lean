module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0339Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
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
cert_test_block_3 14080 38 608 619 11
theorem test14080_complete : Interval test14080 0 619 :=
  (interval_append test14080 0 304 619
  (interval_append test14080 0 144 304
  (interval_append test14080 0 64 144
  (interval_append test14080 0 32 64
  (interval_append test14080 0 16 32
  test14080_block_0
  test14080_block_1)
  (interval_append test14080 32 48 64
  test14080_block_2
  test14080_block_3))
  (interval_append test14080 64 96 144
  (interval_append test14080 64 80 96
  test14080_block_4
  test14080_block_5)
  (interval_append test14080 96 112 144
  test14080_block_6
  (interval_append test14080 112 128 144
  test14080_block_7
  test14080_block_8))))
  (interval_append test14080 144 224 304
  (interval_append test14080 144 176 224
  (interval_append test14080 144 160 176
  test14080_block_9
  test14080_block_10)
  (interval_append test14080 176 192 224
  test14080_block_11
  (interval_append test14080 192 208 224
  test14080_block_12
  test14080_block_13)))
  (interval_append test14080 224 256 304
  (interval_append test14080 224 240 256
  test14080_block_14
  test14080_block_15)
  (interval_append test14080 256 272 304
  test14080_block_16
  (interval_append test14080 272 288 304
  test14080_block_17
  test14080_block_18)))))
  (interval_append test14080 304 464 619
  (interval_append test14080 304 384 464
  (interval_append test14080 304 336 384
  (interval_append test14080 304 320 336
  test14080_block_19
  test14080_block_20)
  (interval_append test14080 336 352 384
  test14080_block_21
  (interval_append test14080 352 368 384
  test14080_block_22
  test14080_block_23)))
  (interval_append test14080 384 416 464
  (interval_append test14080 384 400 416
  test14080_block_24
  test14080_block_25)
  (interval_append test14080 416 432 464
  test14080_block_26
  (interval_append test14080 432 448 464
  test14080_block_27
  test14080_block_28))))
  (interval_append test14080 464 544 619
  (interval_append test14080 464 496 544
  (interval_append test14080 464 480 496
  test14080_block_29
  test14080_block_30)
  (interval_append test14080 496 512 544
  test14080_block_31
  (interval_append test14080 512 528 544
  test14080_block_32
  test14080_block_33)))
  (interval_append test14080 544 576 619
  (interval_append test14080 544 560 576
  test14080_block_34
  test14080_block_35)
  (interval_append test14080 576 592 619
  test14080_block_36
  (interval_append test14080 592 608 619
  test14080_block_37
  test14080_block_38))))))
cert_nodeInterval_3 14080 14699
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
end
end
