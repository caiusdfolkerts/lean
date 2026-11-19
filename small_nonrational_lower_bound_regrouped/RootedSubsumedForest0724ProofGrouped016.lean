module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 136960
cert_test_block_3 136960 0 0 16 16
cert_test_block_3 136960 1 16 32 16
cert_test_block_3 136960 2 32 48 16
cert_test_block_3 136960 3 48 64 16
cert_test_block_3 136960 4 64 80 16
cert_test_block_3 136960 5 80 96 16
cert_test_block_3 136960 6 96 112 16
cert_test_block_3 136960 7 112 128 16
cert_test_block_3 136960 8 128 144 16
cert_test_block_3 136960 9 144 160 16
cert_test_block_3 136960 10 160 176 16
cert_test_block_3 136960 11 176 192 16
cert_test_block_3 136960 12 192 208 16
cert_test_block_3 136960 13 208 224 16
cert_test_block_3 136960 14 224 240 16
cert_test_block_3 136960 15 240 256 16
cert_test_block_3 136960 16 256 272 16
cert_test_block_3 136960 17 272 288 16
cert_test_block_3 136960 18 288 304 16
cert_test_block_3 136960 19 304 320 16
cert_test_block_3 136960 20 320 336 16
cert_test_block_3 136960 21 336 352 16
cert_test_block_3 136960 22 352 368 16
cert_test_block_3 136960 23 368 384 16
cert_test_block_3 136960 24 384 400 16
cert_test_block_3 136960 25 400 416 16
cert_test_block_3 136960 26 416 432 16
cert_test_block_3 136960 27 432 448 16
cert_test_block_3 136960 28 448 464 16
cert_test_block_3 136960 29 464 480 16
cert_test_block_3 136960 30 480 496 16
cert_test_block_3 136960 31 496 512 16
cert_test_block_3 136960 32 512 528 16
cert_test_block_3 136960 33 528 544 16
cert_test_block_3 136960 34 544 560 16
cert_test_block_3 136960 35 560 576 16
cert_test_block_3 136960 36 576 592 16
cert_test_block_3 136960 37 592 608 16
cert_test_block_3 136960 38 608 624 16
cert_test_block_3 136960 39 624 640 16
theorem test136960_complete : Interval test136960 0 640 :=
  (interval_append test136960 0 320 640
  (interval_append test136960 0 160 320
  (interval_append test136960 0 80 160
  (interval_append test136960 0 32 80
  (interval_append test136960 0 16 32
  test136960_block_0
  test136960_block_1)
  (interval_append test136960 32 48 80
  test136960_block_2
  (interval_append test136960 48 64 80
  test136960_block_3
  test136960_block_4)))
  (interval_append test136960 80 112 160
  (interval_append test136960 80 96 112
  test136960_block_5
  test136960_block_6)
  (interval_append test136960 112 128 160
  test136960_block_7
  (interval_append test136960 128 144 160
  test136960_block_8
  test136960_block_9))))
  (interval_append test136960 160 240 320
  (interval_append test136960 160 192 240
  (interval_append test136960 160 176 192
  test136960_block_10
  test136960_block_11)
  (interval_append test136960 192 208 240
  test136960_block_12
  (interval_append test136960 208 224 240
  test136960_block_13
  test136960_block_14)))
  (interval_append test136960 240 272 320
  (interval_append test136960 240 256 272
  test136960_block_15
  test136960_block_16)
  (interval_append test136960 272 288 320
  test136960_block_17
  (interval_append test136960 288 304 320
  test136960_block_18
  test136960_block_19)))))
  (interval_append test136960 320 480 640
  (interval_append test136960 320 400 480
  (interval_append test136960 320 352 400
  (interval_append test136960 320 336 352
  test136960_block_20
  test136960_block_21)
  (interval_append test136960 352 368 400
  test136960_block_22
  (interval_append test136960 368 384 400
  test136960_block_23
  test136960_block_24)))
  (interval_append test136960 400 432 480
  (interval_append test136960 400 416 432
  test136960_block_25
  test136960_block_26)
  (interval_append test136960 432 448 480
  test136960_block_27
  (interval_append test136960 448 464 480
  test136960_block_28
  test136960_block_29))))
  (interval_append test136960 480 560 640
  (interval_append test136960 480 512 560
  (interval_append test136960 480 496 512
  test136960_block_30
  test136960_block_31)
  (interval_append test136960 512 528 560
  test136960_block_32
  (interval_append test136960 528 544 560
  test136960_block_33
  test136960_block_34)))
  (interval_append test136960 560 592 640
  (interval_append test136960 560 576 592
  test136960_block_35
  test136960_block_36)
  (interval_append test136960 592 608 640
  test136960_block_37
  (interval_append test136960 608 624 640
  test136960_block_38
  test136960_block_39))))))
cert_nodeInterval_3 136960 137600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 137600
cert_test_block_3 137600 0 0 16 16
cert_test_block_3 137600 1 16 32 16
cert_test_block_3 137600 2 32 48 16
cert_test_block_3 137600 3 48 64 16
cert_test_block_3 137600 4 64 80 16
cert_test_block_3 137600 5 80 96 16
cert_test_block_3 137600 6 96 112 16
cert_test_block_3 137600 7 112 128 16
cert_test_block_3 137600 8 128 144 16
cert_test_block_3 137600 9 144 160 16
cert_test_block_3 137600 10 160 176 16
cert_test_block_3 137600 11 176 192 16
cert_test_block_3 137600 12 192 208 16
cert_test_block_3 137600 13 208 224 16
cert_test_block_3 137600 14 224 240 16
cert_test_block_3 137600 15 240 256 16
cert_test_block_3 137600 16 256 272 16
cert_test_block_3 137600 17 272 288 16
cert_test_block_3 137600 18 288 304 16
cert_test_block_3 137600 19 304 320 16
cert_test_block_3 137600 20 320 336 16
cert_test_block_3 137600 21 336 352 16
cert_test_block_3 137600 22 352 368 16
cert_test_block_3 137600 23 368 384 16
cert_test_block_3 137600 24 384 400 16
cert_test_block_3 137600 25 400 416 16
cert_test_block_3 137600 26 416 432 16
cert_test_block_3 137600 27 432 448 16
cert_test_block_3 137600 28 448 464 16
cert_test_block_3 137600 29 464 480 16
cert_test_block_3 137600 30 480 496 16
cert_test_block_3 137600 31 496 512 16
cert_test_block_3 137600 32 512 528 16
cert_test_block_3 137600 33 528 544 16
cert_test_block_3 137600 34 544 560 16
cert_test_block_3 137600 35 560 576 16
cert_test_block_3 137600 36 576 592 16
cert_test_block_3 137600 37 592 608 16
cert_test_block_3 137600 38 608 624 16
cert_test_block_3 137600 39 624 640 16
theorem test137600_complete : Interval test137600 0 640 :=
  (interval_append test137600 0 320 640
  (interval_append test137600 0 160 320
  (interval_append test137600 0 80 160
  (interval_append test137600 0 32 80
  (interval_append test137600 0 16 32
  test137600_block_0
  test137600_block_1)
  (interval_append test137600 32 48 80
  test137600_block_2
  (interval_append test137600 48 64 80
  test137600_block_3
  test137600_block_4)))
  (interval_append test137600 80 112 160
  (interval_append test137600 80 96 112
  test137600_block_5
  test137600_block_6)
  (interval_append test137600 112 128 160
  test137600_block_7
  (interval_append test137600 128 144 160
  test137600_block_8
  test137600_block_9))))
  (interval_append test137600 160 240 320
  (interval_append test137600 160 192 240
  (interval_append test137600 160 176 192
  test137600_block_10
  test137600_block_11)
  (interval_append test137600 192 208 240
  test137600_block_12
  (interval_append test137600 208 224 240
  test137600_block_13
  test137600_block_14)))
  (interval_append test137600 240 272 320
  (interval_append test137600 240 256 272
  test137600_block_15
  test137600_block_16)
  (interval_append test137600 272 288 320
  test137600_block_17
  (interval_append test137600 288 304 320
  test137600_block_18
  test137600_block_19)))))
  (interval_append test137600 320 480 640
  (interval_append test137600 320 400 480
  (interval_append test137600 320 352 400
  (interval_append test137600 320 336 352
  test137600_block_20
  test137600_block_21)
  (interval_append test137600 352 368 400
  test137600_block_22
  (interval_append test137600 368 384 400
  test137600_block_23
  test137600_block_24)))
  (interval_append test137600 400 432 480
  (interval_append test137600 400 416 432
  test137600_block_25
  test137600_block_26)
  (interval_append test137600 432 448 480
  test137600_block_27
  (interval_append test137600 448 464 480
  test137600_block_28
  test137600_block_29))))
  (interval_append test137600 480 560 640
  (interval_append test137600 480 512 560
  (interval_append test137600 480 496 512
  test137600_block_30
  test137600_block_31)
  (interval_append test137600 512 528 560
  test137600_block_32
  (interval_append test137600 528 544 560
  test137600_block_33
  test137600_block_34)))
  (interval_append test137600 560 592 640
  (interval_append test137600 560 576 592
  test137600_block_35
  test137600_block_36)
  (interval_append test137600 592 608 640
  test137600_block_37
  (interval_append test137600 608 624 640
  test137600_block_38
  test137600_block_39))))))
cert_nodeInterval_3 137600 138240
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 138240
cert_test_block_3 138240 0 0 16 16
cert_test_block_3 138240 1 16 32 16
cert_test_block_3 138240 2 32 48 16
cert_test_block_3 138240 3 48 64 16
cert_test_block_3 138240 4 64 80 16
cert_test_block_3 138240 5 80 96 16
cert_test_block_3 138240 6 96 112 16
cert_test_block_3 138240 7 112 128 16
cert_test_block_3 138240 8 128 144 16
cert_test_block_3 138240 9 144 160 16
cert_test_block_3 138240 10 160 176 16
cert_test_block_3 138240 11 176 192 16
cert_test_block_3 138240 12 192 208 16
cert_test_block_3 138240 13 208 224 16
cert_test_block_3 138240 14 224 240 16
cert_test_block_3 138240 15 240 256 16
cert_test_block_3 138240 16 256 272 16
cert_test_block_3 138240 17 272 288 16
cert_test_block_3 138240 18 288 304 16
cert_test_block_3 138240 19 304 320 16
cert_test_block_3 138240 20 320 336 16
cert_test_block_3 138240 21 336 352 16
cert_test_block_3 138240 22 352 368 16
cert_test_block_3 138240 23 368 384 16
cert_test_block_3 138240 24 384 400 16
cert_test_block_3 138240 25 400 416 16
cert_test_block_3 138240 26 416 432 16
cert_test_block_3 138240 27 432 448 16
cert_test_block_3 138240 28 448 464 16
cert_test_block_3 138240 29 464 480 16
cert_test_block_3 138240 30 480 496 16
cert_test_block_3 138240 31 496 512 16
cert_test_block_3 138240 32 512 528 16
cert_test_block_3 138240 33 528 544 16
cert_test_block_3 138240 34 544 560 16
cert_test_block_3 138240 35 560 576 16
cert_test_block_3 138240 36 576 592 16
cert_test_block_3 138240 37 592 608 16
cert_test_block_3 138240 38 608 624 16
cert_test_block_3 138240 39 624 640 16
theorem test138240_complete : Interval test138240 0 640 :=
  (interval_append test138240 0 320 640
  (interval_append test138240 0 160 320
  (interval_append test138240 0 80 160
  (interval_append test138240 0 32 80
  (interval_append test138240 0 16 32
  test138240_block_0
  test138240_block_1)
  (interval_append test138240 32 48 80
  test138240_block_2
  (interval_append test138240 48 64 80
  test138240_block_3
  test138240_block_4)))
  (interval_append test138240 80 112 160
  (interval_append test138240 80 96 112
  test138240_block_5
  test138240_block_6)
  (interval_append test138240 112 128 160
  test138240_block_7
  (interval_append test138240 128 144 160
  test138240_block_8
  test138240_block_9))))
  (interval_append test138240 160 240 320
  (interval_append test138240 160 192 240
  (interval_append test138240 160 176 192
  test138240_block_10
  test138240_block_11)
  (interval_append test138240 192 208 240
  test138240_block_12
  (interval_append test138240 208 224 240
  test138240_block_13
  test138240_block_14)))
  (interval_append test138240 240 272 320
  (interval_append test138240 240 256 272
  test138240_block_15
  test138240_block_16)
  (interval_append test138240 272 288 320
  test138240_block_17
  (interval_append test138240 288 304 320
  test138240_block_18
  test138240_block_19)))))
  (interval_append test138240 320 480 640
  (interval_append test138240 320 400 480
  (interval_append test138240 320 352 400
  (interval_append test138240 320 336 352
  test138240_block_20
  test138240_block_21)
  (interval_append test138240 352 368 400
  test138240_block_22
  (interval_append test138240 368 384 400
  test138240_block_23
  test138240_block_24)))
  (interval_append test138240 400 432 480
  (interval_append test138240 400 416 432
  test138240_block_25
  test138240_block_26)
  (interval_append test138240 432 448 480
  test138240_block_27
  (interval_append test138240 448 464 480
  test138240_block_28
  test138240_block_29))))
  (interval_append test138240 480 560 640
  (interval_append test138240 480 512 560
  (interval_append test138240 480 496 512
  test138240_block_30
  test138240_block_31)
  (interval_append test138240 512 528 560
  test138240_block_32
  (interval_append test138240 528 544 560
  test138240_block_33
  test138240_block_34)))
  (interval_append test138240 560 592 640
  (interval_append test138240 560 576 592
  test138240_block_35
  test138240_block_36)
  (interval_append test138240 592 608 640
  test138240_block_37
  (interval_append test138240 608 624 640
  test138240_block_38
  test138240_block_39))))))
cert_nodeInterval_3 138240 138880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 138880
cert_test_block_3 138880 0 0 16 16
cert_test_block_3 138880 1 16 32 16
cert_test_block_3 138880 2 32 48 16
cert_test_block_3 138880 3 48 64 16
cert_test_block_3 138880 4 64 80 16
cert_test_block_3 138880 5 80 96 16
cert_test_block_3 138880 6 96 112 16
cert_test_block_3 138880 7 112 128 16
cert_test_block_3 138880 8 128 144 16
cert_test_block_3 138880 9 144 160 16
cert_test_block_3 138880 10 160 176 16
cert_test_block_3 138880 11 176 192 16
cert_test_block_3 138880 12 192 208 16
cert_test_block_3 138880 13 208 224 16
cert_test_block_3 138880 14 224 240 16
cert_test_block_3 138880 15 240 256 16
cert_test_block_3 138880 16 256 272 16
cert_test_block_3 138880 17 272 288 16
cert_test_block_3 138880 18 288 304 16
cert_test_block_3 138880 19 304 320 16
cert_test_block_3 138880 20 320 336 16
cert_test_block_3 138880 21 336 352 16
cert_test_block_3 138880 22 352 368 16
cert_test_block_3 138880 23 368 384 16
cert_test_block_3 138880 24 384 400 16
cert_test_block_3 138880 25 400 416 16
cert_test_block_3 138880 26 416 432 16
cert_test_block_3 138880 27 432 448 16
cert_test_block_3 138880 28 448 464 16
cert_test_block_3 138880 29 464 480 16
cert_test_block_3 138880 30 480 496 16
cert_test_block_3 138880 31 496 512 16
cert_test_block_3 138880 32 512 528 16
cert_test_block_3 138880 33 528 544 16
cert_test_block_3 138880 34 544 560 16
cert_test_block_3 138880 35 560 576 16
cert_test_block_3 138880 36 576 592 16
cert_test_block_3 138880 37 592 608 16
cert_test_block_3 138880 38 608 624 16
cert_test_block_3 138880 39 624 640 16
theorem test138880_complete : Interval test138880 0 640 :=
  (interval_append test138880 0 320 640
  (interval_append test138880 0 160 320
  (interval_append test138880 0 80 160
  (interval_append test138880 0 32 80
  (interval_append test138880 0 16 32
  test138880_block_0
  test138880_block_1)
  (interval_append test138880 32 48 80
  test138880_block_2
  (interval_append test138880 48 64 80
  test138880_block_3
  test138880_block_4)))
  (interval_append test138880 80 112 160
  (interval_append test138880 80 96 112
  test138880_block_5
  test138880_block_6)
  (interval_append test138880 112 128 160
  test138880_block_7
  (interval_append test138880 128 144 160
  test138880_block_8
  test138880_block_9))))
  (interval_append test138880 160 240 320
  (interval_append test138880 160 192 240
  (interval_append test138880 160 176 192
  test138880_block_10
  test138880_block_11)
  (interval_append test138880 192 208 240
  test138880_block_12
  (interval_append test138880 208 224 240
  test138880_block_13
  test138880_block_14)))
  (interval_append test138880 240 272 320
  (interval_append test138880 240 256 272
  test138880_block_15
  test138880_block_16)
  (interval_append test138880 272 288 320
  test138880_block_17
  (interval_append test138880 288 304 320
  test138880_block_18
  test138880_block_19)))))
  (interval_append test138880 320 480 640
  (interval_append test138880 320 400 480
  (interval_append test138880 320 352 400
  (interval_append test138880 320 336 352
  test138880_block_20
  test138880_block_21)
  (interval_append test138880 352 368 400
  test138880_block_22
  (interval_append test138880 368 384 400
  test138880_block_23
  test138880_block_24)))
  (interval_append test138880 400 432 480
  (interval_append test138880 400 416 432
  test138880_block_25
  test138880_block_26)
  (interval_append test138880 432 448 480
  test138880_block_27
  (interval_append test138880 448 464 480
  test138880_block_28
  test138880_block_29))))
  (interval_append test138880 480 560 640
  (interval_append test138880 480 512 560
  (interval_append test138880 480 496 512
  test138880_block_30
  test138880_block_31)
  (interval_append test138880 512 528 560
  test138880_block_32
  (interval_append test138880 528 544 560
  test138880_block_33
  test138880_block_34)))
  (interval_append test138880 560 592 640
  (interval_append test138880 560 576 592
  test138880_block_35
  test138880_block_36)
  (interval_append test138880 592 608 640
  test138880_block_37
  (interval_append test138880 608 624 640
  test138880_block_38
  test138880_block_39))))))
cert_nodeInterval_3 138880 139520
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 139520
cert_test_block_3 139520 0 0 16 16
cert_test_block_3 139520 1 16 32 16
cert_test_block_3 139520 2 32 48 16
cert_test_block_3 139520 3 48 64 16
cert_test_block_3 139520 4 64 80 16
cert_test_block_3 139520 5 80 96 16
cert_test_block_3 139520 6 96 112 16
cert_test_block_3 139520 7 112 128 16
cert_test_block_3 139520 8 128 144 16
cert_test_block_3 139520 9 144 160 16
cert_test_block_3 139520 10 160 176 16
cert_test_block_3 139520 11 176 192 16
cert_test_block_3 139520 12 192 208 16
cert_test_block_3 139520 13 208 224 16
cert_test_block_3 139520 14 224 240 16
cert_test_block_3 139520 15 240 256 16
cert_test_block_3 139520 16 256 272 16
cert_test_block_3 139520 17 272 288 16
cert_test_block_3 139520 18 288 304 16
cert_test_block_3 139520 19 304 320 16
cert_test_block_3 139520 20 320 336 16
cert_test_block_3 139520 21 336 352 16
cert_test_block_3 139520 22 352 368 16
cert_test_block_3 139520 23 368 384 16
cert_test_block_3 139520 24 384 400 16
cert_test_block_3 139520 25 400 416 16
cert_test_block_3 139520 26 416 432 16
cert_test_block_3 139520 27 432 448 16
cert_test_block_3 139520 28 448 464 16
cert_test_block_3 139520 29 464 480 16
cert_test_block_3 139520 30 480 496 16
cert_test_block_3 139520 31 496 512 16
cert_test_block_3 139520 32 512 528 16
cert_test_block_3 139520 33 528 544 16
cert_test_block_3 139520 34 544 560 16
cert_test_block_3 139520 35 560 576 16
cert_test_block_3 139520 36 576 592 16
cert_test_block_3 139520 37 592 608 16
cert_test_block_3 139520 38 608 624 16
cert_test_block_3 139520 39 624 640 16
theorem test139520_complete : Interval test139520 0 640 :=
  (interval_append test139520 0 320 640
  (interval_append test139520 0 160 320
  (interval_append test139520 0 80 160
  (interval_append test139520 0 32 80
  (interval_append test139520 0 16 32
  test139520_block_0
  test139520_block_1)
  (interval_append test139520 32 48 80
  test139520_block_2
  (interval_append test139520 48 64 80
  test139520_block_3
  test139520_block_4)))
  (interval_append test139520 80 112 160
  (interval_append test139520 80 96 112
  test139520_block_5
  test139520_block_6)
  (interval_append test139520 112 128 160
  test139520_block_7
  (interval_append test139520 128 144 160
  test139520_block_8
  test139520_block_9))))
  (interval_append test139520 160 240 320
  (interval_append test139520 160 192 240
  (interval_append test139520 160 176 192
  test139520_block_10
  test139520_block_11)
  (interval_append test139520 192 208 240
  test139520_block_12
  (interval_append test139520 208 224 240
  test139520_block_13
  test139520_block_14)))
  (interval_append test139520 240 272 320
  (interval_append test139520 240 256 272
  test139520_block_15
  test139520_block_16)
  (interval_append test139520 272 288 320
  test139520_block_17
  (interval_append test139520 288 304 320
  test139520_block_18
  test139520_block_19)))))
  (interval_append test139520 320 480 640
  (interval_append test139520 320 400 480
  (interval_append test139520 320 352 400
  (interval_append test139520 320 336 352
  test139520_block_20
  test139520_block_21)
  (interval_append test139520 352 368 400
  test139520_block_22
  (interval_append test139520 368 384 400
  test139520_block_23
  test139520_block_24)))
  (interval_append test139520 400 432 480
  (interval_append test139520 400 416 432
  test139520_block_25
  test139520_block_26)
  (interval_append test139520 432 448 480
  test139520_block_27
  (interval_append test139520 448 464 480
  test139520_block_28
  test139520_block_29))))
  (interval_append test139520 480 560 640
  (interval_append test139520 480 512 560
  (interval_append test139520 480 496 512
  test139520_block_30
  test139520_block_31)
  (interval_append test139520 512 528 560
  test139520_block_32
  (interval_append test139520 528 544 560
  test139520_block_33
  test139520_block_34)))
  (interval_append test139520 560 592 640
  (interval_append test139520 560 576 592
  test139520_block_35
  test139520_block_36)
  (interval_append test139520 592 608 640
  test139520_block_37
  (interval_append test139520 608 624 640
  test139520_block_38
  test139520_block_39))))))
cert_nodeInterval_3 139520 140160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 140160
cert_test_block_3 140160 0 0 16 16
cert_test_block_3 140160 1 16 32 16
cert_test_block_3 140160 2 32 48 16
cert_test_block_3 140160 3 48 64 16
cert_test_block_3 140160 4 64 80 16
cert_test_block_3 140160 5 80 96 16
cert_test_block_3 140160 6 96 112 16
cert_test_block_3 140160 7 112 128 16
cert_test_block_3 140160 8 128 144 16
cert_test_block_3 140160 9 144 160 16
cert_test_block_3 140160 10 160 176 16
cert_test_block_3 140160 11 176 192 16
cert_test_block_3 140160 12 192 208 16
cert_test_block_3 140160 13 208 224 16
cert_test_block_3 140160 14 224 240 16
cert_test_block_3 140160 15 240 256 16
cert_test_block_3 140160 16 256 272 16
cert_test_block_3 140160 17 272 288 16
cert_test_block_3 140160 18 288 304 16
cert_test_block_3 140160 19 304 320 16
cert_test_block_3 140160 20 320 336 16
cert_test_block_3 140160 21 336 352 16
cert_test_block_3 140160 22 352 368 16
cert_test_block_3 140160 23 368 384 16
cert_test_block_3 140160 24 384 400 16
cert_test_block_3 140160 25 400 416 16
cert_test_block_3 140160 26 416 432 16
cert_test_block_3 140160 27 432 448 16
cert_test_block_3 140160 28 448 464 16
cert_test_block_3 140160 29 464 480 16
cert_test_block_3 140160 30 480 496 16
cert_test_block_3 140160 31 496 512 16
cert_test_block_3 140160 32 512 528 16
cert_test_block_3 140160 33 528 544 16
cert_test_block_3 140160 34 544 560 16
cert_test_block_3 140160 35 560 576 16
cert_test_block_3 140160 36 576 592 16
cert_test_block_3 140160 37 592 608 16
cert_test_block_3 140160 38 608 624 16
cert_test_block_3 140160 39 624 640 16
theorem test140160_complete : Interval test140160 0 640 :=
  (interval_append test140160 0 320 640
  (interval_append test140160 0 160 320
  (interval_append test140160 0 80 160
  (interval_append test140160 0 32 80
  (interval_append test140160 0 16 32
  test140160_block_0
  test140160_block_1)
  (interval_append test140160 32 48 80
  test140160_block_2
  (interval_append test140160 48 64 80
  test140160_block_3
  test140160_block_4)))
  (interval_append test140160 80 112 160
  (interval_append test140160 80 96 112
  test140160_block_5
  test140160_block_6)
  (interval_append test140160 112 128 160
  test140160_block_7
  (interval_append test140160 128 144 160
  test140160_block_8
  test140160_block_9))))
  (interval_append test140160 160 240 320
  (interval_append test140160 160 192 240
  (interval_append test140160 160 176 192
  test140160_block_10
  test140160_block_11)
  (interval_append test140160 192 208 240
  test140160_block_12
  (interval_append test140160 208 224 240
  test140160_block_13
  test140160_block_14)))
  (interval_append test140160 240 272 320
  (interval_append test140160 240 256 272
  test140160_block_15
  test140160_block_16)
  (interval_append test140160 272 288 320
  test140160_block_17
  (interval_append test140160 288 304 320
  test140160_block_18
  test140160_block_19)))))
  (interval_append test140160 320 480 640
  (interval_append test140160 320 400 480
  (interval_append test140160 320 352 400
  (interval_append test140160 320 336 352
  test140160_block_20
  test140160_block_21)
  (interval_append test140160 352 368 400
  test140160_block_22
  (interval_append test140160 368 384 400
  test140160_block_23
  test140160_block_24)))
  (interval_append test140160 400 432 480
  (interval_append test140160 400 416 432
  test140160_block_25
  test140160_block_26)
  (interval_append test140160 432 448 480
  test140160_block_27
  (interval_append test140160 448 464 480
  test140160_block_28
  test140160_block_29))))
  (interval_append test140160 480 560 640
  (interval_append test140160 480 512 560
  (interval_append test140160 480 496 512
  test140160_block_30
  test140160_block_31)
  (interval_append test140160 512 528 560
  test140160_block_32
  (interval_append test140160 528 544 560
  test140160_block_33
  test140160_block_34)))
  (interval_append test140160 560 592 640
  (interval_append test140160 560 576 592
  test140160_block_35
  test140160_block_36)
  (interval_append test140160 592 608 640
  test140160_block_37
  (interval_append test140160 608 624 640
  test140160_block_38
  test140160_block_39))))))
cert_nodeInterval_3 140160 140800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 140800
cert_test_block_3 140800 0 0 16 16
cert_test_block_3 140800 1 16 32 16
cert_test_block_3 140800 2 32 48 16
cert_test_block_3 140800 3 48 64 16
cert_test_block_3 140800 4 64 80 16
cert_test_block_3 140800 5 80 96 16
cert_test_block_3 140800 6 96 112 16
cert_test_block_3 140800 7 112 128 16
cert_test_block_3 140800 8 128 144 16
cert_test_block_3 140800 9 144 160 16
cert_test_block_3 140800 10 160 176 16
cert_test_block_3 140800 11 176 192 16
cert_test_block_3 140800 12 192 208 16
cert_test_block_3 140800 13 208 224 16
cert_test_block_3 140800 14 224 240 16
cert_test_block_3 140800 15 240 256 16
cert_test_block_3 140800 16 256 272 16
cert_test_block_3 140800 17 272 288 16
cert_test_block_3 140800 18 288 304 16
cert_test_block_3 140800 19 304 320 16
cert_test_block_3 140800 20 320 336 16
cert_test_block_3 140800 21 336 352 16
cert_test_block_3 140800 22 352 368 16
cert_test_block_3 140800 23 368 384 16
cert_test_block_3 140800 24 384 400 16
cert_test_block_3 140800 25 400 416 16
cert_test_block_3 140800 26 416 432 16
cert_test_block_3 140800 27 432 448 16
cert_test_block_3 140800 28 448 464 16
cert_test_block_3 140800 29 464 480 16
cert_test_block_3 140800 30 480 496 16
cert_test_block_3 140800 31 496 512 16
cert_test_block_3 140800 32 512 528 16
cert_test_block_3 140800 33 528 544 16
cert_test_block_3 140800 34 544 560 16
cert_test_block_3 140800 35 560 576 16
cert_test_block_3 140800 36 576 592 16
cert_test_block_3 140800 37 592 608 16
cert_test_block_3 140800 38 608 624 16
cert_test_block_3 140800 39 624 640 16
theorem test140800_complete : Interval test140800 0 640 :=
  (interval_append test140800 0 320 640
  (interval_append test140800 0 160 320
  (interval_append test140800 0 80 160
  (interval_append test140800 0 32 80
  (interval_append test140800 0 16 32
  test140800_block_0
  test140800_block_1)
  (interval_append test140800 32 48 80
  test140800_block_2
  (interval_append test140800 48 64 80
  test140800_block_3
  test140800_block_4)))
  (interval_append test140800 80 112 160
  (interval_append test140800 80 96 112
  test140800_block_5
  test140800_block_6)
  (interval_append test140800 112 128 160
  test140800_block_7
  (interval_append test140800 128 144 160
  test140800_block_8
  test140800_block_9))))
  (interval_append test140800 160 240 320
  (interval_append test140800 160 192 240
  (interval_append test140800 160 176 192
  test140800_block_10
  test140800_block_11)
  (interval_append test140800 192 208 240
  test140800_block_12
  (interval_append test140800 208 224 240
  test140800_block_13
  test140800_block_14)))
  (interval_append test140800 240 272 320
  (interval_append test140800 240 256 272
  test140800_block_15
  test140800_block_16)
  (interval_append test140800 272 288 320
  test140800_block_17
  (interval_append test140800 288 304 320
  test140800_block_18
  test140800_block_19)))))
  (interval_append test140800 320 480 640
  (interval_append test140800 320 400 480
  (interval_append test140800 320 352 400
  (interval_append test140800 320 336 352
  test140800_block_20
  test140800_block_21)
  (interval_append test140800 352 368 400
  test140800_block_22
  (interval_append test140800 368 384 400
  test140800_block_23
  test140800_block_24)))
  (interval_append test140800 400 432 480
  (interval_append test140800 400 416 432
  test140800_block_25
  test140800_block_26)
  (interval_append test140800 432 448 480
  test140800_block_27
  (interval_append test140800 448 464 480
  test140800_block_28
  test140800_block_29))))
  (interval_append test140800 480 560 640
  (interval_append test140800 480 512 560
  (interval_append test140800 480 496 512
  test140800_block_30
  test140800_block_31)
  (interval_append test140800 512 528 560
  test140800_block_32
  (interval_append test140800 528 544 560
  test140800_block_33
  test140800_block_34)))
  (interval_append test140800 560 592 640
  (interval_append test140800 560 576 592
  test140800_block_35
  test140800_block_36)
  (interval_append test140800 592 608 640
  test140800_block_37
  (interval_append test140800 608 624 640
  test140800_block_38
  test140800_block_39))))))
cert_nodeInterval_3 140800 141440
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 141440
cert_test_block_3 141440 0 0 16 16
cert_test_block_3 141440 1 16 32 16
cert_test_block_3 141440 2 32 48 16
cert_test_block_3 141440 3 48 64 16
cert_test_block_3 141440 4 64 80 16
cert_test_block_3 141440 5 80 96 16
cert_test_block_3 141440 6 96 112 16
cert_test_block_3 141440 7 112 128 16
cert_test_block_3 141440 8 128 144 16
cert_test_block_3 141440 9 144 160 16
cert_test_block_3 141440 10 160 176 16
cert_test_block_3 141440 11 176 192 16
cert_test_block_3 141440 12 192 208 16
cert_test_block_3 141440 13 208 224 16
cert_test_block_3 141440 14 224 240 16
cert_test_block_3 141440 15 240 256 16
cert_test_block_3 141440 16 256 272 16
cert_test_block_3 141440 17 272 288 16
cert_test_block_3 141440 18 288 304 16
cert_test_block_3 141440 19 304 320 16
cert_test_block_3 141440 20 320 336 16
cert_test_block_3 141440 21 336 352 16
cert_test_block_3 141440 22 352 368 16
cert_test_block_3 141440 23 368 384 16
cert_test_block_3 141440 24 384 400 16
cert_test_block_3 141440 25 400 416 16
cert_test_block_3 141440 26 416 432 16
cert_test_block_3 141440 27 432 448 16
cert_test_block_3 141440 28 448 464 16
cert_test_block_3 141440 29 464 480 16
cert_test_block_3 141440 30 480 496 16
cert_test_block_3 141440 31 496 512 16
cert_test_block_3 141440 32 512 528 16
cert_test_block_3 141440 33 528 544 16
cert_test_block_3 141440 34 544 560 16
cert_test_block_3 141440 35 560 576 16
cert_test_block_3 141440 36 576 592 16
cert_test_block_3 141440 37 592 608 16
cert_test_block_3 141440 38 608 624 16
cert_test_block_3 141440 39 624 640 16
theorem test141440_complete : Interval test141440 0 640 :=
  (interval_append test141440 0 320 640
  (interval_append test141440 0 160 320
  (interval_append test141440 0 80 160
  (interval_append test141440 0 32 80
  (interval_append test141440 0 16 32
  test141440_block_0
  test141440_block_1)
  (interval_append test141440 32 48 80
  test141440_block_2
  (interval_append test141440 48 64 80
  test141440_block_3
  test141440_block_4)))
  (interval_append test141440 80 112 160
  (interval_append test141440 80 96 112
  test141440_block_5
  test141440_block_6)
  (interval_append test141440 112 128 160
  test141440_block_7
  (interval_append test141440 128 144 160
  test141440_block_8
  test141440_block_9))))
  (interval_append test141440 160 240 320
  (interval_append test141440 160 192 240
  (interval_append test141440 160 176 192
  test141440_block_10
  test141440_block_11)
  (interval_append test141440 192 208 240
  test141440_block_12
  (interval_append test141440 208 224 240
  test141440_block_13
  test141440_block_14)))
  (interval_append test141440 240 272 320
  (interval_append test141440 240 256 272
  test141440_block_15
  test141440_block_16)
  (interval_append test141440 272 288 320
  test141440_block_17
  (interval_append test141440 288 304 320
  test141440_block_18
  test141440_block_19)))))
  (interval_append test141440 320 480 640
  (interval_append test141440 320 400 480
  (interval_append test141440 320 352 400
  (interval_append test141440 320 336 352
  test141440_block_20
  test141440_block_21)
  (interval_append test141440 352 368 400
  test141440_block_22
  (interval_append test141440 368 384 400
  test141440_block_23
  test141440_block_24)))
  (interval_append test141440 400 432 480
  (interval_append test141440 400 416 432
  test141440_block_25
  test141440_block_26)
  (interval_append test141440 432 448 480
  test141440_block_27
  (interval_append test141440 448 464 480
  test141440_block_28
  test141440_block_29))))
  (interval_append test141440 480 560 640
  (interval_append test141440 480 512 560
  (interval_append test141440 480 496 512
  test141440_block_30
  test141440_block_31)
  (interval_append test141440 512 528 560
  test141440_block_32
  (interval_append test141440 528 544 560
  test141440_block_33
  test141440_block_34)))
  (interval_append test141440 560 592 640
  (interval_append test141440 560 576 592
  test141440_block_35
  test141440_block_36)
  (interval_append test141440 592 608 640
  test141440_block_37
  (interval_append test141440 608 624 640
  test141440_block_38
  test141440_block_39))))))
cert_nodeInterval_3 141440 142080
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 142080
cert_test_block_3 142080 0 0 16 16
cert_test_block_3 142080 1 16 32 16
cert_test_block_3 142080 2 32 48 16
cert_test_block_3 142080 3 48 64 16
cert_test_block_3 142080 4 64 80 16
cert_test_block_3 142080 5 80 96 16
cert_test_block_3 142080 6 96 112 16
cert_test_block_3 142080 7 112 128 16
cert_test_block_3 142080 8 128 144 16
cert_test_block_3 142080 9 144 160 16
cert_test_block_3 142080 10 160 176 16
cert_test_block_3 142080 11 176 192 16
cert_test_block_3 142080 12 192 208 16
cert_test_block_3 142080 13 208 224 16
cert_test_block_3 142080 14 224 240 16
cert_test_block_3 142080 15 240 256 16
cert_test_block_3 142080 16 256 272 16
cert_test_block_3 142080 17 272 288 16
cert_test_block_3 142080 18 288 304 16
cert_test_block_3 142080 19 304 320 16
cert_test_block_3 142080 20 320 336 16
cert_test_block_3 142080 21 336 352 16
cert_test_block_3 142080 22 352 368 16
cert_test_block_3 142080 23 368 384 16
cert_test_block_3 142080 24 384 400 16
cert_test_block_3 142080 25 400 416 16
cert_test_block_3 142080 26 416 432 16
cert_test_block_3 142080 27 432 448 16
cert_test_block_3 142080 28 448 464 16
cert_test_block_3 142080 29 464 480 16
cert_test_block_3 142080 30 480 496 16
cert_test_block_3 142080 31 496 512 16
cert_test_block_3 142080 32 512 528 16
cert_test_block_3 142080 33 528 544 16
cert_test_block_3 142080 34 544 560 16
cert_test_block_3 142080 35 560 576 16
cert_test_block_3 142080 36 576 592 16
cert_test_block_3 142080 37 592 608 16
cert_test_block_3 142080 38 608 624 16
cert_test_block_3 142080 39 624 640 16
theorem test142080_complete : Interval test142080 0 640 :=
  (interval_append test142080 0 320 640
  (interval_append test142080 0 160 320
  (interval_append test142080 0 80 160
  (interval_append test142080 0 32 80
  (interval_append test142080 0 16 32
  test142080_block_0
  test142080_block_1)
  (interval_append test142080 32 48 80
  test142080_block_2
  (interval_append test142080 48 64 80
  test142080_block_3
  test142080_block_4)))
  (interval_append test142080 80 112 160
  (interval_append test142080 80 96 112
  test142080_block_5
  test142080_block_6)
  (interval_append test142080 112 128 160
  test142080_block_7
  (interval_append test142080 128 144 160
  test142080_block_8
  test142080_block_9))))
  (interval_append test142080 160 240 320
  (interval_append test142080 160 192 240
  (interval_append test142080 160 176 192
  test142080_block_10
  test142080_block_11)
  (interval_append test142080 192 208 240
  test142080_block_12
  (interval_append test142080 208 224 240
  test142080_block_13
  test142080_block_14)))
  (interval_append test142080 240 272 320
  (interval_append test142080 240 256 272
  test142080_block_15
  test142080_block_16)
  (interval_append test142080 272 288 320
  test142080_block_17
  (interval_append test142080 288 304 320
  test142080_block_18
  test142080_block_19)))))
  (interval_append test142080 320 480 640
  (interval_append test142080 320 400 480
  (interval_append test142080 320 352 400
  (interval_append test142080 320 336 352
  test142080_block_20
  test142080_block_21)
  (interval_append test142080 352 368 400
  test142080_block_22
  (interval_append test142080 368 384 400
  test142080_block_23
  test142080_block_24)))
  (interval_append test142080 400 432 480
  (interval_append test142080 400 416 432
  test142080_block_25
  test142080_block_26)
  (interval_append test142080 432 448 480
  test142080_block_27
  (interval_append test142080 448 464 480
  test142080_block_28
  test142080_block_29))))
  (interval_append test142080 480 560 640
  (interval_append test142080 480 512 560
  (interval_append test142080 480 496 512
  test142080_block_30
  test142080_block_31)
  (interval_append test142080 512 528 560
  test142080_block_32
  (interval_append test142080 528 544 560
  test142080_block_33
  test142080_block_34)))
  (interval_append test142080 560 592 640
  (interval_append test142080 560 576 592
  test142080_block_35
  test142080_block_36)
  (interval_append test142080 592 608 640
  test142080_block_37
  (interval_append test142080 608 624 640
  test142080_block_38
  test142080_block_39))))))
cert_nodeInterval_3 142080 142720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 142720
cert_test_block_3 142720 0 0 16 16
cert_test_block_3 142720 1 16 32 16
cert_test_block_3 142720 2 32 48 16
cert_test_block_3 142720 3 48 64 16
cert_test_block_3 142720 4 64 80 16
cert_test_block_3 142720 5 80 96 16
cert_test_block_3 142720 6 96 112 16
cert_test_block_3 142720 7 112 128 16
cert_test_block_3 142720 8 128 144 16
cert_test_block_3 142720 9 144 160 16
cert_test_block_3 142720 10 160 176 16
cert_test_block_3 142720 11 176 192 16
cert_test_block_3 142720 12 192 208 16
cert_test_block_3 142720 13 208 224 16
cert_test_block_3 142720 14 224 240 16
cert_test_block_3 142720 15 240 256 16
cert_test_block_3 142720 16 256 272 16
cert_test_block_3 142720 17 272 288 16
cert_test_block_3 142720 18 288 304 16
cert_test_block_3 142720 19 304 320 16
cert_test_block_3 142720 20 320 336 16
cert_test_block_3 142720 21 336 352 16
cert_test_block_3 142720 22 352 368 16
cert_test_block_3 142720 23 368 384 16
cert_test_block_3 142720 24 384 400 16
cert_test_block_3 142720 25 400 416 16
cert_test_block_3 142720 26 416 432 16
cert_test_block_3 142720 27 432 448 16
cert_test_block_3 142720 28 448 464 16
cert_test_block_3 142720 29 464 480 16
cert_test_block_3 142720 30 480 496 16
cert_test_block_3 142720 31 496 512 16
cert_test_block_3 142720 32 512 528 16
cert_test_block_3 142720 33 528 544 16
cert_test_block_3 142720 34 544 560 16
cert_test_block_3 142720 35 560 576 16
cert_test_block_3 142720 36 576 592 16
cert_test_block_3 142720 37 592 608 16
cert_test_block_3 142720 38 608 624 16
cert_test_block_3 142720 39 624 640 16
theorem test142720_complete : Interval test142720 0 640 :=
  (interval_append test142720 0 320 640
  (interval_append test142720 0 160 320
  (interval_append test142720 0 80 160
  (interval_append test142720 0 32 80
  (interval_append test142720 0 16 32
  test142720_block_0
  test142720_block_1)
  (interval_append test142720 32 48 80
  test142720_block_2
  (interval_append test142720 48 64 80
  test142720_block_3
  test142720_block_4)))
  (interval_append test142720 80 112 160
  (interval_append test142720 80 96 112
  test142720_block_5
  test142720_block_6)
  (interval_append test142720 112 128 160
  test142720_block_7
  (interval_append test142720 128 144 160
  test142720_block_8
  test142720_block_9))))
  (interval_append test142720 160 240 320
  (interval_append test142720 160 192 240
  (interval_append test142720 160 176 192
  test142720_block_10
  test142720_block_11)
  (interval_append test142720 192 208 240
  test142720_block_12
  (interval_append test142720 208 224 240
  test142720_block_13
  test142720_block_14)))
  (interval_append test142720 240 272 320
  (interval_append test142720 240 256 272
  test142720_block_15
  test142720_block_16)
  (interval_append test142720 272 288 320
  test142720_block_17
  (interval_append test142720 288 304 320
  test142720_block_18
  test142720_block_19)))))
  (interval_append test142720 320 480 640
  (interval_append test142720 320 400 480
  (interval_append test142720 320 352 400
  (interval_append test142720 320 336 352
  test142720_block_20
  test142720_block_21)
  (interval_append test142720 352 368 400
  test142720_block_22
  (interval_append test142720 368 384 400
  test142720_block_23
  test142720_block_24)))
  (interval_append test142720 400 432 480
  (interval_append test142720 400 416 432
  test142720_block_25
  test142720_block_26)
  (interval_append test142720 432 448 480
  test142720_block_27
  (interval_append test142720 448 464 480
  test142720_block_28
  test142720_block_29))))
  (interval_append test142720 480 560 640
  (interval_append test142720 480 512 560
  (interval_append test142720 480 496 512
  test142720_block_30
  test142720_block_31)
  (interval_append test142720 512 528 560
  test142720_block_32
  (interval_append test142720 528 544 560
  test142720_block_33
  test142720_block_34)))
  (interval_append test142720 560 592 640
  (interval_append test142720 560 576 592
  test142720_block_35
  test142720_block_36)
  (interval_append test142720 592 608 640
  test142720_block_37
  (interval_append test142720 608 624 640
  test142720_block_38
  test142720_block_39))))))
cert_nodeInterval_3 142720 143360
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 143360
cert_test_block_3 143360 0 0 16 16
cert_test_block_3 143360 1 16 32 16
cert_test_block_3 143360 2 32 48 16
cert_test_block_3 143360 3 48 64 16
cert_test_block_3 143360 4 64 80 16
cert_test_block_3 143360 5 80 96 16
cert_test_block_3 143360 6 96 112 16
cert_test_block_3 143360 7 112 128 16
cert_test_block_3 143360 8 128 144 16
cert_test_block_3 143360 9 144 160 16
cert_test_block_3 143360 10 160 176 16
cert_test_block_3 143360 11 176 192 16
cert_test_block_3 143360 12 192 208 16
cert_test_block_3 143360 13 208 224 16
cert_test_block_3 143360 14 224 240 16
cert_test_block_3 143360 15 240 256 16
cert_test_block_3 143360 16 256 272 16
cert_test_block_3 143360 17 272 288 16
cert_test_block_3 143360 18 288 304 16
cert_test_block_3 143360 19 304 320 16
cert_test_block_3 143360 20 320 336 16
cert_test_block_3 143360 21 336 352 16
cert_test_block_3 143360 22 352 368 16
cert_test_block_3 143360 23 368 384 16
cert_test_block_3 143360 24 384 400 16
cert_test_block_3 143360 25 400 416 16
cert_test_block_3 143360 26 416 432 16
cert_test_block_3 143360 27 432 448 16
cert_test_block_3 143360 28 448 464 16
cert_test_block_3 143360 29 464 480 16
cert_test_block_3 143360 30 480 496 16
cert_test_block_3 143360 31 496 512 16
cert_test_block_3 143360 32 512 528 16
cert_test_block_3 143360 33 528 544 16
cert_test_block_3 143360 34 544 560 16
cert_test_block_3 143360 35 560 576 16
cert_test_block_3 143360 36 576 592 16
cert_test_block_3 143360 37 592 608 16
cert_test_block_3 143360 38 608 624 16
cert_test_block_3 143360 39 624 640 16
theorem test143360_complete : Interval test143360 0 640 :=
  (interval_append test143360 0 320 640
  (interval_append test143360 0 160 320
  (interval_append test143360 0 80 160
  (interval_append test143360 0 32 80
  (interval_append test143360 0 16 32
  test143360_block_0
  test143360_block_1)
  (interval_append test143360 32 48 80
  test143360_block_2
  (interval_append test143360 48 64 80
  test143360_block_3
  test143360_block_4)))
  (interval_append test143360 80 112 160
  (interval_append test143360 80 96 112
  test143360_block_5
  test143360_block_6)
  (interval_append test143360 112 128 160
  test143360_block_7
  (interval_append test143360 128 144 160
  test143360_block_8
  test143360_block_9))))
  (interval_append test143360 160 240 320
  (interval_append test143360 160 192 240
  (interval_append test143360 160 176 192
  test143360_block_10
  test143360_block_11)
  (interval_append test143360 192 208 240
  test143360_block_12
  (interval_append test143360 208 224 240
  test143360_block_13
  test143360_block_14)))
  (interval_append test143360 240 272 320
  (interval_append test143360 240 256 272
  test143360_block_15
  test143360_block_16)
  (interval_append test143360 272 288 320
  test143360_block_17
  (interval_append test143360 288 304 320
  test143360_block_18
  test143360_block_19)))))
  (interval_append test143360 320 480 640
  (interval_append test143360 320 400 480
  (interval_append test143360 320 352 400
  (interval_append test143360 320 336 352
  test143360_block_20
  test143360_block_21)
  (interval_append test143360 352 368 400
  test143360_block_22
  (interval_append test143360 368 384 400
  test143360_block_23
  test143360_block_24)))
  (interval_append test143360 400 432 480
  (interval_append test143360 400 416 432
  test143360_block_25
  test143360_block_26)
  (interval_append test143360 432 448 480
  test143360_block_27
  (interval_append test143360 448 464 480
  test143360_block_28
  test143360_block_29))))
  (interval_append test143360 480 560 640
  (interval_append test143360 480 512 560
  (interval_append test143360 480 496 512
  test143360_block_30
  test143360_block_31)
  (interval_append test143360 512 528 560
  test143360_block_32
  (interval_append test143360 528 544 560
  test143360_block_33
  test143360_block_34)))
  (interval_append test143360 560 592 640
  (interval_append test143360 560 576 592
  test143360_block_35
  test143360_block_36)
  (interval_append test143360 592 608 640
  test143360_block_37
  (interval_append test143360 608 624 640
  test143360_block_38
  test143360_block_39))))))
cert_nodeInterval_3 143360 144000
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 144000
cert_test_block_3 144000 0 0 16 16
cert_test_block_3 144000 1 16 32 16
cert_test_block_3 144000 2 32 48 16
cert_test_block_3 144000 3 48 64 16
cert_test_block_3 144000 4 64 80 16
cert_test_block_3 144000 5 80 96 16
cert_test_block_3 144000 6 96 112 16
cert_test_block_3 144000 7 112 128 16
cert_test_block_3 144000 8 128 144 16
cert_test_block_3 144000 9 144 160 16
cert_test_block_3 144000 10 160 176 16
cert_test_block_3 144000 11 176 192 16
cert_test_block_3 144000 12 192 208 16
cert_test_block_3 144000 13 208 224 16
cert_test_block_3 144000 14 224 240 16
cert_test_block_3 144000 15 240 256 16
cert_test_block_3 144000 16 256 272 16
cert_test_block_3 144000 17 272 288 16
cert_test_block_3 144000 18 288 304 16
cert_test_block_3 144000 19 304 320 16
cert_test_block_3 144000 20 320 336 16
cert_test_block_3 144000 21 336 352 16
cert_test_block_3 144000 22 352 368 16
cert_test_block_3 144000 23 368 384 16
cert_test_block_3 144000 24 384 400 16
cert_test_block_3 144000 25 400 416 16
cert_test_block_3 144000 26 416 432 16
cert_test_block_3 144000 27 432 448 16
cert_test_block_3 144000 28 448 464 16
cert_test_block_3 144000 29 464 480 16
cert_test_block_3 144000 30 480 496 16
cert_test_block_3 144000 31 496 512 16
cert_test_block_3 144000 32 512 528 16
cert_test_block_3 144000 33 528 544 16
cert_test_block_3 144000 34 544 560 16
cert_test_block_3 144000 35 560 576 16
cert_test_block_3 144000 36 576 592 16
cert_test_block_3 144000 37 592 608 16
cert_test_block_3 144000 38 608 624 16
cert_test_block_3 144000 39 624 640 16
theorem test144000_complete : Interval test144000 0 640 :=
  (interval_append test144000 0 320 640
  (interval_append test144000 0 160 320
  (interval_append test144000 0 80 160
  (interval_append test144000 0 32 80
  (interval_append test144000 0 16 32
  test144000_block_0
  test144000_block_1)
  (interval_append test144000 32 48 80
  test144000_block_2
  (interval_append test144000 48 64 80
  test144000_block_3
  test144000_block_4)))
  (interval_append test144000 80 112 160
  (interval_append test144000 80 96 112
  test144000_block_5
  test144000_block_6)
  (interval_append test144000 112 128 160
  test144000_block_7
  (interval_append test144000 128 144 160
  test144000_block_8
  test144000_block_9))))
  (interval_append test144000 160 240 320
  (interval_append test144000 160 192 240
  (interval_append test144000 160 176 192
  test144000_block_10
  test144000_block_11)
  (interval_append test144000 192 208 240
  test144000_block_12
  (interval_append test144000 208 224 240
  test144000_block_13
  test144000_block_14)))
  (interval_append test144000 240 272 320
  (interval_append test144000 240 256 272
  test144000_block_15
  test144000_block_16)
  (interval_append test144000 272 288 320
  test144000_block_17
  (interval_append test144000 288 304 320
  test144000_block_18
  test144000_block_19)))))
  (interval_append test144000 320 480 640
  (interval_append test144000 320 400 480
  (interval_append test144000 320 352 400
  (interval_append test144000 320 336 352
  test144000_block_20
  test144000_block_21)
  (interval_append test144000 352 368 400
  test144000_block_22
  (interval_append test144000 368 384 400
  test144000_block_23
  test144000_block_24)))
  (interval_append test144000 400 432 480
  (interval_append test144000 400 416 432
  test144000_block_25
  test144000_block_26)
  (interval_append test144000 432 448 480
  test144000_block_27
  (interval_append test144000 448 464 480
  test144000_block_28
  test144000_block_29))))
  (interval_append test144000 480 560 640
  (interval_append test144000 480 512 560
  (interval_append test144000 480 496 512
  test144000_block_30
  test144000_block_31)
  (interval_append test144000 512 528 560
  test144000_block_32
  (interval_append test144000 528 544 560
  test144000_block_33
  test144000_block_34)))
  (interval_append test144000 560 592 640
  (interval_append test144000 560 576 592
  test144000_block_35
  test144000_block_36)
  (interval_append test144000 592 608 640
  test144000_block_37
  (interval_append test144000 608 624 640
  test144000_block_38
  test144000_block_39))))))
cert_nodeInterval_3 144000 144640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
