module
prelude
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
def test128000 (i : Nat) := nodeTest (i+128000)
theorem test128000_block_0 : Interval test128000 0 16 :=
  interval_of_check test128000 0 16 (by decide +kernel)

theorem test128000_block_1 : Interval test128000 16 32 :=
  interval_of_check test128000 16 16 (by decide +kernel)

theorem test128000_block_2 : Interval test128000 32 48 :=
  interval_of_check test128000 32 16 (by decide +kernel)

theorem test128000_block_3 : Interval test128000 48 64 :=
  interval_of_check test128000 48 16 (by decide +kernel)

theorem test128000_block_4 : Interval test128000 64 80 :=
  interval_of_check test128000 64 16 (by decide +kernel)

theorem test128000_block_5 : Interval test128000 80 96 :=
  interval_of_check test128000 80 16 (by decide +kernel)

theorem test128000_block_6 : Interval test128000 96 112 :=
  interval_of_check test128000 96 16 (by decide +kernel)

theorem test128000_block_7 : Interval test128000 112 128 :=
  interval_of_check test128000 112 16 (by decide +kernel)

theorem test128000_block_8 : Interval test128000 128 144 :=
  interval_of_check test128000 128 16 (by decide +kernel)

theorem test128000_block_9 : Interval test128000 144 160 :=
  interval_of_check test128000 144 16 (by decide +kernel)

theorem test128000_block_10 : Interval test128000 160 176 :=
  interval_of_check test128000 160 16 (by decide +kernel)

theorem test128000_block_11 : Interval test128000 176 192 :=
  interval_of_check test128000 176 16 (by decide +kernel)

theorem test128000_block_12 : Interval test128000 192 208 :=
  interval_of_check test128000 192 16 (by decide +kernel)

theorem test128000_block_13 : Interval test128000 208 224 :=
  interval_of_check test128000 208 16 (by decide +kernel)

theorem test128000_block_14 : Interval test128000 224 240 :=
  interval_of_check test128000 224 16 (by decide +kernel)

theorem test128000_block_15 : Interval test128000 240 256 :=
  interval_of_check test128000 240 16 (by decide +kernel)

theorem test128000_block_16 : Interval test128000 256 272 :=
  interval_of_check test128000 256 16 (by decide +kernel)

theorem test128000_block_17 : Interval test128000 272 288 :=
  interval_of_check test128000 272 16 (by decide +kernel)

theorem test128000_block_18 : Interval test128000 288 304 :=
  interval_of_check test128000 288 16 (by decide +kernel)

theorem test128000_block_19 : Interval test128000 304 320 :=
  interval_of_check test128000 304 16 (by decide +kernel)

theorem test128000_block_20 : Interval test128000 320 336 :=
  interval_of_check test128000 320 16 (by decide +kernel)

theorem test128000_block_21 : Interval test128000 336 352 :=
  interval_of_check test128000 336 16 (by decide +kernel)

theorem test128000_block_22 : Interval test128000 352 368 :=
  interval_of_check test128000 352 16 (by decide +kernel)

theorem test128000_block_23 : Interval test128000 368 384 :=
  interval_of_check test128000 368 16 (by decide +kernel)

theorem test128000_block_24 : Interval test128000 384 400 :=
  interval_of_check test128000 384 16 (by decide +kernel)

theorem test128000_block_25 : Interval test128000 400 416 :=
  interval_of_check test128000 400 16 (by decide +kernel)

theorem test128000_block_26 : Interval test128000 416 432 :=
  interval_of_check test128000 416 16 (by decide +kernel)

theorem test128000_block_27 : Interval test128000 432 448 :=
  interval_of_check test128000 432 16 (by decide +kernel)

theorem test128000_block_28 : Interval test128000 448 464 :=
  interval_of_check test128000 448 16 (by decide +kernel)

theorem test128000_block_29 : Interval test128000 464 480 :=
  interval_of_check test128000 464 16 (by decide +kernel)

theorem test128000_block_30 : Interval test128000 480 496 :=
  interval_of_check test128000 480 16 (by decide +kernel)

theorem test128000_block_31 : Interval test128000 496 512 :=
  interval_of_check test128000 496 16 (by decide +kernel)

theorem test128000_block_32 : Interval test128000 512 528 :=
  interval_of_check test128000 512 16 (by decide +kernel)

theorem test128000_block_33 : Interval test128000 528 544 :=
  interval_of_check test128000 528 16 (by decide +kernel)

theorem test128000_block_34 : Interval test128000 544 560 :=
  interval_of_check test128000 544 16 (by decide +kernel)

theorem test128000_block_35 : Interval test128000 560 576 :=
  interval_of_check test128000 560 16 (by decide +kernel)

theorem test128000_block_36 : Interval test128000 576 592 :=
  interval_of_check test128000 576 16 (by decide +kernel)

theorem test128000_block_37 : Interval test128000 592 608 :=
  interval_of_check test128000 592 16 (by decide +kernel)

theorem test128000_block_38 : Interval test128000 608 624 :=
  interval_of_check test128000 608 16 (by decide +kernel)

theorem test128000_block_39 : Interval test128000 624 640 :=
  interval_of_check test128000 624 16 (by decide +kernel)

theorem test128000_complete : Interval test128000 0 640 :=
  (interval_append test128000 0 320 640
  (interval_append test128000 0 160 320
  (interval_append test128000 0 80 160
  (interval_append test128000 0 32 80
  (interval_append test128000 0 16 32
  test128000_block_0
  test128000_block_1)
  (interval_append test128000 32 48 80
  test128000_block_2
  (interval_append test128000 48 64 80
  test128000_block_3
  test128000_block_4)))
  (interval_append test128000 80 112 160
  (interval_append test128000 80 96 112
  test128000_block_5
  test128000_block_6)
  (interval_append test128000 112 128 160
  test128000_block_7
  (interval_append test128000 128 144 160
  test128000_block_8
  test128000_block_9))))
  (interval_append test128000 160 240 320
  (interval_append test128000 160 192 240
  (interval_append test128000 160 176 192
  test128000_block_10
  test128000_block_11)
  (interval_append test128000 192 208 240
  test128000_block_12
  (interval_append test128000 208 224 240
  test128000_block_13
  test128000_block_14)))
  (interval_append test128000 240 272 320
  (interval_append test128000 240 256 272
  test128000_block_15
  test128000_block_16)
  (interval_append test128000 272 288 320
  test128000_block_17
  (interval_append test128000 288 304 320
  test128000_block_18
  test128000_block_19)))))
  (interval_append test128000 320 480 640
  (interval_append test128000 320 400 480
  (interval_append test128000 320 352 400
  (interval_append test128000 320 336 352
  test128000_block_20
  test128000_block_21)
  (interval_append test128000 352 368 400
  test128000_block_22
  (interval_append test128000 368 384 400
  test128000_block_23
  test128000_block_24)))
  (interval_append test128000 400 432 480
  (interval_append test128000 400 416 432
  test128000_block_25
  test128000_block_26)
  (interval_append test128000 432 448 480
  test128000_block_27
  (interval_append test128000 448 464 480
  test128000_block_28
  test128000_block_29))))
  (interval_append test128000 480 560 640
  (interval_append test128000 480 512 560
  (interval_append test128000 480 496 512
  test128000_block_30
  test128000_block_31)
  (interval_append test128000 512 528 560
  test128000_block_32
  (interval_append test128000 528 544 560
  test128000_block_33
  test128000_block_34)))
  (interval_append test128000 560 592 640
  (interval_append test128000 560 576 592
  test128000_block_35
  test128000_block_36)
  (interval_append test128000 592 608 640
  test128000_block_37
  (interval_append test128000 608 624 640
  test128000_block_38
  test128000_block_39))))))
theorem nodeInterval128000 : Interval nodeTest 128000 128640 := by
  intro i hlo hhi
  have h := test128000_complete (i-128000) (Nat.zero_le _) (by omega)
  simpa only [test128000, Nat.sub_add_cancel hlo] using h

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
def test128640 (i : Nat) := nodeTest (i+128640)
theorem test128640_block_0 : Interval test128640 0 16 :=
  interval_of_check test128640 0 16 (by decide +kernel)

theorem test128640_block_1 : Interval test128640 16 32 :=
  interval_of_check test128640 16 16 (by decide +kernel)

theorem test128640_block_2 : Interval test128640 32 48 :=
  interval_of_check test128640 32 16 (by decide +kernel)

theorem test128640_block_3 : Interval test128640 48 64 :=
  interval_of_check test128640 48 16 (by decide +kernel)

theorem test128640_block_4 : Interval test128640 64 80 :=
  interval_of_check test128640 64 16 (by decide +kernel)

theorem test128640_block_5 : Interval test128640 80 96 :=
  interval_of_check test128640 80 16 (by decide +kernel)

theorem test128640_block_6 : Interval test128640 96 112 :=
  interval_of_check test128640 96 16 (by decide +kernel)

theorem test128640_block_7 : Interval test128640 112 128 :=
  interval_of_check test128640 112 16 (by decide +kernel)

theorem test128640_block_8 : Interval test128640 128 144 :=
  interval_of_check test128640 128 16 (by decide +kernel)

theorem test128640_block_9 : Interval test128640 144 160 :=
  interval_of_check test128640 144 16 (by decide +kernel)

theorem test128640_block_10 : Interval test128640 160 176 :=
  interval_of_check test128640 160 16 (by decide +kernel)

theorem test128640_block_11 : Interval test128640 176 192 :=
  interval_of_check test128640 176 16 (by decide +kernel)

theorem test128640_block_12 : Interval test128640 192 208 :=
  interval_of_check test128640 192 16 (by decide +kernel)

theorem test128640_block_13 : Interval test128640 208 224 :=
  interval_of_check test128640 208 16 (by decide +kernel)

theorem test128640_block_14 : Interval test128640 224 240 :=
  interval_of_check test128640 224 16 (by decide +kernel)

theorem test128640_block_15 : Interval test128640 240 256 :=
  interval_of_check test128640 240 16 (by decide +kernel)

theorem test128640_block_16 : Interval test128640 256 272 :=
  interval_of_check test128640 256 16 (by decide +kernel)

theorem test128640_block_17 : Interval test128640 272 288 :=
  interval_of_check test128640 272 16 (by decide +kernel)

theorem test128640_block_18 : Interval test128640 288 304 :=
  interval_of_check test128640 288 16 (by decide +kernel)

theorem test128640_block_19 : Interval test128640 304 320 :=
  interval_of_check test128640 304 16 (by decide +kernel)

theorem test128640_block_20 : Interval test128640 320 336 :=
  interval_of_check test128640 320 16 (by decide +kernel)

theorem test128640_block_21 : Interval test128640 336 352 :=
  interval_of_check test128640 336 16 (by decide +kernel)

theorem test128640_block_22 : Interval test128640 352 368 :=
  interval_of_check test128640 352 16 (by decide +kernel)

theorem test128640_block_23 : Interval test128640 368 384 :=
  interval_of_check test128640 368 16 (by decide +kernel)

theorem test128640_block_24 : Interval test128640 384 400 :=
  interval_of_check test128640 384 16 (by decide +kernel)

theorem test128640_block_25 : Interval test128640 400 416 :=
  interval_of_check test128640 400 16 (by decide +kernel)

theorem test128640_block_26 : Interval test128640 416 432 :=
  interval_of_check test128640 416 16 (by decide +kernel)

theorem test128640_block_27 : Interval test128640 432 448 :=
  interval_of_check test128640 432 16 (by decide +kernel)

theorem test128640_block_28 : Interval test128640 448 464 :=
  interval_of_check test128640 448 16 (by decide +kernel)

theorem test128640_block_29 : Interval test128640 464 480 :=
  interval_of_check test128640 464 16 (by decide +kernel)

theorem test128640_block_30 : Interval test128640 480 496 :=
  interval_of_check test128640 480 16 (by decide +kernel)

theorem test128640_block_31 : Interval test128640 496 512 :=
  interval_of_check test128640 496 16 (by decide +kernel)

theorem test128640_block_32 : Interval test128640 512 528 :=
  interval_of_check test128640 512 16 (by decide +kernel)

theorem test128640_block_33 : Interval test128640 528 544 :=
  interval_of_check test128640 528 16 (by decide +kernel)

theorem test128640_block_34 : Interval test128640 544 560 :=
  interval_of_check test128640 544 16 (by decide +kernel)

theorem test128640_block_35 : Interval test128640 560 576 :=
  interval_of_check test128640 560 16 (by decide +kernel)

theorem test128640_block_36 : Interval test128640 576 592 :=
  interval_of_check test128640 576 16 (by decide +kernel)

theorem test128640_block_37 : Interval test128640 592 608 :=
  interval_of_check test128640 592 16 (by decide +kernel)

theorem test128640_block_38 : Interval test128640 608 624 :=
  interval_of_check test128640 608 16 (by decide +kernel)

theorem test128640_block_39 : Interval test128640 624 640 :=
  interval_of_check test128640 624 16 (by decide +kernel)

theorem test128640_complete : Interval test128640 0 640 :=
  (interval_append test128640 0 320 640
  (interval_append test128640 0 160 320
  (interval_append test128640 0 80 160
  (interval_append test128640 0 32 80
  (interval_append test128640 0 16 32
  test128640_block_0
  test128640_block_1)
  (interval_append test128640 32 48 80
  test128640_block_2
  (interval_append test128640 48 64 80
  test128640_block_3
  test128640_block_4)))
  (interval_append test128640 80 112 160
  (interval_append test128640 80 96 112
  test128640_block_5
  test128640_block_6)
  (interval_append test128640 112 128 160
  test128640_block_7
  (interval_append test128640 128 144 160
  test128640_block_8
  test128640_block_9))))
  (interval_append test128640 160 240 320
  (interval_append test128640 160 192 240
  (interval_append test128640 160 176 192
  test128640_block_10
  test128640_block_11)
  (interval_append test128640 192 208 240
  test128640_block_12
  (interval_append test128640 208 224 240
  test128640_block_13
  test128640_block_14)))
  (interval_append test128640 240 272 320
  (interval_append test128640 240 256 272
  test128640_block_15
  test128640_block_16)
  (interval_append test128640 272 288 320
  test128640_block_17
  (interval_append test128640 288 304 320
  test128640_block_18
  test128640_block_19)))))
  (interval_append test128640 320 480 640
  (interval_append test128640 320 400 480
  (interval_append test128640 320 352 400
  (interval_append test128640 320 336 352
  test128640_block_20
  test128640_block_21)
  (interval_append test128640 352 368 400
  test128640_block_22
  (interval_append test128640 368 384 400
  test128640_block_23
  test128640_block_24)))
  (interval_append test128640 400 432 480
  (interval_append test128640 400 416 432
  test128640_block_25
  test128640_block_26)
  (interval_append test128640 432 448 480
  test128640_block_27
  (interval_append test128640 448 464 480
  test128640_block_28
  test128640_block_29))))
  (interval_append test128640 480 560 640
  (interval_append test128640 480 512 560
  (interval_append test128640 480 496 512
  test128640_block_30
  test128640_block_31)
  (interval_append test128640 512 528 560
  test128640_block_32
  (interval_append test128640 528 544 560
  test128640_block_33
  test128640_block_34)))
  (interval_append test128640 560 592 640
  (interval_append test128640 560 576 592
  test128640_block_35
  test128640_block_36)
  (interval_append test128640 592 608 640
  test128640_block_37
  (interval_append test128640 608 624 640
  test128640_block_38
  test128640_block_39))))))
theorem nodeInterval128640 : Interval nodeTest 128640 129280 := by
  intro i hlo hhi
  have h := test128640_complete (i-128640) (Nat.zero_le _) (by omega)
  simpa only [test128640, Nat.sub_add_cancel hlo] using h

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
def test129280 (i : Nat) := nodeTest (i+129280)
theorem test129280_block_0 : Interval test129280 0 16 :=
  interval_of_check test129280 0 16 (by decide +kernel)

theorem test129280_block_1 : Interval test129280 16 32 :=
  interval_of_check test129280 16 16 (by decide +kernel)

theorem test129280_block_2 : Interval test129280 32 48 :=
  interval_of_check test129280 32 16 (by decide +kernel)

theorem test129280_block_3 : Interval test129280 48 64 :=
  interval_of_check test129280 48 16 (by decide +kernel)

theorem test129280_block_4 : Interval test129280 64 80 :=
  interval_of_check test129280 64 16 (by decide +kernel)

theorem test129280_block_5 : Interval test129280 80 96 :=
  interval_of_check test129280 80 16 (by decide +kernel)

theorem test129280_block_6 : Interval test129280 96 112 :=
  interval_of_check test129280 96 16 (by decide +kernel)

theorem test129280_block_7 : Interval test129280 112 128 :=
  interval_of_check test129280 112 16 (by decide +kernel)

theorem test129280_block_8 : Interval test129280 128 144 :=
  interval_of_check test129280 128 16 (by decide +kernel)

theorem test129280_block_9 : Interval test129280 144 160 :=
  interval_of_check test129280 144 16 (by decide +kernel)

theorem test129280_block_10 : Interval test129280 160 176 :=
  interval_of_check test129280 160 16 (by decide +kernel)

theorem test129280_block_11 : Interval test129280 176 192 :=
  interval_of_check test129280 176 16 (by decide +kernel)

theorem test129280_block_12 : Interval test129280 192 208 :=
  interval_of_check test129280 192 16 (by decide +kernel)

theorem test129280_block_13 : Interval test129280 208 224 :=
  interval_of_check test129280 208 16 (by decide +kernel)

theorem test129280_block_14 : Interval test129280 224 240 :=
  interval_of_check test129280 224 16 (by decide +kernel)

theorem test129280_block_15 : Interval test129280 240 256 :=
  interval_of_check test129280 240 16 (by decide +kernel)

theorem test129280_block_16 : Interval test129280 256 272 :=
  interval_of_check test129280 256 16 (by decide +kernel)

theorem test129280_block_17 : Interval test129280 272 288 :=
  interval_of_check test129280 272 16 (by decide +kernel)

theorem test129280_block_18 : Interval test129280 288 304 :=
  interval_of_check test129280 288 16 (by decide +kernel)

theorem test129280_block_19 : Interval test129280 304 320 :=
  interval_of_check test129280 304 16 (by decide +kernel)

theorem test129280_block_20 : Interval test129280 320 336 :=
  interval_of_check test129280 320 16 (by decide +kernel)

theorem test129280_block_21 : Interval test129280 336 352 :=
  interval_of_check test129280 336 16 (by decide +kernel)

theorem test129280_block_22 : Interval test129280 352 368 :=
  interval_of_check test129280 352 16 (by decide +kernel)

theorem test129280_block_23 : Interval test129280 368 384 :=
  interval_of_check test129280 368 16 (by decide +kernel)

theorem test129280_block_24 : Interval test129280 384 400 :=
  interval_of_check test129280 384 16 (by decide +kernel)

theorem test129280_block_25 : Interval test129280 400 416 :=
  interval_of_check test129280 400 16 (by decide +kernel)

theorem test129280_block_26 : Interval test129280 416 432 :=
  interval_of_check test129280 416 16 (by decide +kernel)

theorem test129280_block_27 : Interval test129280 432 448 :=
  interval_of_check test129280 432 16 (by decide +kernel)

theorem test129280_block_28 : Interval test129280 448 464 :=
  interval_of_check test129280 448 16 (by decide +kernel)

theorem test129280_block_29 : Interval test129280 464 480 :=
  interval_of_check test129280 464 16 (by decide +kernel)

theorem test129280_block_30 : Interval test129280 480 496 :=
  interval_of_check test129280 480 16 (by decide +kernel)

theorem test129280_block_31 : Interval test129280 496 512 :=
  interval_of_check test129280 496 16 (by decide +kernel)

theorem test129280_block_32 : Interval test129280 512 528 :=
  interval_of_check test129280 512 16 (by decide +kernel)

theorem test129280_block_33 : Interval test129280 528 544 :=
  interval_of_check test129280 528 16 (by decide +kernel)

theorem test129280_block_34 : Interval test129280 544 560 :=
  interval_of_check test129280 544 16 (by decide +kernel)

theorem test129280_block_35 : Interval test129280 560 576 :=
  interval_of_check test129280 560 16 (by decide +kernel)

theorem test129280_block_36 : Interval test129280 576 592 :=
  interval_of_check test129280 576 16 (by decide +kernel)

theorem test129280_block_37 : Interval test129280 592 608 :=
  interval_of_check test129280 592 16 (by decide +kernel)

theorem test129280_block_38 : Interval test129280 608 624 :=
  interval_of_check test129280 608 16 (by decide +kernel)

theorem test129280_block_39 : Interval test129280 624 640 :=
  interval_of_check test129280 624 16 (by decide +kernel)

theorem test129280_complete : Interval test129280 0 640 :=
  (interval_append test129280 0 320 640
  (interval_append test129280 0 160 320
  (interval_append test129280 0 80 160
  (interval_append test129280 0 32 80
  (interval_append test129280 0 16 32
  test129280_block_0
  test129280_block_1)
  (interval_append test129280 32 48 80
  test129280_block_2
  (interval_append test129280 48 64 80
  test129280_block_3
  test129280_block_4)))
  (interval_append test129280 80 112 160
  (interval_append test129280 80 96 112
  test129280_block_5
  test129280_block_6)
  (interval_append test129280 112 128 160
  test129280_block_7
  (interval_append test129280 128 144 160
  test129280_block_8
  test129280_block_9))))
  (interval_append test129280 160 240 320
  (interval_append test129280 160 192 240
  (interval_append test129280 160 176 192
  test129280_block_10
  test129280_block_11)
  (interval_append test129280 192 208 240
  test129280_block_12
  (interval_append test129280 208 224 240
  test129280_block_13
  test129280_block_14)))
  (interval_append test129280 240 272 320
  (interval_append test129280 240 256 272
  test129280_block_15
  test129280_block_16)
  (interval_append test129280 272 288 320
  test129280_block_17
  (interval_append test129280 288 304 320
  test129280_block_18
  test129280_block_19)))))
  (interval_append test129280 320 480 640
  (interval_append test129280 320 400 480
  (interval_append test129280 320 352 400
  (interval_append test129280 320 336 352
  test129280_block_20
  test129280_block_21)
  (interval_append test129280 352 368 400
  test129280_block_22
  (interval_append test129280 368 384 400
  test129280_block_23
  test129280_block_24)))
  (interval_append test129280 400 432 480
  (interval_append test129280 400 416 432
  test129280_block_25
  test129280_block_26)
  (interval_append test129280 432 448 480
  test129280_block_27
  (interval_append test129280 448 464 480
  test129280_block_28
  test129280_block_29))))
  (interval_append test129280 480 560 640
  (interval_append test129280 480 512 560
  (interval_append test129280 480 496 512
  test129280_block_30
  test129280_block_31)
  (interval_append test129280 512 528 560
  test129280_block_32
  (interval_append test129280 528 544 560
  test129280_block_33
  test129280_block_34)))
  (interval_append test129280 560 592 640
  (interval_append test129280 560 576 592
  test129280_block_35
  test129280_block_36)
  (interval_append test129280 592 608 640
  test129280_block_37
  (interval_append test129280 608 624 640
  test129280_block_38
  test129280_block_39))))))
theorem nodeInterval129280 : Interval nodeTest 129280 129920 := by
  intro i hlo hhi
  have h := test129280_complete (i-129280) (Nat.zero_le _) (by omega)
  simpa only [test129280, Nat.sub_add_cancel hlo] using h

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
def test129920 (i : Nat) := nodeTest (i+129920)
theorem test129920_block_0 : Interval test129920 0 16 :=
  interval_of_check test129920 0 16 (by decide +kernel)

theorem test129920_block_1 : Interval test129920 16 32 :=
  interval_of_check test129920 16 16 (by decide +kernel)

theorem test129920_block_2 : Interval test129920 32 48 :=
  interval_of_check test129920 32 16 (by decide +kernel)

theorem test129920_block_3 : Interval test129920 48 64 :=
  interval_of_check test129920 48 16 (by decide +kernel)

theorem test129920_block_4 : Interval test129920 64 80 :=
  interval_of_check test129920 64 16 (by decide +kernel)

theorem test129920_block_5 : Interval test129920 80 96 :=
  interval_of_check test129920 80 16 (by decide +kernel)

theorem test129920_block_6 : Interval test129920 96 112 :=
  interval_of_check test129920 96 16 (by decide +kernel)

theorem test129920_block_7 : Interval test129920 112 128 :=
  interval_of_check test129920 112 16 (by decide +kernel)

theorem test129920_block_8 : Interval test129920 128 144 :=
  interval_of_check test129920 128 16 (by decide +kernel)

theorem test129920_block_9 : Interval test129920 144 160 :=
  interval_of_check test129920 144 16 (by decide +kernel)

theorem test129920_block_10 : Interval test129920 160 176 :=
  interval_of_check test129920 160 16 (by decide +kernel)

theorem test129920_block_11 : Interval test129920 176 192 :=
  interval_of_check test129920 176 16 (by decide +kernel)

theorem test129920_block_12 : Interval test129920 192 208 :=
  interval_of_check test129920 192 16 (by decide +kernel)

theorem test129920_block_13 : Interval test129920 208 224 :=
  interval_of_check test129920 208 16 (by decide +kernel)

theorem test129920_block_14 : Interval test129920 224 240 :=
  interval_of_check test129920 224 16 (by decide +kernel)

theorem test129920_block_15 : Interval test129920 240 256 :=
  interval_of_check test129920 240 16 (by decide +kernel)

theorem test129920_block_16 : Interval test129920 256 272 :=
  interval_of_check test129920 256 16 (by decide +kernel)

theorem test129920_block_17 : Interval test129920 272 288 :=
  interval_of_check test129920 272 16 (by decide +kernel)

theorem test129920_block_18 : Interval test129920 288 304 :=
  interval_of_check test129920 288 16 (by decide +kernel)

theorem test129920_block_19 : Interval test129920 304 320 :=
  interval_of_check test129920 304 16 (by decide +kernel)

theorem test129920_block_20 : Interval test129920 320 336 :=
  interval_of_check test129920 320 16 (by decide +kernel)

theorem test129920_block_21 : Interval test129920 336 352 :=
  interval_of_check test129920 336 16 (by decide +kernel)

theorem test129920_block_22 : Interval test129920 352 368 :=
  interval_of_check test129920 352 16 (by decide +kernel)

theorem test129920_block_23 : Interval test129920 368 384 :=
  interval_of_check test129920 368 16 (by decide +kernel)

theorem test129920_block_24 : Interval test129920 384 400 :=
  interval_of_check test129920 384 16 (by decide +kernel)

theorem test129920_block_25 : Interval test129920 400 416 :=
  interval_of_check test129920 400 16 (by decide +kernel)

theorem test129920_block_26 : Interval test129920 416 432 :=
  interval_of_check test129920 416 16 (by decide +kernel)

theorem test129920_block_27 : Interval test129920 432 448 :=
  interval_of_check test129920 432 16 (by decide +kernel)

theorem test129920_block_28 : Interval test129920 448 464 :=
  interval_of_check test129920 448 16 (by decide +kernel)

theorem test129920_block_29 : Interval test129920 464 480 :=
  interval_of_check test129920 464 16 (by decide +kernel)

theorem test129920_block_30 : Interval test129920 480 496 :=
  interval_of_check test129920 480 16 (by decide +kernel)

theorem test129920_block_31 : Interval test129920 496 512 :=
  interval_of_check test129920 496 16 (by decide +kernel)

theorem test129920_block_32 : Interval test129920 512 528 :=
  interval_of_check test129920 512 16 (by decide +kernel)

theorem test129920_block_33 : Interval test129920 528 544 :=
  interval_of_check test129920 528 16 (by decide +kernel)

theorem test129920_block_34 : Interval test129920 544 560 :=
  interval_of_check test129920 544 16 (by decide +kernel)

theorem test129920_block_35 : Interval test129920 560 576 :=
  interval_of_check test129920 560 16 (by decide +kernel)

theorem test129920_block_36 : Interval test129920 576 592 :=
  interval_of_check test129920 576 16 (by decide +kernel)

theorem test129920_block_37 : Interval test129920 592 608 :=
  interval_of_check test129920 592 16 (by decide +kernel)

theorem test129920_block_38 : Interval test129920 608 624 :=
  interval_of_check test129920 608 16 (by decide +kernel)

theorem test129920_block_39 : Interval test129920 624 640 :=
  interval_of_check test129920 624 16 (by decide +kernel)

theorem test129920_complete : Interval test129920 0 640 :=
  (interval_append test129920 0 320 640
  (interval_append test129920 0 160 320
  (interval_append test129920 0 80 160
  (interval_append test129920 0 32 80
  (interval_append test129920 0 16 32
  test129920_block_0
  test129920_block_1)
  (interval_append test129920 32 48 80
  test129920_block_2
  (interval_append test129920 48 64 80
  test129920_block_3
  test129920_block_4)))
  (interval_append test129920 80 112 160
  (interval_append test129920 80 96 112
  test129920_block_5
  test129920_block_6)
  (interval_append test129920 112 128 160
  test129920_block_7
  (interval_append test129920 128 144 160
  test129920_block_8
  test129920_block_9))))
  (interval_append test129920 160 240 320
  (interval_append test129920 160 192 240
  (interval_append test129920 160 176 192
  test129920_block_10
  test129920_block_11)
  (interval_append test129920 192 208 240
  test129920_block_12
  (interval_append test129920 208 224 240
  test129920_block_13
  test129920_block_14)))
  (interval_append test129920 240 272 320
  (interval_append test129920 240 256 272
  test129920_block_15
  test129920_block_16)
  (interval_append test129920 272 288 320
  test129920_block_17
  (interval_append test129920 288 304 320
  test129920_block_18
  test129920_block_19)))))
  (interval_append test129920 320 480 640
  (interval_append test129920 320 400 480
  (interval_append test129920 320 352 400
  (interval_append test129920 320 336 352
  test129920_block_20
  test129920_block_21)
  (interval_append test129920 352 368 400
  test129920_block_22
  (interval_append test129920 368 384 400
  test129920_block_23
  test129920_block_24)))
  (interval_append test129920 400 432 480
  (interval_append test129920 400 416 432
  test129920_block_25
  test129920_block_26)
  (interval_append test129920 432 448 480
  test129920_block_27
  (interval_append test129920 448 464 480
  test129920_block_28
  test129920_block_29))))
  (interval_append test129920 480 560 640
  (interval_append test129920 480 512 560
  (interval_append test129920 480 496 512
  test129920_block_30
  test129920_block_31)
  (interval_append test129920 512 528 560
  test129920_block_32
  (interval_append test129920 528 544 560
  test129920_block_33
  test129920_block_34)))
  (interval_append test129920 560 592 640
  (interval_append test129920 560 576 592
  test129920_block_35
  test129920_block_36)
  (interval_append test129920 592 608 640
  test129920_block_37
  (interval_append test129920 608 624 640
  test129920_block_38
  test129920_block_39))))))
theorem nodeInterval129920 : Interval nodeTest 129920 130560 := by
  intro i hlo hhi
  have h := test129920_complete (i-129920) (Nat.zero_le _) (by omega)
  simpa only [test129920, Nat.sub_add_cancel hlo] using h

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
def test130560 (i : Nat) := nodeTest (i+130560)
theorem test130560_block_0 : Interval test130560 0 16 :=
  interval_of_check test130560 0 16 (by decide +kernel)

theorem test130560_block_1 : Interval test130560 16 32 :=
  interval_of_check test130560 16 16 (by decide +kernel)

theorem test130560_block_2 : Interval test130560 32 48 :=
  interval_of_check test130560 32 16 (by decide +kernel)

theorem test130560_block_3 : Interval test130560 48 64 :=
  interval_of_check test130560 48 16 (by decide +kernel)

theorem test130560_block_4 : Interval test130560 64 80 :=
  interval_of_check test130560 64 16 (by decide +kernel)

theorem test130560_block_5 : Interval test130560 80 96 :=
  interval_of_check test130560 80 16 (by decide +kernel)

theorem test130560_block_6 : Interval test130560 96 112 :=
  interval_of_check test130560 96 16 (by decide +kernel)

theorem test130560_block_7 : Interval test130560 112 128 :=
  interval_of_check test130560 112 16 (by decide +kernel)

theorem test130560_block_8 : Interval test130560 128 144 :=
  interval_of_check test130560 128 16 (by decide +kernel)

theorem test130560_block_9 : Interval test130560 144 160 :=
  interval_of_check test130560 144 16 (by decide +kernel)

theorem test130560_block_10 : Interval test130560 160 176 :=
  interval_of_check test130560 160 16 (by decide +kernel)

theorem test130560_block_11 : Interval test130560 176 192 :=
  interval_of_check test130560 176 16 (by decide +kernel)

theorem test130560_block_12 : Interval test130560 192 208 :=
  interval_of_check test130560 192 16 (by decide +kernel)

theorem test130560_block_13 : Interval test130560 208 224 :=
  interval_of_check test130560 208 16 (by decide +kernel)

theorem test130560_block_14 : Interval test130560 224 240 :=
  interval_of_check test130560 224 16 (by decide +kernel)

theorem test130560_block_15 : Interval test130560 240 256 :=
  interval_of_check test130560 240 16 (by decide +kernel)

theorem test130560_block_16 : Interval test130560 256 272 :=
  interval_of_check test130560 256 16 (by decide +kernel)

theorem test130560_block_17 : Interval test130560 272 288 :=
  interval_of_check test130560 272 16 (by decide +kernel)

theorem test130560_block_18 : Interval test130560 288 304 :=
  interval_of_check test130560 288 16 (by decide +kernel)

theorem test130560_block_19 : Interval test130560 304 320 :=
  interval_of_check test130560 304 16 (by decide +kernel)

theorem test130560_block_20 : Interval test130560 320 336 :=
  interval_of_check test130560 320 16 (by decide +kernel)

theorem test130560_block_21 : Interval test130560 336 352 :=
  interval_of_check test130560 336 16 (by decide +kernel)

theorem test130560_block_22 : Interval test130560 352 368 :=
  interval_of_check test130560 352 16 (by decide +kernel)

theorem test130560_block_23 : Interval test130560 368 384 :=
  interval_of_check test130560 368 16 (by decide +kernel)

theorem test130560_block_24 : Interval test130560 384 400 :=
  interval_of_check test130560 384 16 (by decide +kernel)

theorem test130560_block_25 : Interval test130560 400 416 :=
  interval_of_check test130560 400 16 (by decide +kernel)

theorem test130560_block_26 : Interval test130560 416 432 :=
  interval_of_check test130560 416 16 (by decide +kernel)

theorem test130560_block_27 : Interval test130560 432 448 :=
  interval_of_check test130560 432 16 (by decide +kernel)

theorem test130560_block_28 : Interval test130560 448 464 :=
  interval_of_check test130560 448 16 (by decide +kernel)

theorem test130560_block_29 : Interval test130560 464 480 :=
  interval_of_check test130560 464 16 (by decide +kernel)

theorem test130560_block_30 : Interval test130560 480 496 :=
  interval_of_check test130560 480 16 (by decide +kernel)

theorem test130560_block_31 : Interval test130560 496 512 :=
  interval_of_check test130560 496 16 (by decide +kernel)

theorem test130560_block_32 : Interval test130560 512 528 :=
  interval_of_check test130560 512 16 (by decide +kernel)

theorem test130560_block_33 : Interval test130560 528 544 :=
  interval_of_check test130560 528 16 (by decide +kernel)

theorem test130560_block_34 : Interval test130560 544 560 :=
  interval_of_check test130560 544 16 (by decide +kernel)

theorem test130560_block_35 : Interval test130560 560 576 :=
  interval_of_check test130560 560 16 (by decide +kernel)

theorem test130560_block_36 : Interval test130560 576 592 :=
  interval_of_check test130560 576 16 (by decide +kernel)

theorem test130560_block_37 : Interval test130560 592 608 :=
  interval_of_check test130560 592 16 (by decide +kernel)

theorem test130560_block_38 : Interval test130560 608 624 :=
  interval_of_check test130560 608 16 (by decide +kernel)

theorem test130560_block_39 : Interval test130560 624 640 :=
  interval_of_check test130560 624 16 (by decide +kernel)

theorem test130560_complete : Interval test130560 0 640 :=
  (interval_append test130560 0 320 640
  (interval_append test130560 0 160 320
  (interval_append test130560 0 80 160
  (interval_append test130560 0 32 80
  (interval_append test130560 0 16 32
  test130560_block_0
  test130560_block_1)
  (interval_append test130560 32 48 80
  test130560_block_2
  (interval_append test130560 48 64 80
  test130560_block_3
  test130560_block_4)))
  (interval_append test130560 80 112 160
  (interval_append test130560 80 96 112
  test130560_block_5
  test130560_block_6)
  (interval_append test130560 112 128 160
  test130560_block_7
  (interval_append test130560 128 144 160
  test130560_block_8
  test130560_block_9))))
  (interval_append test130560 160 240 320
  (interval_append test130560 160 192 240
  (interval_append test130560 160 176 192
  test130560_block_10
  test130560_block_11)
  (interval_append test130560 192 208 240
  test130560_block_12
  (interval_append test130560 208 224 240
  test130560_block_13
  test130560_block_14)))
  (interval_append test130560 240 272 320
  (interval_append test130560 240 256 272
  test130560_block_15
  test130560_block_16)
  (interval_append test130560 272 288 320
  test130560_block_17
  (interval_append test130560 288 304 320
  test130560_block_18
  test130560_block_19)))))
  (interval_append test130560 320 480 640
  (interval_append test130560 320 400 480
  (interval_append test130560 320 352 400
  (interval_append test130560 320 336 352
  test130560_block_20
  test130560_block_21)
  (interval_append test130560 352 368 400
  test130560_block_22
  (interval_append test130560 368 384 400
  test130560_block_23
  test130560_block_24)))
  (interval_append test130560 400 432 480
  (interval_append test130560 400 416 432
  test130560_block_25
  test130560_block_26)
  (interval_append test130560 432 448 480
  test130560_block_27
  (interval_append test130560 448 464 480
  test130560_block_28
  test130560_block_29))))
  (interval_append test130560 480 560 640
  (interval_append test130560 480 512 560
  (interval_append test130560 480 496 512
  test130560_block_30
  test130560_block_31)
  (interval_append test130560 512 528 560
  test130560_block_32
  (interval_append test130560 528 544 560
  test130560_block_33
  test130560_block_34)))
  (interval_append test130560 560 592 640
  (interval_append test130560 560 576 592
  test130560_block_35
  test130560_block_36)
  (interval_append test130560 592 608 640
  test130560_block_37
  (interval_append test130560 608 624 640
  test130560_block_38
  test130560_block_39))))))
theorem nodeInterval130560 : Interval nodeTest 130560 131200 := by
  intro i hlo hhi
  have h := test130560_complete (i-130560) (Nat.zero_le _) (by omega)
  simpa only [test130560, Nat.sub_add_cancel hlo] using h

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
def test131200 (i : Nat) := nodeTest (i+131200)
theorem test131200_block_0 : Interval test131200 0 16 :=
  interval_of_check test131200 0 16 (by decide +kernel)

theorem test131200_block_1 : Interval test131200 16 32 :=
  interval_of_check test131200 16 16 (by decide +kernel)

theorem test131200_block_2 : Interval test131200 32 48 :=
  interval_of_check test131200 32 16 (by decide +kernel)

theorem test131200_block_3 : Interval test131200 48 64 :=
  interval_of_check test131200 48 16 (by decide +kernel)

theorem test131200_block_4 : Interval test131200 64 80 :=
  interval_of_check test131200 64 16 (by decide +kernel)

theorem test131200_block_5 : Interval test131200 80 96 :=
  interval_of_check test131200 80 16 (by decide +kernel)

theorem test131200_block_6 : Interval test131200 96 112 :=
  interval_of_check test131200 96 16 (by decide +kernel)

theorem test131200_block_7 : Interval test131200 112 128 :=
  interval_of_check test131200 112 16 (by decide +kernel)

theorem test131200_block_8 : Interval test131200 128 144 :=
  interval_of_check test131200 128 16 (by decide +kernel)

theorem test131200_block_9 : Interval test131200 144 160 :=
  interval_of_check test131200 144 16 (by decide +kernel)

theorem test131200_block_10 : Interval test131200 160 176 :=
  interval_of_check test131200 160 16 (by decide +kernel)

theorem test131200_block_11 : Interval test131200 176 192 :=
  interval_of_check test131200 176 16 (by decide +kernel)

theorem test131200_block_12 : Interval test131200 192 208 :=
  interval_of_check test131200 192 16 (by decide +kernel)

theorem test131200_block_13 : Interval test131200 208 224 :=
  interval_of_check test131200 208 16 (by decide +kernel)

theorem test131200_block_14 : Interval test131200 224 240 :=
  interval_of_check test131200 224 16 (by decide +kernel)

theorem test131200_block_15 : Interval test131200 240 256 :=
  interval_of_check test131200 240 16 (by decide +kernel)

theorem test131200_block_16 : Interval test131200 256 272 :=
  interval_of_check test131200 256 16 (by decide +kernel)

theorem test131200_block_17 : Interval test131200 272 288 :=
  interval_of_check test131200 272 16 (by decide +kernel)

theorem test131200_block_18 : Interval test131200 288 304 :=
  interval_of_check test131200 288 16 (by decide +kernel)

theorem test131200_block_19 : Interval test131200 304 320 :=
  interval_of_check test131200 304 16 (by decide +kernel)

theorem test131200_block_20 : Interval test131200 320 336 :=
  interval_of_check test131200 320 16 (by decide +kernel)

theorem test131200_block_21 : Interval test131200 336 352 :=
  interval_of_check test131200 336 16 (by decide +kernel)

theorem test131200_block_22 : Interval test131200 352 368 :=
  interval_of_check test131200 352 16 (by decide +kernel)

theorem test131200_block_23 : Interval test131200 368 384 :=
  interval_of_check test131200 368 16 (by decide +kernel)

theorem test131200_block_24 : Interval test131200 384 400 :=
  interval_of_check test131200 384 16 (by decide +kernel)

theorem test131200_block_25 : Interval test131200 400 416 :=
  interval_of_check test131200 400 16 (by decide +kernel)

theorem test131200_block_26 : Interval test131200 416 432 :=
  interval_of_check test131200 416 16 (by decide +kernel)

theorem test131200_block_27 : Interval test131200 432 448 :=
  interval_of_check test131200 432 16 (by decide +kernel)

theorem test131200_block_28 : Interval test131200 448 464 :=
  interval_of_check test131200 448 16 (by decide +kernel)

theorem test131200_block_29 : Interval test131200 464 480 :=
  interval_of_check test131200 464 16 (by decide +kernel)

theorem test131200_block_30 : Interval test131200 480 496 :=
  interval_of_check test131200 480 16 (by decide +kernel)

theorem test131200_block_31 : Interval test131200 496 512 :=
  interval_of_check test131200 496 16 (by decide +kernel)

theorem test131200_block_32 : Interval test131200 512 528 :=
  interval_of_check test131200 512 16 (by decide +kernel)

theorem test131200_block_33 : Interval test131200 528 544 :=
  interval_of_check test131200 528 16 (by decide +kernel)

theorem test131200_block_34 : Interval test131200 544 560 :=
  interval_of_check test131200 544 16 (by decide +kernel)

theorem test131200_block_35 : Interval test131200 560 576 :=
  interval_of_check test131200 560 16 (by decide +kernel)

theorem test131200_block_36 : Interval test131200 576 592 :=
  interval_of_check test131200 576 16 (by decide +kernel)

theorem test131200_block_37 : Interval test131200 592 608 :=
  interval_of_check test131200 592 16 (by decide +kernel)

theorem test131200_block_38 : Interval test131200 608 624 :=
  interval_of_check test131200 608 16 (by decide +kernel)

theorem test131200_block_39 : Interval test131200 624 640 :=
  interval_of_check test131200 624 16 (by decide +kernel)

theorem test131200_complete : Interval test131200 0 640 :=
  (interval_append test131200 0 320 640
  (interval_append test131200 0 160 320
  (interval_append test131200 0 80 160
  (interval_append test131200 0 32 80
  (interval_append test131200 0 16 32
  test131200_block_0
  test131200_block_1)
  (interval_append test131200 32 48 80
  test131200_block_2
  (interval_append test131200 48 64 80
  test131200_block_3
  test131200_block_4)))
  (interval_append test131200 80 112 160
  (interval_append test131200 80 96 112
  test131200_block_5
  test131200_block_6)
  (interval_append test131200 112 128 160
  test131200_block_7
  (interval_append test131200 128 144 160
  test131200_block_8
  test131200_block_9))))
  (interval_append test131200 160 240 320
  (interval_append test131200 160 192 240
  (interval_append test131200 160 176 192
  test131200_block_10
  test131200_block_11)
  (interval_append test131200 192 208 240
  test131200_block_12
  (interval_append test131200 208 224 240
  test131200_block_13
  test131200_block_14)))
  (interval_append test131200 240 272 320
  (interval_append test131200 240 256 272
  test131200_block_15
  test131200_block_16)
  (interval_append test131200 272 288 320
  test131200_block_17
  (interval_append test131200 288 304 320
  test131200_block_18
  test131200_block_19)))))
  (interval_append test131200 320 480 640
  (interval_append test131200 320 400 480
  (interval_append test131200 320 352 400
  (interval_append test131200 320 336 352
  test131200_block_20
  test131200_block_21)
  (interval_append test131200 352 368 400
  test131200_block_22
  (interval_append test131200 368 384 400
  test131200_block_23
  test131200_block_24)))
  (interval_append test131200 400 432 480
  (interval_append test131200 400 416 432
  test131200_block_25
  test131200_block_26)
  (interval_append test131200 432 448 480
  test131200_block_27
  (interval_append test131200 448 464 480
  test131200_block_28
  test131200_block_29))))
  (interval_append test131200 480 560 640
  (interval_append test131200 480 512 560
  (interval_append test131200 480 496 512
  test131200_block_30
  test131200_block_31)
  (interval_append test131200 512 528 560
  test131200_block_32
  (interval_append test131200 528 544 560
  test131200_block_33
  test131200_block_34)))
  (interval_append test131200 560 592 640
  (interval_append test131200 560 576 592
  test131200_block_35
  test131200_block_36)
  (interval_append test131200 592 608 640
  test131200_block_37
  (interval_append test131200 608 624 640
  test131200_block_38
  test131200_block_39))))))
theorem nodeInterval131200 : Interval nodeTest 131200 131840 := by
  intro i hlo hhi
  have h := test131200_complete (i-131200) (Nat.zero_le _) (by omega)
  simpa only [test131200, Nat.sub_add_cancel hlo] using h

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
def test131840 (i : Nat) := nodeTest (i+131840)
theorem test131840_block_0 : Interval test131840 0 16 :=
  interval_of_check test131840 0 16 (by decide +kernel)

theorem test131840_block_1 : Interval test131840 16 32 :=
  interval_of_check test131840 16 16 (by decide +kernel)

theorem test131840_block_2 : Interval test131840 32 48 :=
  interval_of_check test131840 32 16 (by decide +kernel)

theorem test131840_block_3 : Interval test131840 48 64 :=
  interval_of_check test131840 48 16 (by decide +kernel)

theorem test131840_block_4 : Interval test131840 64 80 :=
  interval_of_check test131840 64 16 (by decide +kernel)

theorem test131840_block_5 : Interval test131840 80 96 :=
  interval_of_check test131840 80 16 (by decide +kernel)

theorem test131840_block_6 : Interval test131840 96 112 :=
  interval_of_check test131840 96 16 (by decide +kernel)

theorem test131840_block_7 : Interval test131840 112 128 :=
  interval_of_check test131840 112 16 (by decide +kernel)

theorem test131840_block_8 : Interval test131840 128 144 :=
  interval_of_check test131840 128 16 (by decide +kernel)

theorem test131840_block_9 : Interval test131840 144 160 :=
  interval_of_check test131840 144 16 (by decide +kernel)

theorem test131840_block_10 : Interval test131840 160 176 :=
  interval_of_check test131840 160 16 (by decide +kernel)

theorem test131840_block_11 : Interval test131840 176 192 :=
  interval_of_check test131840 176 16 (by decide +kernel)

theorem test131840_block_12 : Interval test131840 192 208 :=
  interval_of_check test131840 192 16 (by decide +kernel)

theorem test131840_block_13 : Interval test131840 208 224 :=
  interval_of_check test131840 208 16 (by decide +kernel)

theorem test131840_block_14 : Interval test131840 224 240 :=
  interval_of_check test131840 224 16 (by decide +kernel)

theorem test131840_block_15 : Interval test131840 240 256 :=
  interval_of_check test131840 240 16 (by decide +kernel)

theorem test131840_block_16 : Interval test131840 256 272 :=
  interval_of_check test131840 256 16 (by decide +kernel)

theorem test131840_block_17 : Interval test131840 272 288 :=
  interval_of_check test131840 272 16 (by decide +kernel)

theorem test131840_block_18 : Interval test131840 288 304 :=
  interval_of_check test131840 288 16 (by decide +kernel)

theorem test131840_block_19 : Interval test131840 304 320 :=
  interval_of_check test131840 304 16 (by decide +kernel)

theorem test131840_block_20 : Interval test131840 320 336 :=
  interval_of_check test131840 320 16 (by decide +kernel)

theorem test131840_block_21 : Interval test131840 336 352 :=
  interval_of_check test131840 336 16 (by decide +kernel)

theorem test131840_block_22 : Interval test131840 352 368 :=
  interval_of_check test131840 352 16 (by decide +kernel)

theorem test131840_block_23 : Interval test131840 368 384 :=
  interval_of_check test131840 368 16 (by decide +kernel)

theorem test131840_block_24 : Interval test131840 384 400 :=
  interval_of_check test131840 384 16 (by decide +kernel)

theorem test131840_block_25 : Interval test131840 400 416 :=
  interval_of_check test131840 400 16 (by decide +kernel)

theorem test131840_block_26 : Interval test131840 416 432 :=
  interval_of_check test131840 416 16 (by decide +kernel)

theorem test131840_block_27 : Interval test131840 432 448 :=
  interval_of_check test131840 432 16 (by decide +kernel)

theorem test131840_block_28 : Interval test131840 448 464 :=
  interval_of_check test131840 448 16 (by decide +kernel)

theorem test131840_block_29 : Interval test131840 464 480 :=
  interval_of_check test131840 464 16 (by decide +kernel)

theorem test131840_block_30 : Interval test131840 480 496 :=
  interval_of_check test131840 480 16 (by decide +kernel)

theorem test131840_block_31 : Interval test131840 496 512 :=
  interval_of_check test131840 496 16 (by decide +kernel)

theorem test131840_block_32 : Interval test131840 512 528 :=
  interval_of_check test131840 512 16 (by decide +kernel)

theorem test131840_block_33 : Interval test131840 528 544 :=
  interval_of_check test131840 528 16 (by decide +kernel)

theorem test131840_block_34 : Interval test131840 544 560 :=
  interval_of_check test131840 544 16 (by decide +kernel)

theorem test131840_block_35 : Interval test131840 560 576 :=
  interval_of_check test131840 560 16 (by decide +kernel)

theorem test131840_block_36 : Interval test131840 576 592 :=
  interval_of_check test131840 576 16 (by decide +kernel)

theorem test131840_block_37 : Interval test131840 592 608 :=
  interval_of_check test131840 592 16 (by decide +kernel)

theorem test131840_block_38 : Interval test131840 608 624 :=
  interval_of_check test131840 608 16 (by decide +kernel)

theorem test131840_block_39 : Interval test131840 624 640 :=
  interval_of_check test131840 624 16 (by decide +kernel)

theorem test131840_complete : Interval test131840 0 640 :=
  (interval_append test131840 0 320 640
  (interval_append test131840 0 160 320
  (interval_append test131840 0 80 160
  (interval_append test131840 0 32 80
  (interval_append test131840 0 16 32
  test131840_block_0
  test131840_block_1)
  (interval_append test131840 32 48 80
  test131840_block_2
  (interval_append test131840 48 64 80
  test131840_block_3
  test131840_block_4)))
  (interval_append test131840 80 112 160
  (interval_append test131840 80 96 112
  test131840_block_5
  test131840_block_6)
  (interval_append test131840 112 128 160
  test131840_block_7
  (interval_append test131840 128 144 160
  test131840_block_8
  test131840_block_9))))
  (interval_append test131840 160 240 320
  (interval_append test131840 160 192 240
  (interval_append test131840 160 176 192
  test131840_block_10
  test131840_block_11)
  (interval_append test131840 192 208 240
  test131840_block_12
  (interval_append test131840 208 224 240
  test131840_block_13
  test131840_block_14)))
  (interval_append test131840 240 272 320
  (interval_append test131840 240 256 272
  test131840_block_15
  test131840_block_16)
  (interval_append test131840 272 288 320
  test131840_block_17
  (interval_append test131840 288 304 320
  test131840_block_18
  test131840_block_19)))))
  (interval_append test131840 320 480 640
  (interval_append test131840 320 400 480
  (interval_append test131840 320 352 400
  (interval_append test131840 320 336 352
  test131840_block_20
  test131840_block_21)
  (interval_append test131840 352 368 400
  test131840_block_22
  (interval_append test131840 368 384 400
  test131840_block_23
  test131840_block_24)))
  (interval_append test131840 400 432 480
  (interval_append test131840 400 416 432
  test131840_block_25
  test131840_block_26)
  (interval_append test131840 432 448 480
  test131840_block_27
  (interval_append test131840 448 464 480
  test131840_block_28
  test131840_block_29))))
  (interval_append test131840 480 560 640
  (interval_append test131840 480 512 560
  (interval_append test131840 480 496 512
  test131840_block_30
  test131840_block_31)
  (interval_append test131840 512 528 560
  test131840_block_32
  (interval_append test131840 528 544 560
  test131840_block_33
  test131840_block_34)))
  (interval_append test131840 560 592 640
  (interval_append test131840 560 576 592
  test131840_block_35
  test131840_block_36)
  (interval_append test131840 592 608 640
  test131840_block_37
  (interval_append test131840 608 624 640
  test131840_block_38
  test131840_block_39))))))
theorem nodeInterval131840 : Interval nodeTest 131840 132480 := by
  intro i hlo hhi
  have h := test131840_complete (i-131840) (Nat.zero_le _) (by omega)
  simpa only [test131840, Nat.sub_add_cancel hlo] using h

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
def test132480 (i : Nat) := nodeTest (i+132480)
theorem test132480_block_0 : Interval test132480 0 16 :=
  interval_of_check test132480 0 16 (by decide +kernel)

theorem test132480_block_1 : Interval test132480 16 32 :=
  interval_of_check test132480 16 16 (by decide +kernel)

theorem test132480_block_2 : Interval test132480 32 48 :=
  interval_of_check test132480 32 16 (by decide +kernel)

theorem test132480_block_3 : Interval test132480 48 64 :=
  interval_of_check test132480 48 16 (by decide +kernel)

theorem test132480_block_4 : Interval test132480 64 80 :=
  interval_of_check test132480 64 16 (by decide +kernel)

theorem test132480_block_5 : Interval test132480 80 96 :=
  interval_of_check test132480 80 16 (by decide +kernel)

theorem test132480_block_6 : Interval test132480 96 112 :=
  interval_of_check test132480 96 16 (by decide +kernel)

theorem test132480_block_7 : Interval test132480 112 128 :=
  interval_of_check test132480 112 16 (by decide +kernel)

theorem test132480_block_8 : Interval test132480 128 144 :=
  interval_of_check test132480 128 16 (by decide +kernel)

theorem test132480_block_9 : Interval test132480 144 160 :=
  interval_of_check test132480 144 16 (by decide +kernel)

theorem test132480_block_10 : Interval test132480 160 176 :=
  interval_of_check test132480 160 16 (by decide +kernel)

theorem test132480_block_11 : Interval test132480 176 192 :=
  interval_of_check test132480 176 16 (by decide +kernel)

theorem test132480_block_12 : Interval test132480 192 208 :=
  interval_of_check test132480 192 16 (by decide +kernel)

theorem test132480_block_13 : Interval test132480 208 224 :=
  interval_of_check test132480 208 16 (by decide +kernel)

theorem test132480_block_14 : Interval test132480 224 240 :=
  interval_of_check test132480 224 16 (by decide +kernel)

theorem test132480_block_15 : Interval test132480 240 256 :=
  interval_of_check test132480 240 16 (by decide +kernel)

theorem test132480_block_16 : Interval test132480 256 272 :=
  interval_of_check test132480 256 16 (by decide +kernel)

theorem test132480_block_17 : Interval test132480 272 288 :=
  interval_of_check test132480 272 16 (by decide +kernel)

theorem test132480_block_18 : Interval test132480 288 304 :=
  interval_of_check test132480 288 16 (by decide +kernel)

theorem test132480_block_19 : Interval test132480 304 320 :=
  interval_of_check test132480 304 16 (by decide +kernel)

theorem test132480_block_20 : Interval test132480 320 336 :=
  interval_of_check test132480 320 16 (by decide +kernel)

theorem test132480_block_21 : Interval test132480 336 352 :=
  interval_of_check test132480 336 16 (by decide +kernel)

theorem test132480_block_22 : Interval test132480 352 368 :=
  interval_of_check test132480 352 16 (by decide +kernel)

theorem test132480_block_23 : Interval test132480 368 384 :=
  interval_of_check test132480 368 16 (by decide +kernel)

theorem test132480_block_24 : Interval test132480 384 400 :=
  interval_of_check test132480 384 16 (by decide +kernel)

theorem test132480_block_25 : Interval test132480 400 416 :=
  interval_of_check test132480 400 16 (by decide +kernel)

theorem test132480_block_26 : Interval test132480 416 432 :=
  interval_of_check test132480 416 16 (by decide +kernel)

theorem test132480_block_27 : Interval test132480 432 448 :=
  interval_of_check test132480 432 16 (by decide +kernel)

theorem test132480_block_28 : Interval test132480 448 464 :=
  interval_of_check test132480 448 16 (by decide +kernel)

theorem test132480_block_29 : Interval test132480 464 480 :=
  interval_of_check test132480 464 16 (by decide +kernel)

theorem test132480_block_30 : Interval test132480 480 496 :=
  interval_of_check test132480 480 16 (by decide +kernel)

theorem test132480_block_31 : Interval test132480 496 512 :=
  interval_of_check test132480 496 16 (by decide +kernel)

theorem test132480_block_32 : Interval test132480 512 528 :=
  interval_of_check test132480 512 16 (by decide +kernel)

theorem test132480_block_33 : Interval test132480 528 544 :=
  interval_of_check test132480 528 16 (by decide +kernel)

theorem test132480_block_34 : Interval test132480 544 560 :=
  interval_of_check test132480 544 16 (by decide +kernel)

theorem test132480_block_35 : Interval test132480 560 576 :=
  interval_of_check test132480 560 16 (by decide +kernel)

theorem test132480_block_36 : Interval test132480 576 592 :=
  interval_of_check test132480 576 16 (by decide +kernel)

theorem test132480_block_37 : Interval test132480 592 608 :=
  interval_of_check test132480 592 16 (by decide +kernel)

theorem test132480_block_38 : Interval test132480 608 624 :=
  interval_of_check test132480 608 16 (by decide +kernel)

theorem test132480_block_39 : Interval test132480 624 640 :=
  interval_of_check test132480 624 16 (by decide +kernel)

theorem test132480_complete : Interval test132480 0 640 :=
  (interval_append test132480 0 320 640
  (interval_append test132480 0 160 320
  (interval_append test132480 0 80 160
  (interval_append test132480 0 32 80
  (interval_append test132480 0 16 32
  test132480_block_0
  test132480_block_1)
  (interval_append test132480 32 48 80
  test132480_block_2
  (interval_append test132480 48 64 80
  test132480_block_3
  test132480_block_4)))
  (interval_append test132480 80 112 160
  (interval_append test132480 80 96 112
  test132480_block_5
  test132480_block_6)
  (interval_append test132480 112 128 160
  test132480_block_7
  (interval_append test132480 128 144 160
  test132480_block_8
  test132480_block_9))))
  (interval_append test132480 160 240 320
  (interval_append test132480 160 192 240
  (interval_append test132480 160 176 192
  test132480_block_10
  test132480_block_11)
  (interval_append test132480 192 208 240
  test132480_block_12
  (interval_append test132480 208 224 240
  test132480_block_13
  test132480_block_14)))
  (interval_append test132480 240 272 320
  (interval_append test132480 240 256 272
  test132480_block_15
  test132480_block_16)
  (interval_append test132480 272 288 320
  test132480_block_17
  (interval_append test132480 288 304 320
  test132480_block_18
  test132480_block_19)))))
  (interval_append test132480 320 480 640
  (interval_append test132480 320 400 480
  (interval_append test132480 320 352 400
  (interval_append test132480 320 336 352
  test132480_block_20
  test132480_block_21)
  (interval_append test132480 352 368 400
  test132480_block_22
  (interval_append test132480 368 384 400
  test132480_block_23
  test132480_block_24)))
  (interval_append test132480 400 432 480
  (interval_append test132480 400 416 432
  test132480_block_25
  test132480_block_26)
  (interval_append test132480 432 448 480
  test132480_block_27
  (interval_append test132480 448 464 480
  test132480_block_28
  test132480_block_29))))
  (interval_append test132480 480 560 640
  (interval_append test132480 480 512 560
  (interval_append test132480 480 496 512
  test132480_block_30
  test132480_block_31)
  (interval_append test132480 512 528 560
  test132480_block_32
  (interval_append test132480 528 544 560
  test132480_block_33
  test132480_block_34)))
  (interval_append test132480 560 592 640
  (interval_append test132480 560 576 592
  test132480_block_35
  test132480_block_36)
  (interval_append test132480 592 608 640
  test132480_block_37
  (interval_append test132480 608 624 640
  test132480_block_38
  test132480_block_39))))))
theorem nodeInterval132480 : Interval nodeTest 132480 133120 := by
  intro i hlo hhi
  have h := test132480_complete (i-132480) (Nat.zero_le _) (by omega)
  simpa only [test132480, Nat.sub_add_cancel hlo] using h

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
def test133120 (i : Nat) := nodeTest (i+133120)
theorem test133120_block_0 : Interval test133120 0 16 :=
  interval_of_check test133120 0 16 (by decide +kernel)

theorem test133120_block_1 : Interval test133120 16 32 :=
  interval_of_check test133120 16 16 (by decide +kernel)

theorem test133120_block_2 : Interval test133120 32 48 :=
  interval_of_check test133120 32 16 (by decide +kernel)

theorem test133120_block_3 : Interval test133120 48 64 :=
  interval_of_check test133120 48 16 (by decide +kernel)

theorem test133120_block_4 : Interval test133120 64 80 :=
  interval_of_check test133120 64 16 (by decide +kernel)

theorem test133120_block_5 : Interval test133120 80 96 :=
  interval_of_check test133120 80 16 (by decide +kernel)

theorem test133120_block_6 : Interval test133120 96 112 :=
  interval_of_check test133120 96 16 (by decide +kernel)

theorem test133120_block_7 : Interval test133120 112 128 :=
  interval_of_check test133120 112 16 (by decide +kernel)

theorem test133120_block_8 : Interval test133120 128 144 :=
  interval_of_check test133120 128 16 (by decide +kernel)

theorem test133120_block_9 : Interval test133120 144 160 :=
  interval_of_check test133120 144 16 (by decide +kernel)

theorem test133120_block_10 : Interval test133120 160 176 :=
  interval_of_check test133120 160 16 (by decide +kernel)

theorem test133120_block_11 : Interval test133120 176 192 :=
  interval_of_check test133120 176 16 (by decide +kernel)

theorem test133120_block_12 : Interval test133120 192 208 :=
  interval_of_check test133120 192 16 (by decide +kernel)

theorem test133120_block_13 : Interval test133120 208 224 :=
  interval_of_check test133120 208 16 (by decide +kernel)

theorem test133120_block_14 : Interval test133120 224 240 :=
  interval_of_check test133120 224 16 (by decide +kernel)

theorem test133120_block_15 : Interval test133120 240 256 :=
  interval_of_check test133120 240 16 (by decide +kernel)

theorem test133120_block_16 : Interval test133120 256 272 :=
  interval_of_check test133120 256 16 (by decide +kernel)

theorem test133120_block_17 : Interval test133120 272 288 :=
  interval_of_check test133120 272 16 (by decide +kernel)

theorem test133120_block_18 : Interval test133120 288 304 :=
  interval_of_check test133120 288 16 (by decide +kernel)

theorem test133120_block_19 : Interval test133120 304 320 :=
  interval_of_check test133120 304 16 (by decide +kernel)

theorem test133120_block_20 : Interval test133120 320 336 :=
  interval_of_check test133120 320 16 (by decide +kernel)

theorem test133120_block_21 : Interval test133120 336 352 :=
  interval_of_check test133120 336 16 (by decide +kernel)

theorem test133120_block_22 : Interval test133120 352 368 :=
  interval_of_check test133120 352 16 (by decide +kernel)

theorem test133120_block_23 : Interval test133120 368 384 :=
  interval_of_check test133120 368 16 (by decide +kernel)

theorem test133120_block_24 : Interval test133120 384 400 :=
  interval_of_check test133120 384 16 (by decide +kernel)

theorem test133120_block_25 : Interval test133120 400 416 :=
  interval_of_check test133120 400 16 (by decide +kernel)

theorem test133120_block_26 : Interval test133120 416 432 :=
  interval_of_check test133120 416 16 (by decide +kernel)

theorem test133120_block_27 : Interval test133120 432 448 :=
  interval_of_check test133120 432 16 (by decide +kernel)

theorem test133120_block_28 : Interval test133120 448 464 :=
  interval_of_check test133120 448 16 (by decide +kernel)

theorem test133120_block_29 : Interval test133120 464 480 :=
  interval_of_check test133120 464 16 (by decide +kernel)

theorem test133120_block_30 : Interval test133120 480 496 :=
  interval_of_check test133120 480 16 (by decide +kernel)

theorem test133120_block_31 : Interval test133120 496 512 :=
  interval_of_check test133120 496 16 (by decide +kernel)

theorem test133120_block_32 : Interval test133120 512 528 :=
  interval_of_check test133120 512 16 (by decide +kernel)

theorem test133120_block_33 : Interval test133120 528 544 :=
  interval_of_check test133120 528 16 (by decide +kernel)

theorem test133120_block_34 : Interval test133120 544 560 :=
  interval_of_check test133120 544 16 (by decide +kernel)

theorem test133120_block_35 : Interval test133120 560 576 :=
  interval_of_check test133120 560 16 (by decide +kernel)

theorem test133120_block_36 : Interval test133120 576 592 :=
  interval_of_check test133120 576 16 (by decide +kernel)

theorem test133120_block_37 : Interval test133120 592 608 :=
  interval_of_check test133120 592 16 (by decide +kernel)

theorem test133120_block_38 : Interval test133120 608 624 :=
  interval_of_check test133120 608 16 (by decide +kernel)

theorem test133120_block_39 : Interval test133120 624 640 :=
  interval_of_check test133120 624 16 (by decide +kernel)

theorem test133120_complete : Interval test133120 0 640 :=
  (interval_append test133120 0 320 640
  (interval_append test133120 0 160 320
  (interval_append test133120 0 80 160
  (interval_append test133120 0 32 80
  (interval_append test133120 0 16 32
  test133120_block_0
  test133120_block_1)
  (interval_append test133120 32 48 80
  test133120_block_2
  (interval_append test133120 48 64 80
  test133120_block_3
  test133120_block_4)))
  (interval_append test133120 80 112 160
  (interval_append test133120 80 96 112
  test133120_block_5
  test133120_block_6)
  (interval_append test133120 112 128 160
  test133120_block_7
  (interval_append test133120 128 144 160
  test133120_block_8
  test133120_block_9))))
  (interval_append test133120 160 240 320
  (interval_append test133120 160 192 240
  (interval_append test133120 160 176 192
  test133120_block_10
  test133120_block_11)
  (interval_append test133120 192 208 240
  test133120_block_12
  (interval_append test133120 208 224 240
  test133120_block_13
  test133120_block_14)))
  (interval_append test133120 240 272 320
  (interval_append test133120 240 256 272
  test133120_block_15
  test133120_block_16)
  (interval_append test133120 272 288 320
  test133120_block_17
  (interval_append test133120 288 304 320
  test133120_block_18
  test133120_block_19)))))
  (interval_append test133120 320 480 640
  (interval_append test133120 320 400 480
  (interval_append test133120 320 352 400
  (interval_append test133120 320 336 352
  test133120_block_20
  test133120_block_21)
  (interval_append test133120 352 368 400
  test133120_block_22
  (interval_append test133120 368 384 400
  test133120_block_23
  test133120_block_24)))
  (interval_append test133120 400 432 480
  (interval_append test133120 400 416 432
  test133120_block_25
  test133120_block_26)
  (interval_append test133120 432 448 480
  test133120_block_27
  (interval_append test133120 448 464 480
  test133120_block_28
  test133120_block_29))))
  (interval_append test133120 480 560 640
  (interval_append test133120 480 512 560
  (interval_append test133120 480 496 512
  test133120_block_30
  test133120_block_31)
  (interval_append test133120 512 528 560
  test133120_block_32
  (interval_append test133120 528 544 560
  test133120_block_33
  test133120_block_34)))
  (interval_append test133120 560 592 640
  (interval_append test133120 560 576 592
  test133120_block_35
  test133120_block_36)
  (interval_append test133120 592 608 640
  test133120_block_37
  (interval_append test133120 608 624 640
  test133120_block_38
  test133120_block_39))))))
theorem nodeInterval133120 : Interval nodeTest 133120 133760 := by
  intro i hlo hhi
  have h := test133120_complete (i-133120) (Nat.zero_le _) (by omega)
  simpa only [test133120, Nat.sub_add_cancel hlo] using h

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
def test133760 (i : Nat) := nodeTest (i+133760)
theorem test133760_block_0 : Interval test133760 0 16 :=
  interval_of_check test133760 0 16 (by decide +kernel)

theorem test133760_block_1 : Interval test133760 16 32 :=
  interval_of_check test133760 16 16 (by decide +kernel)

theorem test133760_block_2 : Interval test133760 32 48 :=
  interval_of_check test133760 32 16 (by decide +kernel)

theorem test133760_block_3 : Interval test133760 48 64 :=
  interval_of_check test133760 48 16 (by decide +kernel)

theorem test133760_block_4 : Interval test133760 64 80 :=
  interval_of_check test133760 64 16 (by decide +kernel)

theorem test133760_block_5 : Interval test133760 80 96 :=
  interval_of_check test133760 80 16 (by decide +kernel)

theorem test133760_block_6 : Interval test133760 96 112 :=
  interval_of_check test133760 96 16 (by decide +kernel)

theorem test133760_block_7 : Interval test133760 112 128 :=
  interval_of_check test133760 112 16 (by decide +kernel)

theorem test133760_block_8 : Interval test133760 128 144 :=
  interval_of_check test133760 128 16 (by decide +kernel)

theorem test133760_block_9 : Interval test133760 144 160 :=
  interval_of_check test133760 144 16 (by decide +kernel)

theorem test133760_block_10 : Interval test133760 160 176 :=
  interval_of_check test133760 160 16 (by decide +kernel)

theorem test133760_block_11 : Interval test133760 176 192 :=
  interval_of_check test133760 176 16 (by decide +kernel)

theorem test133760_block_12 : Interval test133760 192 208 :=
  interval_of_check test133760 192 16 (by decide +kernel)

theorem test133760_block_13 : Interval test133760 208 224 :=
  interval_of_check test133760 208 16 (by decide +kernel)

theorem test133760_block_14 : Interval test133760 224 240 :=
  interval_of_check test133760 224 16 (by decide +kernel)

theorem test133760_block_15 : Interval test133760 240 256 :=
  interval_of_check test133760 240 16 (by decide +kernel)

theorem test133760_block_16 : Interval test133760 256 272 :=
  interval_of_check test133760 256 16 (by decide +kernel)

theorem test133760_block_17 : Interval test133760 272 288 :=
  interval_of_check test133760 272 16 (by decide +kernel)

theorem test133760_block_18 : Interval test133760 288 304 :=
  interval_of_check test133760 288 16 (by decide +kernel)

theorem test133760_block_19 : Interval test133760 304 320 :=
  interval_of_check test133760 304 16 (by decide +kernel)

theorem test133760_block_20 : Interval test133760 320 336 :=
  interval_of_check test133760 320 16 (by decide +kernel)

theorem test133760_block_21 : Interval test133760 336 352 :=
  interval_of_check test133760 336 16 (by decide +kernel)

theorem test133760_block_22 : Interval test133760 352 368 :=
  interval_of_check test133760 352 16 (by decide +kernel)

theorem test133760_block_23 : Interval test133760 368 384 :=
  interval_of_check test133760 368 16 (by decide +kernel)

theorem test133760_block_24 : Interval test133760 384 400 :=
  interval_of_check test133760 384 16 (by decide +kernel)

theorem test133760_block_25 : Interval test133760 400 416 :=
  interval_of_check test133760 400 16 (by decide +kernel)

theorem test133760_block_26 : Interval test133760 416 432 :=
  interval_of_check test133760 416 16 (by decide +kernel)

theorem test133760_block_27 : Interval test133760 432 448 :=
  interval_of_check test133760 432 16 (by decide +kernel)

theorem test133760_block_28 : Interval test133760 448 464 :=
  interval_of_check test133760 448 16 (by decide +kernel)

theorem test133760_block_29 : Interval test133760 464 480 :=
  interval_of_check test133760 464 16 (by decide +kernel)

theorem test133760_block_30 : Interval test133760 480 496 :=
  interval_of_check test133760 480 16 (by decide +kernel)

theorem test133760_block_31 : Interval test133760 496 512 :=
  interval_of_check test133760 496 16 (by decide +kernel)

theorem test133760_block_32 : Interval test133760 512 528 :=
  interval_of_check test133760 512 16 (by decide +kernel)

theorem test133760_block_33 : Interval test133760 528 544 :=
  interval_of_check test133760 528 16 (by decide +kernel)

theorem test133760_block_34 : Interval test133760 544 560 :=
  interval_of_check test133760 544 16 (by decide +kernel)

theorem test133760_block_35 : Interval test133760 560 576 :=
  interval_of_check test133760 560 16 (by decide +kernel)

theorem test133760_block_36 : Interval test133760 576 592 :=
  interval_of_check test133760 576 16 (by decide +kernel)

theorem test133760_block_37 : Interval test133760 592 608 :=
  interval_of_check test133760 592 16 (by decide +kernel)

theorem test133760_block_38 : Interval test133760 608 624 :=
  interval_of_check test133760 608 16 (by decide +kernel)

theorem test133760_block_39 : Interval test133760 624 640 :=
  interval_of_check test133760 624 16 (by decide +kernel)

theorem test133760_complete : Interval test133760 0 640 :=
  (interval_append test133760 0 320 640
  (interval_append test133760 0 160 320
  (interval_append test133760 0 80 160
  (interval_append test133760 0 32 80
  (interval_append test133760 0 16 32
  test133760_block_0
  test133760_block_1)
  (interval_append test133760 32 48 80
  test133760_block_2
  (interval_append test133760 48 64 80
  test133760_block_3
  test133760_block_4)))
  (interval_append test133760 80 112 160
  (interval_append test133760 80 96 112
  test133760_block_5
  test133760_block_6)
  (interval_append test133760 112 128 160
  test133760_block_7
  (interval_append test133760 128 144 160
  test133760_block_8
  test133760_block_9))))
  (interval_append test133760 160 240 320
  (interval_append test133760 160 192 240
  (interval_append test133760 160 176 192
  test133760_block_10
  test133760_block_11)
  (interval_append test133760 192 208 240
  test133760_block_12
  (interval_append test133760 208 224 240
  test133760_block_13
  test133760_block_14)))
  (interval_append test133760 240 272 320
  (interval_append test133760 240 256 272
  test133760_block_15
  test133760_block_16)
  (interval_append test133760 272 288 320
  test133760_block_17
  (interval_append test133760 288 304 320
  test133760_block_18
  test133760_block_19)))))
  (interval_append test133760 320 480 640
  (interval_append test133760 320 400 480
  (interval_append test133760 320 352 400
  (interval_append test133760 320 336 352
  test133760_block_20
  test133760_block_21)
  (interval_append test133760 352 368 400
  test133760_block_22
  (interval_append test133760 368 384 400
  test133760_block_23
  test133760_block_24)))
  (interval_append test133760 400 432 480
  (interval_append test133760 400 416 432
  test133760_block_25
  test133760_block_26)
  (interval_append test133760 432 448 480
  test133760_block_27
  (interval_append test133760 448 464 480
  test133760_block_28
  test133760_block_29))))
  (interval_append test133760 480 560 640
  (interval_append test133760 480 512 560
  (interval_append test133760 480 496 512
  test133760_block_30
  test133760_block_31)
  (interval_append test133760 512 528 560
  test133760_block_32
  (interval_append test133760 528 544 560
  test133760_block_33
  test133760_block_34)))
  (interval_append test133760 560 592 640
  (interval_append test133760 560 576 592
  test133760_block_35
  test133760_block_36)
  (interval_append test133760 592 608 640
  test133760_block_37
  (interval_append test133760 608 624 640
  test133760_block_38
  test133760_block_39))))))
theorem nodeInterval133760 : Interval nodeTest 133760 134400 := by
  intro i hlo hhi
  have h := test133760_complete (i-133760) (Nat.zero_le _) (by omega)
  simpa only [test133760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724

end
end
