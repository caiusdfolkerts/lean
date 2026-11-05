module
prelude
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

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
