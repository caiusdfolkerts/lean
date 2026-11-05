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
def test120960 (i : Nat) := nodeTest (i+120960)
theorem test120960_block_0 : Interval test120960 0 16 :=
  interval_of_check test120960 0 16 (by decide +kernel)

theorem test120960_block_1 : Interval test120960 16 32 :=
  interval_of_check test120960 16 16 (by decide +kernel)

theorem test120960_block_2 : Interval test120960 32 48 :=
  interval_of_check test120960 32 16 (by decide +kernel)

theorem test120960_block_3 : Interval test120960 48 64 :=
  interval_of_check test120960 48 16 (by decide +kernel)

theorem test120960_block_4 : Interval test120960 64 80 :=
  interval_of_check test120960 64 16 (by decide +kernel)

theorem test120960_block_5 : Interval test120960 80 96 :=
  interval_of_check test120960 80 16 (by decide +kernel)

theorem test120960_block_6 : Interval test120960 96 112 :=
  interval_of_check test120960 96 16 (by decide +kernel)

theorem test120960_block_7 : Interval test120960 112 128 :=
  interval_of_check test120960 112 16 (by decide +kernel)

theorem test120960_block_8 : Interval test120960 128 144 :=
  interval_of_check test120960 128 16 (by decide +kernel)

theorem test120960_block_9 : Interval test120960 144 160 :=
  interval_of_check test120960 144 16 (by decide +kernel)

theorem test120960_block_10 : Interval test120960 160 176 :=
  interval_of_check test120960 160 16 (by decide +kernel)

theorem test120960_block_11 : Interval test120960 176 192 :=
  interval_of_check test120960 176 16 (by decide +kernel)

theorem test120960_block_12 : Interval test120960 192 208 :=
  interval_of_check test120960 192 16 (by decide +kernel)

theorem test120960_block_13 : Interval test120960 208 224 :=
  interval_of_check test120960 208 16 (by decide +kernel)

theorem test120960_block_14 : Interval test120960 224 240 :=
  interval_of_check test120960 224 16 (by decide +kernel)

theorem test120960_block_15 : Interval test120960 240 256 :=
  interval_of_check test120960 240 16 (by decide +kernel)

theorem test120960_block_16 : Interval test120960 256 272 :=
  interval_of_check test120960 256 16 (by decide +kernel)

theorem test120960_block_17 : Interval test120960 272 288 :=
  interval_of_check test120960 272 16 (by decide +kernel)

theorem test120960_block_18 : Interval test120960 288 304 :=
  interval_of_check test120960 288 16 (by decide +kernel)

theorem test120960_block_19 : Interval test120960 304 320 :=
  interval_of_check test120960 304 16 (by decide +kernel)

theorem test120960_block_20 : Interval test120960 320 336 :=
  interval_of_check test120960 320 16 (by decide +kernel)

theorem test120960_block_21 : Interval test120960 336 352 :=
  interval_of_check test120960 336 16 (by decide +kernel)

theorem test120960_block_22 : Interval test120960 352 368 :=
  interval_of_check test120960 352 16 (by decide +kernel)

theorem test120960_block_23 : Interval test120960 368 384 :=
  interval_of_check test120960 368 16 (by decide +kernel)

theorem test120960_block_24 : Interval test120960 384 400 :=
  interval_of_check test120960 384 16 (by decide +kernel)

theorem test120960_block_25 : Interval test120960 400 416 :=
  interval_of_check test120960 400 16 (by decide +kernel)

theorem test120960_block_26 : Interval test120960 416 432 :=
  interval_of_check test120960 416 16 (by decide +kernel)

theorem test120960_block_27 : Interval test120960 432 448 :=
  interval_of_check test120960 432 16 (by decide +kernel)

theorem test120960_block_28 : Interval test120960 448 464 :=
  interval_of_check test120960 448 16 (by decide +kernel)

theorem test120960_block_29 : Interval test120960 464 480 :=
  interval_of_check test120960 464 16 (by decide +kernel)

theorem test120960_block_30 : Interval test120960 480 496 :=
  interval_of_check test120960 480 16 (by decide +kernel)

theorem test120960_block_31 : Interval test120960 496 512 :=
  interval_of_check test120960 496 16 (by decide +kernel)

theorem test120960_block_32 : Interval test120960 512 528 :=
  interval_of_check test120960 512 16 (by decide +kernel)

theorem test120960_block_33 : Interval test120960 528 544 :=
  interval_of_check test120960 528 16 (by decide +kernel)

theorem test120960_block_34 : Interval test120960 544 560 :=
  interval_of_check test120960 544 16 (by decide +kernel)

theorem test120960_block_35 : Interval test120960 560 576 :=
  interval_of_check test120960 560 16 (by decide +kernel)

theorem test120960_block_36 : Interval test120960 576 592 :=
  interval_of_check test120960 576 16 (by decide +kernel)

theorem test120960_block_37 : Interval test120960 592 608 :=
  interval_of_check test120960 592 16 (by decide +kernel)

theorem test120960_block_38 : Interval test120960 608 624 :=
  interval_of_check test120960 608 16 (by decide +kernel)

theorem test120960_block_39 : Interval test120960 624 640 :=
  interval_of_check test120960 624 16 (by decide +kernel)

theorem test120960_complete : Interval test120960 0 640 :=
  (interval_append test120960 0 320 640
  (interval_append test120960 0 160 320
  (interval_append test120960 0 80 160
  (interval_append test120960 0 32 80
  (interval_append test120960 0 16 32
  test120960_block_0
  test120960_block_1)
  (interval_append test120960 32 48 80
  test120960_block_2
  (interval_append test120960 48 64 80
  test120960_block_3
  test120960_block_4)))
  (interval_append test120960 80 112 160
  (interval_append test120960 80 96 112
  test120960_block_5
  test120960_block_6)
  (interval_append test120960 112 128 160
  test120960_block_7
  (interval_append test120960 128 144 160
  test120960_block_8
  test120960_block_9))))
  (interval_append test120960 160 240 320
  (interval_append test120960 160 192 240
  (interval_append test120960 160 176 192
  test120960_block_10
  test120960_block_11)
  (interval_append test120960 192 208 240
  test120960_block_12
  (interval_append test120960 208 224 240
  test120960_block_13
  test120960_block_14)))
  (interval_append test120960 240 272 320
  (interval_append test120960 240 256 272
  test120960_block_15
  test120960_block_16)
  (interval_append test120960 272 288 320
  test120960_block_17
  (interval_append test120960 288 304 320
  test120960_block_18
  test120960_block_19)))))
  (interval_append test120960 320 480 640
  (interval_append test120960 320 400 480
  (interval_append test120960 320 352 400
  (interval_append test120960 320 336 352
  test120960_block_20
  test120960_block_21)
  (interval_append test120960 352 368 400
  test120960_block_22
  (interval_append test120960 368 384 400
  test120960_block_23
  test120960_block_24)))
  (interval_append test120960 400 432 480
  (interval_append test120960 400 416 432
  test120960_block_25
  test120960_block_26)
  (interval_append test120960 432 448 480
  test120960_block_27
  (interval_append test120960 448 464 480
  test120960_block_28
  test120960_block_29))))
  (interval_append test120960 480 560 640
  (interval_append test120960 480 512 560
  (interval_append test120960 480 496 512
  test120960_block_30
  test120960_block_31)
  (interval_append test120960 512 528 560
  test120960_block_32
  (interval_append test120960 528 544 560
  test120960_block_33
  test120960_block_34)))
  (interval_append test120960 560 592 640
  (interval_append test120960 560 576 592
  test120960_block_35
  test120960_block_36)
  (interval_append test120960 592 608 640
  test120960_block_37
  (interval_append test120960 608 624 640
  test120960_block_38
  test120960_block_39))))))
theorem nodeInterval120960 : Interval nodeTest 120960 121600 := by
  intro i hlo hhi
  have h := test120960_complete (i-120960) (Nat.zero_le _) (by omega)
  simpa only [test120960, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
