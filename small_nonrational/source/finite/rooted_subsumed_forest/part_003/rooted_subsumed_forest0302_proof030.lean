module
prelude
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test19200 (i : Nat) := nodeTest (i+19200)
theorem test19200_block_0 : Interval test19200 0 16 :=
  interval_of_check test19200 0 16 (by decide +kernel)

theorem test19200_block_1 : Interval test19200 16 32 :=
  interval_of_check test19200 16 16 (by decide +kernel)

theorem test19200_block_2 : Interval test19200 32 48 :=
  interval_of_check test19200 32 16 (by decide +kernel)

theorem test19200_block_3 : Interval test19200 48 64 :=
  interval_of_check test19200 48 16 (by decide +kernel)

theorem test19200_block_4 : Interval test19200 64 80 :=
  interval_of_check test19200 64 16 (by decide +kernel)

theorem test19200_block_5 : Interval test19200 80 96 :=
  interval_of_check test19200 80 16 (by decide +kernel)

theorem test19200_block_6 : Interval test19200 96 112 :=
  interval_of_check test19200 96 16 (by decide +kernel)

theorem test19200_block_7 : Interval test19200 112 128 :=
  interval_of_check test19200 112 16 (by decide +kernel)

theorem test19200_block_8 : Interval test19200 128 144 :=
  interval_of_check test19200 128 16 (by decide +kernel)

theorem test19200_block_9 : Interval test19200 144 160 :=
  interval_of_check test19200 144 16 (by decide +kernel)

theorem test19200_block_10 : Interval test19200 160 176 :=
  interval_of_check test19200 160 16 (by decide +kernel)

theorem test19200_block_11 : Interval test19200 176 192 :=
  interval_of_check test19200 176 16 (by decide +kernel)

theorem test19200_block_12 : Interval test19200 192 208 :=
  interval_of_check test19200 192 16 (by decide +kernel)

theorem test19200_block_13 : Interval test19200 208 224 :=
  interval_of_check test19200 208 16 (by decide +kernel)

theorem test19200_block_14 : Interval test19200 224 240 :=
  interval_of_check test19200 224 16 (by decide +kernel)

theorem test19200_block_15 : Interval test19200 240 256 :=
  interval_of_check test19200 240 16 (by decide +kernel)

theorem test19200_block_16 : Interval test19200 256 272 :=
  interval_of_check test19200 256 16 (by decide +kernel)

theorem test19200_block_17 : Interval test19200 272 288 :=
  interval_of_check test19200 272 16 (by decide +kernel)

theorem test19200_block_18 : Interval test19200 288 304 :=
  interval_of_check test19200 288 16 (by decide +kernel)

theorem test19200_block_19 : Interval test19200 304 320 :=
  interval_of_check test19200 304 16 (by decide +kernel)

theorem test19200_block_20 : Interval test19200 320 336 :=
  interval_of_check test19200 320 16 (by decide +kernel)

theorem test19200_block_21 : Interval test19200 336 352 :=
  interval_of_check test19200 336 16 (by decide +kernel)

theorem test19200_block_22 : Interval test19200 352 368 :=
  interval_of_check test19200 352 16 (by decide +kernel)

theorem test19200_block_23 : Interval test19200 368 384 :=
  interval_of_check test19200 368 16 (by decide +kernel)

theorem test19200_block_24 : Interval test19200 384 400 :=
  interval_of_check test19200 384 16 (by decide +kernel)

theorem test19200_block_25 : Interval test19200 400 416 :=
  interval_of_check test19200 400 16 (by decide +kernel)

theorem test19200_block_26 : Interval test19200 416 432 :=
  interval_of_check test19200 416 16 (by decide +kernel)

theorem test19200_block_27 : Interval test19200 432 448 :=
  interval_of_check test19200 432 16 (by decide +kernel)

theorem test19200_block_28 : Interval test19200 448 464 :=
  interval_of_check test19200 448 16 (by decide +kernel)

theorem test19200_block_29 : Interval test19200 464 480 :=
  interval_of_check test19200 464 16 (by decide +kernel)

theorem test19200_block_30 : Interval test19200 480 496 :=
  interval_of_check test19200 480 16 (by decide +kernel)

theorem test19200_block_31 : Interval test19200 496 512 :=
  interval_of_check test19200 496 16 (by decide +kernel)

theorem test19200_block_32 : Interval test19200 512 528 :=
  interval_of_check test19200 512 16 (by decide +kernel)

theorem test19200_block_33 : Interval test19200 528 544 :=
  interval_of_check test19200 528 16 (by decide +kernel)

theorem test19200_block_34 : Interval test19200 544 560 :=
  interval_of_check test19200 544 16 (by decide +kernel)

theorem test19200_block_35 : Interval test19200 560 576 :=
  interval_of_check test19200 560 16 (by decide +kernel)

theorem test19200_block_36 : Interval test19200 576 592 :=
  interval_of_check test19200 576 16 (by decide +kernel)

theorem test19200_block_37 : Interval test19200 592 608 :=
  interval_of_check test19200 592 16 (by decide +kernel)

theorem test19200_block_38 : Interval test19200 608 624 :=
  interval_of_check test19200 608 16 (by decide +kernel)

theorem test19200_block_39 : Interval test19200 624 638 :=
  interval_of_check test19200 624 14 (by decide +kernel)

theorem test19200_complete : Interval test19200 0 638 :=
  (interval_append test19200 0 320 638
  (interval_append test19200 0 160 320
  (interval_append test19200 0 80 160
  (interval_append test19200 0 32 80
  (interval_append test19200 0 16 32
  test19200_block_0
  test19200_block_1)
  (interval_append test19200 32 48 80
  test19200_block_2
  (interval_append test19200 48 64 80
  test19200_block_3
  test19200_block_4)))
  (interval_append test19200 80 112 160
  (interval_append test19200 80 96 112
  test19200_block_5
  test19200_block_6)
  (interval_append test19200 112 128 160
  test19200_block_7
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9))))
  (interval_append test19200 160 240 320
  (interval_append test19200 160 192 240
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11)
  (interval_append test19200 192 208 240
  test19200_block_12
  (interval_append test19200 208 224 240
  test19200_block_13
  test19200_block_14)))
  (interval_append test19200 240 272 320
  (interval_append test19200 240 256 272
  test19200_block_15
  test19200_block_16)
  (interval_append test19200 272 288 320
  test19200_block_17
  (interval_append test19200 288 304 320
  test19200_block_18
  test19200_block_19)))))
  (interval_append test19200 320 480 638
  (interval_append test19200 320 400 480
  (interval_append test19200 320 352 400
  (interval_append test19200 320 336 352
  test19200_block_20
  test19200_block_21)
  (interval_append test19200 352 368 400
  test19200_block_22
  (interval_append test19200 368 384 400
  test19200_block_23
  test19200_block_24)))
  (interval_append test19200 400 432 480
  (interval_append test19200 400 416 432
  test19200_block_25
  test19200_block_26)
  (interval_append test19200 432 448 480
  test19200_block_27
  (interval_append test19200 448 464 480
  test19200_block_28
  test19200_block_29))))
  (interval_append test19200 480 560 638
  (interval_append test19200 480 512 560
  (interval_append test19200 480 496 512
  test19200_block_30
  test19200_block_31)
  (interval_append test19200 512 528 560
  test19200_block_32
  (interval_append test19200 528 544 560
  test19200_block_33
  test19200_block_34)))
  (interval_append test19200 560 592 638
  (interval_append test19200 560 576 592
  test19200_block_35
  test19200_block_36)
  (interval_append test19200 592 608 638
  test19200_block_37
  (interval_append test19200 608 624 638
  test19200_block_38
  test19200_block_39))))))
theorem nodeInterval19200 : Interval nodeTest 19200 19838 := by
  intro i hlo hhi
  have h := test19200_complete (i-19200) (Nat.zero_le _) (by omega)
  simpa only [test19200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
