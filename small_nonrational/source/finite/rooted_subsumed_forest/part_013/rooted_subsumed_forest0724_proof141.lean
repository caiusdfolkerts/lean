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
def test90240 (i : Nat) := nodeTest (i+90240)
theorem test90240_block_0 : Interval test90240 0 16 :=
  interval_of_check test90240 0 16 (by decide +kernel)

theorem test90240_block_1 : Interval test90240 16 32 :=
  interval_of_check test90240 16 16 (by decide +kernel)

theorem test90240_block_2 : Interval test90240 32 48 :=
  interval_of_check test90240 32 16 (by decide +kernel)

theorem test90240_block_3 : Interval test90240 48 64 :=
  interval_of_check test90240 48 16 (by decide +kernel)

theorem test90240_block_4 : Interval test90240 64 80 :=
  interval_of_check test90240 64 16 (by decide +kernel)

theorem test90240_block_5 : Interval test90240 80 96 :=
  interval_of_check test90240 80 16 (by decide +kernel)

theorem test90240_block_6 : Interval test90240 96 112 :=
  interval_of_check test90240 96 16 (by decide +kernel)

theorem test90240_block_7 : Interval test90240 112 128 :=
  interval_of_check test90240 112 16 (by decide +kernel)

theorem test90240_block_8 : Interval test90240 128 144 :=
  interval_of_check test90240 128 16 (by decide +kernel)

theorem test90240_block_9 : Interval test90240 144 160 :=
  interval_of_check test90240 144 16 (by decide +kernel)

theorem test90240_block_10 : Interval test90240 160 176 :=
  interval_of_check test90240 160 16 (by decide +kernel)

theorem test90240_block_11 : Interval test90240 176 192 :=
  interval_of_check test90240 176 16 (by decide +kernel)

theorem test90240_block_12 : Interval test90240 192 208 :=
  interval_of_check test90240 192 16 (by decide +kernel)

theorem test90240_block_13 : Interval test90240 208 224 :=
  interval_of_check test90240 208 16 (by decide +kernel)

theorem test90240_block_14 : Interval test90240 224 240 :=
  interval_of_check test90240 224 16 (by decide +kernel)

theorem test90240_block_15 : Interval test90240 240 256 :=
  interval_of_check test90240 240 16 (by decide +kernel)

theorem test90240_block_16 : Interval test90240 256 272 :=
  interval_of_check test90240 256 16 (by decide +kernel)

theorem test90240_block_17 : Interval test90240 272 288 :=
  interval_of_check test90240 272 16 (by decide +kernel)

theorem test90240_block_18 : Interval test90240 288 304 :=
  interval_of_check test90240 288 16 (by decide +kernel)

theorem test90240_block_19 : Interval test90240 304 320 :=
  interval_of_check test90240 304 16 (by decide +kernel)

theorem test90240_block_20 : Interval test90240 320 336 :=
  interval_of_check test90240 320 16 (by decide +kernel)

theorem test90240_block_21 : Interval test90240 336 352 :=
  interval_of_check test90240 336 16 (by decide +kernel)

theorem test90240_block_22 : Interval test90240 352 368 :=
  interval_of_check test90240 352 16 (by decide +kernel)

theorem test90240_block_23 : Interval test90240 368 384 :=
  interval_of_check test90240 368 16 (by decide +kernel)

theorem test90240_block_24 : Interval test90240 384 400 :=
  interval_of_check test90240 384 16 (by decide +kernel)

theorem test90240_block_25 : Interval test90240 400 416 :=
  interval_of_check test90240 400 16 (by decide +kernel)

theorem test90240_block_26 : Interval test90240 416 432 :=
  interval_of_check test90240 416 16 (by decide +kernel)

theorem test90240_block_27 : Interval test90240 432 448 :=
  interval_of_check test90240 432 16 (by decide +kernel)

theorem test90240_block_28 : Interval test90240 448 464 :=
  interval_of_check test90240 448 16 (by decide +kernel)

theorem test90240_block_29 : Interval test90240 464 480 :=
  interval_of_check test90240 464 16 (by decide +kernel)

theorem test90240_block_30 : Interval test90240 480 496 :=
  interval_of_check test90240 480 16 (by decide +kernel)

theorem test90240_block_31 : Interval test90240 496 512 :=
  interval_of_check test90240 496 16 (by decide +kernel)

theorem test90240_block_32 : Interval test90240 512 528 :=
  interval_of_check test90240 512 16 (by decide +kernel)

theorem test90240_block_33 : Interval test90240 528 544 :=
  interval_of_check test90240 528 16 (by decide +kernel)

theorem test90240_block_34 : Interval test90240 544 560 :=
  interval_of_check test90240 544 16 (by decide +kernel)

theorem test90240_block_35 : Interval test90240 560 576 :=
  interval_of_check test90240 560 16 (by decide +kernel)

theorem test90240_block_36 : Interval test90240 576 592 :=
  interval_of_check test90240 576 16 (by decide +kernel)

theorem test90240_block_37 : Interval test90240 592 608 :=
  interval_of_check test90240 592 16 (by decide +kernel)

theorem test90240_block_38 : Interval test90240 608 624 :=
  interval_of_check test90240 608 16 (by decide +kernel)

theorem test90240_block_39 : Interval test90240 624 640 :=
  interval_of_check test90240 624 16 (by decide +kernel)

theorem test90240_complete : Interval test90240 0 640 :=
  (interval_append test90240 0 320 640
  (interval_append test90240 0 160 320
  (interval_append test90240 0 80 160
  (interval_append test90240 0 32 80
  (interval_append test90240 0 16 32
  test90240_block_0
  test90240_block_1)
  (interval_append test90240 32 48 80
  test90240_block_2
  (interval_append test90240 48 64 80
  test90240_block_3
  test90240_block_4)))
  (interval_append test90240 80 112 160
  (interval_append test90240 80 96 112
  test90240_block_5
  test90240_block_6)
  (interval_append test90240 112 128 160
  test90240_block_7
  (interval_append test90240 128 144 160
  test90240_block_8
  test90240_block_9))))
  (interval_append test90240 160 240 320
  (interval_append test90240 160 192 240
  (interval_append test90240 160 176 192
  test90240_block_10
  test90240_block_11)
  (interval_append test90240 192 208 240
  test90240_block_12
  (interval_append test90240 208 224 240
  test90240_block_13
  test90240_block_14)))
  (interval_append test90240 240 272 320
  (interval_append test90240 240 256 272
  test90240_block_15
  test90240_block_16)
  (interval_append test90240 272 288 320
  test90240_block_17
  (interval_append test90240 288 304 320
  test90240_block_18
  test90240_block_19)))))
  (interval_append test90240 320 480 640
  (interval_append test90240 320 400 480
  (interval_append test90240 320 352 400
  (interval_append test90240 320 336 352
  test90240_block_20
  test90240_block_21)
  (interval_append test90240 352 368 400
  test90240_block_22
  (interval_append test90240 368 384 400
  test90240_block_23
  test90240_block_24)))
  (interval_append test90240 400 432 480
  (interval_append test90240 400 416 432
  test90240_block_25
  test90240_block_26)
  (interval_append test90240 432 448 480
  test90240_block_27
  (interval_append test90240 448 464 480
  test90240_block_28
  test90240_block_29))))
  (interval_append test90240 480 560 640
  (interval_append test90240 480 512 560
  (interval_append test90240 480 496 512
  test90240_block_30
  test90240_block_31)
  (interval_append test90240 512 528 560
  test90240_block_32
  (interval_append test90240 528 544 560
  test90240_block_33
  test90240_block_34)))
  (interval_append test90240 560 592 640
  (interval_append test90240 560 576 592
  test90240_block_35
  test90240_block_36)
  (interval_append test90240 592 608 640
  test90240_block_37
  (interval_append test90240 608 624 640
  test90240_block_38
  test90240_block_39))))))
theorem nodeInterval90240 : Interval nodeTest 90240 90880 := by
  intro i hlo hhi
  have h := test90240_complete (i-90240) (Nat.zero_le _) (by omega)
  simpa only [test90240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
