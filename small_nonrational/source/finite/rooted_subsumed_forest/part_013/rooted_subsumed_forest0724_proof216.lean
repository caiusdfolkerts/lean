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
def test138240 (i : Nat) := nodeTest (i+138240)
theorem test138240_block_0 : Interval test138240 0 16 :=
  interval_of_check test138240 0 16 (by decide +kernel)

theorem test138240_block_1 : Interval test138240 16 32 :=
  interval_of_check test138240 16 16 (by decide +kernel)

theorem test138240_block_2 : Interval test138240 32 48 :=
  interval_of_check test138240 32 16 (by decide +kernel)

theorem test138240_block_3 : Interval test138240 48 64 :=
  interval_of_check test138240 48 16 (by decide +kernel)

theorem test138240_block_4 : Interval test138240 64 80 :=
  interval_of_check test138240 64 16 (by decide +kernel)

theorem test138240_block_5 : Interval test138240 80 96 :=
  interval_of_check test138240 80 16 (by decide +kernel)

theorem test138240_block_6 : Interval test138240 96 112 :=
  interval_of_check test138240 96 16 (by decide +kernel)

theorem test138240_block_7 : Interval test138240 112 128 :=
  interval_of_check test138240 112 16 (by decide +kernel)

theorem test138240_block_8 : Interval test138240 128 144 :=
  interval_of_check test138240 128 16 (by decide +kernel)

theorem test138240_block_9 : Interval test138240 144 160 :=
  interval_of_check test138240 144 16 (by decide +kernel)

theorem test138240_block_10 : Interval test138240 160 176 :=
  interval_of_check test138240 160 16 (by decide +kernel)

theorem test138240_block_11 : Interval test138240 176 192 :=
  interval_of_check test138240 176 16 (by decide +kernel)

theorem test138240_block_12 : Interval test138240 192 208 :=
  interval_of_check test138240 192 16 (by decide +kernel)

theorem test138240_block_13 : Interval test138240 208 224 :=
  interval_of_check test138240 208 16 (by decide +kernel)

theorem test138240_block_14 : Interval test138240 224 240 :=
  interval_of_check test138240 224 16 (by decide +kernel)

theorem test138240_block_15 : Interval test138240 240 256 :=
  interval_of_check test138240 240 16 (by decide +kernel)

theorem test138240_block_16 : Interval test138240 256 272 :=
  interval_of_check test138240 256 16 (by decide +kernel)

theorem test138240_block_17 : Interval test138240 272 288 :=
  interval_of_check test138240 272 16 (by decide +kernel)

theorem test138240_block_18 : Interval test138240 288 304 :=
  interval_of_check test138240 288 16 (by decide +kernel)

theorem test138240_block_19 : Interval test138240 304 320 :=
  interval_of_check test138240 304 16 (by decide +kernel)

theorem test138240_block_20 : Interval test138240 320 336 :=
  interval_of_check test138240 320 16 (by decide +kernel)

theorem test138240_block_21 : Interval test138240 336 352 :=
  interval_of_check test138240 336 16 (by decide +kernel)

theorem test138240_block_22 : Interval test138240 352 368 :=
  interval_of_check test138240 352 16 (by decide +kernel)

theorem test138240_block_23 : Interval test138240 368 384 :=
  interval_of_check test138240 368 16 (by decide +kernel)

theorem test138240_block_24 : Interval test138240 384 400 :=
  interval_of_check test138240 384 16 (by decide +kernel)

theorem test138240_block_25 : Interval test138240 400 416 :=
  interval_of_check test138240 400 16 (by decide +kernel)

theorem test138240_block_26 : Interval test138240 416 432 :=
  interval_of_check test138240 416 16 (by decide +kernel)

theorem test138240_block_27 : Interval test138240 432 448 :=
  interval_of_check test138240 432 16 (by decide +kernel)

theorem test138240_block_28 : Interval test138240 448 464 :=
  interval_of_check test138240 448 16 (by decide +kernel)

theorem test138240_block_29 : Interval test138240 464 480 :=
  interval_of_check test138240 464 16 (by decide +kernel)

theorem test138240_block_30 : Interval test138240 480 496 :=
  interval_of_check test138240 480 16 (by decide +kernel)

theorem test138240_block_31 : Interval test138240 496 512 :=
  interval_of_check test138240 496 16 (by decide +kernel)

theorem test138240_block_32 : Interval test138240 512 528 :=
  interval_of_check test138240 512 16 (by decide +kernel)

theorem test138240_block_33 : Interval test138240 528 544 :=
  interval_of_check test138240 528 16 (by decide +kernel)

theorem test138240_block_34 : Interval test138240 544 560 :=
  interval_of_check test138240 544 16 (by decide +kernel)

theorem test138240_block_35 : Interval test138240 560 576 :=
  interval_of_check test138240 560 16 (by decide +kernel)

theorem test138240_block_36 : Interval test138240 576 592 :=
  interval_of_check test138240 576 16 (by decide +kernel)

theorem test138240_block_37 : Interval test138240 592 608 :=
  interval_of_check test138240 592 16 (by decide +kernel)

theorem test138240_block_38 : Interval test138240 608 624 :=
  interval_of_check test138240 608 16 (by decide +kernel)

theorem test138240_block_39 : Interval test138240 624 640 :=
  interval_of_check test138240 624 16 (by decide +kernel)

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
theorem nodeInterval138240 : Interval nodeTest 138240 138880 := by
  intro i hlo hhi
  have h := test138240_complete (i-138240) (Nat.zero_le _) (by omega)
  simpa only [test138240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
