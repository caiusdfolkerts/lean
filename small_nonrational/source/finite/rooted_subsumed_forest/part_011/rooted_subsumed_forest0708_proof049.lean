module
prelude
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test31360 (i : Nat) := nodeTest (i+31360)
theorem test31360_block_0 : Interval test31360 0 16 :=
  interval_of_check test31360 0 16 (by decide +kernel)

theorem test31360_block_1 : Interval test31360 16 32 :=
  interval_of_check test31360 16 16 (by decide +kernel)

theorem test31360_block_2 : Interval test31360 32 48 :=
  interval_of_check test31360 32 16 (by decide +kernel)

theorem test31360_block_3 : Interval test31360 48 64 :=
  interval_of_check test31360 48 16 (by decide +kernel)

theorem test31360_block_4 : Interval test31360 64 80 :=
  interval_of_check test31360 64 16 (by decide +kernel)

theorem test31360_block_5 : Interval test31360 80 96 :=
  interval_of_check test31360 80 16 (by decide +kernel)

theorem test31360_block_6 : Interval test31360 96 112 :=
  interval_of_check test31360 96 16 (by decide +kernel)

theorem test31360_block_7 : Interval test31360 112 128 :=
  interval_of_check test31360 112 16 (by decide +kernel)

theorem test31360_block_8 : Interval test31360 128 144 :=
  interval_of_check test31360 128 16 (by decide +kernel)

theorem test31360_block_9 : Interval test31360 144 160 :=
  interval_of_check test31360 144 16 (by decide +kernel)

theorem test31360_block_10 : Interval test31360 160 176 :=
  interval_of_check test31360 160 16 (by decide +kernel)

theorem test31360_block_11 : Interval test31360 176 192 :=
  interval_of_check test31360 176 16 (by decide +kernel)

theorem test31360_block_12 : Interval test31360 192 208 :=
  interval_of_check test31360 192 16 (by decide +kernel)

theorem test31360_block_13 : Interval test31360 208 224 :=
  interval_of_check test31360 208 16 (by decide +kernel)

theorem test31360_block_14 : Interval test31360 224 240 :=
  interval_of_check test31360 224 16 (by decide +kernel)

theorem test31360_block_15 : Interval test31360 240 256 :=
  interval_of_check test31360 240 16 (by decide +kernel)

theorem test31360_block_16 : Interval test31360 256 272 :=
  interval_of_check test31360 256 16 (by decide +kernel)

theorem test31360_block_17 : Interval test31360 272 288 :=
  interval_of_check test31360 272 16 (by decide +kernel)

theorem test31360_block_18 : Interval test31360 288 304 :=
  interval_of_check test31360 288 16 (by decide +kernel)

theorem test31360_block_19 : Interval test31360 304 320 :=
  interval_of_check test31360 304 16 (by decide +kernel)

theorem test31360_block_20 : Interval test31360 320 336 :=
  interval_of_check test31360 320 16 (by decide +kernel)

theorem test31360_block_21 : Interval test31360 336 352 :=
  interval_of_check test31360 336 16 (by decide +kernel)

theorem test31360_block_22 : Interval test31360 352 368 :=
  interval_of_check test31360 352 16 (by decide +kernel)

theorem test31360_block_23 : Interval test31360 368 384 :=
  interval_of_check test31360 368 16 (by decide +kernel)

theorem test31360_block_24 : Interval test31360 384 400 :=
  interval_of_check test31360 384 16 (by decide +kernel)

theorem test31360_block_25 : Interval test31360 400 416 :=
  interval_of_check test31360 400 16 (by decide +kernel)

theorem test31360_block_26 : Interval test31360 416 432 :=
  interval_of_check test31360 416 16 (by decide +kernel)

theorem test31360_block_27 : Interval test31360 432 448 :=
  interval_of_check test31360 432 16 (by decide +kernel)

theorem test31360_block_28 : Interval test31360 448 464 :=
  interval_of_check test31360 448 16 (by decide +kernel)

theorem test31360_block_29 : Interval test31360 464 480 :=
  interval_of_check test31360 464 16 (by decide +kernel)

theorem test31360_block_30 : Interval test31360 480 496 :=
  interval_of_check test31360 480 16 (by decide +kernel)

theorem test31360_block_31 : Interval test31360 496 512 :=
  interval_of_check test31360 496 16 (by decide +kernel)

theorem test31360_block_32 : Interval test31360 512 528 :=
  interval_of_check test31360 512 16 (by decide +kernel)

theorem test31360_block_33 : Interval test31360 528 544 :=
  interval_of_check test31360 528 16 (by decide +kernel)

theorem test31360_block_34 : Interval test31360 544 560 :=
  interval_of_check test31360 544 16 (by decide +kernel)

theorem test31360_block_35 : Interval test31360 560 576 :=
  interval_of_check test31360 560 16 (by decide +kernel)

theorem test31360_block_36 : Interval test31360 576 592 :=
  interval_of_check test31360 576 16 (by decide +kernel)

theorem test31360_block_37 : Interval test31360 592 608 :=
  interval_of_check test31360 592 16 (by decide +kernel)

theorem test31360_block_38 : Interval test31360 608 624 :=
  interval_of_check test31360 608 16 (by decide +kernel)

theorem test31360_block_39 : Interval test31360 624 640 :=
  interval_of_check test31360 624 16 (by decide +kernel)

theorem test31360_complete : Interval test31360 0 640 :=
  (interval_append test31360 0 320 640
  (interval_append test31360 0 160 320
  (interval_append test31360 0 80 160
  (interval_append test31360 0 32 80
  (interval_append test31360 0 16 32
  test31360_block_0
  test31360_block_1)
  (interval_append test31360 32 48 80
  test31360_block_2
  (interval_append test31360 48 64 80
  test31360_block_3
  test31360_block_4)))
  (interval_append test31360 80 112 160
  (interval_append test31360 80 96 112
  test31360_block_5
  test31360_block_6)
  (interval_append test31360 112 128 160
  test31360_block_7
  (interval_append test31360 128 144 160
  test31360_block_8
  test31360_block_9))))
  (interval_append test31360 160 240 320
  (interval_append test31360 160 192 240
  (interval_append test31360 160 176 192
  test31360_block_10
  test31360_block_11)
  (interval_append test31360 192 208 240
  test31360_block_12
  (interval_append test31360 208 224 240
  test31360_block_13
  test31360_block_14)))
  (interval_append test31360 240 272 320
  (interval_append test31360 240 256 272
  test31360_block_15
  test31360_block_16)
  (interval_append test31360 272 288 320
  test31360_block_17
  (interval_append test31360 288 304 320
  test31360_block_18
  test31360_block_19)))))
  (interval_append test31360 320 480 640
  (interval_append test31360 320 400 480
  (interval_append test31360 320 352 400
  (interval_append test31360 320 336 352
  test31360_block_20
  test31360_block_21)
  (interval_append test31360 352 368 400
  test31360_block_22
  (interval_append test31360 368 384 400
  test31360_block_23
  test31360_block_24)))
  (interval_append test31360 400 432 480
  (interval_append test31360 400 416 432
  test31360_block_25
  test31360_block_26)
  (interval_append test31360 432 448 480
  test31360_block_27
  (interval_append test31360 448 464 480
  test31360_block_28
  test31360_block_29))))
  (interval_append test31360 480 560 640
  (interval_append test31360 480 512 560
  (interval_append test31360 480 496 512
  test31360_block_30
  test31360_block_31)
  (interval_append test31360 512 528 560
  test31360_block_32
  (interval_append test31360 528 544 560
  test31360_block_33
  test31360_block_34)))
  (interval_append test31360 560 592 640
  (interval_append test31360 560 576 592
  test31360_block_35
  test31360_block_36)
  (interval_append test31360 592 608 640
  test31360_block_37
  (interval_append test31360 608 624 640
  test31360_block_38
  test31360_block_39))))))
theorem nodeInterval31360 : Interval nodeTest 31360 32000 := by
  intro i hlo hhi
  have h := test31360_complete (i-31360) (Nat.zero_le _) (by omega)
  simpa only [test31360, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
