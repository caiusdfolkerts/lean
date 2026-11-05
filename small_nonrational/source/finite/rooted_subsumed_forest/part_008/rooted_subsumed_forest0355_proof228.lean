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
def test145920 (i : Nat) := nodeTest (i+145920)
theorem test145920_block_0 : Interval test145920 0 16 :=
  interval_of_check test145920 0 16 (by decide +kernel)

theorem test145920_block_1 : Interval test145920 16 32 :=
  interval_of_check test145920 16 16 (by decide +kernel)

theorem test145920_block_2 : Interval test145920 32 48 :=
  interval_of_check test145920 32 16 (by decide +kernel)

theorem test145920_block_3 : Interval test145920 48 64 :=
  interval_of_check test145920 48 16 (by decide +kernel)

theorem test145920_block_4 : Interval test145920 64 80 :=
  interval_of_check test145920 64 16 (by decide +kernel)

theorem test145920_block_5 : Interval test145920 80 96 :=
  interval_of_check test145920 80 16 (by decide +kernel)

theorem test145920_block_6 : Interval test145920 96 112 :=
  interval_of_check test145920 96 16 (by decide +kernel)

theorem test145920_block_7 : Interval test145920 112 128 :=
  interval_of_check test145920 112 16 (by decide +kernel)

theorem test145920_block_8 : Interval test145920 128 144 :=
  interval_of_check test145920 128 16 (by decide +kernel)

theorem test145920_block_9 : Interval test145920 144 160 :=
  interval_of_check test145920 144 16 (by decide +kernel)

theorem test145920_block_10 : Interval test145920 160 176 :=
  interval_of_check test145920 160 16 (by decide +kernel)

theorem test145920_block_11 : Interval test145920 176 192 :=
  interval_of_check test145920 176 16 (by decide +kernel)

theorem test145920_block_12 : Interval test145920 192 208 :=
  interval_of_check test145920 192 16 (by decide +kernel)

theorem test145920_block_13 : Interval test145920 208 224 :=
  interval_of_check test145920 208 16 (by decide +kernel)

theorem test145920_block_14 : Interval test145920 224 240 :=
  interval_of_check test145920 224 16 (by decide +kernel)

theorem test145920_block_15 : Interval test145920 240 256 :=
  interval_of_check test145920 240 16 (by decide +kernel)

theorem test145920_block_16 : Interval test145920 256 272 :=
  interval_of_check test145920 256 16 (by decide +kernel)

theorem test145920_block_17 : Interval test145920 272 288 :=
  interval_of_check test145920 272 16 (by decide +kernel)

theorem test145920_block_18 : Interval test145920 288 304 :=
  interval_of_check test145920 288 16 (by decide +kernel)

theorem test145920_block_19 : Interval test145920 304 320 :=
  interval_of_check test145920 304 16 (by decide +kernel)

theorem test145920_block_20 : Interval test145920 320 336 :=
  interval_of_check test145920 320 16 (by decide +kernel)

theorem test145920_block_21 : Interval test145920 336 352 :=
  interval_of_check test145920 336 16 (by decide +kernel)

theorem test145920_block_22 : Interval test145920 352 368 :=
  interval_of_check test145920 352 16 (by decide +kernel)

theorem test145920_block_23 : Interval test145920 368 384 :=
  interval_of_check test145920 368 16 (by decide +kernel)

theorem test145920_block_24 : Interval test145920 384 400 :=
  interval_of_check test145920 384 16 (by decide +kernel)

theorem test145920_block_25 : Interval test145920 400 416 :=
  interval_of_check test145920 400 16 (by decide +kernel)

theorem test145920_block_26 : Interval test145920 416 432 :=
  interval_of_check test145920 416 16 (by decide +kernel)

theorem test145920_block_27 : Interval test145920 432 448 :=
  interval_of_check test145920 432 16 (by decide +kernel)

theorem test145920_block_28 : Interval test145920 448 464 :=
  interval_of_check test145920 448 16 (by decide +kernel)

theorem test145920_block_29 : Interval test145920 464 480 :=
  interval_of_check test145920 464 16 (by decide +kernel)

theorem test145920_block_30 : Interval test145920 480 496 :=
  interval_of_check test145920 480 16 (by decide +kernel)

theorem test145920_block_31 : Interval test145920 496 512 :=
  interval_of_check test145920 496 16 (by decide +kernel)

theorem test145920_block_32 : Interval test145920 512 528 :=
  interval_of_check test145920 512 16 (by decide +kernel)

theorem test145920_block_33 : Interval test145920 528 544 :=
  interval_of_check test145920 528 16 (by decide +kernel)

theorem test145920_block_34 : Interval test145920 544 560 :=
  interval_of_check test145920 544 16 (by decide +kernel)

theorem test145920_block_35 : Interval test145920 560 576 :=
  interval_of_check test145920 560 16 (by decide +kernel)

theorem test145920_block_36 : Interval test145920 576 592 :=
  interval_of_check test145920 576 16 (by decide +kernel)

theorem test145920_block_37 : Interval test145920 592 608 :=
  interval_of_check test145920 592 16 (by decide +kernel)

theorem test145920_block_38 : Interval test145920 608 624 :=
  interval_of_check test145920 608 16 (by decide +kernel)

theorem test145920_block_39 : Interval test145920 624 640 :=
  interval_of_check test145920 624 16 (by decide +kernel)

theorem test145920_complete : Interval test145920 0 640 :=
  (interval_append test145920 0 320 640
  (interval_append test145920 0 160 320
  (interval_append test145920 0 80 160
  (interval_append test145920 0 32 80
  (interval_append test145920 0 16 32
  test145920_block_0
  test145920_block_1)
  (interval_append test145920 32 48 80
  test145920_block_2
  (interval_append test145920 48 64 80
  test145920_block_3
  test145920_block_4)))
  (interval_append test145920 80 112 160
  (interval_append test145920 80 96 112
  test145920_block_5
  test145920_block_6)
  (interval_append test145920 112 128 160
  test145920_block_7
  (interval_append test145920 128 144 160
  test145920_block_8
  test145920_block_9))))
  (interval_append test145920 160 240 320
  (interval_append test145920 160 192 240
  (interval_append test145920 160 176 192
  test145920_block_10
  test145920_block_11)
  (interval_append test145920 192 208 240
  test145920_block_12
  (interval_append test145920 208 224 240
  test145920_block_13
  test145920_block_14)))
  (interval_append test145920 240 272 320
  (interval_append test145920 240 256 272
  test145920_block_15
  test145920_block_16)
  (interval_append test145920 272 288 320
  test145920_block_17
  (interval_append test145920 288 304 320
  test145920_block_18
  test145920_block_19)))))
  (interval_append test145920 320 480 640
  (interval_append test145920 320 400 480
  (interval_append test145920 320 352 400
  (interval_append test145920 320 336 352
  test145920_block_20
  test145920_block_21)
  (interval_append test145920 352 368 400
  test145920_block_22
  (interval_append test145920 368 384 400
  test145920_block_23
  test145920_block_24)))
  (interval_append test145920 400 432 480
  (interval_append test145920 400 416 432
  test145920_block_25
  test145920_block_26)
  (interval_append test145920 432 448 480
  test145920_block_27
  (interval_append test145920 448 464 480
  test145920_block_28
  test145920_block_29))))
  (interval_append test145920 480 560 640
  (interval_append test145920 480 512 560
  (interval_append test145920 480 496 512
  test145920_block_30
  test145920_block_31)
  (interval_append test145920 512 528 560
  test145920_block_32
  (interval_append test145920 528 544 560
  test145920_block_33
  test145920_block_34)))
  (interval_append test145920 560 592 640
  (interval_append test145920 560 576 592
  test145920_block_35
  test145920_block_36)
  (interval_append test145920 592 608 640
  test145920_block_37
  (interval_append test145920 608 624 640
  test145920_block_38
  test145920_block_39))))))
theorem nodeInterval145920 : Interval nodeTest 145920 146560 := by
  intro i hlo hhi
  have h := test145920_complete (i-145920) (Nat.zero_le _) (by omega)
  simpa only [test145920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
