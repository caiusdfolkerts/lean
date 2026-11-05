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
def test12160 (i : Nat) := nodeTest (i+12160)
theorem test12160_block_0 : Interval test12160 0 16 :=
  interval_of_check test12160 0 16 (by decide +kernel)

theorem test12160_block_1 : Interval test12160 16 32 :=
  interval_of_check test12160 16 16 (by decide +kernel)

theorem test12160_block_2 : Interval test12160 32 48 :=
  interval_of_check test12160 32 16 (by decide +kernel)

theorem test12160_block_3 : Interval test12160 48 64 :=
  interval_of_check test12160 48 16 (by decide +kernel)

theorem test12160_block_4 : Interval test12160 64 80 :=
  interval_of_check test12160 64 16 (by decide +kernel)

theorem test12160_block_5 : Interval test12160 80 96 :=
  interval_of_check test12160 80 16 (by decide +kernel)

theorem test12160_block_6 : Interval test12160 96 112 :=
  interval_of_check test12160 96 16 (by decide +kernel)

theorem test12160_block_7 : Interval test12160 112 128 :=
  interval_of_check test12160 112 16 (by decide +kernel)

theorem test12160_block_8 : Interval test12160 128 144 :=
  interval_of_check test12160 128 16 (by decide +kernel)

theorem test12160_block_9 : Interval test12160 144 160 :=
  interval_of_check test12160 144 16 (by decide +kernel)

theorem test12160_block_10 : Interval test12160 160 176 :=
  interval_of_check test12160 160 16 (by decide +kernel)

theorem test12160_block_11 : Interval test12160 176 192 :=
  interval_of_check test12160 176 16 (by decide +kernel)

theorem test12160_block_12 : Interval test12160 192 208 :=
  interval_of_check test12160 192 16 (by decide +kernel)

theorem test12160_block_13 : Interval test12160 208 224 :=
  interval_of_check test12160 208 16 (by decide +kernel)

theorem test12160_block_14 : Interval test12160 224 240 :=
  interval_of_check test12160 224 16 (by decide +kernel)

theorem test12160_block_15 : Interval test12160 240 256 :=
  interval_of_check test12160 240 16 (by decide +kernel)

theorem test12160_block_16 : Interval test12160 256 272 :=
  interval_of_check test12160 256 16 (by decide +kernel)

theorem test12160_block_17 : Interval test12160 272 288 :=
  interval_of_check test12160 272 16 (by decide +kernel)

theorem test12160_block_18 : Interval test12160 288 304 :=
  interval_of_check test12160 288 16 (by decide +kernel)

theorem test12160_block_19 : Interval test12160 304 320 :=
  interval_of_check test12160 304 16 (by decide +kernel)

theorem test12160_block_20 : Interval test12160 320 336 :=
  interval_of_check test12160 320 16 (by decide +kernel)

theorem test12160_block_21 : Interval test12160 336 352 :=
  interval_of_check test12160 336 16 (by decide +kernel)

theorem test12160_block_22 : Interval test12160 352 368 :=
  interval_of_check test12160 352 16 (by decide +kernel)

theorem test12160_block_23 : Interval test12160 368 384 :=
  interval_of_check test12160 368 16 (by decide +kernel)

theorem test12160_block_24 : Interval test12160 384 400 :=
  interval_of_check test12160 384 16 (by decide +kernel)

theorem test12160_block_25 : Interval test12160 400 416 :=
  interval_of_check test12160 400 16 (by decide +kernel)

theorem test12160_block_26 : Interval test12160 416 432 :=
  interval_of_check test12160 416 16 (by decide +kernel)

theorem test12160_block_27 : Interval test12160 432 448 :=
  interval_of_check test12160 432 16 (by decide +kernel)

theorem test12160_block_28 : Interval test12160 448 464 :=
  interval_of_check test12160 448 16 (by decide +kernel)

theorem test12160_block_29 : Interval test12160 464 480 :=
  interval_of_check test12160 464 16 (by decide +kernel)

theorem test12160_block_30 : Interval test12160 480 496 :=
  interval_of_check test12160 480 16 (by decide +kernel)

theorem test12160_block_31 : Interval test12160 496 512 :=
  interval_of_check test12160 496 16 (by decide +kernel)

theorem test12160_block_32 : Interval test12160 512 528 :=
  interval_of_check test12160 512 16 (by decide +kernel)

theorem test12160_block_33 : Interval test12160 528 544 :=
  interval_of_check test12160 528 16 (by decide +kernel)

theorem test12160_block_34 : Interval test12160 544 560 :=
  interval_of_check test12160 544 16 (by decide +kernel)

theorem test12160_block_35 : Interval test12160 560 576 :=
  interval_of_check test12160 560 16 (by decide +kernel)

theorem test12160_block_36 : Interval test12160 576 592 :=
  interval_of_check test12160 576 16 (by decide +kernel)

theorem test12160_block_37 : Interval test12160 592 608 :=
  interval_of_check test12160 592 16 (by decide +kernel)

theorem test12160_block_38 : Interval test12160 608 624 :=
  interval_of_check test12160 608 16 (by decide +kernel)

theorem test12160_block_39 : Interval test12160 624 640 :=
  interval_of_check test12160 624 16 (by decide +kernel)

theorem test12160_complete : Interval test12160 0 640 :=
  (interval_append test12160 0 320 640
  (interval_append test12160 0 160 320
  (interval_append test12160 0 80 160
  (interval_append test12160 0 32 80
  (interval_append test12160 0 16 32
  test12160_block_0
  test12160_block_1)
  (interval_append test12160 32 48 80
  test12160_block_2
  (interval_append test12160 48 64 80
  test12160_block_3
  test12160_block_4)))
  (interval_append test12160 80 112 160
  (interval_append test12160 80 96 112
  test12160_block_5
  test12160_block_6)
  (interval_append test12160 112 128 160
  test12160_block_7
  (interval_append test12160 128 144 160
  test12160_block_8
  test12160_block_9))))
  (interval_append test12160 160 240 320
  (interval_append test12160 160 192 240
  (interval_append test12160 160 176 192
  test12160_block_10
  test12160_block_11)
  (interval_append test12160 192 208 240
  test12160_block_12
  (interval_append test12160 208 224 240
  test12160_block_13
  test12160_block_14)))
  (interval_append test12160 240 272 320
  (interval_append test12160 240 256 272
  test12160_block_15
  test12160_block_16)
  (interval_append test12160 272 288 320
  test12160_block_17
  (interval_append test12160 288 304 320
  test12160_block_18
  test12160_block_19)))))
  (interval_append test12160 320 480 640
  (interval_append test12160 320 400 480
  (interval_append test12160 320 352 400
  (interval_append test12160 320 336 352
  test12160_block_20
  test12160_block_21)
  (interval_append test12160 352 368 400
  test12160_block_22
  (interval_append test12160 368 384 400
  test12160_block_23
  test12160_block_24)))
  (interval_append test12160 400 432 480
  (interval_append test12160 400 416 432
  test12160_block_25
  test12160_block_26)
  (interval_append test12160 432 448 480
  test12160_block_27
  (interval_append test12160 448 464 480
  test12160_block_28
  test12160_block_29))))
  (interval_append test12160 480 560 640
  (interval_append test12160 480 512 560
  (interval_append test12160 480 496 512
  test12160_block_30
  test12160_block_31)
  (interval_append test12160 512 528 560
  test12160_block_32
  (interval_append test12160 528 544 560
  test12160_block_33
  test12160_block_34)))
  (interval_append test12160 560 592 640
  (interval_append test12160 560 576 592
  test12160_block_35
  test12160_block_36)
  (interval_append test12160 592 608 640
  test12160_block_37
  (interval_append test12160 608 624 640
  test12160_block_38
  test12160_block_39))))))
theorem nodeInterval12160 : Interval nodeTest 12160 12800 := by
  intro i hlo hhi
  have h := test12160_complete (i-12160) (Nat.zero_le _) (by omega)
  simpa only [test12160, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
