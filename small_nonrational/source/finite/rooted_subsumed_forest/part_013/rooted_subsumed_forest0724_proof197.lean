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
def test126080 (i : Nat) := nodeTest (i+126080)
theorem test126080_block_0 : Interval test126080 0 16 :=
  interval_of_check test126080 0 16 (by decide +kernel)

theorem test126080_block_1 : Interval test126080 16 32 :=
  interval_of_check test126080 16 16 (by decide +kernel)

theorem test126080_block_2 : Interval test126080 32 48 :=
  interval_of_check test126080 32 16 (by decide +kernel)

theorem test126080_block_3 : Interval test126080 48 64 :=
  interval_of_check test126080 48 16 (by decide +kernel)

theorem test126080_block_4 : Interval test126080 64 80 :=
  interval_of_check test126080 64 16 (by decide +kernel)

theorem test126080_block_5 : Interval test126080 80 96 :=
  interval_of_check test126080 80 16 (by decide +kernel)

theorem test126080_block_6 : Interval test126080 96 112 :=
  interval_of_check test126080 96 16 (by decide +kernel)

theorem test126080_block_7 : Interval test126080 112 128 :=
  interval_of_check test126080 112 16 (by decide +kernel)

theorem test126080_block_8 : Interval test126080 128 144 :=
  interval_of_check test126080 128 16 (by decide +kernel)

theorem test126080_block_9 : Interval test126080 144 160 :=
  interval_of_check test126080 144 16 (by decide +kernel)

theorem test126080_block_10 : Interval test126080 160 176 :=
  interval_of_check test126080 160 16 (by decide +kernel)

theorem test126080_block_11 : Interval test126080 176 192 :=
  interval_of_check test126080 176 16 (by decide +kernel)

theorem test126080_block_12 : Interval test126080 192 208 :=
  interval_of_check test126080 192 16 (by decide +kernel)

theorem test126080_block_13 : Interval test126080 208 224 :=
  interval_of_check test126080 208 16 (by decide +kernel)

theorem test126080_block_14 : Interval test126080 224 240 :=
  interval_of_check test126080 224 16 (by decide +kernel)

theorem test126080_block_15 : Interval test126080 240 256 :=
  interval_of_check test126080 240 16 (by decide +kernel)

theorem test126080_block_16 : Interval test126080 256 272 :=
  interval_of_check test126080 256 16 (by decide +kernel)

theorem test126080_block_17 : Interval test126080 272 288 :=
  interval_of_check test126080 272 16 (by decide +kernel)

theorem test126080_block_18 : Interval test126080 288 304 :=
  interval_of_check test126080 288 16 (by decide +kernel)

theorem test126080_block_19 : Interval test126080 304 320 :=
  interval_of_check test126080 304 16 (by decide +kernel)

theorem test126080_block_20 : Interval test126080 320 336 :=
  interval_of_check test126080 320 16 (by decide +kernel)

theorem test126080_block_21 : Interval test126080 336 352 :=
  interval_of_check test126080 336 16 (by decide +kernel)

theorem test126080_block_22 : Interval test126080 352 368 :=
  interval_of_check test126080 352 16 (by decide +kernel)

theorem test126080_block_23 : Interval test126080 368 384 :=
  interval_of_check test126080 368 16 (by decide +kernel)

theorem test126080_block_24 : Interval test126080 384 400 :=
  interval_of_check test126080 384 16 (by decide +kernel)

theorem test126080_block_25 : Interval test126080 400 416 :=
  interval_of_check test126080 400 16 (by decide +kernel)

theorem test126080_block_26 : Interval test126080 416 432 :=
  interval_of_check test126080 416 16 (by decide +kernel)

theorem test126080_block_27 : Interval test126080 432 448 :=
  interval_of_check test126080 432 16 (by decide +kernel)

theorem test126080_block_28 : Interval test126080 448 464 :=
  interval_of_check test126080 448 16 (by decide +kernel)

theorem test126080_block_29 : Interval test126080 464 480 :=
  interval_of_check test126080 464 16 (by decide +kernel)

theorem test126080_block_30 : Interval test126080 480 496 :=
  interval_of_check test126080 480 16 (by decide +kernel)

theorem test126080_block_31 : Interval test126080 496 512 :=
  interval_of_check test126080 496 16 (by decide +kernel)

theorem test126080_block_32 : Interval test126080 512 528 :=
  interval_of_check test126080 512 16 (by decide +kernel)

theorem test126080_block_33 : Interval test126080 528 544 :=
  interval_of_check test126080 528 16 (by decide +kernel)

theorem test126080_block_34 : Interval test126080 544 560 :=
  interval_of_check test126080 544 16 (by decide +kernel)

theorem test126080_block_35 : Interval test126080 560 576 :=
  interval_of_check test126080 560 16 (by decide +kernel)

theorem test126080_block_36 : Interval test126080 576 592 :=
  interval_of_check test126080 576 16 (by decide +kernel)

theorem test126080_block_37 : Interval test126080 592 608 :=
  interval_of_check test126080 592 16 (by decide +kernel)

theorem test126080_block_38 : Interval test126080 608 624 :=
  interval_of_check test126080 608 16 (by decide +kernel)

theorem test126080_block_39 : Interval test126080 624 640 :=
  interval_of_check test126080 624 16 (by decide +kernel)

theorem test126080_complete : Interval test126080 0 640 :=
  (interval_append test126080 0 320 640
  (interval_append test126080 0 160 320
  (interval_append test126080 0 80 160
  (interval_append test126080 0 32 80
  (interval_append test126080 0 16 32
  test126080_block_0
  test126080_block_1)
  (interval_append test126080 32 48 80
  test126080_block_2
  (interval_append test126080 48 64 80
  test126080_block_3
  test126080_block_4)))
  (interval_append test126080 80 112 160
  (interval_append test126080 80 96 112
  test126080_block_5
  test126080_block_6)
  (interval_append test126080 112 128 160
  test126080_block_7
  (interval_append test126080 128 144 160
  test126080_block_8
  test126080_block_9))))
  (interval_append test126080 160 240 320
  (interval_append test126080 160 192 240
  (interval_append test126080 160 176 192
  test126080_block_10
  test126080_block_11)
  (interval_append test126080 192 208 240
  test126080_block_12
  (interval_append test126080 208 224 240
  test126080_block_13
  test126080_block_14)))
  (interval_append test126080 240 272 320
  (interval_append test126080 240 256 272
  test126080_block_15
  test126080_block_16)
  (interval_append test126080 272 288 320
  test126080_block_17
  (interval_append test126080 288 304 320
  test126080_block_18
  test126080_block_19)))))
  (interval_append test126080 320 480 640
  (interval_append test126080 320 400 480
  (interval_append test126080 320 352 400
  (interval_append test126080 320 336 352
  test126080_block_20
  test126080_block_21)
  (interval_append test126080 352 368 400
  test126080_block_22
  (interval_append test126080 368 384 400
  test126080_block_23
  test126080_block_24)))
  (interval_append test126080 400 432 480
  (interval_append test126080 400 416 432
  test126080_block_25
  test126080_block_26)
  (interval_append test126080 432 448 480
  test126080_block_27
  (interval_append test126080 448 464 480
  test126080_block_28
  test126080_block_29))))
  (interval_append test126080 480 560 640
  (interval_append test126080 480 512 560
  (interval_append test126080 480 496 512
  test126080_block_30
  test126080_block_31)
  (interval_append test126080 512 528 560
  test126080_block_32
  (interval_append test126080 528 544 560
  test126080_block_33
  test126080_block_34)))
  (interval_append test126080 560 592 640
  (interval_append test126080 560 576 592
  test126080_block_35
  test126080_block_36)
  (interval_append test126080 592 608 640
  test126080_block_37
  (interval_append test126080 608 624 640
  test126080_block_38
  test126080_block_39))))))
theorem nodeInterval126080 : Interval nodeTest 126080 126720 := by
  intro i hlo hhi
  have h := test126080_complete (i-126080) (Nat.zero_le _) (by omega)
  simpa only [test126080, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
