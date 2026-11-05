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
def test55040 (i : Nat) := nodeTest (i+55040)
theorem test55040_block_0 : Interval test55040 0 16 :=
  interval_of_check test55040 0 16 (by decide +kernel)

theorem test55040_block_1 : Interval test55040 16 32 :=
  interval_of_check test55040 16 16 (by decide +kernel)

theorem test55040_block_2 : Interval test55040 32 48 :=
  interval_of_check test55040 32 16 (by decide +kernel)

theorem test55040_block_3 : Interval test55040 48 64 :=
  interval_of_check test55040 48 16 (by decide +kernel)

theorem test55040_block_4 : Interval test55040 64 80 :=
  interval_of_check test55040 64 16 (by decide +kernel)

theorem test55040_block_5 : Interval test55040 80 96 :=
  interval_of_check test55040 80 16 (by decide +kernel)

theorem test55040_block_6 : Interval test55040 96 112 :=
  interval_of_check test55040 96 16 (by decide +kernel)

theorem test55040_block_7 : Interval test55040 112 128 :=
  interval_of_check test55040 112 16 (by decide +kernel)

theorem test55040_block_8 : Interval test55040 128 144 :=
  interval_of_check test55040 128 16 (by decide +kernel)

theorem test55040_block_9 : Interval test55040 144 160 :=
  interval_of_check test55040 144 16 (by decide +kernel)

theorem test55040_block_10 : Interval test55040 160 176 :=
  interval_of_check test55040 160 16 (by decide +kernel)

theorem test55040_block_11 : Interval test55040 176 192 :=
  interval_of_check test55040 176 16 (by decide +kernel)

theorem test55040_block_12 : Interval test55040 192 208 :=
  interval_of_check test55040 192 16 (by decide +kernel)

theorem test55040_block_13 : Interval test55040 208 224 :=
  interval_of_check test55040 208 16 (by decide +kernel)

theorem test55040_block_14 : Interval test55040 224 240 :=
  interval_of_check test55040 224 16 (by decide +kernel)

theorem test55040_block_15 : Interval test55040 240 256 :=
  interval_of_check test55040 240 16 (by decide +kernel)

theorem test55040_block_16 : Interval test55040 256 272 :=
  interval_of_check test55040 256 16 (by decide +kernel)

theorem test55040_block_17 : Interval test55040 272 288 :=
  interval_of_check test55040 272 16 (by decide +kernel)

theorem test55040_block_18 : Interval test55040 288 304 :=
  interval_of_check test55040 288 16 (by decide +kernel)

theorem test55040_block_19 : Interval test55040 304 320 :=
  interval_of_check test55040 304 16 (by decide +kernel)

theorem test55040_block_20 : Interval test55040 320 336 :=
  interval_of_check test55040 320 16 (by decide +kernel)

theorem test55040_block_21 : Interval test55040 336 352 :=
  interval_of_check test55040 336 16 (by decide +kernel)

theorem test55040_block_22 : Interval test55040 352 368 :=
  interval_of_check test55040 352 16 (by decide +kernel)

theorem test55040_block_23 : Interval test55040 368 384 :=
  interval_of_check test55040 368 16 (by decide +kernel)

theorem test55040_block_24 : Interval test55040 384 400 :=
  interval_of_check test55040 384 16 (by decide +kernel)

theorem test55040_block_25 : Interval test55040 400 416 :=
  interval_of_check test55040 400 16 (by decide +kernel)

theorem test55040_block_26 : Interval test55040 416 432 :=
  interval_of_check test55040 416 16 (by decide +kernel)

theorem test55040_block_27 : Interval test55040 432 448 :=
  interval_of_check test55040 432 16 (by decide +kernel)

theorem test55040_block_28 : Interval test55040 448 464 :=
  interval_of_check test55040 448 16 (by decide +kernel)

theorem test55040_block_29 : Interval test55040 464 480 :=
  interval_of_check test55040 464 16 (by decide +kernel)

theorem test55040_block_30 : Interval test55040 480 496 :=
  interval_of_check test55040 480 16 (by decide +kernel)

theorem test55040_block_31 : Interval test55040 496 512 :=
  interval_of_check test55040 496 16 (by decide +kernel)

theorem test55040_block_32 : Interval test55040 512 528 :=
  interval_of_check test55040 512 16 (by decide +kernel)

theorem test55040_block_33 : Interval test55040 528 544 :=
  interval_of_check test55040 528 16 (by decide +kernel)

theorem test55040_block_34 : Interval test55040 544 560 :=
  interval_of_check test55040 544 16 (by decide +kernel)

theorem test55040_block_35 : Interval test55040 560 576 :=
  interval_of_check test55040 560 16 (by decide +kernel)

theorem test55040_block_36 : Interval test55040 576 592 :=
  interval_of_check test55040 576 16 (by decide +kernel)

theorem test55040_block_37 : Interval test55040 592 608 :=
  interval_of_check test55040 592 16 (by decide +kernel)

theorem test55040_block_38 : Interval test55040 608 624 :=
  interval_of_check test55040 608 16 (by decide +kernel)

theorem test55040_block_39 : Interval test55040 624 640 :=
  interval_of_check test55040 624 16 (by decide +kernel)

theorem test55040_complete : Interval test55040 0 640 :=
  (interval_append test55040 0 320 640
  (interval_append test55040 0 160 320
  (interval_append test55040 0 80 160
  (interval_append test55040 0 32 80
  (interval_append test55040 0 16 32
  test55040_block_0
  test55040_block_1)
  (interval_append test55040 32 48 80
  test55040_block_2
  (interval_append test55040 48 64 80
  test55040_block_3
  test55040_block_4)))
  (interval_append test55040 80 112 160
  (interval_append test55040 80 96 112
  test55040_block_5
  test55040_block_6)
  (interval_append test55040 112 128 160
  test55040_block_7
  (interval_append test55040 128 144 160
  test55040_block_8
  test55040_block_9))))
  (interval_append test55040 160 240 320
  (interval_append test55040 160 192 240
  (interval_append test55040 160 176 192
  test55040_block_10
  test55040_block_11)
  (interval_append test55040 192 208 240
  test55040_block_12
  (interval_append test55040 208 224 240
  test55040_block_13
  test55040_block_14)))
  (interval_append test55040 240 272 320
  (interval_append test55040 240 256 272
  test55040_block_15
  test55040_block_16)
  (interval_append test55040 272 288 320
  test55040_block_17
  (interval_append test55040 288 304 320
  test55040_block_18
  test55040_block_19)))))
  (interval_append test55040 320 480 640
  (interval_append test55040 320 400 480
  (interval_append test55040 320 352 400
  (interval_append test55040 320 336 352
  test55040_block_20
  test55040_block_21)
  (interval_append test55040 352 368 400
  test55040_block_22
  (interval_append test55040 368 384 400
  test55040_block_23
  test55040_block_24)))
  (interval_append test55040 400 432 480
  (interval_append test55040 400 416 432
  test55040_block_25
  test55040_block_26)
  (interval_append test55040 432 448 480
  test55040_block_27
  (interval_append test55040 448 464 480
  test55040_block_28
  test55040_block_29))))
  (interval_append test55040 480 560 640
  (interval_append test55040 480 512 560
  (interval_append test55040 480 496 512
  test55040_block_30
  test55040_block_31)
  (interval_append test55040 512 528 560
  test55040_block_32
  (interval_append test55040 528 544 560
  test55040_block_33
  test55040_block_34)))
  (interval_append test55040 560 592 640
  (interval_append test55040 560 576 592
  test55040_block_35
  test55040_block_36)
  (interval_append test55040 592 608 640
  test55040_block_37
  (interval_append test55040 608 624 640
  test55040_block_38
  test55040_block_39))))))
theorem nodeInterval55040 : Interval nodeTest 55040 55680 := by
  intro i hlo hhi
  have h := test55040_complete (i-55040) (Nat.zero_le _) (by omega)
  simpa only [test55040, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
