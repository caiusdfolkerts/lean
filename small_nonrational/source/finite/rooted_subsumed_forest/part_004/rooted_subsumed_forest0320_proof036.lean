module
prelude
public import RootedSubsumedForest0320Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test23040 (i : Nat) := nodeTest (i+23040)
theorem test23040_block_0 : Interval test23040 0 16 :=
  interval_of_check test23040 0 16 (by decide +kernel)

theorem test23040_block_1 : Interval test23040 16 32 :=
  interval_of_check test23040 16 16 (by decide +kernel)

theorem test23040_block_2 : Interval test23040 32 48 :=
  interval_of_check test23040 32 16 (by decide +kernel)

theorem test23040_block_3 : Interval test23040 48 64 :=
  interval_of_check test23040 48 16 (by decide +kernel)

theorem test23040_block_4 : Interval test23040 64 80 :=
  interval_of_check test23040 64 16 (by decide +kernel)

theorem test23040_block_5 : Interval test23040 80 96 :=
  interval_of_check test23040 80 16 (by decide +kernel)

theorem test23040_block_6 : Interval test23040 96 112 :=
  interval_of_check test23040 96 16 (by decide +kernel)

theorem test23040_block_7 : Interval test23040 112 128 :=
  interval_of_check test23040 112 16 (by decide +kernel)

theorem test23040_block_8 : Interval test23040 128 144 :=
  interval_of_check test23040 128 16 (by decide +kernel)

theorem test23040_block_9 : Interval test23040 144 160 :=
  interval_of_check test23040 144 16 (by decide +kernel)

theorem test23040_block_10 : Interval test23040 160 176 :=
  interval_of_check test23040 160 16 (by decide +kernel)

theorem test23040_block_11 : Interval test23040 176 192 :=
  interval_of_check test23040 176 16 (by decide +kernel)

theorem test23040_block_12 : Interval test23040 192 208 :=
  interval_of_check test23040 192 16 (by decide +kernel)

theorem test23040_block_13 : Interval test23040 208 224 :=
  interval_of_check test23040 208 16 (by decide +kernel)

theorem test23040_block_14 : Interval test23040 224 240 :=
  interval_of_check test23040 224 16 (by decide +kernel)

theorem test23040_block_15 : Interval test23040 240 256 :=
  interval_of_check test23040 240 16 (by decide +kernel)

theorem test23040_block_16 : Interval test23040 256 272 :=
  interval_of_check test23040 256 16 (by decide +kernel)

theorem test23040_block_17 : Interval test23040 272 288 :=
  interval_of_check test23040 272 16 (by decide +kernel)

theorem test23040_block_18 : Interval test23040 288 304 :=
  interval_of_check test23040 288 16 (by decide +kernel)

theorem test23040_block_19 : Interval test23040 304 320 :=
  interval_of_check test23040 304 16 (by decide +kernel)

theorem test23040_block_20 : Interval test23040 320 336 :=
  interval_of_check test23040 320 16 (by decide +kernel)

theorem test23040_block_21 : Interval test23040 336 352 :=
  interval_of_check test23040 336 16 (by decide +kernel)

theorem test23040_block_22 : Interval test23040 352 368 :=
  interval_of_check test23040 352 16 (by decide +kernel)

theorem test23040_block_23 : Interval test23040 368 384 :=
  interval_of_check test23040 368 16 (by decide +kernel)

theorem test23040_block_24 : Interval test23040 384 400 :=
  interval_of_check test23040 384 16 (by decide +kernel)

theorem test23040_block_25 : Interval test23040 400 416 :=
  interval_of_check test23040 400 16 (by decide +kernel)

theorem test23040_block_26 : Interval test23040 416 432 :=
  interval_of_check test23040 416 16 (by decide +kernel)

theorem test23040_block_27 : Interval test23040 432 448 :=
  interval_of_check test23040 432 16 (by decide +kernel)

theorem test23040_block_28 : Interval test23040 448 464 :=
  interval_of_check test23040 448 16 (by decide +kernel)

theorem test23040_block_29 : Interval test23040 464 480 :=
  interval_of_check test23040 464 16 (by decide +kernel)

theorem test23040_block_30 : Interval test23040 480 496 :=
  interval_of_check test23040 480 16 (by decide +kernel)

theorem test23040_block_31 : Interval test23040 496 512 :=
  interval_of_check test23040 496 16 (by decide +kernel)

theorem test23040_block_32 : Interval test23040 512 528 :=
  interval_of_check test23040 512 16 (by decide +kernel)

theorem test23040_block_33 : Interval test23040 528 544 :=
  interval_of_check test23040 528 16 (by decide +kernel)

theorem test23040_block_34 : Interval test23040 544 560 :=
  interval_of_check test23040 544 16 (by decide +kernel)

theorem test23040_block_35 : Interval test23040 560 576 :=
  interval_of_check test23040 560 16 (by decide +kernel)

theorem test23040_block_36 : Interval test23040 576 592 :=
  interval_of_check test23040 576 16 (by decide +kernel)

theorem test23040_block_37 : Interval test23040 592 608 :=
  interval_of_check test23040 592 16 (by decide +kernel)

theorem test23040_block_38 : Interval test23040 608 624 :=
  interval_of_check test23040 608 16 (by decide +kernel)

theorem test23040_block_39 : Interval test23040 624 640 :=
  interval_of_check test23040 624 16 (by decide +kernel)

theorem test23040_complete : Interval test23040 0 640 :=
  (interval_append test23040 0 320 640
  (interval_append test23040 0 160 320
  (interval_append test23040 0 80 160
  (interval_append test23040 0 32 80
  (interval_append test23040 0 16 32
  test23040_block_0
  test23040_block_1)
  (interval_append test23040 32 48 80
  test23040_block_2
  (interval_append test23040 48 64 80
  test23040_block_3
  test23040_block_4)))
  (interval_append test23040 80 112 160
  (interval_append test23040 80 96 112
  test23040_block_5
  test23040_block_6)
  (interval_append test23040 112 128 160
  test23040_block_7
  (interval_append test23040 128 144 160
  test23040_block_8
  test23040_block_9))))
  (interval_append test23040 160 240 320
  (interval_append test23040 160 192 240
  (interval_append test23040 160 176 192
  test23040_block_10
  test23040_block_11)
  (interval_append test23040 192 208 240
  test23040_block_12
  (interval_append test23040 208 224 240
  test23040_block_13
  test23040_block_14)))
  (interval_append test23040 240 272 320
  (interval_append test23040 240 256 272
  test23040_block_15
  test23040_block_16)
  (interval_append test23040 272 288 320
  test23040_block_17
  (interval_append test23040 288 304 320
  test23040_block_18
  test23040_block_19)))))
  (interval_append test23040 320 480 640
  (interval_append test23040 320 400 480
  (interval_append test23040 320 352 400
  (interval_append test23040 320 336 352
  test23040_block_20
  test23040_block_21)
  (interval_append test23040 352 368 400
  test23040_block_22
  (interval_append test23040 368 384 400
  test23040_block_23
  test23040_block_24)))
  (interval_append test23040 400 432 480
  (interval_append test23040 400 416 432
  test23040_block_25
  test23040_block_26)
  (interval_append test23040 432 448 480
  test23040_block_27
  (interval_append test23040 448 464 480
  test23040_block_28
  test23040_block_29))))
  (interval_append test23040 480 560 640
  (interval_append test23040 480 512 560
  (interval_append test23040 480 496 512
  test23040_block_30
  test23040_block_31)
  (interval_append test23040 512 528 560
  test23040_block_32
  (interval_append test23040 528 544 560
  test23040_block_33
  test23040_block_34)))
  (interval_append test23040 560 592 640
  (interval_append test23040 560 576 592
  test23040_block_35
  test23040_block_36)
  (interval_append test23040 592 608 640
  test23040_block_37
  (interval_append test23040 608 624 640
  test23040_block_38
  test23040_block_39))))))
theorem nodeInterval23040 : Interval nodeTest 23040 23680 := by
  intro i hlo hhi
  have h := test23040_complete (i-23040) (Nat.zero_le _) (by omega)
  simpa only [test23040, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
