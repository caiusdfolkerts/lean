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
def test36480 (i : Nat) := nodeTest (i+36480)
theorem test36480_block_0 : Interval test36480 0 16 :=
  interval_of_check test36480 0 16 (by decide +kernel)

theorem test36480_block_1 : Interval test36480 16 32 :=
  interval_of_check test36480 16 16 (by decide +kernel)

theorem test36480_block_2 : Interval test36480 32 48 :=
  interval_of_check test36480 32 16 (by decide +kernel)

theorem test36480_block_3 : Interval test36480 48 64 :=
  interval_of_check test36480 48 16 (by decide +kernel)

theorem test36480_block_4 : Interval test36480 64 80 :=
  interval_of_check test36480 64 16 (by decide +kernel)

theorem test36480_block_5 : Interval test36480 80 96 :=
  interval_of_check test36480 80 16 (by decide +kernel)

theorem test36480_block_6 : Interval test36480 96 112 :=
  interval_of_check test36480 96 16 (by decide +kernel)

theorem test36480_block_7 : Interval test36480 112 128 :=
  interval_of_check test36480 112 16 (by decide +kernel)

theorem test36480_block_8 : Interval test36480 128 144 :=
  interval_of_check test36480 128 16 (by decide +kernel)

theorem test36480_block_9 : Interval test36480 144 160 :=
  interval_of_check test36480 144 16 (by decide +kernel)

theorem test36480_block_10 : Interval test36480 160 176 :=
  interval_of_check test36480 160 16 (by decide +kernel)

theorem test36480_block_11 : Interval test36480 176 192 :=
  interval_of_check test36480 176 16 (by decide +kernel)

theorem test36480_block_12 : Interval test36480 192 208 :=
  interval_of_check test36480 192 16 (by decide +kernel)

theorem test36480_block_13 : Interval test36480 208 224 :=
  interval_of_check test36480 208 16 (by decide +kernel)

theorem test36480_block_14 : Interval test36480 224 240 :=
  interval_of_check test36480 224 16 (by decide +kernel)

theorem test36480_block_15 : Interval test36480 240 256 :=
  interval_of_check test36480 240 16 (by decide +kernel)

theorem test36480_block_16 : Interval test36480 256 272 :=
  interval_of_check test36480 256 16 (by decide +kernel)

theorem test36480_block_17 : Interval test36480 272 288 :=
  interval_of_check test36480 272 16 (by decide +kernel)

theorem test36480_block_18 : Interval test36480 288 304 :=
  interval_of_check test36480 288 16 (by decide +kernel)

theorem test36480_block_19 : Interval test36480 304 320 :=
  interval_of_check test36480 304 16 (by decide +kernel)

theorem test36480_block_20 : Interval test36480 320 336 :=
  interval_of_check test36480 320 16 (by decide +kernel)

theorem test36480_block_21 : Interval test36480 336 352 :=
  interval_of_check test36480 336 16 (by decide +kernel)

theorem test36480_block_22 : Interval test36480 352 368 :=
  interval_of_check test36480 352 16 (by decide +kernel)

theorem test36480_block_23 : Interval test36480 368 384 :=
  interval_of_check test36480 368 16 (by decide +kernel)

theorem test36480_block_24 : Interval test36480 384 400 :=
  interval_of_check test36480 384 16 (by decide +kernel)

theorem test36480_block_25 : Interval test36480 400 416 :=
  interval_of_check test36480 400 16 (by decide +kernel)

theorem test36480_block_26 : Interval test36480 416 432 :=
  interval_of_check test36480 416 16 (by decide +kernel)

theorem test36480_block_27 : Interval test36480 432 448 :=
  interval_of_check test36480 432 16 (by decide +kernel)

theorem test36480_block_28 : Interval test36480 448 464 :=
  interval_of_check test36480 448 16 (by decide +kernel)

theorem test36480_block_29 : Interval test36480 464 480 :=
  interval_of_check test36480 464 16 (by decide +kernel)

theorem test36480_block_30 : Interval test36480 480 496 :=
  interval_of_check test36480 480 16 (by decide +kernel)

theorem test36480_block_31 : Interval test36480 496 512 :=
  interval_of_check test36480 496 16 (by decide +kernel)

theorem test36480_block_32 : Interval test36480 512 528 :=
  interval_of_check test36480 512 16 (by decide +kernel)

theorem test36480_block_33 : Interval test36480 528 544 :=
  interval_of_check test36480 528 16 (by decide +kernel)

theorem test36480_block_34 : Interval test36480 544 560 :=
  interval_of_check test36480 544 16 (by decide +kernel)

theorem test36480_block_35 : Interval test36480 560 576 :=
  interval_of_check test36480 560 16 (by decide +kernel)

theorem test36480_block_36 : Interval test36480 576 592 :=
  interval_of_check test36480 576 16 (by decide +kernel)

theorem test36480_block_37 : Interval test36480 592 608 :=
  interval_of_check test36480 592 16 (by decide +kernel)

theorem test36480_block_38 : Interval test36480 608 624 :=
  interval_of_check test36480 608 16 (by decide +kernel)

theorem test36480_block_39 : Interval test36480 624 640 :=
  interval_of_check test36480 624 16 (by decide +kernel)

theorem test36480_complete : Interval test36480 0 640 :=
  (interval_append test36480 0 320 640
  (interval_append test36480 0 160 320
  (interval_append test36480 0 80 160
  (interval_append test36480 0 32 80
  (interval_append test36480 0 16 32
  test36480_block_0
  test36480_block_1)
  (interval_append test36480 32 48 80
  test36480_block_2
  (interval_append test36480 48 64 80
  test36480_block_3
  test36480_block_4)))
  (interval_append test36480 80 112 160
  (interval_append test36480 80 96 112
  test36480_block_5
  test36480_block_6)
  (interval_append test36480 112 128 160
  test36480_block_7
  (interval_append test36480 128 144 160
  test36480_block_8
  test36480_block_9))))
  (interval_append test36480 160 240 320
  (interval_append test36480 160 192 240
  (interval_append test36480 160 176 192
  test36480_block_10
  test36480_block_11)
  (interval_append test36480 192 208 240
  test36480_block_12
  (interval_append test36480 208 224 240
  test36480_block_13
  test36480_block_14)))
  (interval_append test36480 240 272 320
  (interval_append test36480 240 256 272
  test36480_block_15
  test36480_block_16)
  (interval_append test36480 272 288 320
  test36480_block_17
  (interval_append test36480 288 304 320
  test36480_block_18
  test36480_block_19)))))
  (interval_append test36480 320 480 640
  (interval_append test36480 320 400 480
  (interval_append test36480 320 352 400
  (interval_append test36480 320 336 352
  test36480_block_20
  test36480_block_21)
  (interval_append test36480 352 368 400
  test36480_block_22
  (interval_append test36480 368 384 400
  test36480_block_23
  test36480_block_24)))
  (interval_append test36480 400 432 480
  (interval_append test36480 400 416 432
  test36480_block_25
  test36480_block_26)
  (interval_append test36480 432 448 480
  test36480_block_27
  (interval_append test36480 448 464 480
  test36480_block_28
  test36480_block_29))))
  (interval_append test36480 480 560 640
  (interval_append test36480 480 512 560
  (interval_append test36480 480 496 512
  test36480_block_30
  test36480_block_31)
  (interval_append test36480 512 528 560
  test36480_block_32
  (interval_append test36480 528 544 560
  test36480_block_33
  test36480_block_34)))
  (interval_append test36480 560 592 640
  (interval_append test36480 560 576 592
  test36480_block_35
  test36480_block_36)
  (interval_append test36480 592 608 640
  test36480_block_37
  (interval_append test36480 608 624 640
  test36480_block_38
  test36480_block_39))))))
theorem nodeInterval36480 : Interval nodeTest 36480 37120 := by
  intro i hlo hhi
  have h := test36480_complete (i-36480) (Nat.zero_le _) (by omega)
  simpa only [test36480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
