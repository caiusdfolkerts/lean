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
def test107520 (i : Nat) := nodeTest (i+107520)
theorem test107520_block_0 : Interval test107520 0 16 :=
  interval_of_check test107520 0 16 (by decide +kernel)

theorem test107520_block_1 : Interval test107520 16 32 :=
  interval_of_check test107520 16 16 (by decide +kernel)

theorem test107520_block_2 : Interval test107520 32 48 :=
  interval_of_check test107520 32 16 (by decide +kernel)

theorem test107520_block_3 : Interval test107520 48 64 :=
  interval_of_check test107520 48 16 (by decide +kernel)

theorem test107520_block_4 : Interval test107520 64 80 :=
  interval_of_check test107520 64 16 (by decide +kernel)

theorem test107520_block_5 : Interval test107520 80 96 :=
  interval_of_check test107520 80 16 (by decide +kernel)

theorem test107520_block_6 : Interval test107520 96 112 :=
  interval_of_check test107520 96 16 (by decide +kernel)

theorem test107520_block_7 : Interval test107520 112 128 :=
  interval_of_check test107520 112 16 (by decide +kernel)

theorem test107520_block_8 : Interval test107520 128 144 :=
  interval_of_check test107520 128 16 (by decide +kernel)

theorem test107520_block_9 : Interval test107520 144 160 :=
  interval_of_check test107520 144 16 (by decide +kernel)

theorem test107520_block_10 : Interval test107520 160 176 :=
  interval_of_check test107520 160 16 (by decide +kernel)

theorem test107520_block_11 : Interval test107520 176 192 :=
  interval_of_check test107520 176 16 (by decide +kernel)

theorem test107520_block_12 : Interval test107520 192 208 :=
  interval_of_check test107520 192 16 (by decide +kernel)

theorem test107520_block_13 : Interval test107520 208 224 :=
  interval_of_check test107520 208 16 (by decide +kernel)

theorem test107520_block_14 : Interval test107520 224 240 :=
  interval_of_check test107520 224 16 (by decide +kernel)

theorem test107520_block_15 : Interval test107520 240 256 :=
  interval_of_check test107520 240 16 (by decide +kernel)

theorem test107520_block_16 : Interval test107520 256 272 :=
  interval_of_check test107520 256 16 (by decide +kernel)

theorem test107520_block_17 : Interval test107520 272 288 :=
  interval_of_check test107520 272 16 (by decide +kernel)

theorem test107520_block_18 : Interval test107520 288 304 :=
  interval_of_check test107520 288 16 (by decide +kernel)

theorem test107520_block_19 : Interval test107520 304 320 :=
  interval_of_check test107520 304 16 (by decide +kernel)

theorem test107520_block_20 : Interval test107520 320 336 :=
  interval_of_check test107520 320 16 (by decide +kernel)

theorem test107520_block_21 : Interval test107520 336 352 :=
  interval_of_check test107520 336 16 (by decide +kernel)

theorem test107520_block_22 : Interval test107520 352 368 :=
  interval_of_check test107520 352 16 (by decide +kernel)

theorem test107520_block_23 : Interval test107520 368 384 :=
  interval_of_check test107520 368 16 (by decide +kernel)

theorem test107520_block_24 : Interval test107520 384 400 :=
  interval_of_check test107520 384 16 (by decide +kernel)

theorem test107520_block_25 : Interval test107520 400 416 :=
  interval_of_check test107520 400 16 (by decide +kernel)

theorem test107520_block_26 : Interval test107520 416 432 :=
  interval_of_check test107520 416 16 (by decide +kernel)

theorem test107520_block_27 : Interval test107520 432 448 :=
  interval_of_check test107520 432 16 (by decide +kernel)

theorem test107520_block_28 : Interval test107520 448 464 :=
  interval_of_check test107520 448 16 (by decide +kernel)

theorem test107520_block_29 : Interval test107520 464 480 :=
  interval_of_check test107520 464 16 (by decide +kernel)

theorem test107520_block_30 : Interval test107520 480 496 :=
  interval_of_check test107520 480 16 (by decide +kernel)

theorem test107520_block_31 : Interval test107520 496 512 :=
  interval_of_check test107520 496 16 (by decide +kernel)

theorem test107520_block_32 : Interval test107520 512 528 :=
  interval_of_check test107520 512 16 (by decide +kernel)

theorem test107520_block_33 : Interval test107520 528 544 :=
  interval_of_check test107520 528 16 (by decide +kernel)

theorem test107520_block_34 : Interval test107520 544 560 :=
  interval_of_check test107520 544 16 (by decide +kernel)

theorem test107520_block_35 : Interval test107520 560 576 :=
  interval_of_check test107520 560 16 (by decide +kernel)

theorem test107520_block_36 : Interval test107520 576 592 :=
  interval_of_check test107520 576 16 (by decide +kernel)

theorem test107520_block_37 : Interval test107520 592 608 :=
  interval_of_check test107520 592 16 (by decide +kernel)

theorem test107520_block_38 : Interval test107520 608 624 :=
  interval_of_check test107520 608 16 (by decide +kernel)

theorem test107520_block_39 : Interval test107520 624 640 :=
  interval_of_check test107520 624 16 (by decide +kernel)

theorem test107520_complete : Interval test107520 0 640 :=
  (interval_append test107520 0 320 640
  (interval_append test107520 0 160 320
  (interval_append test107520 0 80 160
  (interval_append test107520 0 32 80
  (interval_append test107520 0 16 32
  test107520_block_0
  test107520_block_1)
  (interval_append test107520 32 48 80
  test107520_block_2
  (interval_append test107520 48 64 80
  test107520_block_3
  test107520_block_4)))
  (interval_append test107520 80 112 160
  (interval_append test107520 80 96 112
  test107520_block_5
  test107520_block_6)
  (interval_append test107520 112 128 160
  test107520_block_7
  (interval_append test107520 128 144 160
  test107520_block_8
  test107520_block_9))))
  (interval_append test107520 160 240 320
  (interval_append test107520 160 192 240
  (interval_append test107520 160 176 192
  test107520_block_10
  test107520_block_11)
  (interval_append test107520 192 208 240
  test107520_block_12
  (interval_append test107520 208 224 240
  test107520_block_13
  test107520_block_14)))
  (interval_append test107520 240 272 320
  (interval_append test107520 240 256 272
  test107520_block_15
  test107520_block_16)
  (interval_append test107520 272 288 320
  test107520_block_17
  (interval_append test107520 288 304 320
  test107520_block_18
  test107520_block_19)))))
  (interval_append test107520 320 480 640
  (interval_append test107520 320 400 480
  (interval_append test107520 320 352 400
  (interval_append test107520 320 336 352
  test107520_block_20
  test107520_block_21)
  (interval_append test107520 352 368 400
  test107520_block_22
  (interval_append test107520 368 384 400
  test107520_block_23
  test107520_block_24)))
  (interval_append test107520 400 432 480
  (interval_append test107520 400 416 432
  test107520_block_25
  test107520_block_26)
  (interval_append test107520 432 448 480
  test107520_block_27
  (interval_append test107520 448 464 480
  test107520_block_28
  test107520_block_29))))
  (interval_append test107520 480 560 640
  (interval_append test107520 480 512 560
  (interval_append test107520 480 496 512
  test107520_block_30
  test107520_block_31)
  (interval_append test107520 512 528 560
  test107520_block_32
  (interval_append test107520 528 544 560
  test107520_block_33
  test107520_block_34)))
  (interval_append test107520 560 592 640
  (interval_append test107520 560 576 592
  test107520_block_35
  test107520_block_36)
  (interval_append test107520 592 608 640
  test107520_block_37
  (interval_append test107520 608 624 640
  test107520_block_38
  test107520_block_39))))))
theorem nodeInterval107520 : Interval nodeTest 107520 108160 := by
  intro i hlo hhi
  have h := test107520_complete (i-107520) (Nat.zero_le _) (by omega)
  simpa only [test107520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
