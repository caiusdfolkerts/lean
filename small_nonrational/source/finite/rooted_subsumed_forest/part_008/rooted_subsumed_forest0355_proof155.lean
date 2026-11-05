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
def test99200 (i : Nat) := nodeTest (i+99200)
theorem test99200_block_0 : Interval test99200 0 16 :=
  interval_of_check test99200 0 16 (by decide +kernel)

theorem test99200_block_1 : Interval test99200 16 32 :=
  interval_of_check test99200 16 16 (by decide +kernel)

theorem test99200_block_2 : Interval test99200 32 48 :=
  interval_of_check test99200 32 16 (by decide +kernel)

theorem test99200_block_3 : Interval test99200 48 64 :=
  interval_of_check test99200 48 16 (by decide +kernel)

theorem test99200_block_4 : Interval test99200 64 80 :=
  interval_of_check test99200 64 16 (by decide +kernel)

theorem test99200_block_5 : Interval test99200 80 96 :=
  interval_of_check test99200 80 16 (by decide +kernel)

theorem test99200_block_6 : Interval test99200 96 112 :=
  interval_of_check test99200 96 16 (by decide +kernel)

theorem test99200_block_7 : Interval test99200 112 128 :=
  interval_of_check test99200 112 16 (by decide +kernel)

theorem test99200_block_8 : Interval test99200 128 144 :=
  interval_of_check test99200 128 16 (by decide +kernel)

theorem test99200_block_9 : Interval test99200 144 160 :=
  interval_of_check test99200 144 16 (by decide +kernel)

theorem test99200_block_10 : Interval test99200 160 176 :=
  interval_of_check test99200 160 16 (by decide +kernel)

theorem test99200_block_11 : Interval test99200 176 192 :=
  interval_of_check test99200 176 16 (by decide +kernel)

theorem test99200_block_12 : Interval test99200 192 208 :=
  interval_of_check test99200 192 16 (by decide +kernel)

theorem test99200_block_13 : Interval test99200 208 224 :=
  interval_of_check test99200 208 16 (by decide +kernel)

theorem test99200_block_14 : Interval test99200 224 240 :=
  interval_of_check test99200 224 16 (by decide +kernel)

theorem test99200_block_15 : Interval test99200 240 256 :=
  interval_of_check test99200 240 16 (by decide +kernel)

theorem test99200_block_16 : Interval test99200 256 272 :=
  interval_of_check test99200 256 16 (by decide +kernel)

theorem test99200_block_17 : Interval test99200 272 288 :=
  interval_of_check test99200 272 16 (by decide +kernel)

theorem test99200_block_18 : Interval test99200 288 304 :=
  interval_of_check test99200 288 16 (by decide +kernel)

theorem test99200_block_19 : Interval test99200 304 320 :=
  interval_of_check test99200 304 16 (by decide +kernel)

theorem test99200_block_20 : Interval test99200 320 336 :=
  interval_of_check test99200 320 16 (by decide +kernel)

theorem test99200_block_21 : Interval test99200 336 352 :=
  interval_of_check test99200 336 16 (by decide +kernel)

theorem test99200_block_22 : Interval test99200 352 368 :=
  interval_of_check test99200 352 16 (by decide +kernel)

theorem test99200_block_23 : Interval test99200 368 384 :=
  interval_of_check test99200 368 16 (by decide +kernel)

theorem test99200_block_24 : Interval test99200 384 400 :=
  interval_of_check test99200 384 16 (by decide +kernel)

theorem test99200_block_25 : Interval test99200 400 416 :=
  interval_of_check test99200 400 16 (by decide +kernel)

theorem test99200_block_26 : Interval test99200 416 432 :=
  interval_of_check test99200 416 16 (by decide +kernel)

theorem test99200_block_27 : Interval test99200 432 448 :=
  interval_of_check test99200 432 16 (by decide +kernel)

theorem test99200_block_28 : Interval test99200 448 464 :=
  interval_of_check test99200 448 16 (by decide +kernel)

theorem test99200_block_29 : Interval test99200 464 480 :=
  interval_of_check test99200 464 16 (by decide +kernel)

theorem test99200_block_30 : Interval test99200 480 496 :=
  interval_of_check test99200 480 16 (by decide +kernel)

theorem test99200_block_31 : Interval test99200 496 512 :=
  interval_of_check test99200 496 16 (by decide +kernel)

theorem test99200_block_32 : Interval test99200 512 528 :=
  interval_of_check test99200 512 16 (by decide +kernel)

theorem test99200_block_33 : Interval test99200 528 544 :=
  interval_of_check test99200 528 16 (by decide +kernel)

theorem test99200_block_34 : Interval test99200 544 560 :=
  interval_of_check test99200 544 16 (by decide +kernel)

theorem test99200_block_35 : Interval test99200 560 576 :=
  interval_of_check test99200 560 16 (by decide +kernel)

theorem test99200_block_36 : Interval test99200 576 592 :=
  interval_of_check test99200 576 16 (by decide +kernel)

theorem test99200_block_37 : Interval test99200 592 608 :=
  interval_of_check test99200 592 16 (by decide +kernel)

theorem test99200_block_38 : Interval test99200 608 624 :=
  interval_of_check test99200 608 16 (by decide +kernel)

theorem test99200_block_39 : Interval test99200 624 640 :=
  interval_of_check test99200 624 16 (by decide +kernel)

theorem test99200_complete : Interval test99200 0 640 :=
  (interval_append test99200 0 320 640
  (interval_append test99200 0 160 320
  (interval_append test99200 0 80 160
  (interval_append test99200 0 32 80
  (interval_append test99200 0 16 32
  test99200_block_0
  test99200_block_1)
  (interval_append test99200 32 48 80
  test99200_block_2
  (interval_append test99200 48 64 80
  test99200_block_3
  test99200_block_4)))
  (interval_append test99200 80 112 160
  (interval_append test99200 80 96 112
  test99200_block_5
  test99200_block_6)
  (interval_append test99200 112 128 160
  test99200_block_7
  (interval_append test99200 128 144 160
  test99200_block_8
  test99200_block_9))))
  (interval_append test99200 160 240 320
  (interval_append test99200 160 192 240
  (interval_append test99200 160 176 192
  test99200_block_10
  test99200_block_11)
  (interval_append test99200 192 208 240
  test99200_block_12
  (interval_append test99200 208 224 240
  test99200_block_13
  test99200_block_14)))
  (interval_append test99200 240 272 320
  (interval_append test99200 240 256 272
  test99200_block_15
  test99200_block_16)
  (interval_append test99200 272 288 320
  test99200_block_17
  (interval_append test99200 288 304 320
  test99200_block_18
  test99200_block_19)))))
  (interval_append test99200 320 480 640
  (interval_append test99200 320 400 480
  (interval_append test99200 320 352 400
  (interval_append test99200 320 336 352
  test99200_block_20
  test99200_block_21)
  (interval_append test99200 352 368 400
  test99200_block_22
  (interval_append test99200 368 384 400
  test99200_block_23
  test99200_block_24)))
  (interval_append test99200 400 432 480
  (interval_append test99200 400 416 432
  test99200_block_25
  test99200_block_26)
  (interval_append test99200 432 448 480
  test99200_block_27
  (interval_append test99200 448 464 480
  test99200_block_28
  test99200_block_29))))
  (interval_append test99200 480 560 640
  (interval_append test99200 480 512 560
  (interval_append test99200 480 496 512
  test99200_block_30
  test99200_block_31)
  (interval_append test99200 512 528 560
  test99200_block_32
  (interval_append test99200 528 544 560
  test99200_block_33
  test99200_block_34)))
  (interval_append test99200 560 592 640
  (interval_append test99200 560 576 592
  test99200_block_35
  test99200_block_36)
  (interval_append test99200 592 608 640
  test99200_block_37
  (interval_append test99200 608 624 640
  test99200_block_38
  test99200_block_39))))))
theorem nodeInterval99200 : Interval nodeTest 99200 99840 := by
  intro i hlo hhi
  have h := test99200_complete (i-99200) (Nat.zero_le _) (by omega)
  simpa only [test99200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
