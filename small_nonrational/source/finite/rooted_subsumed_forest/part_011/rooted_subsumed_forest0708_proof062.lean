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
def test39680 (i : Nat) := nodeTest (i+39680)
theorem test39680_block_0 : Interval test39680 0 16 :=
  interval_of_check test39680 0 16 (by decide +kernel)

theorem test39680_block_1 : Interval test39680 16 32 :=
  interval_of_check test39680 16 16 (by decide +kernel)

theorem test39680_block_2 : Interval test39680 32 48 :=
  interval_of_check test39680 32 16 (by decide +kernel)

theorem test39680_block_3 : Interval test39680 48 64 :=
  interval_of_check test39680 48 16 (by decide +kernel)

theorem test39680_block_4 : Interval test39680 64 80 :=
  interval_of_check test39680 64 16 (by decide +kernel)

theorem test39680_block_5 : Interval test39680 80 96 :=
  interval_of_check test39680 80 16 (by decide +kernel)

theorem test39680_block_6 : Interval test39680 96 112 :=
  interval_of_check test39680 96 16 (by decide +kernel)

theorem test39680_block_7 : Interval test39680 112 128 :=
  interval_of_check test39680 112 16 (by decide +kernel)

theorem test39680_block_8 : Interval test39680 128 144 :=
  interval_of_check test39680 128 16 (by decide +kernel)

theorem test39680_block_9 : Interval test39680 144 160 :=
  interval_of_check test39680 144 16 (by decide +kernel)

theorem test39680_block_10 : Interval test39680 160 176 :=
  interval_of_check test39680 160 16 (by decide +kernel)

theorem test39680_block_11 : Interval test39680 176 192 :=
  interval_of_check test39680 176 16 (by decide +kernel)

theorem test39680_block_12 : Interval test39680 192 208 :=
  interval_of_check test39680 192 16 (by decide +kernel)

theorem test39680_block_13 : Interval test39680 208 224 :=
  interval_of_check test39680 208 16 (by decide +kernel)

theorem test39680_block_14 : Interval test39680 224 240 :=
  interval_of_check test39680 224 16 (by decide +kernel)

theorem test39680_block_15 : Interval test39680 240 256 :=
  interval_of_check test39680 240 16 (by decide +kernel)

theorem test39680_block_16 : Interval test39680 256 272 :=
  interval_of_check test39680 256 16 (by decide +kernel)

theorem test39680_block_17 : Interval test39680 272 288 :=
  interval_of_check test39680 272 16 (by decide +kernel)

theorem test39680_block_18 : Interval test39680 288 304 :=
  interval_of_check test39680 288 16 (by decide +kernel)

theorem test39680_block_19 : Interval test39680 304 320 :=
  interval_of_check test39680 304 16 (by decide +kernel)

theorem test39680_block_20 : Interval test39680 320 336 :=
  interval_of_check test39680 320 16 (by decide +kernel)

theorem test39680_block_21 : Interval test39680 336 352 :=
  interval_of_check test39680 336 16 (by decide +kernel)

theorem test39680_block_22 : Interval test39680 352 368 :=
  interval_of_check test39680 352 16 (by decide +kernel)

theorem test39680_block_23 : Interval test39680 368 384 :=
  interval_of_check test39680 368 16 (by decide +kernel)

theorem test39680_block_24 : Interval test39680 384 400 :=
  interval_of_check test39680 384 16 (by decide +kernel)

theorem test39680_block_25 : Interval test39680 400 416 :=
  interval_of_check test39680 400 16 (by decide +kernel)

theorem test39680_block_26 : Interval test39680 416 432 :=
  interval_of_check test39680 416 16 (by decide +kernel)

theorem test39680_block_27 : Interval test39680 432 448 :=
  interval_of_check test39680 432 16 (by decide +kernel)

theorem test39680_block_28 : Interval test39680 448 464 :=
  interval_of_check test39680 448 16 (by decide +kernel)

theorem test39680_block_29 : Interval test39680 464 480 :=
  interval_of_check test39680 464 16 (by decide +kernel)

theorem test39680_block_30 : Interval test39680 480 496 :=
  interval_of_check test39680 480 16 (by decide +kernel)

theorem test39680_block_31 : Interval test39680 496 512 :=
  interval_of_check test39680 496 16 (by decide +kernel)

theorem test39680_block_32 : Interval test39680 512 528 :=
  interval_of_check test39680 512 16 (by decide +kernel)

theorem test39680_block_33 : Interval test39680 528 544 :=
  interval_of_check test39680 528 16 (by decide +kernel)

theorem test39680_block_34 : Interval test39680 544 560 :=
  interval_of_check test39680 544 16 (by decide +kernel)

theorem test39680_block_35 : Interval test39680 560 576 :=
  interval_of_check test39680 560 16 (by decide +kernel)

theorem test39680_block_36 : Interval test39680 576 592 :=
  interval_of_check test39680 576 16 (by decide +kernel)

theorem test39680_block_37 : Interval test39680 592 608 :=
  interval_of_check test39680 592 16 (by decide +kernel)

theorem test39680_block_38 : Interval test39680 608 624 :=
  interval_of_check test39680 608 16 (by decide +kernel)

theorem test39680_block_39 : Interval test39680 624 640 :=
  interval_of_check test39680 624 16 (by decide +kernel)

theorem test39680_complete : Interval test39680 0 640 :=
  (interval_append test39680 0 320 640
  (interval_append test39680 0 160 320
  (interval_append test39680 0 80 160
  (interval_append test39680 0 32 80
  (interval_append test39680 0 16 32
  test39680_block_0
  test39680_block_1)
  (interval_append test39680 32 48 80
  test39680_block_2
  (interval_append test39680 48 64 80
  test39680_block_3
  test39680_block_4)))
  (interval_append test39680 80 112 160
  (interval_append test39680 80 96 112
  test39680_block_5
  test39680_block_6)
  (interval_append test39680 112 128 160
  test39680_block_7
  (interval_append test39680 128 144 160
  test39680_block_8
  test39680_block_9))))
  (interval_append test39680 160 240 320
  (interval_append test39680 160 192 240
  (interval_append test39680 160 176 192
  test39680_block_10
  test39680_block_11)
  (interval_append test39680 192 208 240
  test39680_block_12
  (interval_append test39680 208 224 240
  test39680_block_13
  test39680_block_14)))
  (interval_append test39680 240 272 320
  (interval_append test39680 240 256 272
  test39680_block_15
  test39680_block_16)
  (interval_append test39680 272 288 320
  test39680_block_17
  (interval_append test39680 288 304 320
  test39680_block_18
  test39680_block_19)))))
  (interval_append test39680 320 480 640
  (interval_append test39680 320 400 480
  (interval_append test39680 320 352 400
  (interval_append test39680 320 336 352
  test39680_block_20
  test39680_block_21)
  (interval_append test39680 352 368 400
  test39680_block_22
  (interval_append test39680 368 384 400
  test39680_block_23
  test39680_block_24)))
  (interval_append test39680 400 432 480
  (interval_append test39680 400 416 432
  test39680_block_25
  test39680_block_26)
  (interval_append test39680 432 448 480
  test39680_block_27
  (interval_append test39680 448 464 480
  test39680_block_28
  test39680_block_29))))
  (interval_append test39680 480 560 640
  (interval_append test39680 480 512 560
  (interval_append test39680 480 496 512
  test39680_block_30
  test39680_block_31)
  (interval_append test39680 512 528 560
  test39680_block_32
  (interval_append test39680 528 544 560
  test39680_block_33
  test39680_block_34)))
  (interval_append test39680 560 592 640
  (interval_append test39680 560 576 592
  test39680_block_35
  test39680_block_36)
  (interval_append test39680 592 608 640
  test39680_block_37
  (interval_append test39680 608 624 640
  test39680_block_38
  test39680_block_39))))))
theorem nodeInterval39680 : Interval nodeTest 39680 40320 := by
  intro i hlo hhi
  have h := test39680_complete (i-39680) (Nat.zero_le _) (by omega)
  simpa only [test39680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
