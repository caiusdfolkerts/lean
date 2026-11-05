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
def test88320 (i : Nat) := nodeTest (i+88320)
theorem test88320_block_0 : Interval test88320 0 16 :=
  interval_of_check test88320 0 16 (by decide +kernel)

theorem test88320_block_1 : Interval test88320 16 32 :=
  interval_of_check test88320 16 16 (by decide +kernel)

theorem test88320_block_2 : Interval test88320 32 48 :=
  interval_of_check test88320 32 16 (by decide +kernel)

theorem test88320_block_3 : Interval test88320 48 64 :=
  interval_of_check test88320 48 16 (by decide +kernel)

theorem test88320_block_4 : Interval test88320 64 80 :=
  interval_of_check test88320 64 16 (by decide +kernel)

theorem test88320_block_5 : Interval test88320 80 96 :=
  interval_of_check test88320 80 16 (by decide +kernel)

theorem test88320_block_6 : Interval test88320 96 112 :=
  interval_of_check test88320 96 16 (by decide +kernel)

theorem test88320_block_7 : Interval test88320 112 128 :=
  interval_of_check test88320 112 16 (by decide +kernel)

theorem test88320_block_8 : Interval test88320 128 144 :=
  interval_of_check test88320 128 16 (by decide +kernel)

theorem test88320_block_9 : Interval test88320 144 160 :=
  interval_of_check test88320 144 16 (by decide +kernel)

theorem test88320_block_10 : Interval test88320 160 176 :=
  interval_of_check test88320 160 16 (by decide +kernel)

theorem test88320_block_11 : Interval test88320 176 192 :=
  interval_of_check test88320 176 16 (by decide +kernel)

theorem test88320_block_12 : Interval test88320 192 208 :=
  interval_of_check test88320 192 16 (by decide +kernel)

theorem test88320_block_13 : Interval test88320 208 224 :=
  interval_of_check test88320 208 16 (by decide +kernel)

theorem test88320_block_14 : Interval test88320 224 240 :=
  interval_of_check test88320 224 16 (by decide +kernel)

theorem test88320_block_15 : Interval test88320 240 256 :=
  interval_of_check test88320 240 16 (by decide +kernel)

theorem test88320_block_16 : Interval test88320 256 272 :=
  interval_of_check test88320 256 16 (by decide +kernel)

theorem test88320_block_17 : Interval test88320 272 288 :=
  interval_of_check test88320 272 16 (by decide +kernel)

theorem test88320_block_18 : Interval test88320 288 304 :=
  interval_of_check test88320 288 16 (by decide +kernel)

theorem test88320_block_19 : Interval test88320 304 320 :=
  interval_of_check test88320 304 16 (by decide +kernel)

theorem test88320_block_20 : Interval test88320 320 336 :=
  interval_of_check test88320 320 16 (by decide +kernel)

theorem test88320_block_21 : Interval test88320 336 352 :=
  interval_of_check test88320 336 16 (by decide +kernel)

theorem test88320_block_22 : Interval test88320 352 368 :=
  interval_of_check test88320 352 16 (by decide +kernel)

theorem test88320_block_23 : Interval test88320 368 384 :=
  interval_of_check test88320 368 16 (by decide +kernel)

theorem test88320_block_24 : Interval test88320 384 400 :=
  interval_of_check test88320 384 16 (by decide +kernel)

theorem test88320_block_25 : Interval test88320 400 416 :=
  interval_of_check test88320 400 16 (by decide +kernel)

theorem test88320_block_26 : Interval test88320 416 432 :=
  interval_of_check test88320 416 16 (by decide +kernel)

theorem test88320_block_27 : Interval test88320 432 448 :=
  interval_of_check test88320 432 16 (by decide +kernel)

theorem test88320_block_28 : Interval test88320 448 464 :=
  interval_of_check test88320 448 16 (by decide +kernel)

theorem test88320_block_29 : Interval test88320 464 480 :=
  interval_of_check test88320 464 16 (by decide +kernel)

theorem test88320_block_30 : Interval test88320 480 496 :=
  interval_of_check test88320 480 16 (by decide +kernel)

theorem test88320_block_31 : Interval test88320 496 512 :=
  interval_of_check test88320 496 16 (by decide +kernel)

theorem test88320_block_32 : Interval test88320 512 528 :=
  interval_of_check test88320 512 16 (by decide +kernel)

theorem test88320_block_33 : Interval test88320 528 544 :=
  interval_of_check test88320 528 16 (by decide +kernel)

theorem test88320_block_34 : Interval test88320 544 560 :=
  interval_of_check test88320 544 16 (by decide +kernel)

theorem test88320_block_35 : Interval test88320 560 576 :=
  interval_of_check test88320 560 16 (by decide +kernel)

theorem test88320_block_36 : Interval test88320 576 592 :=
  interval_of_check test88320 576 16 (by decide +kernel)

theorem test88320_block_37 : Interval test88320 592 608 :=
  interval_of_check test88320 592 16 (by decide +kernel)

theorem test88320_block_38 : Interval test88320 608 624 :=
  interval_of_check test88320 608 16 (by decide +kernel)

theorem test88320_block_39 : Interval test88320 624 640 :=
  interval_of_check test88320 624 16 (by decide +kernel)

theorem test88320_complete : Interval test88320 0 640 :=
  (interval_append test88320 0 320 640
  (interval_append test88320 0 160 320
  (interval_append test88320 0 80 160
  (interval_append test88320 0 32 80
  (interval_append test88320 0 16 32
  test88320_block_0
  test88320_block_1)
  (interval_append test88320 32 48 80
  test88320_block_2
  (interval_append test88320 48 64 80
  test88320_block_3
  test88320_block_4)))
  (interval_append test88320 80 112 160
  (interval_append test88320 80 96 112
  test88320_block_5
  test88320_block_6)
  (interval_append test88320 112 128 160
  test88320_block_7
  (interval_append test88320 128 144 160
  test88320_block_8
  test88320_block_9))))
  (interval_append test88320 160 240 320
  (interval_append test88320 160 192 240
  (interval_append test88320 160 176 192
  test88320_block_10
  test88320_block_11)
  (interval_append test88320 192 208 240
  test88320_block_12
  (interval_append test88320 208 224 240
  test88320_block_13
  test88320_block_14)))
  (interval_append test88320 240 272 320
  (interval_append test88320 240 256 272
  test88320_block_15
  test88320_block_16)
  (interval_append test88320 272 288 320
  test88320_block_17
  (interval_append test88320 288 304 320
  test88320_block_18
  test88320_block_19)))))
  (interval_append test88320 320 480 640
  (interval_append test88320 320 400 480
  (interval_append test88320 320 352 400
  (interval_append test88320 320 336 352
  test88320_block_20
  test88320_block_21)
  (interval_append test88320 352 368 400
  test88320_block_22
  (interval_append test88320 368 384 400
  test88320_block_23
  test88320_block_24)))
  (interval_append test88320 400 432 480
  (interval_append test88320 400 416 432
  test88320_block_25
  test88320_block_26)
  (interval_append test88320 432 448 480
  test88320_block_27
  (interval_append test88320 448 464 480
  test88320_block_28
  test88320_block_29))))
  (interval_append test88320 480 560 640
  (interval_append test88320 480 512 560
  (interval_append test88320 480 496 512
  test88320_block_30
  test88320_block_31)
  (interval_append test88320 512 528 560
  test88320_block_32
  (interval_append test88320 528 544 560
  test88320_block_33
  test88320_block_34)))
  (interval_append test88320 560 592 640
  (interval_append test88320 560 576 592
  test88320_block_35
  test88320_block_36)
  (interval_append test88320 592 608 640
  test88320_block_37
  (interval_append test88320 608 624 640
  test88320_block_38
  test88320_block_39))))))
theorem nodeInterval88320 : Interval nodeTest 88320 88960 := by
  intro i hlo hhi
  have h := test88320_complete (i-88320) (Nat.zero_le _) (by omega)
  simpa only [test88320, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
