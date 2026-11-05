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
def test61440 (i : Nat) := nodeTest (i+61440)
theorem test61440_block_0 : Interval test61440 0 16 :=
  interval_of_check test61440 0 16 (by decide +kernel)

theorem test61440_block_1 : Interval test61440 16 32 :=
  interval_of_check test61440 16 16 (by decide +kernel)

theorem test61440_block_2 : Interval test61440 32 48 :=
  interval_of_check test61440 32 16 (by decide +kernel)

theorem test61440_block_3 : Interval test61440 48 64 :=
  interval_of_check test61440 48 16 (by decide +kernel)

theorem test61440_block_4 : Interval test61440 64 80 :=
  interval_of_check test61440 64 16 (by decide +kernel)

theorem test61440_block_5 : Interval test61440 80 96 :=
  interval_of_check test61440 80 16 (by decide +kernel)

theorem test61440_block_6 : Interval test61440 96 112 :=
  interval_of_check test61440 96 16 (by decide +kernel)

theorem test61440_block_7 : Interval test61440 112 128 :=
  interval_of_check test61440 112 16 (by decide +kernel)

theorem test61440_block_8 : Interval test61440 128 144 :=
  interval_of_check test61440 128 16 (by decide +kernel)

theorem test61440_block_9 : Interval test61440 144 160 :=
  interval_of_check test61440 144 16 (by decide +kernel)

theorem test61440_block_10 : Interval test61440 160 176 :=
  interval_of_check test61440 160 16 (by decide +kernel)

theorem test61440_block_11 : Interval test61440 176 192 :=
  interval_of_check test61440 176 16 (by decide +kernel)

theorem test61440_block_12 : Interval test61440 192 208 :=
  interval_of_check test61440 192 16 (by decide +kernel)

theorem test61440_block_13 : Interval test61440 208 224 :=
  interval_of_check test61440 208 16 (by decide +kernel)

theorem test61440_block_14 : Interval test61440 224 240 :=
  interval_of_check test61440 224 16 (by decide +kernel)

theorem test61440_block_15 : Interval test61440 240 256 :=
  interval_of_check test61440 240 16 (by decide +kernel)

theorem test61440_block_16 : Interval test61440 256 272 :=
  interval_of_check test61440 256 16 (by decide +kernel)

theorem test61440_block_17 : Interval test61440 272 288 :=
  interval_of_check test61440 272 16 (by decide +kernel)

theorem test61440_block_18 : Interval test61440 288 304 :=
  interval_of_check test61440 288 16 (by decide +kernel)

theorem test61440_block_19 : Interval test61440 304 320 :=
  interval_of_check test61440 304 16 (by decide +kernel)

theorem test61440_block_20 : Interval test61440 320 336 :=
  interval_of_check test61440 320 16 (by decide +kernel)

theorem test61440_block_21 : Interval test61440 336 352 :=
  interval_of_check test61440 336 16 (by decide +kernel)

theorem test61440_block_22 : Interval test61440 352 368 :=
  interval_of_check test61440 352 16 (by decide +kernel)

theorem test61440_block_23 : Interval test61440 368 384 :=
  interval_of_check test61440 368 16 (by decide +kernel)

theorem test61440_block_24 : Interval test61440 384 400 :=
  interval_of_check test61440 384 16 (by decide +kernel)

theorem test61440_block_25 : Interval test61440 400 416 :=
  interval_of_check test61440 400 16 (by decide +kernel)

theorem test61440_block_26 : Interval test61440 416 432 :=
  interval_of_check test61440 416 16 (by decide +kernel)

theorem test61440_block_27 : Interval test61440 432 448 :=
  interval_of_check test61440 432 16 (by decide +kernel)

theorem test61440_block_28 : Interval test61440 448 464 :=
  interval_of_check test61440 448 16 (by decide +kernel)

theorem test61440_block_29 : Interval test61440 464 480 :=
  interval_of_check test61440 464 16 (by decide +kernel)

theorem test61440_block_30 : Interval test61440 480 496 :=
  interval_of_check test61440 480 16 (by decide +kernel)

theorem test61440_block_31 : Interval test61440 496 512 :=
  interval_of_check test61440 496 16 (by decide +kernel)

theorem test61440_block_32 : Interval test61440 512 528 :=
  interval_of_check test61440 512 16 (by decide +kernel)

theorem test61440_block_33 : Interval test61440 528 544 :=
  interval_of_check test61440 528 16 (by decide +kernel)

theorem test61440_block_34 : Interval test61440 544 560 :=
  interval_of_check test61440 544 16 (by decide +kernel)

theorem test61440_block_35 : Interval test61440 560 576 :=
  interval_of_check test61440 560 16 (by decide +kernel)

theorem test61440_block_36 : Interval test61440 576 592 :=
  interval_of_check test61440 576 16 (by decide +kernel)

theorem test61440_block_37 : Interval test61440 592 608 :=
  interval_of_check test61440 592 16 (by decide +kernel)

theorem test61440_block_38 : Interval test61440 608 624 :=
  interval_of_check test61440 608 16 (by decide +kernel)

theorem test61440_block_39 : Interval test61440 624 640 :=
  interval_of_check test61440 624 16 (by decide +kernel)

theorem test61440_complete : Interval test61440 0 640 :=
  (interval_append test61440 0 320 640
  (interval_append test61440 0 160 320
  (interval_append test61440 0 80 160
  (interval_append test61440 0 32 80
  (interval_append test61440 0 16 32
  test61440_block_0
  test61440_block_1)
  (interval_append test61440 32 48 80
  test61440_block_2
  (interval_append test61440 48 64 80
  test61440_block_3
  test61440_block_4)))
  (interval_append test61440 80 112 160
  (interval_append test61440 80 96 112
  test61440_block_5
  test61440_block_6)
  (interval_append test61440 112 128 160
  test61440_block_7
  (interval_append test61440 128 144 160
  test61440_block_8
  test61440_block_9))))
  (interval_append test61440 160 240 320
  (interval_append test61440 160 192 240
  (interval_append test61440 160 176 192
  test61440_block_10
  test61440_block_11)
  (interval_append test61440 192 208 240
  test61440_block_12
  (interval_append test61440 208 224 240
  test61440_block_13
  test61440_block_14)))
  (interval_append test61440 240 272 320
  (interval_append test61440 240 256 272
  test61440_block_15
  test61440_block_16)
  (interval_append test61440 272 288 320
  test61440_block_17
  (interval_append test61440 288 304 320
  test61440_block_18
  test61440_block_19)))))
  (interval_append test61440 320 480 640
  (interval_append test61440 320 400 480
  (interval_append test61440 320 352 400
  (interval_append test61440 320 336 352
  test61440_block_20
  test61440_block_21)
  (interval_append test61440 352 368 400
  test61440_block_22
  (interval_append test61440 368 384 400
  test61440_block_23
  test61440_block_24)))
  (interval_append test61440 400 432 480
  (interval_append test61440 400 416 432
  test61440_block_25
  test61440_block_26)
  (interval_append test61440 432 448 480
  test61440_block_27
  (interval_append test61440 448 464 480
  test61440_block_28
  test61440_block_29))))
  (interval_append test61440 480 560 640
  (interval_append test61440 480 512 560
  (interval_append test61440 480 496 512
  test61440_block_30
  test61440_block_31)
  (interval_append test61440 512 528 560
  test61440_block_32
  (interval_append test61440 528 544 560
  test61440_block_33
  test61440_block_34)))
  (interval_append test61440 560 592 640
  (interval_append test61440 560 576 592
  test61440_block_35
  test61440_block_36)
  (interval_append test61440 592 608 640
  test61440_block_37
  (interval_append test61440 608 624 640
  test61440_block_38
  test61440_block_39))))))
theorem nodeInterval61440 : Interval nodeTest 61440 62080 := by
  intro i hlo hhi
  have h := test61440_complete (i-61440) (Nat.zero_le _) (by omega)
  simpa only [test61440, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
