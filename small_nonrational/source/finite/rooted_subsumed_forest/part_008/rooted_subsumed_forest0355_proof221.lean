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
def test141440 (i : Nat) := nodeTest (i+141440)
theorem test141440_block_0 : Interval test141440 0 16 :=
  interval_of_check test141440 0 16 (by decide +kernel)

theorem test141440_block_1 : Interval test141440 16 32 :=
  interval_of_check test141440 16 16 (by decide +kernel)

theorem test141440_block_2 : Interval test141440 32 48 :=
  interval_of_check test141440 32 16 (by decide +kernel)

theorem test141440_block_3 : Interval test141440 48 64 :=
  interval_of_check test141440 48 16 (by decide +kernel)

theorem test141440_block_4 : Interval test141440 64 80 :=
  interval_of_check test141440 64 16 (by decide +kernel)

theorem test141440_block_5 : Interval test141440 80 96 :=
  interval_of_check test141440 80 16 (by decide +kernel)

theorem test141440_block_6 : Interval test141440 96 112 :=
  interval_of_check test141440 96 16 (by decide +kernel)

theorem test141440_block_7 : Interval test141440 112 128 :=
  interval_of_check test141440 112 16 (by decide +kernel)

theorem test141440_block_8 : Interval test141440 128 144 :=
  interval_of_check test141440 128 16 (by decide +kernel)

theorem test141440_block_9 : Interval test141440 144 160 :=
  interval_of_check test141440 144 16 (by decide +kernel)

theorem test141440_block_10 : Interval test141440 160 176 :=
  interval_of_check test141440 160 16 (by decide +kernel)

theorem test141440_block_11 : Interval test141440 176 192 :=
  interval_of_check test141440 176 16 (by decide +kernel)

theorem test141440_block_12 : Interval test141440 192 208 :=
  interval_of_check test141440 192 16 (by decide +kernel)

theorem test141440_block_13 : Interval test141440 208 224 :=
  interval_of_check test141440 208 16 (by decide +kernel)

theorem test141440_block_14 : Interval test141440 224 240 :=
  interval_of_check test141440 224 16 (by decide +kernel)

theorem test141440_block_15 : Interval test141440 240 256 :=
  interval_of_check test141440 240 16 (by decide +kernel)

theorem test141440_block_16 : Interval test141440 256 272 :=
  interval_of_check test141440 256 16 (by decide +kernel)

theorem test141440_block_17 : Interval test141440 272 288 :=
  interval_of_check test141440 272 16 (by decide +kernel)

theorem test141440_block_18 : Interval test141440 288 304 :=
  interval_of_check test141440 288 16 (by decide +kernel)

theorem test141440_block_19 : Interval test141440 304 320 :=
  interval_of_check test141440 304 16 (by decide +kernel)

theorem test141440_block_20 : Interval test141440 320 336 :=
  interval_of_check test141440 320 16 (by decide +kernel)

theorem test141440_block_21 : Interval test141440 336 352 :=
  interval_of_check test141440 336 16 (by decide +kernel)

theorem test141440_block_22 : Interval test141440 352 368 :=
  interval_of_check test141440 352 16 (by decide +kernel)

theorem test141440_block_23 : Interval test141440 368 384 :=
  interval_of_check test141440 368 16 (by decide +kernel)

theorem test141440_block_24 : Interval test141440 384 400 :=
  interval_of_check test141440 384 16 (by decide +kernel)

theorem test141440_block_25 : Interval test141440 400 416 :=
  interval_of_check test141440 400 16 (by decide +kernel)

theorem test141440_block_26 : Interval test141440 416 432 :=
  interval_of_check test141440 416 16 (by decide +kernel)

theorem test141440_block_27 : Interval test141440 432 448 :=
  interval_of_check test141440 432 16 (by decide +kernel)

theorem test141440_block_28 : Interval test141440 448 464 :=
  interval_of_check test141440 448 16 (by decide +kernel)

theorem test141440_block_29 : Interval test141440 464 480 :=
  interval_of_check test141440 464 16 (by decide +kernel)

theorem test141440_block_30 : Interval test141440 480 496 :=
  interval_of_check test141440 480 16 (by decide +kernel)

theorem test141440_block_31 : Interval test141440 496 512 :=
  interval_of_check test141440 496 16 (by decide +kernel)

theorem test141440_block_32 : Interval test141440 512 528 :=
  interval_of_check test141440 512 16 (by decide +kernel)

theorem test141440_block_33 : Interval test141440 528 544 :=
  interval_of_check test141440 528 16 (by decide +kernel)

theorem test141440_block_34 : Interval test141440 544 560 :=
  interval_of_check test141440 544 16 (by decide +kernel)

theorem test141440_block_35 : Interval test141440 560 576 :=
  interval_of_check test141440 560 16 (by decide +kernel)

theorem test141440_block_36 : Interval test141440 576 592 :=
  interval_of_check test141440 576 16 (by decide +kernel)

theorem test141440_block_37 : Interval test141440 592 608 :=
  interval_of_check test141440 592 16 (by decide +kernel)

theorem test141440_block_38 : Interval test141440 608 624 :=
  interval_of_check test141440 608 16 (by decide +kernel)

theorem test141440_block_39 : Interval test141440 624 640 :=
  interval_of_check test141440 624 16 (by decide +kernel)

theorem test141440_complete : Interval test141440 0 640 :=
  (interval_append test141440 0 320 640
  (interval_append test141440 0 160 320
  (interval_append test141440 0 80 160
  (interval_append test141440 0 32 80
  (interval_append test141440 0 16 32
  test141440_block_0
  test141440_block_1)
  (interval_append test141440 32 48 80
  test141440_block_2
  (interval_append test141440 48 64 80
  test141440_block_3
  test141440_block_4)))
  (interval_append test141440 80 112 160
  (interval_append test141440 80 96 112
  test141440_block_5
  test141440_block_6)
  (interval_append test141440 112 128 160
  test141440_block_7
  (interval_append test141440 128 144 160
  test141440_block_8
  test141440_block_9))))
  (interval_append test141440 160 240 320
  (interval_append test141440 160 192 240
  (interval_append test141440 160 176 192
  test141440_block_10
  test141440_block_11)
  (interval_append test141440 192 208 240
  test141440_block_12
  (interval_append test141440 208 224 240
  test141440_block_13
  test141440_block_14)))
  (interval_append test141440 240 272 320
  (interval_append test141440 240 256 272
  test141440_block_15
  test141440_block_16)
  (interval_append test141440 272 288 320
  test141440_block_17
  (interval_append test141440 288 304 320
  test141440_block_18
  test141440_block_19)))))
  (interval_append test141440 320 480 640
  (interval_append test141440 320 400 480
  (interval_append test141440 320 352 400
  (interval_append test141440 320 336 352
  test141440_block_20
  test141440_block_21)
  (interval_append test141440 352 368 400
  test141440_block_22
  (interval_append test141440 368 384 400
  test141440_block_23
  test141440_block_24)))
  (interval_append test141440 400 432 480
  (interval_append test141440 400 416 432
  test141440_block_25
  test141440_block_26)
  (interval_append test141440 432 448 480
  test141440_block_27
  (interval_append test141440 448 464 480
  test141440_block_28
  test141440_block_29))))
  (interval_append test141440 480 560 640
  (interval_append test141440 480 512 560
  (interval_append test141440 480 496 512
  test141440_block_30
  test141440_block_31)
  (interval_append test141440 512 528 560
  test141440_block_32
  (interval_append test141440 528 544 560
  test141440_block_33
  test141440_block_34)))
  (interval_append test141440 560 592 640
  (interval_append test141440 560 576 592
  test141440_block_35
  test141440_block_36)
  (interval_append test141440 592 608 640
  test141440_block_37
  (interval_append test141440 608 624 640
  test141440_block_38
  test141440_block_39))))))
theorem nodeInterval141440 : Interval nodeTest 141440 142080 := by
  intro i hlo hhi
  have h := test141440_complete (i-141440) (Nat.zero_le _) (by omega)
  simpa only [test141440, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
