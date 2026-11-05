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
def test117120 (i : Nat) := nodeTest (i+117120)
theorem test117120_block_0 : Interval test117120 0 16 :=
  interval_of_check test117120 0 16 (by decide +kernel)

theorem test117120_block_1 : Interval test117120 16 32 :=
  interval_of_check test117120 16 16 (by decide +kernel)

theorem test117120_block_2 : Interval test117120 32 48 :=
  interval_of_check test117120 32 16 (by decide +kernel)

theorem test117120_block_3 : Interval test117120 48 64 :=
  interval_of_check test117120 48 16 (by decide +kernel)

theorem test117120_block_4 : Interval test117120 64 80 :=
  interval_of_check test117120 64 16 (by decide +kernel)

theorem test117120_block_5 : Interval test117120 80 96 :=
  interval_of_check test117120 80 16 (by decide +kernel)

theorem test117120_block_6 : Interval test117120 96 112 :=
  interval_of_check test117120 96 16 (by decide +kernel)

theorem test117120_block_7 : Interval test117120 112 128 :=
  interval_of_check test117120 112 16 (by decide +kernel)

theorem test117120_block_8 : Interval test117120 128 144 :=
  interval_of_check test117120 128 16 (by decide +kernel)

theorem test117120_block_9 : Interval test117120 144 160 :=
  interval_of_check test117120 144 16 (by decide +kernel)

theorem test117120_block_10 : Interval test117120 160 176 :=
  interval_of_check test117120 160 16 (by decide +kernel)

theorem test117120_block_11 : Interval test117120 176 192 :=
  interval_of_check test117120 176 16 (by decide +kernel)

theorem test117120_block_12 : Interval test117120 192 208 :=
  interval_of_check test117120 192 16 (by decide +kernel)

theorem test117120_block_13 : Interval test117120 208 224 :=
  interval_of_check test117120 208 16 (by decide +kernel)

theorem test117120_block_14 : Interval test117120 224 240 :=
  interval_of_check test117120 224 16 (by decide +kernel)

theorem test117120_block_15 : Interval test117120 240 256 :=
  interval_of_check test117120 240 16 (by decide +kernel)

theorem test117120_block_16 : Interval test117120 256 272 :=
  interval_of_check test117120 256 16 (by decide +kernel)

theorem test117120_block_17 : Interval test117120 272 288 :=
  interval_of_check test117120 272 16 (by decide +kernel)

theorem test117120_block_18 : Interval test117120 288 304 :=
  interval_of_check test117120 288 16 (by decide +kernel)

theorem test117120_block_19 : Interval test117120 304 320 :=
  interval_of_check test117120 304 16 (by decide +kernel)

theorem test117120_block_20 : Interval test117120 320 336 :=
  interval_of_check test117120 320 16 (by decide +kernel)

theorem test117120_block_21 : Interval test117120 336 352 :=
  interval_of_check test117120 336 16 (by decide +kernel)

theorem test117120_block_22 : Interval test117120 352 368 :=
  interval_of_check test117120 352 16 (by decide +kernel)

theorem test117120_block_23 : Interval test117120 368 384 :=
  interval_of_check test117120 368 16 (by decide +kernel)

theorem test117120_block_24 : Interval test117120 384 400 :=
  interval_of_check test117120 384 16 (by decide +kernel)

theorem test117120_block_25 : Interval test117120 400 416 :=
  interval_of_check test117120 400 16 (by decide +kernel)

theorem test117120_block_26 : Interval test117120 416 432 :=
  interval_of_check test117120 416 16 (by decide +kernel)

theorem test117120_block_27 : Interval test117120 432 448 :=
  interval_of_check test117120 432 16 (by decide +kernel)

theorem test117120_block_28 : Interval test117120 448 464 :=
  interval_of_check test117120 448 16 (by decide +kernel)

theorem test117120_block_29 : Interval test117120 464 480 :=
  interval_of_check test117120 464 16 (by decide +kernel)

theorem test117120_block_30 : Interval test117120 480 496 :=
  interval_of_check test117120 480 16 (by decide +kernel)

theorem test117120_block_31 : Interval test117120 496 512 :=
  interval_of_check test117120 496 16 (by decide +kernel)

theorem test117120_block_32 : Interval test117120 512 528 :=
  interval_of_check test117120 512 16 (by decide +kernel)

theorem test117120_block_33 : Interval test117120 528 544 :=
  interval_of_check test117120 528 16 (by decide +kernel)

theorem test117120_block_34 : Interval test117120 544 560 :=
  interval_of_check test117120 544 16 (by decide +kernel)

theorem test117120_block_35 : Interval test117120 560 576 :=
  interval_of_check test117120 560 16 (by decide +kernel)

theorem test117120_block_36 : Interval test117120 576 592 :=
  interval_of_check test117120 576 16 (by decide +kernel)

theorem test117120_block_37 : Interval test117120 592 608 :=
  interval_of_check test117120 592 16 (by decide +kernel)

theorem test117120_block_38 : Interval test117120 608 624 :=
  interval_of_check test117120 608 16 (by decide +kernel)

theorem test117120_block_39 : Interval test117120 624 640 :=
  interval_of_check test117120 624 16 (by decide +kernel)

theorem test117120_complete : Interval test117120 0 640 :=
  (interval_append test117120 0 320 640
  (interval_append test117120 0 160 320
  (interval_append test117120 0 80 160
  (interval_append test117120 0 32 80
  (interval_append test117120 0 16 32
  test117120_block_0
  test117120_block_1)
  (interval_append test117120 32 48 80
  test117120_block_2
  (interval_append test117120 48 64 80
  test117120_block_3
  test117120_block_4)))
  (interval_append test117120 80 112 160
  (interval_append test117120 80 96 112
  test117120_block_5
  test117120_block_6)
  (interval_append test117120 112 128 160
  test117120_block_7
  (interval_append test117120 128 144 160
  test117120_block_8
  test117120_block_9))))
  (interval_append test117120 160 240 320
  (interval_append test117120 160 192 240
  (interval_append test117120 160 176 192
  test117120_block_10
  test117120_block_11)
  (interval_append test117120 192 208 240
  test117120_block_12
  (interval_append test117120 208 224 240
  test117120_block_13
  test117120_block_14)))
  (interval_append test117120 240 272 320
  (interval_append test117120 240 256 272
  test117120_block_15
  test117120_block_16)
  (interval_append test117120 272 288 320
  test117120_block_17
  (interval_append test117120 288 304 320
  test117120_block_18
  test117120_block_19)))))
  (interval_append test117120 320 480 640
  (interval_append test117120 320 400 480
  (interval_append test117120 320 352 400
  (interval_append test117120 320 336 352
  test117120_block_20
  test117120_block_21)
  (interval_append test117120 352 368 400
  test117120_block_22
  (interval_append test117120 368 384 400
  test117120_block_23
  test117120_block_24)))
  (interval_append test117120 400 432 480
  (interval_append test117120 400 416 432
  test117120_block_25
  test117120_block_26)
  (interval_append test117120 432 448 480
  test117120_block_27
  (interval_append test117120 448 464 480
  test117120_block_28
  test117120_block_29))))
  (interval_append test117120 480 560 640
  (interval_append test117120 480 512 560
  (interval_append test117120 480 496 512
  test117120_block_30
  test117120_block_31)
  (interval_append test117120 512 528 560
  test117120_block_32
  (interval_append test117120 528 544 560
  test117120_block_33
  test117120_block_34)))
  (interval_append test117120 560 592 640
  (interval_append test117120 560 576 592
  test117120_block_35
  test117120_block_36)
  (interval_append test117120 592 608 640
  test117120_block_37
  (interval_append test117120 608 624 640
  test117120_block_38
  test117120_block_39))))))
theorem nodeInterval117120 : Interval nodeTest 117120 117760 := by
  intro i hlo hhi
  have h := test117120_complete (i-117120) (Nat.zero_le _) (by omega)
  simpa only [test117120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
