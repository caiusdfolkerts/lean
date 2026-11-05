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
def test25600 (i : Nat) := nodeTest (i+25600)
theorem test25600_block_0 : Interval test25600 0 16 :=
  interval_of_check test25600 0 16 (by decide +kernel)

theorem test25600_block_1 : Interval test25600 16 32 :=
  interval_of_check test25600 16 16 (by decide +kernel)

theorem test25600_block_2 : Interval test25600 32 48 :=
  interval_of_check test25600 32 16 (by decide +kernel)

theorem test25600_block_3 : Interval test25600 48 64 :=
  interval_of_check test25600 48 16 (by decide +kernel)

theorem test25600_block_4 : Interval test25600 64 80 :=
  interval_of_check test25600 64 16 (by decide +kernel)

theorem test25600_block_5 : Interval test25600 80 96 :=
  interval_of_check test25600 80 16 (by decide +kernel)

theorem test25600_block_6 : Interval test25600 96 112 :=
  interval_of_check test25600 96 16 (by decide +kernel)

theorem test25600_block_7 : Interval test25600 112 128 :=
  interval_of_check test25600 112 16 (by decide +kernel)

theorem test25600_block_8 : Interval test25600 128 144 :=
  interval_of_check test25600 128 16 (by decide +kernel)

theorem test25600_block_9 : Interval test25600 144 160 :=
  interval_of_check test25600 144 16 (by decide +kernel)

theorem test25600_block_10 : Interval test25600 160 176 :=
  interval_of_check test25600 160 16 (by decide +kernel)

theorem test25600_block_11 : Interval test25600 176 192 :=
  interval_of_check test25600 176 16 (by decide +kernel)

theorem test25600_block_12 : Interval test25600 192 208 :=
  interval_of_check test25600 192 16 (by decide +kernel)

theorem test25600_block_13 : Interval test25600 208 224 :=
  interval_of_check test25600 208 16 (by decide +kernel)

theorem test25600_block_14 : Interval test25600 224 240 :=
  interval_of_check test25600 224 16 (by decide +kernel)

theorem test25600_block_15 : Interval test25600 240 256 :=
  interval_of_check test25600 240 16 (by decide +kernel)

theorem test25600_block_16 : Interval test25600 256 272 :=
  interval_of_check test25600 256 16 (by decide +kernel)

theorem test25600_block_17 : Interval test25600 272 288 :=
  interval_of_check test25600 272 16 (by decide +kernel)

theorem test25600_block_18 : Interval test25600 288 304 :=
  interval_of_check test25600 288 16 (by decide +kernel)

theorem test25600_block_19 : Interval test25600 304 320 :=
  interval_of_check test25600 304 16 (by decide +kernel)

theorem test25600_block_20 : Interval test25600 320 336 :=
  interval_of_check test25600 320 16 (by decide +kernel)

theorem test25600_block_21 : Interval test25600 336 352 :=
  interval_of_check test25600 336 16 (by decide +kernel)

theorem test25600_block_22 : Interval test25600 352 368 :=
  interval_of_check test25600 352 16 (by decide +kernel)

theorem test25600_block_23 : Interval test25600 368 384 :=
  interval_of_check test25600 368 16 (by decide +kernel)

theorem test25600_block_24 : Interval test25600 384 400 :=
  interval_of_check test25600 384 16 (by decide +kernel)

theorem test25600_block_25 : Interval test25600 400 416 :=
  interval_of_check test25600 400 16 (by decide +kernel)

theorem test25600_block_26 : Interval test25600 416 432 :=
  interval_of_check test25600 416 16 (by decide +kernel)

theorem test25600_block_27 : Interval test25600 432 448 :=
  interval_of_check test25600 432 16 (by decide +kernel)

theorem test25600_block_28 : Interval test25600 448 464 :=
  interval_of_check test25600 448 16 (by decide +kernel)

theorem test25600_block_29 : Interval test25600 464 480 :=
  interval_of_check test25600 464 16 (by decide +kernel)

theorem test25600_block_30 : Interval test25600 480 496 :=
  interval_of_check test25600 480 16 (by decide +kernel)

theorem test25600_block_31 : Interval test25600 496 512 :=
  interval_of_check test25600 496 16 (by decide +kernel)

theorem test25600_block_32 : Interval test25600 512 528 :=
  interval_of_check test25600 512 16 (by decide +kernel)

theorem test25600_block_33 : Interval test25600 528 544 :=
  interval_of_check test25600 528 16 (by decide +kernel)

theorem test25600_block_34 : Interval test25600 544 560 :=
  interval_of_check test25600 544 16 (by decide +kernel)

theorem test25600_block_35 : Interval test25600 560 576 :=
  interval_of_check test25600 560 16 (by decide +kernel)

theorem test25600_block_36 : Interval test25600 576 592 :=
  interval_of_check test25600 576 16 (by decide +kernel)

theorem test25600_block_37 : Interval test25600 592 608 :=
  interval_of_check test25600 592 16 (by decide +kernel)

theorem test25600_block_38 : Interval test25600 608 624 :=
  interval_of_check test25600 608 16 (by decide +kernel)

theorem test25600_block_39 : Interval test25600 624 640 :=
  interval_of_check test25600 624 16 (by decide +kernel)

theorem test25600_complete : Interval test25600 0 640 :=
  (interval_append test25600 0 320 640
  (interval_append test25600 0 160 320
  (interval_append test25600 0 80 160
  (interval_append test25600 0 32 80
  (interval_append test25600 0 16 32
  test25600_block_0
  test25600_block_1)
  (interval_append test25600 32 48 80
  test25600_block_2
  (interval_append test25600 48 64 80
  test25600_block_3
  test25600_block_4)))
  (interval_append test25600 80 112 160
  (interval_append test25600 80 96 112
  test25600_block_5
  test25600_block_6)
  (interval_append test25600 112 128 160
  test25600_block_7
  (interval_append test25600 128 144 160
  test25600_block_8
  test25600_block_9))))
  (interval_append test25600 160 240 320
  (interval_append test25600 160 192 240
  (interval_append test25600 160 176 192
  test25600_block_10
  test25600_block_11)
  (interval_append test25600 192 208 240
  test25600_block_12
  (interval_append test25600 208 224 240
  test25600_block_13
  test25600_block_14)))
  (interval_append test25600 240 272 320
  (interval_append test25600 240 256 272
  test25600_block_15
  test25600_block_16)
  (interval_append test25600 272 288 320
  test25600_block_17
  (interval_append test25600 288 304 320
  test25600_block_18
  test25600_block_19)))))
  (interval_append test25600 320 480 640
  (interval_append test25600 320 400 480
  (interval_append test25600 320 352 400
  (interval_append test25600 320 336 352
  test25600_block_20
  test25600_block_21)
  (interval_append test25600 352 368 400
  test25600_block_22
  (interval_append test25600 368 384 400
  test25600_block_23
  test25600_block_24)))
  (interval_append test25600 400 432 480
  (interval_append test25600 400 416 432
  test25600_block_25
  test25600_block_26)
  (interval_append test25600 432 448 480
  test25600_block_27
  (interval_append test25600 448 464 480
  test25600_block_28
  test25600_block_29))))
  (interval_append test25600 480 560 640
  (interval_append test25600 480 512 560
  (interval_append test25600 480 496 512
  test25600_block_30
  test25600_block_31)
  (interval_append test25600 512 528 560
  test25600_block_32
  (interval_append test25600 528 544 560
  test25600_block_33
  test25600_block_34)))
  (interval_append test25600 560 592 640
  (interval_append test25600 560 576 592
  test25600_block_35
  test25600_block_36)
  (interval_append test25600 592 608 640
  test25600_block_37
  (interval_append test25600 608 624 640
  test25600_block_38
  test25600_block_39))))))
theorem nodeInterval25600 : Interval nodeTest 25600 26240 := by
  intro i hlo hhi
  have h := test25600_complete (i-25600) (Nat.zero_le _) (by omega)
  simpa only [test25600, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
