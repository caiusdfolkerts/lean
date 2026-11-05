module
prelude
public import RootedSubsumedForest0232Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_block_8 : Interval test0 128 144 :=
  interval_of_check test0 128 16 (by decide +kernel)

theorem test0_block_9 : Interval test0 144 160 :=
  interval_of_check test0 144 16 (by decide +kernel)

theorem test0_block_10 : Interval test0 160 176 :=
  interval_of_check test0 160 16 (by decide +kernel)

theorem test0_block_11 : Interval test0 176 192 :=
  interval_of_check test0 176 16 (by decide +kernel)

theorem test0_block_12 : Interval test0 192 208 :=
  interval_of_check test0 192 16 (by decide +kernel)

theorem test0_block_13 : Interval test0 208 224 :=
  interval_of_check test0 208 16 (by decide +kernel)

theorem test0_block_14 : Interval test0 224 240 :=
  interval_of_check test0 224 16 (by decide +kernel)

theorem test0_block_15 : Interval test0 240 256 :=
  interval_of_check test0 240 16 (by decide +kernel)

theorem test0_block_16 : Interval test0 256 272 :=
  interval_of_check test0 256 16 (by decide +kernel)

theorem test0_block_17 : Interval test0 272 288 :=
  interval_of_check test0 272 16 (by decide +kernel)

theorem test0_block_18 : Interval test0 288 304 :=
  interval_of_check test0 288 16 (by decide +kernel)

theorem test0_block_19 : Interval test0 304 320 :=
  interval_of_check test0 304 16 (by decide +kernel)

theorem test0_block_20 : Interval test0 320 336 :=
  interval_of_check test0 320 16 (by decide +kernel)

theorem test0_block_21 : Interval test0 336 352 :=
  interval_of_check test0 336 16 (by decide +kernel)

theorem test0_block_22 : Interval test0 352 368 :=
  interval_of_check test0 352 16 (by decide +kernel)

theorem test0_block_23 : Interval test0 368 384 :=
  interval_of_check test0 368 16 (by decide +kernel)

theorem test0_block_24 : Interval test0 384 400 :=
  interval_of_check test0 384 16 (by decide +kernel)

theorem test0_block_25 : Interval test0 400 416 :=
  interval_of_check test0 400 16 (by decide +kernel)

theorem test0_block_26 : Interval test0 416 432 :=
  interval_of_check test0 416 16 (by decide +kernel)

theorem test0_block_27 : Interval test0 432 448 :=
  interval_of_check test0 432 16 (by decide +kernel)

theorem test0_block_28 : Interval test0 448 464 :=
  interval_of_check test0 448 16 (by decide +kernel)

theorem test0_block_29 : Interval test0 464 480 :=
  interval_of_check test0 464 16 (by decide +kernel)

theorem test0_block_30 : Interval test0 480 496 :=
  interval_of_check test0 480 16 (by decide +kernel)

theorem test0_block_31 : Interval test0 496 512 :=
  interval_of_check test0 496 16 (by decide +kernel)

theorem test0_block_32 : Interval test0 512 528 :=
  interval_of_check test0 512 16 (by decide +kernel)

theorem test0_block_33 : Interval test0 528 544 :=
  interval_of_check test0 528 16 (by decide +kernel)

theorem test0_block_34 : Interval test0 544 560 :=
  interval_of_check test0 544 16 (by decide +kernel)

theorem test0_block_35 : Interval test0 560 576 :=
  interval_of_check test0 560 16 (by decide +kernel)

theorem test0_block_36 : Interval test0 576 592 :=
  interval_of_check test0 576 16 (by decide +kernel)

theorem test0_block_37 : Interval test0 592 608 :=
  interval_of_check test0 592 16 (by decide +kernel)

theorem test0_block_38 : Interval test0 608 624 :=
  interval_of_check test0 608 16 (by decide +kernel)

theorem test0_block_39 : Interval test0 624 640 :=
  interval_of_check test0 624 16 (by decide +kernel)

theorem test0_complete : Interval test0 0 640 :=
  (interval_append test0 0 320 640
  (interval_append test0 0 160 320
  (interval_append test0 0 80 160
  (interval_append test0 0 32 80
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 80
  test0_block_2
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)))
  (interval_append test0 80 112 160
  (interval_append test0 80 96 112
  test0_block_5
  test0_block_6)
  (interval_append test0 112 128 160
  test0_block_7
  (interval_append test0 128 144 160
  test0_block_8
  test0_block_9))))
  (interval_append test0 160 240 320
  (interval_append test0 160 192 240
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11)
  (interval_append test0 192 208 240
  test0_block_12
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14)))
  (interval_append test0 240 272 320
  (interval_append test0 240 256 272
  test0_block_15
  test0_block_16)
  (interval_append test0 272 288 320
  test0_block_17
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19)))))
  (interval_append test0 320 480 640
  (interval_append test0 320 400 480
  (interval_append test0 320 352 400
  (interval_append test0 320 336 352
  test0_block_20
  test0_block_21)
  (interval_append test0 352 368 400
  test0_block_22
  (interval_append test0 368 384 400
  test0_block_23
  test0_block_24)))
  (interval_append test0 400 432 480
  (interval_append test0 400 416 432
  test0_block_25
  test0_block_26)
  (interval_append test0 432 448 480
  test0_block_27
  (interval_append test0 448 464 480
  test0_block_28
  test0_block_29))))
  (interval_append test0 480 560 640
  (interval_append test0 480 512 560
  (interval_append test0 480 496 512
  test0_block_30
  test0_block_31)
  (interval_append test0 512 528 560
  test0_block_32
  (interval_append test0 528 544 560
  test0_block_33
  test0_block_34)))
  (interval_append test0 560 592 640
  (interval_append test0 560 576 592
  test0_block_35
  test0_block_36)
  (interval_append test0 592 608 640
  test0_block_37
  (interval_append test0 608 624 640
  test0_block_38
  test0_block_39))))))
theorem nodeInterval0 : Interval nodeTest 0 640 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
