module
prelude
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test51200 (i : Nat) := nodeTest (i+51200)
theorem test51200_block_0 : Interval test51200 0 16 :=
  interval_of_check test51200 0 16 (by decide +kernel)

theorem test51200_block_1 : Interval test51200 16 32 :=
  interval_of_check test51200 16 16 (by decide +kernel)

theorem test51200_block_2 : Interval test51200 32 48 :=
  interval_of_check test51200 32 16 (by decide +kernel)

theorem test51200_block_3 : Interval test51200 48 64 :=
  interval_of_check test51200 48 16 (by decide +kernel)

theorem test51200_block_4 : Interval test51200 64 80 :=
  interval_of_check test51200 64 16 (by decide +kernel)

theorem test51200_block_5 : Interval test51200 80 96 :=
  interval_of_check test51200 80 16 (by decide +kernel)

theorem test51200_block_6 : Interval test51200 96 112 :=
  interval_of_check test51200 96 16 (by decide +kernel)

theorem test51200_block_7 : Interval test51200 112 128 :=
  interval_of_check test51200 112 16 (by decide +kernel)

theorem test51200_block_8 : Interval test51200 128 144 :=
  interval_of_check test51200 128 16 (by decide +kernel)

theorem test51200_block_9 : Interval test51200 144 160 :=
  interval_of_check test51200 144 16 (by decide +kernel)

theorem test51200_block_10 : Interval test51200 160 176 :=
  interval_of_check test51200 160 16 (by decide +kernel)

theorem test51200_block_11 : Interval test51200 176 192 :=
  interval_of_check test51200 176 16 (by decide +kernel)

theorem test51200_block_12 : Interval test51200 192 208 :=
  interval_of_check test51200 192 16 (by decide +kernel)

theorem test51200_block_13 : Interval test51200 208 224 :=
  interval_of_check test51200 208 16 (by decide +kernel)

theorem test51200_block_14 : Interval test51200 224 240 :=
  interval_of_check test51200 224 16 (by decide +kernel)

theorem test51200_block_15 : Interval test51200 240 256 :=
  interval_of_check test51200 240 16 (by decide +kernel)

theorem test51200_block_16 : Interval test51200 256 272 :=
  interval_of_check test51200 256 16 (by decide +kernel)

theorem test51200_block_17 : Interval test51200 272 288 :=
  interval_of_check test51200 272 16 (by decide +kernel)

theorem test51200_block_18 : Interval test51200 288 304 :=
  interval_of_check test51200 288 16 (by decide +kernel)

theorem test51200_block_19 : Interval test51200 304 320 :=
  interval_of_check test51200 304 16 (by decide +kernel)

theorem test51200_block_20 : Interval test51200 320 336 :=
  interval_of_check test51200 320 16 (by decide +kernel)

theorem test51200_block_21 : Interval test51200 336 352 :=
  interval_of_check test51200 336 16 (by decide +kernel)

theorem test51200_block_22 : Interval test51200 352 368 :=
  interval_of_check test51200 352 16 (by decide +kernel)

theorem test51200_block_23 : Interval test51200 368 384 :=
  interval_of_check test51200 368 16 (by decide +kernel)

theorem test51200_block_24 : Interval test51200 384 400 :=
  interval_of_check test51200 384 16 (by decide +kernel)

theorem test51200_block_25 : Interval test51200 400 416 :=
  interval_of_check test51200 400 16 (by decide +kernel)

theorem test51200_block_26 : Interval test51200 416 432 :=
  interval_of_check test51200 416 16 (by decide +kernel)

theorem test51200_block_27 : Interval test51200 432 448 :=
  interval_of_check test51200 432 16 (by decide +kernel)

theorem test51200_block_28 : Interval test51200 448 464 :=
  interval_of_check test51200 448 16 (by decide +kernel)

theorem test51200_block_29 : Interval test51200 464 480 :=
  interval_of_check test51200 464 16 (by decide +kernel)

theorem test51200_block_30 : Interval test51200 480 496 :=
  interval_of_check test51200 480 16 (by decide +kernel)

theorem test51200_block_31 : Interval test51200 496 512 :=
  interval_of_check test51200 496 16 (by decide +kernel)

theorem test51200_block_32 : Interval test51200 512 528 :=
  interval_of_check test51200 512 16 (by decide +kernel)

theorem test51200_block_33 : Interval test51200 528 544 :=
  interval_of_check test51200 528 16 (by decide +kernel)

theorem test51200_block_34 : Interval test51200 544 560 :=
  interval_of_check test51200 544 16 (by decide +kernel)

theorem test51200_block_35 : Interval test51200 560 576 :=
  interval_of_check test51200 560 16 (by decide +kernel)

theorem test51200_block_36 : Interval test51200 576 592 :=
  interval_of_check test51200 576 16 (by decide +kernel)

theorem test51200_block_37 : Interval test51200 592 608 :=
  interval_of_check test51200 592 16 (by decide +kernel)

theorem test51200_block_38 : Interval test51200 608 624 :=
  interval_of_check test51200 608 16 (by decide +kernel)

theorem test51200_block_39 : Interval test51200 624 640 :=
  interval_of_check test51200 624 16 (by decide +kernel)

theorem test51200_complete : Interval test51200 0 640 :=
  (interval_append test51200 0 320 640
  (interval_append test51200 0 160 320
  (interval_append test51200 0 80 160
  (interval_append test51200 0 32 80
  (interval_append test51200 0 16 32
  test51200_block_0
  test51200_block_1)
  (interval_append test51200 32 48 80
  test51200_block_2
  (interval_append test51200 48 64 80
  test51200_block_3
  test51200_block_4)))
  (interval_append test51200 80 112 160
  (interval_append test51200 80 96 112
  test51200_block_5
  test51200_block_6)
  (interval_append test51200 112 128 160
  test51200_block_7
  (interval_append test51200 128 144 160
  test51200_block_8
  test51200_block_9))))
  (interval_append test51200 160 240 320
  (interval_append test51200 160 192 240
  (interval_append test51200 160 176 192
  test51200_block_10
  test51200_block_11)
  (interval_append test51200 192 208 240
  test51200_block_12
  (interval_append test51200 208 224 240
  test51200_block_13
  test51200_block_14)))
  (interval_append test51200 240 272 320
  (interval_append test51200 240 256 272
  test51200_block_15
  test51200_block_16)
  (interval_append test51200 272 288 320
  test51200_block_17
  (interval_append test51200 288 304 320
  test51200_block_18
  test51200_block_19)))))
  (interval_append test51200 320 480 640
  (interval_append test51200 320 400 480
  (interval_append test51200 320 352 400
  (interval_append test51200 320 336 352
  test51200_block_20
  test51200_block_21)
  (interval_append test51200 352 368 400
  test51200_block_22
  (interval_append test51200 368 384 400
  test51200_block_23
  test51200_block_24)))
  (interval_append test51200 400 432 480
  (interval_append test51200 400 416 432
  test51200_block_25
  test51200_block_26)
  (interval_append test51200 432 448 480
  test51200_block_27
  (interval_append test51200 448 464 480
  test51200_block_28
  test51200_block_29))))
  (interval_append test51200 480 560 640
  (interval_append test51200 480 512 560
  (interval_append test51200 480 496 512
  test51200_block_30
  test51200_block_31)
  (interval_append test51200 512 528 560
  test51200_block_32
  (interval_append test51200 528 544 560
  test51200_block_33
  test51200_block_34)))
  (interval_append test51200 560 592 640
  (interval_append test51200 560 576 592
  test51200_block_35
  test51200_block_36)
  (interval_append test51200 592 608 640
  test51200_block_37
  (interval_append test51200 608 624 640
  test51200_block_38
  test51200_block_39))))))
theorem nodeInterval51200 : Interval nodeTest 51200 51840 := by
  intro i hlo hhi
  have h := test51200_complete (i-51200) (Nat.zero_le _) (by omega)
  simpa only [test51200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
