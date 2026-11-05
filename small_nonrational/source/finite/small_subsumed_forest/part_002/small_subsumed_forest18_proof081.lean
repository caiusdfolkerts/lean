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
def test51840 (i : Nat) := nodeTest (i+51840)
theorem test51840_block_0 : Interval test51840 0 16 :=
  interval_of_check test51840 0 16 (by decide +kernel)

theorem test51840_block_1 : Interval test51840 16 32 :=
  interval_of_check test51840 16 16 (by decide +kernel)

theorem test51840_block_2 : Interval test51840 32 48 :=
  interval_of_check test51840 32 16 (by decide +kernel)

theorem test51840_block_3 : Interval test51840 48 64 :=
  interval_of_check test51840 48 16 (by decide +kernel)

theorem test51840_block_4 : Interval test51840 64 80 :=
  interval_of_check test51840 64 16 (by decide +kernel)

theorem test51840_block_5 : Interval test51840 80 96 :=
  interval_of_check test51840 80 16 (by decide +kernel)

theorem test51840_block_6 : Interval test51840 96 112 :=
  interval_of_check test51840 96 16 (by decide +kernel)

theorem test51840_block_7 : Interval test51840 112 128 :=
  interval_of_check test51840 112 16 (by decide +kernel)

theorem test51840_block_8 : Interval test51840 128 144 :=
  interval_of_check test51840 128 16 (by decide +kernel)

theorem test51840_block_9 : Interval test51840 144 160 :=
  interval_of_check test51840 144 16 (by decide +kernel)

theorem test51840_block_10 : Interval test51840 160 176 :=
  interval_of_check test51840 160 16 (by decide +kernel)

theorem test51840_block_11 : Interval test51840 176 192 :=
  interval_of_check test51840 176 16 (by decide +kernel)

theorem test51840_block_12 : Interval test51840 192 208 :=
  interval_of_check test51840 192 16 (by decide +kernel)

theorem test51840_block_13 : Interval test51840 208 224 :=
  interval_of_check test51840 208 16 (by decide +kernel)

theorem test51840_block_14 : Interval test51840 224 240 :=
  interval_of_check test51840 224 16 (by decide +kernel)

theorem test51840_block_15 : Interval test51840 240 256 :=
  interval_of_check test51840 240 16 (by decide +kernel)

theorem test51840_block_16 : Interval test51840 256 272 :=
  interval_of_check test51840 256 16 (by decide +kernel)

theorem test51840_block_17 : Interval test51840 272 288 :=
  interval_of_check test51840 272 16 (by decide +kernel)

theorem test51840_block_18 : Interval test51840 288 304 :=
  interval_of_check test51840 288 16 (by decide +kernel)

theorem test51840_block_19 : Interval test51840 304 320 :=
  interval_of_check test51840 304 16 (by decide +kernel)

theorem test51840_block_20 : Interval test51840 320 336 :=
  interval_of_check test51840 320 16 (by decide +kernel)

theorem test51840_block_21 : Interval test51840 336 352 :=
  interval_of_check test51840 336 16 (by decide +kernel)

theorem test51840_block_22 : Interval test51840 352 368 :=
  interval_of_check test51840 352 16 (by decide +kernel)

theorem test51840_block_23 : Interval test51840 368 384 :=
  interval_of_check test51840 368 16 (by decide +kernel)

theorem test51840_block_24 : Interval test51840 384 400 :=
  interval_of_check test51840 384 16 (by decide +kernel)

theorem test51840_block_25 : Interval test51840 400 416 :=
  interval_of_check test51840 400 16 (by decide +kernel)

theorem test51840_block_26 : Interval test51840 416 432 :=
  interval_of_check test51840 416 16 (by decide +kernel)

theorem test51840_block_27 : Interval test51840 432 448 :=
  interval_of_check test51840 432 16 (by decide +kernel)

theorem test51840_block_28 : Interval test51840 448 464 :=
  interval_of_check test51840 448 16 (by decide +kernel)

theorem test51840_block_29 : Interval test51840 464 480 :=
  interval_of_check test51840 464 16 (by decide +kernel)

theorem test51840_block_30 : Interval test51840 480 496 :=
  interval_of_check test51840 480 16 (by decide +kernel)

theorem test51840_block_31 : Interval test51840 496 512 :=
  interval_of_check test51840 496 16 (by decide +kernel)

theorem test51840_block_32 : Interval test51840 512 528 :=
  interval_of_check test51840 512 16 (by decide +kernel)

theorem test51840_block_33 : Interval test51840 528 544 :=
  interval_of_check test51840 528 16 (by decide +kernel)

theorem test51840_block_34 : Interval test51840 544 560 :=
  interval_of_check test51840 544 16 (by decide +kernel)

theorem test51840_block_35 : Interval test51840 560 576 :=
  interval_of_check test51840 560 16 (by decide +kernel)

theorem test51840_block_36 : Interval test51840 576 592 :=
  interval_of_check test51840 576 16 (by decide +kernel)

theorem test51840_block_37 : Interval test51840 592 608 :=
  interval_of_check test51840 592 16 (by decide +kernel)

theorem test51840_block_38 : Interval test51840 608 624 :=
  interval_of_check test51840 608 16 (by decide +kernel)

theorem test51840_block_39 : Interval test51840 624 640 :=
  interval_of_check test51840 624 16 (by decide +kernel)

theorem test51840_complete : Interval test51840 0 640 :=
  (interval_append test51840 0 320 640
  (interval_append test51840 0 160 320
  (interval_append test51840 0 80 160
  (interval_append test51840 0 32 80
  (interval_append test51840 0 16 32
  test51840_block_0
  test51840_block_1)
  (interval_append test51840 32 48 80
  test51840_block_2
  (interval_append test51840 48 64 80
  test51840_block_3
  test51840_block_4)))
  (interval_append test51840 80 112 160
  (interval_append test51840 80 96 112
  test51840_block_5
  test51840_block_6)
  (interval_append test51840 112 128 160
  test51840_block_7
  (interval_append test51840 128 144 160
  test51840_block_8
  test51840_block_9))))
  (interval_append test51840 160 240 320
  (interval_append test51840 160 192 240
  (interval_append test51840 160 176 192
  test51840_block_10
  test51840_block_11)
  (interval_append test51840 192 208 240
  test51840_block_12
  (interval_append test51840 208 224 240
  test51840_block_13
  test51840_block_14)))
  (interval_append test51840 240 272 320
  (interval_append test51840 240 256 272
  test51840_block_15
  test51840_block_16)
  (interval_append test51840 272 288 320
  test51840_block_17
  (interval_append test51840 288 304 320
  test51840_block_18
  test51840_block_19)))))
  (interval_append test51840 320 480 640
  (interval_append test51840 320 400 480
  (interval_append test51840 320 352 400
  (interval_append test51840 320 336 352
  test51840_block_20
  test51840_block_21)
  (interval_append test51840 352 368 400
  test51840_block_22
  (interval_append test51840 368 384 400
  test51840_block_23
  test51840_block_24)))
  (interval_append test51840 400 432 480
  (interval_append test51840 400 416 432
  test51840_block_25
  test51840_block_26)
  (interval_append test51840 432 448 480
  test51840_block_27
  (interval_append test51840 448 464 480
  test51840_block_28
  test51840_block_29))))
  (interval_append test51840 480 560 640
  (interval_append test51840 480 512 560
  (interval_append test51840 480 496 512
  test51840_block_30
  test51840_block_31)
  (interval_append test51840 512 528 560
  test51840_block_32
  (interval_append test51840 528 544 560
  test51840_block_33
  test51840_block_34)))
  (interval_append test51840 560 592 640
  (interval_append test51840 560 576 592
  test51840_block_35
  test51840_block_36)
  (interval_append test51840 592 608 640
  test51840_block_37
  (interval_append test51840 608 624 640
  test51840_block_38
  test51840_block_39))))))
theorem nodeInterval51840 : Interval nodeTest 51840 52480 := by
  intro i hlo hhi
  have h := test51840_complete (i-51840) (Nat.zero_le _) (by omega)
  simpa only [test51840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
