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
def test50560 (i : Nat) := nodeTest (i+50560)
theorem test50560_block_0 : Interval test50560 0 16 :=
  interval_of_check test50560 0 16 (by decide +kernel)

theorem test50560_block_1 : Interval test50560 16 32 :=
  interval_of_check test50560 16 16 (by decide +kernel)

theorem test50560_block_2 : Interval test50560 32 48 :=
  interval_of_check test50560 32 16 (by decide +kernel)

theorem test50560_block_3 : Interval test50560 48 64 :=
  interval_of_check test50560 48 16 (by decide +kernel)

theorem test50560_block_4 : Interval test50560 64 80 :=
  interval_of_check test50560 64 16 (by decide +kernel)

theorem test50560_block_5 : Interval test50560 80 96 :=
  interval_of_check test50560 80 16 (by decide +kernel)

theorem test50560_block_6 : Interval test50560 96 112 :=
  interval_of_check test50560 96 16 (by decide +kernel)

theorem test50560_block_7 : Interval test50560 112 128 :=
  interval_of_check test50560 112 16 (by decide +kernel)

theorem test50560_block_8 : Interval test50560 128 144 :=
  interval_of_check test50560 128 16 (by decide +kernel)

theorem test50560_block_9 : Interval test50560 144 160 :=
  interval_of_check test50560 144 16 (by decide +kernel)

theorem test50560_block_10 : Interval test50560 160 176 :=
  interval_of_check test50560 160 16 (by decide +kernel)

theorem test50560_block_11 : Interval test50560 176 192 :=
  interval_of_check test50560 176 16 (by decide +kernel)

theorem test50560_block_12 : Interval test50560 192 208 :=
  interval_of_check test50560 192 16 (by decide +kernel)

theorem test50560_block_13 : Interval test50560 208 224 :=
  interval_of_check test50560 208 16 (by decide +kernel)

theorem test50560_block_14 : Interval test50560 224 240 :=
  interval_of_check test50560 224 16 (by decide +kernel)

theorem test50560_block_15 : Interval test50560 240 256 :=
  interval_of_check test50560 240 16 (by decide +kernel)

theorem test50560_block_16 : Interval test50560 256 272 :=
  interval_of_check test50560 256 16 (by decide +kernel)

theorem test50560_block_17 : Interval test50560 272 288 :=
  interval_of_check test50560 272 16 (by decide +kernel)

theorem test50560_block_18 : Interval test50560 288 304 :=
  interval_of_check test50560 288 16 (by decide +kernel)

theorem test50560_block_19 : Interval test50560 304 320 :=
  interval_of_check test50560 304 16 (by decide +kernel)

theorem test50560_block_20 : Interval test50560 320 336 :=
  interval_of_check test50560 320 16 (by decide +kernel)

theorem test50560_block_21 : Interval test50560 336 352 :=
  interval_of_check test50560 336 16 (by decide +kernel)

theorem test50560_block_22 : Interval test50560 352 368 :=
  interval_of_check test50560 352 16 (by decide +kernel)

theorem test50560_block_23 : Interval test50560 368 384 :=
  interval_of_check test50560 368 16 (by decide +kernel)

theorem test50560_block_24 : Interval test50560 384 400 :=
  interval_of_check test50560 384 16 (by decide +kernel)

theorem test50560_block_25 : Interval test50560 400 416 :=
  interval_of_check test50560 400 16 (by decide +kernel)

theorem test50560_block_26 : Interval test50560 416 432 :=
  interval_of_check test50560 416 16 (by decide +kernel)

theorem test50560_block_27 : Interval test50560 432 448 :=
  interval_of_check test50560 432 16 (by decide +kernel)

theorem test50560_block_28 : Interval test50560 448 464 :=
  interval_of_check test50560 448 16 (by decide +kernel)

theorem test50560_block_29 : Interval test50560 464 480 :=
  interval_of_check test50560 464 16 (by decide +kernel)

theorem test50560_block_30 : Interval test50560 480 496 :=
  interval_of_check test50560 480 16 (by decide +kernel)

theorem test50560_block_31 : Interval test50560 496 512 :=
  interval_of_check test50560 496 16 (by decide +kernel)

theorem test50560_block_32 : Interval test50560 512 528 :=
  interval_of_check test50560 512 16 (by decide +kernel)

theorem test50560_block_33 : Interval test50560 528 544 :=
  interval_of_check test50560 528 16 (by decide +kernel)

theorem test50560_block_34 : Interval test50560 544 560 :=
  interval_of_check test50560 544 16 (by decide +kernel)

theorem test50560_block_35 : Interval test50560 560 576 :=
  interval_of_check test50560 560 16 (by decide +kernel)

theorem test50560_block_36 : Interval test50560 576 592 :=
  interval_of_check test50560 576 16 (by decide +kernel)

theorem test50560_block_37 : Interval test50560 592 608 :=
  interval_of_check test50560 592 16 (by decide +kernel)

theorem test50560_block_38 : Interval test50560 608 624 :=
  interval_of_check test50560 608 16 (by decide +kernel)

theorem test50560_block_39 : Interval test50560 624 640 :=
  interval_of_check test50560 624 16 (by decide +kernel)

theorem test50560_complete : Interval test50560 0 640 :=
  (interval_append test50560 0 320 640
  (interval_append test50560 0 160 320
  (interval_append test50560 0 80 160
  (interval_append test50560 0 32 80
  (interval_append test50560 0 16 32
  test50560_block_0
  test50560_block_1)
  (interval_append test50560 32 48 80
  test50560_block_2
  (interval_append test50560 48 64 80
  test50560_block_3
  test50560_block_4)))
  (interval_append test50560 80 112 160
  (interval_append test50560 80 96 112
  test50560_block_5
  test50560_block_6)
  (interval_append test50560 112 128 160
  test50560_block_7
  (interval_append test50560 128 144 160
  test50560_block_8
  test50560_block_9))))
  (interval_append test50560 160 240 320
  (interval_append test50560 160 192 240
  (interval_append test50560 160 176 192
  test50560_block_10
  test50560_block_11)
  (interval_append test50560 192 208 240
  test50560_block_12
  (interval_append test50560 208 224 240
  test50560_block_13
  test50560_block_14)))
  (interval_append test50560 240 272 320
  (interval_append test50560 240 256 272
  test50560_block_15
  test50560_block_16)
  (interval_append test50560 272 288 320
  test50560_block_17
  (interval_append test50560 288 304 320
  test50560_block_18
  test50560_block_19)))))
  (interval_append test50560 320 480 640
  (interval_append test50560 320 400 480
  (interval_append test50560 320 352 400
  (interval_append test50560 320 336 352
  test50560_block_20
  test50560_block_21)
  (interval_append test50560 352 368 400
  test50560_block_22
  (interval_append test50560 368 384 400
  test50560_block_23
  test50560_block_24)))
  (interval_append test50560 400 432 480
  (interval_append test50560 400 416 432
  test50560_block_25
  test50560_block_26)
  (interval_append test50560 432 448 480
  test50560_block_27
  (interval_append test50560 448 464 480
  test50560_block_28
  test50560_block_29))))
  (interval_append test50560 480 560 640
  (interval_append test50560 480 512 560
  (interval_append test50560 480 496 512
  test50560_block_30
  test50560_block_31)
  (interval_append test50560 512 528 560
  test50560_block_32
  (interval_append test50560 528 544 560
  test50560_block_33
  test50560_block_34)))
  (interval_append test50560 560 592 640
  (interval_append test50560 560 576 592
  test50560_block_35
  test50560_block_36)
  (interval_append test50560 592 608 640
  test50560_block_37
  (interval_append test50560 608 624 640
  test50560_block_38
  test50560_block_39))))))
theorem nodeInterval50560 : Interval nodeTest 50560 51200 := by
  intro i hlo hhi
  have h := test50560_complete (i-50560) (Nat.zero_le _) (by omega)
  simpa only [test50560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
