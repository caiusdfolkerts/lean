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
def test38400 (i : Nat) := nodeTest (i+38400)
theorem test38400_block_0 : Interval test38400 0 16 :=
  interval_of_check test38400 0 16 (by decide +kernel)

theorem test38400_block_1 : Interval test38400 16 32 :=
  interval_of_check test38400 16 16 (by decide +kernel)

theorem test38400_block_2 : Interval test38400 32 48 :=
  interval_of_check test38400 32 16 (by decide +kernel)

theorem test38400_block_3 : Interval test38400 48 64 :=
  interval_of_check test38400 48 16 (by decide +kernel)

theorem test38400_block_4 : Interval test38400 64 80 :=
  interval_of_check test38400 64 16 (by decide +kernel)

theorem test38400_block_5 : Interval test38400 80 96 :=
  interval_of_check test38400 80 16 (by decide +kernel)

theorem test38400_block_6 : Interval test38400 96 112 :=
  interval_of_check test38400 96 16 (by decide +kernel)

theorem test38400_block_7 : Interval test38400 112 128 :=
  interval_of_check test38400 112 16 (by decide +kernel)

theorem test38400_block_8 : Interval test38400 128 144 :=
  interval_of_check test38400 128 16 (by decide +kernel)

theorem test38400_block_9 : Interval test38400 144 160 :=
  interval_of_check test38400 144 16 (by decide +kernel)

theorem test38400_block_10 : Interval test38400 160 176 :=
  interval_of_check test38400 160 16 (by decide +kernel)

theorem test38400_block_11 : Interval test38400 176 192 :=
  interval_of_check test38400 176 16 (by decide +kernel)

theorem test38400_block_12 : Interval test38400 192 208 :=
  interval_of_check test38400 192 16 (by decide +kernel)

theorem test38400_block_13 : Interval test38400 208 224 :=
  interval_of_check test38400 208 16 (by decide +kernel)

theorem test38400_block_14 : Interval test38400 224 240 :=
  interval_of_check test38400 224 16 (by decide +kernel)

theorem test38400_block_15 : Interval test38400 240 256 :=
  interval_of_check test38400 240 16 (by decide +kernel)

theorem test38400_block_16 : Interval test38400 256 272 :=
  interval_of_check test38400 256 16 (by decide +kernel)

theorem test38400_block_17 : Interval test38400 272 288 :=
  interval_of_check test38400 272 16 (by decide +kernel)

theorem test38400_block_18 : Interval test38400 288 304 :=
  interval_of_check test38400 288 16 (by decide +kernel)

theorem test38400_block_19 : Interval test38400 304 320 :=
  interval_of_check test38400 304 16 (by decide +kernel)

theorem test38400_block_20 : Interval test38400 320 336 :=
  interval_of_check test38400 320 16 (by decide +kernel)

theorem test38400_block_21 : Interval test38400 336 352 :=
  interval_of_check test38400 336 16 (by decide +kernel)

theorem test38400_block_22 : Interval test38400 352 368 :=
  interval_of_check test38400 352 16 (by decide +kernel)

theorem test38400_block_23 : Interval test38400 368 384 :=
  interval_of_check test38400 368 16 (by decide +kernel)

theorem test38400_block_24 : Interval test38400 384 400 :=
  interval_of_check test38400 384 16 (by decide +kernel)

theorem test38400_block_25 : Interval test38400 400 416 :=
  interval_of_check test38400 400 16 (by decide +kernel)

theorem test38400_block_26 : Interval test38400 416 432 :=
  interval_of_check test38400 416 16 (by decide +kernel)

theorem test38400_block_27 : Interval test38400 432 448 :=
  interval_of_check test38400 432 16 (by decide +kernel)

theorem test38400_block_28 : Interval test38400 448 464 :=
  interval_of_check test38400 448 16 (by decide +kernel)

theorem test38400_block_29 : Interval test38400 464 480 :=
  interval_of_check test38400 464 16 (by decide +kernel)

theorem test38400_block_30 : Interval test38400 480 496 :=
  interval_of_check test38400 480 16 (by decide +kernel)

theorem test38400_block_31 : Interval test38400 496 512 :=
  interval_of_check test38400 496 16 (by decide +kernel)

theorem test38400_block_32 : Interval test38400 512 528 :=
  interval_of_check test38400 512 16 (by decide +kernel)

theorem test38400_block_33 : Interval test38400 528 544 :=
  interval_of_check test38400 528 16 (by decide +kernel)

theorem test38400_block_34 : Interval test38400 544 560 :=
  interval_of_check test38400 544 16 (by decide +kernel)

theorem test38400_block_35 : Interval test38400 560 576 :=
  interval_of_check test38400 560 16 (by decide +kernel)

theorem test38400_block_36 : Interval test38400 576 592 :=
  interval_of_check test38400 576 16 (by decide +kernel)

theorem test38400_block_37 : Interval test38400 592 608 :=
  interval_of_check test38400 592 16 (by decide +kernel)

theorem test38400_block_38 : Interval test38400 608 624 :=
  interval_of_check test38400 608 16 (by decide +kernel)

theorem test38400_block_39 : Interval test38400 624 640 :=
  interval_of_check test38400 624 16 (by decide +kernel)

theorem test38400_complete : Interval test38400 0 640 :=
  (interval_append test38400 0 320 640
  (interval_append test38400 0 160 320
  (interval_append test38400 0 80 160
  (interval_append test38400 0 32 80
  (interval_append test38400 0 16 32
  test38400_block_0
  test38400_block_1)
  (interval_append test38400 32 48 80
  test38400_block_2
  (interval_append test38400 48 64 80
  test38400_block_3
  test38400_block_4)))
  (interval_append test38400 80 112 160
  (interval_append test38400 80 96 112
  test38400_block_5
  test38400_block_6)
  (interval_append test38400 112 128 160
  test38400_block_7
  (interval_append test38400 128 144 160
  test38400_block_8
  test38400_block_9))))
  (interval_append test38400 160 240 320
  (interval_append test38400 160 192 240
  (interval_append test38400 160 176 192
  test38400_block_10
  test38400_block_11)
  (interval_append test38400 192 208 240
  test38400_block_12
  (interval_append test38400 208 224 240
  test38400_block_13
  test38400_block_14)))
  (interval_append test38400 240 272 320
  (interval_append test38400 240 256 272
  test38400_block_15
  test38400_block_16)
  (interval_append test38400 272 288 320
  test38400_block_17
  (interval_append test38400 288 304 320
  test38400_block_18
  test38400_block_19)))))
  (interval_append test38400 320 480 640
  (interval_append test38400 320 400 480
  (interval_append test38400 320 352 400
  (interval_append test38400 320 336 352
  test38400_block_20
  test38400_block_21)
  (interval_append test38400 352 368 400
  test38400_block_22
  (interval_append test38400 368 384 400
  test38400_block_23
  test38400_block_24)))
  (interval_append test38400 400 432 480
  (interval_append test38400 400 416 432
  test38400_block_25
  test38400_block_26)
  (interval_append test38400 432 448 480
  test38400_block_27
  (interval_append test38400 448 464 480
  test38400_block_28
  test38400_block_29))))
  (interval_append test38400 480 560 640
  (interval_append test38400 480 512 560
  (interval_append test38400 480 496 512
  test38400_block_30
  test38400_block_31)
  (interval_append test38400 512 528 560
  test38400_block_32
  (interval_append test38400 528 544 560
  test38400_block_33
  test38400_block_34)))
  (interval_append test38400 560 592 640
  (interval_append test38400 560 576 592
  test38400_block_35
  test38400_block_36)
  (interval_append test38400 592 608 640
  test38400_block_37
  (interval_append test38400 608 624 640
  test38400_block_38
  test38400_block_39))))))
theorem nodeInterval38400 : Interval nodeTest 38400 39040 := by
  intro i hlo hhi
  have h := test38400_complete (i-38400) (Nat.zero_le _) (by omega)
  simpa only [test38400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
