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
def test43520 (i : Nat) := nodeTest (i+43520)
theorem test43520_block_0 : Interval test43520 0 16 :=
  interval_of_check test43520 0 16 (by decide +kernel)

theorem test43520_block_1 : Interval test43520 16 32 :=
  interval_of_check test43520 16 16 (by decide +kernel)

theorem test43520_block_2 : Interval test43520 32 48 :=
  interval_of_check test43520 32 16 (by decide +kernel)

theorem test43520_block_3 : Interval test43520 48 64 :=
  interval_of_check test43520 48 16 (by decide +kernel)

theorem test43520_block_4 : Interval test43520 64 80 :=
  interval_of_check test43520 64 16 (by decide +kernel)

theorem test43520_block_5 : Interval test43520 80 96 :=
  interval_of_check test43520 80 16 (by decide +kernel)

theorem test43520_block_6 : Interval test43520 96 112 :=
  interval_of_check test43520 96 16 (by decide +kernel)

theorem test43520_block_7 : Interval test43520 112 128 :=
  interval_of_check test43520 112 16 (by decide +kernel)

theorem test43520_block_8 : Interval test43520 128 144 :=
  interval_of_check test43520 128 16 (by decide +kernel)

theorem test43520_block_9 : Interval test43520 144 160 :=
  interval_of_check test43520 144 16 (by decide +kernel)

theorem test43520_block_10 : Interval test43520 160 176 :=
  interval_of_check test43520 160 16 (by decide +kernel)

theorem test43520_block_11 : Interval test43520 176 192 :=
  interval_of_check test43520 176 16 (by decide +kernel)

theorem test43520_block_12 : Interval test43520 192 208 :=
  interval_of_check test43520 192 16 (by decide +kernel)

theorem test43520_block_13 : Interval test43520 208 224 :=
  interval_of_check test43520 208 16 (by decide +kernel)

theorem test43520_block_14 : Interval test43520 224 240 :=
  interval_of_check test43520 224 16 (by decide +kernel)

theorem test43520_block_15 : Interval test43520 240 256 :=
  interval_of_check test43520 240 16 (by decide +kernel)

theorem test43520_block_16 : Interval test43520 256 272 :=
  interval_of_check test43520 256 16 (by decide +kernel)

theorem test43520_block_17 : Interval test43520 272 288 :=
  interval_of_check test43520 272 16 (by decide +kernel)

theorem test43520_block_18 : Interval test43520 288 304 :=
  interval_of_check test43520 288 16 (by decide +kernel)

theorem test43520_block_19 : Interval test43520 304 320 :=
  interval_of_check test43520 304 16 (by decide +kernel)

theorem test43520_block_20 : Interval test43520 320 336 :=
  interval_of_check test43520 320 16 (by decide +kernel)

theorem test43520_block_21 : Interval test43520 336 352 :=
  interval_of_check test43520 336 16 (by decide +kernel)

theorem test43520_block_22 : Interval test43520 352 368 :=
  interval_of_check test43520 352 16 (by decide +kernel)

theorem test43520_block_23 : Interval test43520 368 384 :=
  interval_of_check test43520 368 16 (by decide +kernel)

theorem test43520_block_24 : Interval test43520 384 400 :=
  interval_of_check test43520 384 16 (by decide +kernel)

theorem test43520_block_25 : Interval test43520 400 416 :=
  interval_of_check test43520 400 16 (by decide +kernel)

theorem test43520_block_26 : Interval test43520 416 432 :=
  interval_of_check test43520 416 16 (by decide +kernel)

theorem test43520_block_27 : Interval test43520 432 448 :=
  interval_of_check test43520 432 16 (by decide +kernel)

theorem test43520_block_28 : Interval test43520 448 464 :=
  interval_of_check test43520 448 16 (by decide +kernel)

theorem test43520_block_29 : Interval test43520 464 480 :=
  interval_of_check test43520 464 16 (by decide +kernel)

theorem test43520_block_30 : Interval test43520 480 496 :=
  interval_of_check test43520 480 16 (by decide +kernel)

theorem test43520_block_31 : Interval test43520 496 512 :=
  interval_of_check test43520 496 16 (by decide +kernel)

theorem test43520_block_32 : Interval test43520 512 528 :=
  interval_of_check test43520 512 16 (by decide +kernel)

theorem test43520_block_33 : Interval test43520 528 544 :=
  interval_of_check test43520 528 16 (by decide +kernel)

theorem test43520_block_34 : Interval test43520 544 560 :=
  interval_of_check test43520 544 16 (by decide +kernel)

theorem test43520_block_35 : Interval test43520 560 576 :=
  interval_of_check test43520 560 16 (by decide +kernel)

theorem test43520_block_36 : Interval test43520 576 592 :=
  interval_of_check test43520 576 16 (by decide +kernel)

theorem test43520_block_37 : Interval test43520 592 608 :=
  interval_of_check test43520 592 16 (by decide +kernel)

theorem test43520_block_38 : Interval test43520 608 624 :=
  interval_of_check test43520 608 16 (by decide +kernel)

theorem test43520_block_39 : Interval test43520 624 640 :=
  interval_of_check test43520 624 16 (by decide +kernel)

theorem test43520_complete : Interval test43520 0 640 :=
  (interval_append test43520 0 320 640
  (interval_append test43520 0 160 320
  (interval_append test43520 0 80 160
  (interval_append test43520 0 32 80
  (interval_append test43520 0 16 32
  test43520_block_0
  test43520_block_1)
  (interval_append test43520 32 48 80
  test43520_block_2
  (interval_append test43520 48 64 80
  test43520_block_3
  test43520_block_4)))
  (interval_append test43520 80 112 160
  (interval_append test43520 80 96 112
  test43520_block_5
  test43520_block_6)
  (interval_append test43520 112 128 160
  test43520_block_7
  (interval_append test43520 128 144 160
  test43520_block_8
  test43520_block_9))))
  (interval_append test43520 160 240 320
  (interval_append test43520 160 192 240
  (interval_append test43520 160 176 192
  test43520_block_10
  test43520_block_11)
  (interval_append test43520 192 208 240
  test43520_block_12
  (interval_append test43520 208 224 240
  test43520_block_13
  test43520_block_14)))
  (interval_append test43520 240 272 320
  (interval_append test43520 240 256 272
  test43520_block_15
  test43520_block_16)
  (interval_append test43520 272 288 320
  test43520_block_17
  (interval_append test43520 288 304 320
  test43520_block_18
  test43520_block_19)))))
  (interval_append test43520 320 480 640
  (interval_append test43520 320 400 480
  (interval_append test43520 320 352 400
  (interval_append test43520 320 336 352
  test43520_block_20
  test43520_block_21)
  (interval_append test43520 352 368 400
  test43520_block_22
  (interval_append test43520 368 384 400
  test43520_block_23
  test43520_block_24)))
  (interval_append test43520 400 432 480
  (interval_append test43520 400 416 432
  test43520_block_25
  test43520_block_26)
  (interval_append test43520 432 448 480
  test43520_block_27
  (interval_append test43520 448 464 480
  test43520_block_28
  test43520_block_29))))
  (interval_append test43520 480 560 640
  (interval_append test43520 480 512 560
  (interval_append test43520 480 496 512
  test43520_block_30
  test43520_block_31)
  (interval_append test43520 512 528 560
  test43520_block_32
  (interval_append test43520 528 544 560
  test43520_block_33
  test43520_block_34)))
  (interval_append test43520 560 592 640
  (interval_append test43520 560 576 592
  test43520_block_35
  test43520_block_36)
  (interval_append test43520 592 608 640
  test43520_block_37
  (interval_append test43520 608 624 640
  test43520_block_38
  test43520_block_39))))))
theorem nodeInterval43520 : Interval nodeTest 43520 44160 := by
  intro i hlo hhi
  have h := test43520_complete (i-43520) (Nat.zero_le _) (by omega)
  simpa only [test43520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
