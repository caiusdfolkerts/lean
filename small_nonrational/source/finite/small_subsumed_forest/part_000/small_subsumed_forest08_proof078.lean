module
prelude
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test49920 (i : Nat) := nodeTest (i+49920)
theorem test49920_block_0 : Interval test49920 0 16 :=
  interval_of_check test49920 0 16 (by decide +kernel)

theorem test49920_block_1 : Interval test49920 16 32 :=
  interval_of_check test49920 16 16 (by decide +kernel)

theorem test49920_block_2 : Interval test49920 32 48 :=
  interval_of_check test49920 32 16 (by decide +kernel)

theorem test49920_block_3 : Interval test49920 48 64 :=
  interval_of_check test49920 48 16 (by decide +kernel)

theorem test49920_block_4 : Interval test49920 64 80 :=
  interval_of_check test49920 64 16 (by decide +kernel)

theorem test49920_block_5 : Interval test49920 80 96 :=
  interval_of_check test49920 80 16 (by decide +kernel)

theorem test49920_block_6 : Interval test49920 96 112 :=
  interval_of_check test49920 96 16 (by decide +kernel)

theorem test49920_block_7 : Interval test49920 112 128 :=
  interval_of_check test49920 112 16 (by decide +kernel)

theorem test49920_block_8 : Interval test49920 128 144 :=
  interval_of_check test49920 128 16 (by decide +kernel)

theorem test49920_block_9 : Interval test49920 144 160 :=
  interval_of_check test49920 144 16 (by decide +kernel)

theorem test49920_block_10 : Interval test49920 160 176 :=
  interval_of_check test49920 160 16 (by decide +kernel)

theorem test49920_block_11 : Interval test49920 176 192 :=
  interval_of_check test49920 176 16 (by decide +kernel)

theorem test49920_block_12 : Interval test49920 192 208 :=
  interval_of_check test49920 192 16 (by decide +kernel)

theorem test49920_block_13 : Interval test49920 208 224 :=
  interval_of_check test49920 208 16 (by decide +kernel)

theorem test49920_block_14 : Interval test49920 224 240 :=
  interval_of_check test49920 224 16 (by decide +kernel)

theorem test49920_block_15 : Interval test49920 240 256 :=
  interval_of_check test49920 240 16 (by decide +kernel)

theorem test49920_block_16 : Interval test49920 256 272 :=
  interval_of_check test49920 256 16 (by decide +kernel)

theorem test49920_block_17 : Interval test49920 272 288 :=
  interval_of_check test49920 272 16 (by decide +kernel)

theorem test49920_block_18 : Interval test49920 288 304 :=
  interval_of_check test49920 288 16 (by decide +kernel)

theorem test49920_block_19 : Interval test49920 304 320 :=
  interval_of_check test49920 304 16 (by decide +kernel)

theorem test49920_block_20 : Interval test49920 320 336 :=
  interval_of_check test49920 320 16 (by decide +kernel)

theorem test49920_block_21 : Interval test49920 336 352 :=
  interval_of_check test49920 336 16 (by decide +kernel)

theorem test49920_block_22 : Interval test49920 352 368 :=
  interval_of_check test49920 352 16 (by decide +kernel)

theorem test49920_block_23 : Interval test49920 368 384 :=
  interval_of_check test49920 368 16 (by decide +kernel)

theorem test49920_block_24 : Interval test49920 384 400 :=
  interval_of_check test49920 384 16 (by decide +kernel)

theorem test49920_block_25 : Interval test49920 400 416 :=
  interval_of_check test49920 400 16 (by decide +kernel)

theorem test49920_block_26 : Interval test49920 416 432 :=
  interval_of_check test49920 416 16 (by decide +kernel)

theorem test49920_block_27 : Interval test49920 432 448 :=
  interval_of_check test49920 432 16 (by decide +kernel)

theorem test49920_block_28 : Interval test49920 448 464 :=
  interval_of_check test49920 448 16 (by decide +kernel)

theorem test49920_block_29 : Interval test49920 464 480 :=
  interval_of_check test49920 464 16 (by decide +kernel)

theorem test49920_block_30 : Interval test49920 480 496 :=
  interval_of_check test49920 480 16 (by decide +kernel)

theorem test49920_block_31 : Interval test49920 496 512 :=
  interval_of_check test49920 496 16 (by decide +kernel)

theorem test49920_block_32 : Interval test49920 512 528 :=
  interval_of_check test49920 512 16 (by decide +kernel)

theorem test49920_block_33 : Interval test49920 528 544 :=
  interval_of_check test49920 528 16 (by decide +kernel)

theorem test49920_block_34 : Interval test49920 544 560 :=
  interval_of_check test49920 544 16 (by decide +kernel)

theorem test49920_block_35 : Interval test49920 560 576 :=
  interval_of_check test49920 560 16 (by decide +kernel)

theorem test49920_block_36 : Interval test49920 576 592 :=
  interval_of_check test49920 576 16 (by decide +kernel)

theorem test49920_block_37 : Interval test49920 592 608 :=
  interval_of_check test49920 592 16 (by decide +kernel)

theorem test49920_block_38 : Interval test49920 608 624 :=
  interval_of_check test49920 608 16 (by decide +kernel)

theorem test49920_block_39 : Interval test49920 624 640 :=
  interval_of_check test49920 624 16 (by decide +kernel)

theorem test49920_complete : Interval test49920 0 640 :=
  (interval_append test49920 0 320 640
  (interval_append test49920 0 160 320
  (interval_append test49920 0 80 160
  (interval_append test49920 0 32 80
  (interval_append test49920 0 16 32
  test49920_block_0
  test49920_block_1)
  (interval_append test49920 32 48 80
  test49920_block_2
  (interval_append test49920 48 64 80
  test49920_block_3
  test49920_block_4)))
  (interval_append test49920 80 112 160
  (interval_append test49920 80 96 112
  test49920_block_5
  test49920_block_6)
  (interval_append test49920 112 128 160
  test49920_block_7
  (interval_append test49920 128 144 160
  test49920_block_8
  test49920_block_9))))
  (interval_append test49920 160 240 320
  (interval_append test49920 160 192 240
  (interval_append test49920 160 176 192
  test49920_block_10
  test49920_block_11)
  (interval_append test49920 192 208 240
  test49920_block_12
  (interval_append test49920 208 224 240
  test49920_block_13
  test49920_block_14)))
  (interval_append test49920 240 272 320
  (interval_append test49920 240 256 272
  test49920_block_15
  test49920_block_16)
  (interval_append test49920 272 288 320
  test49920_block_17
  (interval_append test49920 288 304 320
  test49920_block_18
  test49920_block_19)))))
  (interval_append test49920 320 480 640
  (interval_append test49920 320 400 480
  (interval_append test49920 320 352 400
  (interval_append test49920 320 336 352
  test49920_block_20
  test49920_block_21)
  (interval_append test49920 352 368 400
  test49920_block_22
  (interval_append test49920 368 384 400
  test49920_block_23
  test49920_block_24)))
  (interval_append test49920 400 432 480
  (interval_append test49920 400 416 432
  test49920_block_25
  test49920_block_26)
  (interval_append test49920 432 448 480
  test49920_block_27
  (interval_append test49920 448 464 480
  test49920_block_28
  test49920_block_29))))
  (interval_append test49920 480 560 640
  (interval_append test49920 480 512 560
  (interval_append test49920 480 496 512
  test49920_block_30
  test49920_block_31)
  (interval_append test49920 512 528 560
  test49920_block_32
  (interval_append test49920 528 544 560
  test49920_block_33
  test49920_block_34)))
  (interval_append test49920 560 592 640
  (interval_append test49920 560 576 592
  test49920_block_35
  test49920_block_36)
  (interval_append test49920 592 608 640
  test49920_block_37
  (interval_append test49920 608 624 640
  test49920_block_38
  test49920_block_39))))))
theorem nodeInterval49920 : Interval nodeTest 49920 50560 := by
  intro i hlo hhi
  have h := test49920_complete (i-49920) (Nat.zero_le _) (by omega)
  simpa only [test49920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
