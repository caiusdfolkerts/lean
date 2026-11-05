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
def test10880 (i : Nat) := nodeTest (i+10880)
theorem test10880_block_0 : Interval test10880 0 16 :=
  interval_of_check test10880 0 16 (by decide +kernel)

theorem test10880_block_1 : Interval test10880 16 32 :=
  interval_of_check test10880 16 16 (by decide +kernel)

theorem test10880_block_2 : Interval test10880 32 48 :=
  interval_of_check test10880 32 16 (by decide +kernel)

theorem test10880_block_3 : Interval test10880 48 64 :=
  interval_of_check test10880 48 16 (by decide +kernel)

theorem test10880_block_4 : Interval test10880 64 80 :=
  interval_of_check test10880 64 16 (by decide +kernel)

theorem test10880_block_5 : Interval test10880 80 96 :=
  interval_of_check test10880 80 16 (by decide +kernel)

theorem test10880_block_6 : Interval test10880 96 112 :=
  interval_of_check test10880 96 16 (by decide +kernel)

theorem test10880_block_7 : Interval test10880 112 128 :=
  interval_of_check test10880 112 16 (by decide +kernel)

theorem test10880_block_8 : Interval test10880 128 144 :=
  interval_of_check test10880 128 16 (by decide +kernel)

theorem test10880_block_9 : Interval test10880 144 160 :=
  interval_of_check test10880 144 16 (by decide +kernel)

theorem test10880_block_10 : Interval test10880 160 176 :=
  interval_of_check test10880 160 16 (by decide +kernel)

theorem test10880_block_11 : Interval test10880 176 192 :=
  interval_of_check test10880 176 16 (by decide +kernel)

theorem test10880_block_12 : Interval test10880 192 208 :=
  interval_of_check test10880 192 16 (by decide +kernel)

theorem test10880_block_13 : Interval test10880 208 224 :=
  interval_of_check test10880 208 16 (by decide +kernel)

theorem test10880_block_14 : Interval test10880 224 240 :=
  interval_of_check test10880 224 16 (by decide +kernel)

theorem test10880_block_15 : Interval test10880 240 256 :=
  interval_of_check test10880 240 16 (by decide +kernel)

theorem test10880_block_16 : Interval test10880 256 272 :=
  interval_of_check test10880 256 16 (by decide +kernel)

theorem test10880_block_17 : Interval test10880 272 288 :=
  interval_of_check test10880 272 16 (by decide +kernel)

theorem test10880_block_18 : Interval test10880 288 304 :=
  interval_of_check test10880 288 16 (by decide +kernel)

theorem test10880_block_19 : Interval test10880 304 320 :=
  interval_of_check test10880 304 16 (by decide +kernel)

theorem test10880_block_20 : Interval test10880 320 336 :=
  interval_of_check test10880 320 16 (by decide +kernel)

theorem test10880_block_21 : Interval test10880 336 352 :=
  interval_of_check test10880 336 16 (by decide +kernel)

theorem test10880_block_22 : Interval test10880 352 368 :=
  interval_of_check test10880 352 16 (by decide +kernel)

theorem test10880_block_23 : Interval test10880 368 384 :=
  interval_of_check test10880 368 16 (by decide +kernel)

theorem test10880_block_24 : Interval test10880 384 400 :=
  interval_of_check test10880 384 16 (by decide +kernel)

theorem test10880_block_25 : Interval test10880 400 416 :=
  interval_of_check test10880 400 16 (by decide +kernel)

theorem test10880_block_26 : Interval test10880 416 432 :=
  interval_of_check test10880 416 16 (by decide +kernel)

theorem test10880_block_27 : Interval test10880 432 448 :=
  interval_of_check test10880 432 16 (by decide +kernel)

theorem test10880_block_28 : Interval test10880 448 464 :=
  interval_of_check test10880 448 16 (by decide +kernel)

theorem test10880_block_29 : Interval test10880 464 480 :=
  interval_of_check test10880 464 16 (by decide +kernel)

theorem test10880_block_30 : Interval test10880 480 496 :=
  interval_of_check test10880 480 16 (by decide +kernel)

theorem test10880_block_31 : Interval test10880 496 512 :=
  interval_of_check test10880 496 16 (by decide +kernel)

theorem test10880_block_32 : Interval test10880 512 528 :=
  interval_of_check test10880 512 16 (by decide +kernel)

theorem test10880_block_33 : Interval test10880 528 544 :=
  interval_of_check test10880 528 16 (by decide +kernel)

theorem test10880_block_34 : Interval test10880 544 560 :=
  interval_of_check test10880 544 16 (by decide +kernel)

theorem test10880_block_35 : Interval test10880 560 576 :=
  interval_of_check test10880 560 16 (by decide +kernel)

theorem test10880_block_36 : Interval test10880 576 592 :=
  interval_of_check test10880 576 16 (by decide +kernel)

theorem test10880_block_37 : Interval test10880 592 608 :=
  interval_of_check test10880 592 16 (by decide +kernel)

theorem test10880_block_38 : Interval test10880 608 624 :=
  interval_of_check test10880 608 16 (by decide +kernel)

theorem test10880_block_39 : Interval test10880 624 640 :=
  interval_of_check test10880 624 16 (by decide +kernel)

theorem test10880_complete : Interval test10880 0 640 :=
  (interval_append test10880 0 320 640
  (interval_append test10880 0 160 320
  (interval_append test10880 0 80 160
  (interval_append test10880 0 32 80
  (interval_append test10880 0 16 32
  test10880_block_0
  test10880_block_1)
  (interval_append test10880 32 48 80
  test10880_block_2
  (interval_append test10880 48 64 80
  test10880_block_3
  test10880_block_4)))
  (interval_append test10880 80 112 160
  (interval_append test10880 80 96 112
  test10880_block_5
  test10880_block_6)
  (interval_append test10880 112 128 160
  test10880_block_7
  (interval_append test10880 128 144 160
  test10880_block_8
  test10880_block_9))))
  (interval_append test10880 160 240 320
  (interval_append test10880 160 192 240
  (interval_append test10880 160 176 192
  test10880_block_10
  test10880_block_11)
  (interval_append test10880 192 208 240
  test10880_block_12
  (interval_append test10880 208 224 240
  test10880_block_13
  test10880_block_14)))
  (interval_append test10880 240 272 320
  (interval_append test10880 240 256 272
  test10880_block_15
  test10880_block_16)
  (interval_append test10880 272 288 320
  test10880_block_17
  (interval_append test10880 288 304 320
  test10880_block_18
  test10880_block_19)))))
  (interval_append test10880 320 480 640
  (interval_append test10880 320 400 480
  (interval_append test10880 320 352 400
  (interval_append test10880 320 336 352
  test10880_block_20
  test10880_block_21)
  (interval_append test10880 352 368 400
  test10880_block_22
  (interval_append test10880 368 384 400
  test10880_block_23
  test10880_block_24)))
  (interval_append test10880 400 432 480
  (interval_append test10880 400 416 432
  test10880_block_25
  test10880_block_26)
  (interval_append test10880 432 448 480
  test10880_block_27
  (interval_append test10880 448 464 480
  test10880_block_28
  test10880_block_29))))
  (interval_append test10880 480 560 640
  (interval_append test10880 480 512 560
  (interval_append test10880 480 496 512
  test10880_block_30
  test10880_block_31)
  (interval_append test10880 512 528 560
  test10880_block_32
  (interval_append test10880 528 544 560
  test10880_block_33
  test10880_block_34)))
  (interval_append test10880 560 592 640
  (interval_append test10880 560 576 592
  test10880_block_35
  test10880_block_36)
  (interval_append test10880 592 608 640
  test10880_block_37
  (interval_append test10880 608 624 640
  test10880_block_38
  test10880_block_39))))))
theorem nodeInterval10880 : Interval nodeTest 10880 11520 := by
  intro i hlo hhi
  have h := test10880_complete (i-10880) (Nat.zero_le _) (by omega)
  simpa only [test10880, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
