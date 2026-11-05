module
prelude
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test10240 (i : Nat) := nodeTest (i+10240)
theorem test10240_block_0 : Interval test10240 0 16 :=
  interval_of_check test10240 0 16 (by decide +kernel)

theorem test10240_block_1 : Interval test10240 16 32 :=
  interval_of_check test10240 16 16 (by decide +kernel)

theorem test10240_block_2 : Interval test10240 32 48 :=
  interval_of_check test10240 32 16 (by decide +kernel)

theorem test10240_block_3 : Interval test10240 48 64 :=
  interval_of_check test10240 48 16 (by decide +kernel)

theorem test10240_block_4 : Interval test10240 64 80 :=
  interval_of_check test10240 64 16 (by decide +kernel)

theorem test10240_block_5 : Interval test10240 80 96 :=
  interval_of_check test10240 80 16 (by decide +kernel)

theorem test10240_block_6 : Interval test10240 96 112 :=
  interval_of_check test10240 96 16 (by decide +kernel)

theorem test10240_block_7 : Interval test10240 112 128 :=
  interval_of_check test10240 112 16 (by decide +kernel)

theorem test10240_block_8 : Interval test10240 128 144 :=
  interval_of_check test10240 128 16 (by decide +kernel)

theorem test10240_block_9 : Interval test10240 144 160 :=
  interval_of_check test10240 144 16 (by decide +kernel)

theorem test10240_block_10 : Interval test10240 160 176 :=
  interval_of_check test10240 160 16 (by decide +kernel)

theorem test10240_block_11 : Interval test10240 176 192 :=
  interval_of_check test10240 176 16 (by decide +kernel)

theorem test10240_block_12 : Interval test10240 192 208 :=
  interval_of_check test10240 192 16 (by decide +kernel)

theorem test10240_block_13 : Interval test10240 208 224 :=
  interval_of_check test10240 208 16 (by decide +kernel)

theorem test10240_block_14 : Interval test10240 224 240 :=
  interval_of_check test10240 224 16 (by decide +kernel)

theorem test10240_block_15 : Interval test10240 240 256 :=
  interval_of_check test10240 240 16 (by decide +kernel)

theorem test10240_block_16 : Interval test10240 256 272 :=
  interval_of_check test10240 256 16 (by decide +kernel)

theorem test10240_block_17 : Interval test10240 272 288 :=
  interval_of_check test10240 272 16 (by decide +kernel)

theorem test10240_block_18 : Interval test10240 288 304 :=
  interval_of_check test10240 288 16 (by decide +kernel)

theorem test10240_block_19 : Interval test10240 304 320 :=
  interval_of_check test10240 304 16 (by decide +kernel)

theorem test10240_block_20 : Interval test10240 320 336 :=
  interval_of_check test10240 320 16 (by decide +kernel)

theorem test10240_block_21 : Interval test10240 336 352 :=
  interval_of_check test10240 336 16 (by decide +kernel)

theorem test10240_block_22 : Interval test10240 352 368 :=
  interval_of_check test10240 352 16 (by decide +kernel)

theorem test10240_block_23 : Interval test10240 368 384 :=
  interval_of_check test10240 368 16 (by decide +kernel)

theorem test10240_block_24 : Interval test10240 384 400 :=
  interval_of_check test10240 384 16 (by decide +kernel)

theorem test10240_block_25 : Interval test10240 400 416 :=
  interval_of_check test10240 400 16 (by decide +kernel)

theorem test10240_block_26 : Interval test10240 416 432 :=
  interval_of_check test10240 416 16 (by decide +kernel)

theorem test10240_block_27 : Interval test10240 432 448 :=
  interval_of_check test10240 432 16 (by decide +kernel)

theorem test10240_block_28 : Interval test10240 448 464 :=
  interval_of_check test10240 448 16 (by decide +kernel)

theorem test10240_block_29 : Interval test10240 464 480 :=
  interval_of_check test10240 464 16 (by decide +kernel)

theorem test10240_block_30 : Interval test10240 480 496 :=
  interval_of_check test10240 480 16 (by decide +kernel)

theorem test10240_block_31 : Interval test10240 496 512 :=
  interval_of_check test10240 496 16 (by decide +kernel)

theorem test10240_block_32 : Interval test10240 512 528 :=
  interval_of_check test10240 512 16 (by decide +kernel)

theorem test10240_block_33 : Interval test10240 528 544 :=
  interval_of_check test10240 528 16 (by decide +kernel)

theorem test10240_block_34 : Interval test10240 544 560 :=
  interval_of_check test10240 544 16 (by decide +kernel)

theorem test10240_block_35 : Interval test10240 560 576 :=
  interval_of_check test10240 560 16 (by decide +kernel)

theorem test10240_block_36 : Interval test10240 576 592 :=
  interval_of_check test10240 576 16 (by decide +kernel)

theorem test10240_block_37 : Interval test10240 592 608 :=
  interval_of_check test10240 592 16 (by decide +kernel)

theorem test10240_block_38 : Interval test10240 608 624 :=
  interval_of_check test10240 608 16 (by decide +kernel)

theorem test10240_block_39 : Interval test10240 624 640 :=
  interval_of_check test10240 624 16 (by decide +kernel)

theorem test10240_complete : Interval test10240 0 640 :=
  (interval_append test10240 0 320 640
  (interval_append test10240 0 160 320
  (interval_append test10240 0 80 160
  (interval_append test10240 0 32 80
  (interval_append test10240 0 16 32
  test10240_block_0
  test10240_block_1)
  (interval_append test10240 32 48 80
  test10240_block_2
  (interval_append test10240 48 64 80
  test10240_block_3
  test10240_block_4)))
  (interval_append test10240 80 112 160
  (interval_append test10240 80 96 112
  test10240_block_5
  test10240_block_6)
  (interval_append test10240 112 128 160
  test10240_block_7
  (interval_append test10240 128 144 160
  test10240_block_8
  test10240_block_9))))
  (interval_append test10240 160 240 320
  (interval_append test10240 160 192 240
  (interval_append test10240 160 176 192
  test10240_block_10
  test10240_block_11)
  (interval_append test10240 192 208 240
  test10240_block_12
  (interval_append test10240 208 224 240
  test10240_block_13
  test10240_block_14)))
  (interval_append test10240 240 272 320
  (interval_append test10240 240 256 272
  test10240_block_15
  test10240_block_16)
  (interval_append test10240 272 288 320
  test10240_block_17
  (interval_append test10240 288 304 320
  test10240_block_18
  test10240_block_19)))))
  (interval_append test10240 320 480 640
  (interval_append test10240 320 400 480
  (interval_append test10240 320 352 400
  (interval_append test10240 320 336 352
  test10240_block_20
  test10240_block_21)
  (interval_append test10240 352 368 400
  test10240_block_22
  (interval_append test10240 368 384 400
  test10240_block_23
  test10240_block_24)))
  (interval_append test10240 400 432 480
  (interval_append test10240 400 416 432
  test10240_block_25
  test10240_block_26)
  (interval_append test10240 432 448 480
  test10240_block_27
  (interval_append test10240 448 464 480
  test10240_block_28
  test10240_block_29))))
  (interval_append test10240 480 560 640
  (interval_append test10240 480 512 560
  (interval_append test10240 480 496 512
  test10240_block_30
  test10240_block_31)
  (interval_append test10240 512 528 560
  test10240_block_32
  (interval_append test10240 528 544 560
  test10240_block_33
  test10240_block_34)))
  (interval_append test10240 560 592 640
  (interval_append test10240 560 576 592
  test10240_block_35
  test10240_block_36)
  (interval_append test10240 592 608 640
  test10240_block_37
  (interval_append test10240 608 624 640
  test10240_block_38
  test10240_block_39))))))
theorem nodeInterval10240 : Interval nodeTest 10240 10880 := by
  intro i hlo hhi
  have h := test10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [test10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
