module
prelude
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test53760 (i : Nat) := nodeTest (i+53760)
theorem test53760_block_0 : Interval test53760 0 16 :=
  interval_of_check test53760 0 16 (by decide +kernel)

theorem test53760_block_1 : Interval test53760 16 32 :=
  interval_of_check test53760 16 16 (by decide +kernel)

theorem test53760_block_2 : Interval test53760 32 48 :=
  interval_of_check test53760 32 16 (by decide +kernel)

theorem test53760_block_3 : Interval test53760 48 64 :=
  interval_of_check test53760 48 16 (by decide +kernel)

theorem test53760_block_4 : Interval test53760 64 80 :=
  interval_of_check test53760 64 16 (by decide +kernel)

theorem test53760_block_5 : Interval test53760 80 96 :=
  interval_of_check test53760 80 16 (by decide +kernel)

theorem test53760_block_6 : Interval test53760 96 112 :=
  interval_of_check test53760 96 16 (by decide +kernel)

theorem test53760_block_7 : Interval test53760 112 128 :=
  interval_of_check test53760 112 16 (by decide +kernel)

theorem test53760_block_8 : Interval test53760 128 144 :=
  interval_of_check test53760 128 16 (by decide +kernel)

theorem test53760_block_9 : Interval test53760 144 160 :=
  interval_of_check test53760 144 16 (by decide +kernel)

theorem test53760_block_10 : Interval test53760 160 176 :=
  interval_of_check test53760 160 16 (by decide +kernel)

theorem test53760_block_11 : Interval test53760 176 192 :=
  interval_of_check test53760 176 16 (by decide +kernel)

theorem test53760_block_12 : Interval test53760 192 208 :=
  interval_of_check test53760 192 16 (by decide +kernel)

theorem test53760_block_13 : Interval test53760 208 224 :=
  interval_of_check test53760 208 16 (by decide +kernel)

theorem test53760_block_14 : Interval test53760 224 240 :=
  interval_of_check test53760 224 16 (by decide +kernel)

theorem test53760_block_15 : Interval test53760 240 256 :=
  interval_of_check test53760 240 16 (by decide +kernel)

theorem test53760_block_16 : Interval test53760 256 272 :=
  interval_of_check test53760 256 16 (by decide +kernel)

theorem test53760_block_17 : Interval test53760 272 288 :=
  interval_of_check test53760 272 16 (by decide +kernel)

theorem test53760_block_18 : Interval test53760 288 304 :=
  interval_of_check test53760 288 16 (by decide +kernel)

theorem test53760_block_19 : Interval test53760 304 320 :=
  interval_of_check test53760 304 16 (by decide +kernel)

theorem test53760_block_20 : Interval test53760 320 336 :=
  interval_of_check test53760 320 16 (by decide +kernel)

theorem test53760_block_21 : Interval test53760 336 352 :=
  interval_of_check test53760 336 16 (by decide +kernel)

theorem test53760_block_22 : Interval test53760 352 368 :=
  interval_of_check test53760 352 16 (by decide +kernel)

theorem test53760_block_23 : Interval test53760 368 384 :=
  interval_of_check test53760 368 16 (by decide +kernel)

theorem test53760_block_24 : Interval test53760 384 400 :=
  interval_of_check test53760 384 16 (by decide +kernel)

theorem test53760_block_25 : Interval test53760 400 416 :=
  interval_of_check test53760 400 16 (by decide +kernel)

theorem test53760_block_26 : Interval test53760 416 432 :=
  interval_of_check test53760 416 16 (by decide +kernel)

theorem test53760_block_27 : Interval test53760 432 448 :=
  interval_of_check test53760 432 16 (by decide +kernel)

theorem test53760_block_28 : Interval test53760 448 464 :=
  interval_of_check test53760 448 16 (by decide +kernel)

theorem test53760_block_29 : Interval test53760 464 480 :=
  interval_of_check test53760 464 16 (by decide +kernel)

theorem test53760_block_30 : Interval test53760 480 496 :=
  interval_of_check test53760 480 16 (by decide +kernel)

theorem test53760_block_31 : Interval test53760 496 512 :=
  interval_of_check test53760 496 16 (by decide +kernel)

theorem test53760_block_32 : Interval test53760 512 528 :=
  interval_of_check test53760 512 16 (by decide +kernel)

theorem test53760_block_33 : Interval test53760 528 544 :=
  interval_of_check test53760 528 16 (by decide +kernel)

theorem test53760_block_34 : Interval test53760 544 560 :=
  interval_of_check test53760 544 16 (by decide +kernel)

theorem test53760_block_35 : Interval test53760 560 576 :=
  interval_of_check test53760 560 16 (by decide +kernel)

theorem test53760_block_36 : Interval test53760 576 592 :=
  interval_of_check test53760 576 16 (by decide +kernel)

theorem test53760_block_37 : Interval test53760 592 608 :=
  interval_of_check test53760 592 16 (by decide +kernel)

theorem test53760_block_38 : Interval test53760 608 624 :=
  interval_of_check test53760 608 16 (by decide +kernel)

theorem test53760_block_39 : Interval test53760 624 640 :=
  interval_of_check test53760 624 16 (by decide +kernel)

theorem test53760_complete : Interval test53760 0 640 :=
  (interval_append test53760 0 320 640
  (interval_append test53760 0 160 320
  (interval_append test53760 0 80 160
  (interval_append test53760 0 32 80
  (interval_append test53760 0 16 32
  test53760_block_0
  test53760_block_1)
  (interval_append test53760 32 48 80
  test53760_block_2
  (interval_append test53760 48 64 80
  test53760_block_3
  test53760_block_4)))
  (interval_append test53760 80 112 160
  (interval_append test53760 80 96 112
  test53760_block_5
  test53760_block_6)
  (interval_append test53760 112 128 160
  test53760_block_7
  (interval_append test53760 128 144 160
  test53760_block_8
  test53760_block_9))))
  (interval_append test53760 160 240 320
  (interval_append test53760 160 192 240
  (interval_append test53760 160 176 192
  test53760_block_10
  test53760_block_11)
  (interval_append test53760 192 208 240
  test53760_block_12
  (interval_append test53760 208 224 240
  test53760_block_13
  test53760_block_14)))
  (interval_append test53760 240 272 320
  (interval_append test53760 240 256 272
  test53760_block_15
  test53760_block_16)
  (interval_append test53760 272 288 320
  test53760_block_17
  (interval_append test53760 288 304 320
  test53760_block_18
  test53760_block_19)))))
  (interval_append test53760 320 480 640
  (interval_append test53760 320 400 480
  (interval_append test53760 320 352 400
  (interval_append test53760 320 336 352
  test53760_block_20
  test53760_block_21)
  (interval_append test53760 352 368 400
  test53760_block_22
  (interval_append test53760 368 384 400
  test53760_block_23
  test53760_block_24)))
  (interval_append test53760 400 432 480
  (interval_append test53760 400 416 432
  test53760_block_25
  test53760_block_26)
  (interval_append test53760 432 448 480
  test53760_block_27
  (interval_append test53760 448 464 480
  test53760_block_28
  test53760_block_29))))
  (interval_append test53760 480 560 640
  (interval_append test53760 480 512 560
  (interval_append test53760 480 496 512
  test53760_block_30
  test53760_block_31)
  (interval_append test53760 512 528 560
  test53760_block_32
  (interval_append test53760 528 544 560
  test53760_block_33
  test53760_block_34)))
  (interval_append test53760 560 592 640
  (interval_append test53760 560 576 592
  test53760_block_35
  test53760_block_36)
  (interval_append test53760 592 608 640
  test53760_block_37
  (interval_append test53760 608 624 640
  test53760_block_38
  test53760_block_39))))))
theorem nodeInterval53760 : Interval nodeTest 53760 54400 := by
  intro i hlo hhi
  have h := test53760_complete (i-53760) (Nat.zero_le _) (by omega)
  simpa only [test53760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
