module
prelude
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test86400 (i : Nat) := nodeTest (i+86400)
theorem test86400_block_0 : Interval test86400 0 16 :=
  interval_of_check test86400 0 16 (by decide +kernel)

theorem test86400_block_1 : Interval test86400 16 32 :=
  interval_of_check test86400 16 16 (by decide +kernel)

theorem test86400_block_2 : Interval test86400 32 48 :=
  interval_of_check test86400 32 16 (by decide +kernel)

theorem test86400_block_3 : Interval test86400 48 64 :=
  interval_of_check test86400 48 16 (by decide +kernel)

theorem test86400_block_4 : Interval test86400 64 80 :=
  interval_of_check test86400 64 16 (by decide +kernel)

theorem test86400_block_5 : Interval test86400 80 96 :=
  interval_of_check test86400 80 16 (by decide +kernel)

theorem test86400_block_6 : Interval test86400 96 112 :=
  interval_of_check test86400 96 16 (by decide +kernel)

theorem test86400_block_7 : Interval test86400 112 128 :=
  interval_of_check test86400 112 16 (by decide +kernel)

theorem test86400_block_8 : Interval test86400 128 144 :=
  interval_of_check test86400 128 16 (by decide +kernel)

theorem test86400_block_9 : Interval test86400 144 160 :=
  interval_of_check test86400 144 16 (by decide +kernel)

theorem test86400_block_10 : Interval test86400 160 176 :=
  interval_of_check test86400 160 16 (by decide +kernel)

theorem test86400_block_11 : Interval test86400 176 192 :=
  interval_of_check test86400 176 16 (by decide +kernel)

theorem test86400_block_12 : Interval test86400 192 208 :=
  interval_of_check test86400 192 16 (by decide +kernel)

theorem test86400_block_13 : Interval test86400 208 224 :=
  interval_of_check test86400 208 16 (by decide +kernel)

theorem test86400_block_14 : Interval test86400 224 240 :=
  interval_of_check test86400 224 16 (by decide +kernel)

theorem test86400_block_15 : Interval test86400 240 256 :=
  interval_of_check test86400 240 16 (by decide +kernel)

theorem test86400_block_16 : Interval test86400 256 272 :=
  interval_of_check test86400 256 16 (by decide +kernel)

theorem test86400_block_17 : Interval test86400 272 288 :=
  interval_of_check test86400 272 16 (by decide +kernel)

theorem test86400_block_18 : Interval test86400 288 304 :=
  interval_of_check test86400 288 16 (by decide +kernel)

theorem test86400_block_19 : Interval test86400 304 320 :=
  interval_of_check test86400 304 16 (by decide +kernel)

theorem test86400_block_20 : Interval test86400 320 336 :=
  interval_of_check test86400 320 16 (by decide +kernel)

theorem test86400_block_21 : Interval test86400 336 352 :=
  interval_of_check test86400 336 16 (by decide +kernel)

theorem test86400_block_22 : Interval test86400 352 368 :=
  interval_of_check test86400 352 16 (by decide +kernel)

theorem test86400_block_23 : Interval test86400 368 384 :=
  interval_of_check test86400 368 16 (by decide +kernel)

theorem test86400_block_24 : Interval test86400 384 400 :=
  interval_of_check test86400 384 16 (by decide +kernel)

theorem test86400_block_25 : Interval test86400 400 416 :=
  interval_of_check test86400 400 16 (by decide +kernel)

theorem test86400_block_26 : Interval test86400 416 432 :=
  interval_of_check test86400 416 16 (by decide +kernel)

theorem test86400_block_27 : Interval test86400 432 448 :=
  interval_of_check test86400 432 16 (by decide +kernel)

theorem test86400_block_28 : Interval test86400 448 464 :=
  interval_of_check test86400 448 16 (by decide +kernel)

theorem test86400_block_29 : Interval test86400 464 480 :=
  interval_of_check test86400 464 16 (by decide +kernel)

theorem test86400_block_30 : Interval test86400 480 496 :=
  interval_of_check test86400 480 16 (by decide +kernel)

theorem test86400_block_31 : Interval test86400 496 512 :=
  interval_of_check test86400 496 16 (by decide +kernel)

theorem test86400_block_32 : Interval test86400 512 528 :=
  interval_of_check test86400 512 16 (by decide +kernel)

theorem test86400_block_33 : Interval test86400 528 544 :=
  interval_of_check test86400 528 16 (by decide +kernel)

theorem test86400_block_34 : Interval test86400 544 560 :=
  interval_of_check test86400 544 16 (by decide +kernel)

theorem test86400_block_35 : Interval test86400 560 576 :=
  interval_of_check test86400 560 16 (by decide +kernel)

theorem test86400_block_36 : Interval test86400 576 592 :=
  interval_of_check test86400 576 16 (by decide +kernel)

theorem test86400_block_37 : Interval test86400 592 608 :=
  interval_of_check test86400 592 16 (by decide +kernel)

theorem test86400_block_38 : Interval test86400 608 624 :=
  interval_of_check test86400 608 16 (by decide +kernel)

theorem test86400_block_39 : Interval test86400 624 640 :=
  interval_of_check test86400 624 16 (by decide +kernel)

theorem test86400_complete : Interval test86400 0 640 :=
  (interval_append test86400 0 320 640
  (interval_append test86400 0 160 320
  (interval_append test86400 0 80 160
  (interval_append test86400 0 32 80
  (interval_append test86400 0 16 32
  test86400_block_0
  test86400_block_1)
  (interval_append test86400 32 48 80
  test86400_block_2
  (interval_append test86400 48 64 80
  test86400_block_3
  test86400_block_4)))
  (interval_append test86400 80 112 160
  (interval_append test86400 80 96 112
  test86400_block_5
  test86400_block_6)
  (interval_append test86400 112 128 160
  test86400_block_7
  (interval_append test86400 128 144 160
  test86400_block_8
  test86400_block_9))))
  (interval_append test86400 160 240 320
  (interval_append test86400 160 192 240
  (interval_append test86400 160 176 192
  test86400_block_10
  test86400_block_11)
  (interval_append test86400 192 208 240
  test86400_block_12
  (interval_append test86400 208 224 240
  test86400_block_13
  test86400_block_14)))
  (interval_append test86400 240 272 320
  (interval_append test86400 240 256 272
  test86400_block_15
  test86400_block_16)
  (interval_append test86400 272 288 320
  test86400_block_17
  (interval_append test86400 288 304 320
  test86400_block_18
  test86400_block_19)))))
  (interval_append test86400 320 480 640
  (interval_append test86400 320 400 480
  (interval_append test86400 320 352 400
  (interval_append test86400 320 336 352
  test86400_block_20
  test86400_block_21)
  (interval_append test86400 352 368 400
  test86400_block_22
  (interval_append test86400 368 384 400
  test86400_block_23
  test86400_block_24)))
  (interval_append test86400 400 432 480
  (interval_append test86400 400 416 432
  test86400_block_25
  test86400_block_26)
  (interval_append test86400 432 448 480
  test86400_block_27
  (interval_append test86400 448 464 480
  test86400_block_28
  test86400_block_29))))
  (interval_append test86400 480 560 640
  (interval_append test86400 480 512 560
  (interval_append test86400 480 496 512
  test86400_block_30
  test86400_block_31)
  (interval_append test86400 512 528 560
  test86400_block_32
  (interval_append test86400 528 544 560
  test86400_block_33
  test86400_block_34)))
  (interval_append test86400 560 592 640
  (interval_append test86400 560 576 592
  test86400_block_35
  test86400_block_36)
  (interval_append test86400 592 608 640
  test86400_block_37
  (interval_append test86400 608 624 640
  test86400_block_38
  test86400_block_39))))))
theorem nodeInterval86400 : Interval nodeTest 86400 87040 := by
  intro i hlo hhi
  have h := test86400_complete (i-86400) (Nat.zero_le _) (by omega)
  simpa only [test86400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
