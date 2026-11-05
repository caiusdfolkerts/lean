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
def test60800 (i : Nat) := nodeTest (i+60800)
theorem test60800_block_0 : Interval test60800 0 16 :=
  interval_of_check test60800 0 16 (by decide +kernel)

theorem test60800_block_1 : Interval test60800 16 32 :=
  interval_of_check test60800 16 16 (by decide +kernel)

theorem test60800_block_2 : Interval test60800 32 48 :=
  interval_of_check test60800 32 16 (by decide +kernel)

theorem test60800_block_3 : Interval test60800 48 64 :=
  interval_of_check test60800 48 16 (by decide +kernel)

theorem test60800_block_4 : Interval test60800 64 80 :=
  interval_of_check test60800 64 16 (by decide +kernel)

theorem test60800_block_5 : Interval test60800 80 96 :=
  interval_of_check test60800 80 16 (by decide +kernel)

theorem test60800_block_6 : Interval test60800 96 112 :=
  interval_of_check test60800 96 16 (by decide +kernel)

theorem test60800_block_7 : Interval test60800 112 128 :=
  interval_of_check test60800 112 16 (by decide +kernel)

theorem test60800_block_8 : Interval test60800 128 144 :=
  interval_of_check test60800 128 16 (by decide +kernel)

theorem test60800_block_9 : Interval test60800 144 160 :=
  interval_of_check test60800 144 16 (by decide +kernel)

theorem test60800_block_10 : Interval test60800 160 176 :=
  interval_of_check test60800 160 16 (by decide +kernel)

theorem test60800_block_11 : Interval test60800 176 192 :=
  interval_of_check test60800 176 16 (by decide +kernel)

theorem test60800_block_12 : Interval test60800 192 208 :=
  interval_of_check test60800 192 16 (by decide +kernel)

theorem test60800_block_13 : Interval test60800 208 224 :=
  interval_of_check test60800 208 16 (by decide +kernel)

theorem test60800_block_14 : Interval test60800 224 240 :=
  interval_of_check test60800 224 16 (by decide +kernel)

theorem test60800_block_15 : Interval test60800 240 256 :=
  interval_of_check test60800 240 16 (by decide +kernel)

theorem test60800_block_16 : Interval test60800 256 272 :=
  interval_of_check test60800 256 16 (by decide +kernel)

theorem test60800_block_17 : Interval test60800 272 288 :=
  interval_of_check test60800 272 16 (by decide +kernel)

theorem test60800_block_18 : Interval test60800 288 304 :=
  interval_of_check test60800 288 16 (by decide +kernel)

theorem test60800_block_19 : Interval test60800 304 320 :=
  interval_of_check test60800 304 16 (by decide +kernel)

theorem test60800_block_20 : Interval test60800 320 336 :=
  interval_of_check test60800 320 16 (by decide +kernel)

theorem test60800_block_21 : Interval test60800 336 352 :=
  interval_of_check test60800 336 16 (by decide +kernel)

theorem test60800_block_22 : Interval test60800 352 368 :=
  interval_of_check test60800 352 16 (by decide +kernel)

theorem test60800_block_23 : Interval test60800 368 384 :=
  interval_of_check test60800 368 16 (by decide +kernel)

theorem test60800_block_24 : Interval test60800 384 400 :=
  interval_of_check test60800 384 16 (by decide +kernel)

theorem test60800_block_25 : Interval test60800 400 416 :=
  interval_of_check test60800 400 16 (by decide +kernel)

theorem test60800_block_26 : Interval test60800 416 432 :=
  interval_of_check test60800 416 16 (by decide +kernel)

theorem test60800_block_27 : Interval test60800 432 448 :=
  interval_of_check test60800 432 16 (by decide +kernel)

theorem test60800_block_28 : Interval test60800 448 464 :=
  interval_of_check test60800 448 16 (by decide +kernel)

theorem test60800_block_29 : Interval test60800 464 480 :=
  interval_of_check test60800 464 16 (by decide +kernel)

theorem test60800_block_30 : Interval test60800 480 496 :=
  interval_of_check test60800 480 16 (by decide +kernel)

theorem test60800_block_31 : Interval test60800 496 512 :=
  interval_of_check test60800 496 16 (by decide +kernel)

theorem test60800_block_32 : Interval test60800 512 528 :=
  interval_of_check test60800 512 16 (by decide +kernel)

theorem test60800_block_33 : Interval test60800 528 544 :=
  interval_of_check test60800 528 16 (by decide +kernel)

theorem test60800_block_34 : Interval test60800 544 560 :=
  interval_of_check test60800 544 16 (by decide +kernel)

theorem test60800_block_35 : Interval test60800 560 576 :=
  interval_of_check test60800 560 16 (by decide +kernel)

theorem test60800_block_36 : Interval test60800 576 592 :=
  interval_of_check test60800 576 16 (by decide +kernel)

theorem test60800_block_37 : Interval test60800 592 608 :=
  interval_of_check test60800 592 16 (by decide +kernel)

theorem test60800_block_38 : Interval test60800 608 624 :=
  interval_of_check test60800 608 16 (by decide +kernel)

theorem test60800_block_39 : Interval test60800 624 640 :=
  interval_of_check test60800 624 16 (by decide +kernel)

theorem test60800_complete : Interval test60800 0 640 :=
  (interval_append test60800 0 320 640
  (interval_append test60800 0 160 320
  (interval_append test60800 0 80 160
  (interval_append test60800 0 32 80
  (interval_append test60800 0 16 32
  test60800_block_0
  test60800_block_1)
  (interval_append test60800 32 48 80
  test60800_block_2
  (interval_append test60800 48 64 80
  test60800_block_3
  test60800_block_4)))
  (interval_append test60800 80 112 160
  (interval_append test60800 80 96 112
  test60800_block_5
  test60800_block_6)
  (interval_append test60800 112 128 160
  test60800_block_7
  (interval_append test60800 128 144 160
  test60800_block_8
  test60800_block_9))))
  (interval_append test60800 160 240 320
  (interval_append test60800 160 192 240
  (interval_append test60800 160 176 192
  test60800_block_10
  test60800_block_11)
  (interval_append test60800 192 208 240
  test60800_block_12
  (interval_append test60800 208 224 240
  test60800_block_13
  test60800_block_14)))
  (interval_append test60800 240 272 320
  (interval_append test60800 240 256 272
  test60800_block_15
  test60800_block_16)
  (interval_append test60800 272 288 320
  test60800_block_17
  (interval_append test60800 288 304 320
  test60800_block_18
  test60800_block_19)))))
  (interval_append test60800 320 480 640
  (interval_append test60800 320 400 480
  (interval_append test60800 320 352 400
  (interval_append test60800 320 336 352
  test60800_block_20
  test60800_block_21)
  (interval_append test60800 352 368 400
  test60800_block_22
  (interval_append test60800 368 384 400
  test60800_block_23
  test60800_block_24)))
  (interval_append test60800 400 432 480
  (interval_append test60800 400 416 432
  test60800_block_25
  test60800_block_26)
  (interval_append test60800 432 448 480
  test60800_block_27
  (interval_append test60800 448 464 480
  test60800_block_28
  test60800_block_29))))
  (interval_append test60800 480 560 640
  (interval_append test60800 480 512 560
  (interval_append test60800 480 496 512
  test60800_block_30
  test60800_block_31)
  (interval_append test60800 512 528 560
  test60800_block_32
  (interval_append test60800 528 544 560
  test60800_block_33
  test60800_block_34)))
  (interval_append test60800 560 592 640
  (interval_append test60800 560 576 592
  test60800_block_35
  test60800_block_36)
  (interval_append test60800 592 608 640
  test60800_block_37
  (interval_append test60800 608 624 640
  test60800_block_38
  test60800_block_39))))))
theorem nodeInterval60800 : Interval nodeTest 60800 61440 := by
  intro i hlo hhi
  have h := test60800_complete (i-60800) (Nat.zero_le _) (by omega)
  simpa only [test60800, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
