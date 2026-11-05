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
def test14080 (i : Nat) := nodeTest (i+14080)
theorem test14080_block_0 : Interval test14080 0 16 :=
  interval_of_check test14080 0 16 (by decide +kernel)

theorem test14080_block_1 : Interval test14080 16 32 :=
  interval_of_check test14080 16 16 (by decide +kernel)

theorem test14080_block_2 : Interval test14080 32 48 :=
  interval_of_check test14080 32 16 (by decide +kernel)

theorem test14080_block_3 : Interval test14080 48 64 :=
  interval_of_check test14080 48 16 (by decide +kernel)

theorem test14080_block_4 : Interval test14080 64 80 :=
  interval_of_check test14080 64 16 (by decide +kernel)

theorem test14080_block_5 : Interval test14080 80 96 :=
  interval_of_check test14080 80 16 (by decide +kernel)

theorem test14080_block_6 : Interval test14080 96 112 :=
  interval_of_check test14080 96 16 (by decide +kernel)

theorem test14080_block_7 : Interval test14080 112 128 :=
  interval_of_check test14080 112 16 (by decide +kernel)

theorem test14080_block_8 : Interval test14080 128 144 :=
  interval_of_check test14080 128 16 (by decide +kernel)

theorem test14080_block_9 : Interval test14080 144 160 :=
  interval_of_check test14080 144 16 (by decide +kernel)

theorem test14080_block_10 : Interval test14080 160 176 :=
  interval_of_check test14080 160 16 (by decide +kernel)

theorem test14080_block_11 : Interval test14080 176 192 :=
  interval_of_check test14080 176 16 (by decide +kernel)

theorem test14080_block_12 : Interval test14080 192 208 :=
  interval_of_check test14080 192 16 (by decide +kernel)

theorem test14080_block_13 : Interval test14080 208 224 :=
  interval_of_check test14080 208 16 (by decide +kernel)

theorem test14080_block_14 : Interval test14080 224 240 :=
  interval_of_check test14080 224 16 (by decide +kernel)

theorem test14080_block_15 : Interval test14080 240 256 :=
  interval_of_check test14080 240 16 (by decide +kernel)

theorem test14080_block_16 : Interval test14080 256 272 :=
  interval_of_check test14080 256 16 (by decide +kernel)

theorem test14080_block_17 : Interval test14080 272 288 :=
  interval_of_check test14080 272 16 (by decide +kernel)

theorem test14080_block_18 : Interval test14080 288 304 :=
  interval_of_check test14080 288 16 (by decide +kernel)

theorem test14080_block_19 : Interval test14080 304 320 :=
  interval_of_check test14080 304 16 (by decide +kernel)

theorem test14080_block_20 : Interval test14080 320 336 :=
  interval_of_check test14080 320 16 (by decide +kernel)

theorem test14080_block_21 : Interval test14080 336 352 :=
  interval_of_check test14080 336 16 (by decide +kernel)

theorem test14080_block_22 : Interval test14080 352 368 :=
  interval_of_check test14080 352 16 (by decide +kernel)

theorem test14080_block_23 : Interval test14080 368 384 :=
  interval_of_check test14080 368 16 (by decide +kernel)

theorem test14080_block_24 : Interval test14080 384 400 :=
  interval_of_check test14080 384 16 (by decide +kernel)

theorem test14080_block_25 : Interval test14080 400 416 :=
  interval_of_check test14080 400 16 (by decide +kernel)

theorem test14080_block_26 : Interval test14080 416 432 :=
  interval_of_check test14080 416 16 (by decide +kernel)

theorem test14080_block_27 : Interval test14080 432 448 :=
  interval_of_check test14080 432 16 (by decide +kernel)

theorem test14080_block_28 : Interval test14080 448 464 :=
  interval_of_check test14080 448 16 (by decide +kernel)

theorem test14080_block_29 : Interval test14080 464 480 :=
  interval_of_check test14080 464 16 (by decide +kernel)

theorem test14080_block_30 : Interval test14080 480 496 :=
  interval_of_check test14080 480 16 (by decide +kernel)

theorem test14080_block_31 : Interval test14080 496 512 :=
  interval_of_check test14080 496 16 (by decide +kernel)

theorem test14080_block_32 : Interval test14080 512 528 :=
  interval_of_check test14080 512 16 (by decide +kernel)

theorem test14080_block_33 : Interval test14080 528 544 :=
  interval_of_check test14080 528 16 (by decide +kernel)

theorem test14080_block_34 : Interval test14080 544 560 :=
  interval_of_check test14080 544 16 (by decide +kernel)

theorem test14080_block_35 : Interval test14080 560 576 :=
  interval_of_check test14080 560 16 (by decide +kernel)

theorem test14080_block_36 : Interval test14080 576 592 :=
  interval_of_check test14080 576 16 (by decide +kernel)

theorem test14080_block_37 : Interval test14080 592 608 :=
  interval_of_check test14080 592 16 (by decide +kernel)

theorem test14080_block_38 : Interval test14080 608 624 :=
  interval_of_check test14080 608 16 (by decide +kernel)

theorem test14080_block_39 : Interval test14080 624 640 :=
  interval_of_check test14080 624 16 (by decide +kernel)

theorem test14080_complete : Interval test14080 0 640 :=
  (interval_append test14080 0 320 640
  (interval_append test14080 0 160 320
  (interval_append test14080 0 80 160
  (interval_append test14080 0 32 80
  (interval_append test14080 0 16 32
  test14080_block_0
  test14080_block_1)
  (interval_append test14080 32 48 80
  test14080_block_2
  (interval_append test14080 48 64 80
  test14080_block_3
  test14080_block_4)))
  (interval_append test14080 80 112 160
  (interval_append test14080 80 96 112
  test14080_block_5
  test14080_block_6)
  (interval_append test14080 112 128 160
  test14080_block_7
  (interval_append test14080 128 144 160
  test14080_block_8
  test14080_block_9))))
  (interval_append test14080 160 240 320
  (interval_append test14080 160 192 240
  (interval_append test14080 160 176 192
  test14080_block_10
  test14080_block_11)
  (interval_append test14080 192 208 240
  test14080_block_12
  (interval_append test14080 208 224 240
  test14080_block_13
  test14080_block_14)))
  (interval_append test14080 240 272 320
  (interval_append test14080 240 256 272
  test14080_block_15
  test14080_block_16)
  (interval_append test14080 272 288 320
  test14080_block_17
  (interval_append test14080 288 304 320
  test14080_block_18
  test14080_block_19)))))
  (interval_append test14080 320 480 640
  (interval_append test14080 320 400 480
  (interval_append test14080 320 352 400
  (interval_append test14080 320 336 352
  test14080_block_20
  test14080_block_21)
  (interval_append test14080 352 368 400
  test14080_block_22
  (interval_append test14080 368 384 400
  test14080_block_23
  test14080_block_24)))
  (interval_append test14080 400 432 480
  (interval_append test14080 400 416 432
  test14080_block_25
  test14080_block_26)
  (interval_append test14080 432 448 480
  test14080_block_27
  (interval_append test14080 448 464 480
  test14080_block_28
  test14080_block_29))))
  (interval_append test14080 480 560 640
  (interval_append test14080 480 512 560
  (interval_append test14080 480 496 512
  test14080_block_30
  test14080_block_31)
  (interval_append test14080 512 528 560
  test14080_block_32
  (interval_append test14080 528 544 560
  test14080_block_33
  test14080_block_34)))
  (interval_append test14080 560 592 640
  (interval_append test14080 560 576 592
  test14080_block_35
  test14080_block_36)
  (interval_append test14080 592 608 640
  test14080_block_37
  (interval_append test14080 608 624 640
  test14080_block_38
  test14080_block_39))))))
theorem nodeInterval14080 : Interval nodeTest 14080 14720 := by
  intro i hlo hhi
  have h := test14080_complete (i-14080) (Nat.zero_le _) (by omega)
  simpa only [test14080, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
