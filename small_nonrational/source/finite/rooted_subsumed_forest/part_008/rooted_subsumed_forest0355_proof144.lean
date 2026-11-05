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
def test92160 (i : Nat) := nodeTest (i+92160)
theorem test92160_block_0 : Interval test92160 0 16 :=
  interval_of_check test92160 0 16 (by decide +kernel)

theorem test92160_block_1 : Interval test92160 16 32 :=
  interval_of_check test92160 16 16 (by decide +kernel)

theorem test92160_block_2 : Interval test92160 32 48 :=
  interval_of_check test92160 32 16 (by decide +kernel)

theorem test92160_block_3 : Interval test92160 48 64 :=
  interval_of_check test92160 48 16 (by decide +kernel)

theorem test92160_block_4 : Interval test92160 64 80 :=
  interval_of_check test92160 64 16 (by decide +kernel)

theorem test92160_block_5 : Interval test92160 80 96 :=
  interval_of_check test92160 80 16 (by decide +kernel)

theorem test92160_block_6 : Interval test92160 96 112 :=
  interval_of_check test92160 96 16 (by decide +kernel)

theorem test92160_block_7 : Interval test92160 112 128 :=
  interval_of_check test92160 112 16 (by decide +kernel)

theorem test92160_block_8 : Interval test92160 128 144 :=
  interval_of_check test92160 128 16 (by decide +kernel)

theorem test92160_block_9 : Interval test92160 144 160 :=
  interval_of_check test92160 144 16 (by decide +kernel)

theorem test92160_block_10 : Interval test92160 160 176 :=
  interval_of_check test92160 160 16 (by decide +kernel)

theorem test92160_block_11 : Interval test92160 176 192 :=
  interval_of_check test92160 176 16 (by decide +kernel)

theorem test92160_block_12 : Interval test92160 192 208 :=
  interval_of_check test92160 192 16 (by decide +kernel)

theorem test92160_block_13 : Interval test92160 208 224 :=
  interval_of_check test92160 208 16 (by decide +kernel)

theorem test92160_block_14 : Interval test92160 224 240 :=
  interval_of_check test92160 224 16 (by decide +kernel)

theorem test92160_block_15 : Interval test92160 240 256 :=
  interval_of_check test92160 240 16 (by decide +kernel)

theorem test92160_block_16 : Interval test92160 256 272 :=
  interval_of_check test92160 256 16 (by decide +kernel)

theorem test92160_block_17 : Interval test92160 272 288 :=
  interval_of_check test92160 272 16 (by decide +kernel)

theorem test92160_block_18 : Interval test92160 288 304 :=
  interval_of_check test92160 288 16 (by decide +kernel)

theorem test92160_block_19 : Interval test92160 304 320 :=
  interval_of_check test92160 304 16 (by decide +kernel)

theorem test92160_block_20 : Interval test92160 320 336 :=
  interval_of_check test92160 320 16 (by decide +kernel)

theorem test92160_block_21 : Interval test92160 336 352 :=
  interval_of_check test92160 336 16 (by decide +kernel)

theorem test92160_block_22 : Interval test92160 352 368 :=
  interval_of_check test92160 352 16 (by decide +kernel)

theorem test92160_block_23 : Interval test92160 368 384 :=
  interval_of_check test92160 368 16 (by decide +kernel)

theorem test92160_block_24 : Interval test92160 384 400 :=
  interval_of_check test92160 384 16 (by decide +kernel)

theorem test92160_block_25 : Interval test92160 400 416 :=
  interval_of_check test92160 400 16 (by decide +kernel)

theorem test92160_block_26 : Interval test92160 416 432 :=
  interval_of_check test92160 416 16 (by decide +kernel)

theorem test92160_block_27 : Interval test92160 432 448 :=
  interval_of_check test92160 432 16 (by decide +kernel)

theorem test92160_block_28 : Interval test92160 448 464 :=
  interval_of_check test92160 448 16 (by decide +kernel)

theorem test92160_block_29 : Interval test92160 464 480 :=
  interval_of_check test92160 464 16 (by decide +kernel)

theorem test92160_block_30 : Interval test92160 480 496 :=
  interval_of_check test92160 480 16 (by decide +kernel)

theorem test92160_block_31 : Interval test92160 496 512 :=
  interval_of_check test92160 496 16 (by decide +kernel)

theorem test92160_block_32 : Interval test92160 512 528 :=
  interval_of_check test92160 512 16 (by decide +kernel)

theorem test92160_block_33 : Interval test92160 528 544 :=
  interval_of_check test92160 528 16 (by decide +kernel)

theorem test92160_block_34 : Interval test92160 544 560 :=
  interval_of_check test92160 544 16 (by decide +kernel)

theorem test92160_block_35 : Interval test92160 560 576 :=
  interval_of_check test92160 560 16 (by decide +kernel)

theorem test92160_block_36 : Interval test92160 576 592 :=
  interval_of_check test92160 576 16 (by decide +kernel)

theorem test92160_block_37 : Interval test92160 592 608 :=
  interval_of_check test92160 592 16 (by decide +kernel)

theorem test92160_block_38 : Interval test92160 608 624 :=
  interval_of_check test92160 608 16 (by decide +kernel)

theorem test92160_block_39 : Interval test92160 624 640 :=
  interval_of_check test92160 624 16 (by decide +kernel)

theorem test92160_complete : Interval test92160 0 640 :=
  (interval_append test92160 0 320 640
  (interval_append test92160 0 160 320
  (interval_append test92160 0 80 160
  (interval_append test92160 0 32 80
  (interval_append test92160 0 16 32
  test92160_block_0
  test92160_block_1)
  (interval_append test92160 32 48 80
  test92160_block_2
  (interval_append test92160 48 64 80
  test92160_block_3
  test92160_block_4)))
  (interval_append test92160 80 112 160
  (interval_append test92160 80 96 112
  test92160_block_5
  test92160_block_6)
  (interval_append test92160 112 128 160
  test92160_block_7
  (interval_append test92160 128 144 160
  test92160_block_8
  test92160_block_9))))
  (interval_append test92160 160 240 320
  (interval_append test92160 160 192 240
  (interval_append test92160 160 176 192
  test92160_block_10
  test92160_block_11)
  (interval_append test92160 192 208 240
  test92160_block_12
  (interval_append test92160 208 224 240
  test92160_block_13
  test92160_block_14)))
  (interval_append test92160 240 272 320
  (interval_append test92160 240 256 272
  test92160_block_15
  test92160_block_16)
  (interval_append test92160 272 288 320
  test92160_block_17
  (interval_append test92160 288 304 320
  test92160_block_18
  test92160_block_19)))))
  (interval_append test92160 320 480 640
  (interval_append test92160 320 400 480
  (interval_append test92160 320 352 400
  (interval_append test92160 320 336 352
  test92160_block_20
  test92160_block_21)
  (interval_append test92160 352 368 400
  test92160_block_22
  (interval_append test92160 368 384 400
  test92160_block_23
  test92160_block_24)))
  (interval_append test92160 400 432 480
  (interval_append test92160 400 416 432
  test92160_block_25
  test92160_block_26)
  (interval_append test92160 432 448 480
  test92160_block_27
  (interval_append test92160 448 464 480
  test92160_block_28
  test92160_block_29))))
  (interval_append test92160 480 560 640
  (interval_append test92160 480 512 560
  (interval_append test92160 480 496 512
  test92160_block_30
  test92160_block_31)
  (interval_append test92160 512 528 560
  test92160_block_32
  (interval_append test92160 528 544 560
  test92160_block_33
  test92160_block_34)))
  (interval_append test92160 560 592 640
  (interval_append test92160 560 576 592
  test92160_block_35
  test92160_block_36)
  (interval_append test92160 592 608 640
  test92160_block_37
  (interval_append test92160 608 624 640
  test92160_block_38
  test92160_block_39))))))
theorem nodeInterval92160 : Interval nodeTest 92160 92800 := by
  intro i hlo hhi
  have h := test92160_complete (i-92160) (Nat.zero_le _) (by omega)
  simpa only [test92160, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
