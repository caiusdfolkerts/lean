module
prelude
public import RootedSubsumedForest0320Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test26880 (i : Nat) := nodeTest (i+26880)
theorem test26880_block_0 : Interval test26880 0 16 :=
  interval_of_check test26880 0 16 (by decide +kernel)

theorem test26880_block_1 : Interval test26880 16 32 :=
  interval_of_check test26880 16 16 (by decide +kernel)

theorem test26880_block_2 : Interval test26880 32 48 :=
  interval_of_check test26880 32 16 (by decide +kernel)

theorem test26880_block_3 : Interval test26880 48 64 :=
  interval_of_check test26880 48 16 (by decide +kernel)

theorem test26880_block_4 : Interval test26880 64 80 :=
  interval_of_check test26880 64 16 (by decide +kernel)

theorem test26880_block_5 : Interval test26880 80 96 :=
  interval_of_check test26880 80 16 (by decide +kernel)

theorem test26880_block_6 : Interval test26880 96 112 :=
  interval_of_check test26880 96 16 (by decide +kernel)

theorem test26880_block_7 : Interval test26880 112 128 :=
  interval_of_check test26880 112 16 (by decide +kernel)

theorem test26880_block_8 : Interval test26880 128 144 :=
  interval_of_check test26880 128 16 (by decide +kernel)

theorem test26880_block_9 : Interval test26880 144 160 :=
  interval_of_check test26880 144 16 (by decide +kernel)

theorem test26880_block_10 : Interval test26880 160 176 :=
  interval_of_check test26880 160 16 (by decide +kernel)

theorem test26880_block_11 : Interval test26880 176 192 :=
  interval_of_check test26880 176 16 (by decide +kernel)

theorem test26880_block_12 : Interval test26880 192 208 :=
  interval_of_check test26880 192 16 (by decide +kernel)

theorem test26880_block_13 : Interval test26880 208 224 :=
  interval_of_check test26880 208 16 (by decide +kernel)

theorem test26880_block_14 : Interval test26880 224 240 :=
  interval_of_check test26880 224 16 (by decide +kernel)

theorem test26880_block_15 : Interval test26880 240 256 :=
  interval_of_check test26880 240 16 (by decide +kernel)

theorem test26880_block_16 : Interval test26880 256 272 :=
  interval_of_check test26880 256 16 (by decide +kernel)

theorem test26880_block_17 : Interval test26880 272 288 :=
  interval_of_check test26880 272 16 (by decide +kernel)

theorem test26880_block_18 : Interval test26880 288 304 :=
  interval_of_check test26880 288 16 (by decide +kernel)

theorem test26880_block_19 : Interval test26880 304 320 :=
  interval_of_check test26880 304 16 (by decide +kernel)

theorem test26880_block_20 : Interval test26880 320 336 :=
  interval_of_check test26880 320 16 (by decide +kernel)

theorem test26880_block_21 : Interval test26880 336 352 :=
  interval_of_check test26880 336 16 (by decide +kernel)

theorem test26880_block_22 : Interval test26880 352 368 :=
  interval_of_check test26880 352 16 (by decide +kernel)

theorem test26880_block_23 : Interval test26880 368 384 :=
  interval_of_check test26880 368 16 (by decide +kernel)

theorem test26880_block_24 : Interval test26880 384 400 :=
  interval_of_check test26880 384 16 (by decide +kernel)

theorem test26880_block_25 : Interval test26880 400 416 :=
  interval_of_check test26880 400 16 (by decide +kernel)

theorem test26880_block_26 : Interval test26880 416 432 :=
  interval_of_check test26880 416 16 (by decide +kernel)

theorem test26880_block_27 : Interval test26880 432 448 :=
  interval_of_check test26880 432 16 (by decide +kernel)

theorem test26880_block_28 : Interval test26880 448 464 :=
  interval_of_check test26880 448 16 (by decide +kernel)

theorem test26880_block_29 : Interval test26880 464 480 :=
  interval_of_check test26880 464 16 (by decide +kernel)

theorem test26880_block_30 : Interval test26880 480 496 :=
  interval_of_check test26880 480 16 (by decide +kernel)

theorem test26880_block_31 : Interval test26880 496 512 :=
  interval_of_check test26880 496 16 (by decide +kernel)

theorem test26880_block_32 : Interval test26880 512 528 :=
  interval_of_check test26880 512 16 (by decide +kernel)

theorem test26880_block_33 : Interval test26880 528 544 :=
  interval_of_check test26880 528 16 (by decide +kernel)

theorem test26880_block_34 : Interval test26880 544 560 :=
  interval_of_check test26880 544 16 (by decide +kernel)

theorem test26880_block_35 : Interval test26880 560 576 :=
  interval_of_check test26880 560 16 (by decide +kernel)

theorem test26880_block_36 : Interval test26880 576 592 :=
  interval_of_check test26880 576 16 (by decide +kernel)

theorem test26880_block_37 : Interval test26880 592 608 :=
  interval_of_check test26880 592 16 (by decide +kernel)

theorem test26880_block_38 : Interval test26880 608 624 :=
  interval_of_check test26880 608 16 (by decide +kernel)

theorem test26880_block_39 : Interval test26880 624 640 :=
  interval_of_check test26880 624 16 (by decide +kernel)

theorem test26880_complete : Interval test26880 0 640 :=
  (interval_append test26880 0 320 640
  (interval_append test26880 0 160 320
  (interval_append test26880 0 80 160
  (interval_append test26880 0 32 80
  (interval_append test26880 0 16 32
  test26880_block_0
  test26880_block_1)
  (interval_append test26880 32 48 80
  test26880_block_2
  (interval_append test26880 48 64 80
  test26880_block_3
  test26880_block_4)))
  (interval_append test26880 80 112 160
  (interval_append test26880 80 96 112
  test26880_block_5
  test26880_block_6)
  (interval_append test26880 112 128 160
  test26880_block_7
  (interval_append test26880 128 144 160
  test26880_block_8
  test26880_block_9))))
  (interval_append test26880 160 240 320
  (interval_append test26880 160 192 240
  (interval_append test26880 160 176 192
  test26880_block_10
  test26880_block_11)
  (interval_append test26880 192 208 240
  test26880_block_12
  (interval_append test26880 208 224 240
  test26880_block_13
  test26880_block_14)))
  (interval_append test26880 240 272 320
  (interval_append test26880 240 256 272
  test26880_block_15
  test26880_block_16)
  (interval_append test26880 272 288 320
  test26880_block_17
  (interval_append test26880 288 304 320
  test26880_block_18
  test26880_block_19)))))
  (interval_append test26880 320 480 640
  (interval_append test26880 320 400 480
  (interval_append test26880 320 352 400
  (interval_append test26880 320 336 352
  test26880_block_20
  test26880_block_21)
  (interval_append test26880 352 368 400
  test26880_block_22
  (interval_append test26880 368 384 400
  test26880_block_23
  test26880_block_24)))
  (interval_append test26880 400 432 480
  (interval_append test26880 400 416 432
  test26880_block_25
  test26880_block_26)
  (interval_append test26880 432 448 480
  test26880_block_27
  (interval_append test26880 448 464 480
  test26880_block_28
  test26880_block_29))))
  (interval_append test26880 480 560 640
  (interval_append test26880 480 512 560
  (interval_append test26880 480 496 512
  test26880_block_30
  test26880_block_31)
  (interval_append test26880 512 528 560
  test26880_block_32
  (interval_append test26880 528 544 560
  test26880_block_33
  test26880_block_34)))
  (interval_append test26880 560 592 640
  (interval_append test26880 560 576 592
  test26880_block_35
  test26880_block_36)
  (interval_append test26880 592 608 640
  test26880_block_37
  (interval_append test26880 608 624 640
  test26880_block_38
  test26880_block_39))))))
theorem nodeInterval26880 : Interval nodeTest 26880 27520 := by
  intro i hlo hhi
  have h := test26880_complete (i-26880) (Nat.zero_le _) (by omega)
  simpa only [test26880, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
