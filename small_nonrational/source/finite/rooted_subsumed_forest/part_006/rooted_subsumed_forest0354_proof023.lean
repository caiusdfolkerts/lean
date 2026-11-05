module
prelude
public import RootedSubsumedForest0354Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test14720 (i : Nat) := nodeTest (i+14720)
theorem test14720_block_0 : Interval test14720 0 16 :=
  interval_of_check test14720 0 16 (by decide +kernel)

theorem test14720_block_1 : Interval test14720 16 32 :=
  interval_of_check test14720 16 16 (by decide +kernel)

theorem test14720_block_2 : Interval test14720 32 48 :=
  interval_of_check test14720 32 16 (by decide +kernel)

theorem test14720_block_3 : Interval test14720 48 64 :=
  interval_of_check test14720 48 16 (by decide +kernel)

theorem test14720_block_4 : Interval test14720 64 80 :=
  interval_of_check test14720 64 16 (by decide +kernel)

theorem test14720_block_5 : Interval test14720 80 96 :=
  interval_of_check test14720 80 16 (by decide +kernel)

theorem test14720_block_6 : Interval test14720 96 112 :=
  interval_of_check test14720 96 16 (by decide +kernel)

theorem test14720_block_7 : Interval test14720 112 128 :=
  interval_of_check test14720 112 16 (by decide +kernel)

theorem test14720_block_8 : Interval test14720 128 144 :=
  interval_of_check test14720 128 16 (by decide +kernel)

theorem test14720_block_9 : Interval test14720 144 160 :=
  interval_of_check test14720 144 16 (by decide +kernel)

theorem test14720_block_10 : Interval test14720 160 176 :=
  interval_of_check test14720 160 16 (by decide +kernel)

theorem test14720_block_11 : Interval test14720 176 192 :=
  interval_of_check test14720 176 16 (by decide +kernel)

theorem test14720_block_12 : Interval test14720 192 208 :=
  interval_of_check test14720 192 16 (by decide +kernel)

theorem test14720_block_13 : Interval test14720 208 224 :=
  interval_of_check test14720 208 16 (by decide +kernel)

theorem test14720_block_14 : Interval test14720 224 240 :=
  interval_of_check test14720 224 16 (by decide +kernel)

theorem test14720_block_15 : Interval test14720 240 256 :=
  interval_of_check test14720 240 16 (by decide +kernel)

theorem test14720_block_16 : Interval test14720 256 272 :=
  interval_of_check test14720 256 16 (by decide +kernel)

theorem test14720_block_17 : Interval test14720 272 288 :=
  interval_of_check test14720 272 16 (by decide +kernel)

theorem test14720_block_18 : Interval test14720 288 304 :=
  interval_of_check test14720 288 16 (by decide +kernel)

theorem test14720_block_19 : Interval test14720 304 320 :=
  interval_of_check test14720 304 16 (by decide +kernel)

theorem test14720_block_20 : Interval test14720 320 336 :=
  interval_of_check test14720 320 16 (by decide +kernel)

theorem test14720_block_21 : Interval test14720 336 352 :=
  interval_of_check test14720 336 16 (by decide +kernel)

theorem test14720_block_22 : Interval test14720 352 368 :=
  interval_of_check test14720 352 16 (by decide +kernel)

theorem test14720_block_23 : Interval test14720 368 384 :=
  interval_of_check test14720 368 16 (by decide +kernel)

theorem test14720_block_24 : Interval test14720 384 400 :=
  interval_of_check test14720 384 16 (by decide +kernel)

theorem test14720_block_25 : Interval test14720 400 416 :=
  interval_of_check test14720 400 16 (by decide +kernel)

theorem test14720_block_26 : Interval test14720 416 432 :=
  interval_of_check test14720 416 16 (by decide +kernel)

theorem test14720_block_27 : Interval test14720 432 448 :=
  interval_of_check test14720 432 16 (by decide +kernel)

theorem test14720_block_28 : Interval test14720 448 464 :=
  interval_of_check test14720 448 16 (by decide +kernel)

theorem test14720_block_29 : Interval test14720 464 480 :=
  interval_of_check test14720 464 16 (by decide +kernel)

theorem test14720_block_30 : Interval test14720 480 496 :=
  interval_of_check test14720 480 16 (by decide +kernel)

theorem test14720_block_31 : Interval test14720 496 512 :=
  interval_of_check test14720 496 16 (by decide +kernel)

theorem test14720_block_32 : Interval test14720 512 528 :=
  interval_of_check test14720 512 16 (by decide +kernel)

theorem test14720_block_33 : Interval test14720 528 544 :=
  interval_of_check test14720 528 16 (by decide +kernel)

theorem test14720_block_34 : Interval test14720 544 560 :=
  interval_of_check test14720 544 16 (by decide +kernel)

theorem test14720_block_35 : Interval test14720 560 576 :=
  interval_of_check test14720 560 16 (by decide +kernel)

theorem test14720_block_36 : Interval test14720 576 592 :=
  interval_of_check test14720 576 16 (by decide +kernel)

theorem test14720_block_37 : Interval test14720 592 608 :=
  interval_of_check test14720 592 16 (by decide +kernel)

theorem test14720_block_38 : Interval test14720 608 624 :=
  interval_of_check test14720 608 16 (by decide +kernel)

theorem test14720_block_39 : Interval test14720 624 640 :=
  interval_of_check test14720 624 16 (by decide +kernel)

theorem test14720_complete : Interval test14720 0 640 :=
  (interval_append test14720 0 320 640
  (interval_append test14720 0 160 320
  (interval_append test14720 0 80 160
  (interval_append test14720 0 32 80
  (interval_append test14720 0 16 32
  test14720_block_0
  test14720_block_1)
  (interval_append test14720 32 48 80
  test14720_block_2
  (interval_append test14720 48 64 80
  test14720_block_3
  test14720_block_4)))
  (interval_append test14720 80 112 160
  (interval_append test14720 80 96 112
  test14720_block_5
  test14720_block_6)
  (interval_append test14720 112 128 160
  test14720_block_7
  (interval_append test14720 128 144 160
  test14720_block_8
  test14720_block_9))))
  (interval_append test14720 160 240 320
  (interval_append test14720 160 192 240
  (interval_append test14720 160 176 192
  test14720_block_10
  test14720_block_11)
  (interval_append test14720 192 208 240
  test14720_block_12
  (interval_append test14720 208 224 240
  test14720_block_13
  test14720_block_14)))
  (interval_append test14720 240 272 320
  (interval_append test14720 240 256 272
  test14720_block_15
  test14720_block_16)
  (interval_append test14720 272 288 320
  test14720_block_17
  (interval_append test14720 288 304 320
  test14720_block_18
  test14720_block_19)))))
  (interval_append test14720 320 480 640
  (interval_append test14720 320 400 480
  (interval_append test14720 320 352 400
  (interval_append test14720 320 336 352
  test14720_block_20
  test14720_block_21)
  (interval_append test14720 352 368 400
  test14720_block_22
  (interval_append test14720 368 384 400
  test14720_block_23
  test14720_block_24)))
  (interval_append test14720 400 432 480
  (interval_append test14720 400 416 432
  test14720_block_25
  test14720_block_26)
  (interval_append test14720 432 448 480
  test14720_block_27
  (interval_append test14720 448 464 480
  test14720_block_28
  test14720_block_29))))
  (interval_append test14720 480 560 640
  (interval_append test14720 480 512 560
  (interval_append test14720 480 496 512
  test14720_block_30
  test14720_block_31)
  (interval_append test14720 512 528 560
  test14720_block_32
  (interval_append test14720 528 544 560
  test14720_block_33
  test14720_block_34)))
  (interval_append test14720 560 592 640
  (interval_append test14720 560 576 592
  test14720_block_35
  test14720_block_36)
  (interval_append test14720 592 608 640
  test14720_block_37
  (interval_append test14720 608 624 640
  test14720_block_38
  test14720_block_39))))))
theorem nodeInterval14720 : Interval nodeTest 14720 15360 := by
  intro i hlo hhi
  have h := test14720_complete (i-14720) (Nat.zero_le _) (by omega)
  simpa only [test14720, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
