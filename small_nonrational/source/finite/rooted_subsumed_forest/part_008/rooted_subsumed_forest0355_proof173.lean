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
def test110720 (i : Nat) := nodeTest (i+110720)
theorem test110720_block_0 : Interval test110720 0 16 :=
  interval_of_check test110720 0 16 (by decide +kernel)

theorem test110720_block_1 : Interval test110720 16 32 :=
  interval_of_check test110720 16 16 (by decide +kernel)

theorem test110720_block_2 : Interval test110720 32 48 :=
  interval_of_check test110720 32 16 (by decide +kernel)

theorem test110720_block_3 : Interval test110720 48 64 :=
  interval_of_check test110720 48 16 (by decide +kernel)

theorem test110720_block_4 : Interval test110720 64 80 :=
  interval_of_check test110720 64 16 (by decide +kernel)

theorem test110720_block_5 : Interval test110720 80 96 :=
  interval_of_check test110720 80 16 (by decide +kernel)

theorem test110720_block_6 : Interval test110720 96 112 :=
  interval_of_check test110720 96 16 (by decide +kernel)

theorem test110720_block_7 : Interval test110720 112 128 :=
  interval_of_check test110720 112 16 (by decide +kernel)

theorem test110720_block_8 : Interval test110720 128 144 :=
  interval_of_check test110720 128 16 (by decide +kernel)

theorem test110720_block_9 : Interval test110720 144 160 :=
  interval_of_check test110720 144 16 (by decide +kernel)

theorem test110720_block_10 : Interval test110720 160 176 :=
  interval_of_check test110720 160 16 (by decide +kernel)

theorem test110720_block_11 : Interval test110720 176 192 :=
  interval_of_check test110720 176 16 (by decide +kernel)

theorem test110720_block_12 : Interval test110720 192 208 :=
  interval_of_check test110720 192 16 (by decide +kernel)

theorem test110720_block_13 : Interval test110720 208 224 :=
  interval_of_check test110720 208 16 (by decide +kernel)

theorem test110720_block_14 : Interval test110720 224 240 :=
  interval_of_check test110720 224 16 (by decide +kernel)

theorem test110720_block_15 : Interval test110720 240 256 :=
  interval_of_check test110720 240 16 (by decide +kernel)

theorem test110720_block_16 : Interval test110720 256 272 :=
  interval_of_check test110720 256 16 (by decide +kernel)

theorem test110720_block_17 : Interval test110720 272 288 :=
  interval_of_check test110720 272 16 (by decide +kernel)

theorem test110720_block_18 : Interval test110720 288 304 :=
  interval_of_check test110720 288 16 (by decide +kernel)

theorem test110720_block_19 : Interval test110720 304 320 :=
  interval_of_check test110720 304 16 (by decide +kernel)

theorem test110720_block_20 : Interval test110720 320 336 :=
  interval_of_check test110720 320 16 (by decide +kernel)

theorem test110720_block_21 : Interval test110720 336 352 :=
  interval_of_check test110720 336 16 (by decide +kernel)

theorem test110720_block_22 : Interval test110720 352 368 :=
  interval_of_check test110720 352 16 (by decide +kernel)

theorem test110720_block_23 : Interval test110720 368 384 :=
  interval_of_check test110720 368 16 (by decide +kernel)

theorem test110720_block_24 : Interval test110720 384 400 :=
  interval_of_check test110720 384 16 (by decide +kernel)

theorem test110720_block_25 : Interval test110720 400 416 :=
  interval_of_check test110720 400 16 (by decide +kernel)

theorem test110720_block_26 : Interval test110720 416 432 :=
  interval_of_check test110720 416 16 (by decide +kernel)

theorem test110720_block_27 : Interval test110720 432 448 :=
  interval_of_check test110720 432 16 (by decide +kernel)

theorem test110720_block_28 : Interval test110720 448 464 :=
  interval_of_check test110720 448 16 (by decide +kernel)

theorem test110720_block_29 : Interval test110720 464 480 :=
  interval_of_check test110720 464 16 (by decide +kernel)

theorem test110720_block_30 : Interval test110720 480 496 :=
  interval_of_check test110720 480 16 (by decide +kernel)

theorem test110720_block_31 : Interval test110720 496 512 :=
  interval_of_check test110720 496 16 (by decide +kernel)

theorem test110720_block_32 : Interval test110720 512 528 :=
  interval_of_check test110720 512 16 (by decide +kernel)

theorem test110720_block_33 : Interval test110720 528 544 :=
  interval_of_check test110720 528 16 (by decide +kernel)

theorem test110720_block_34 : Interval test110720 544 560 :=
  interval_of_check test110720 544 16 (by decide +kernel)

theorem test110720_block_35 : Interval test110720 560 576 :=
  interval_of_check test110720 560 16 (by decide +kernel)

theorem test110720_block_36 : Interval test110720 576 592 :=
  interval_of_check test110720 576 16 (by decide +kernel)

theorem test110720_block_37 : Interval test110720 592 608 :=
  interval_of_check test110720 592 16 (by decide +kernel)

theorem test110720_block_38 : Interval test110720 608 624 :=
  interval_of_check test110720 608 16 (by decide +kernel)

theorem test110720_block_39 : Interval test110720 624 640 :=
  interval_of_check test110720 624 16 (by decide +kernel)

theorem test110720_complete : Interval test110720 0 640 :=
  (interval_append test110720 0 320 640
  (interval_append test110720 0 160 320
  (interval_append test110720 0 80 160
  (interval_append test110720 0 32 80
  (interval_append test110720 0 16 32
  test110720_block_0
  test110720_block_1)
  (interval_append test110720 32 48 80
  test110720_block_2
  (interval_append test110720 48 64 80
  test110720_block_3
  test110720_block_4)))
  (interval_append test110720 80 112 160
  (interval_append test110720 80 96 112
  test110720_block_5
  test110720_block_6)
  (interval_append test110720 112 128 160
  test110720_block_7
  (interval_append test110720 128 144 160
  test110720_block_8
  test110720_block_9))))
  (interval_append test110720 160 240 320
  (interval_append test110720 160 192 240
  (interval_append test110720 160 176 192
  test110720_block_10
  test110720_block_11)
  (interval_append test110720 192 208 240
  test110720_block_12
  (interval_append test110720 208 224 240
  test110720_block_13
  test110720_block_14)))
  (interval_append test110720 240 272 320
  (interval_append test110720 240 256 272
  test110720_block_15
  test110720_block_16)
  (interval_append test110720 272 288 320
  test110720_block_17
  (interval_append test110720 288 304 320
  test110720_block_18
  test110720_block_19)))))
  (interval_append test110720 320 480 640
  (interval_append test110720 320 400 480
  (interval_append test110720 320 352 400
  (interval_append test110720 320 336 352
  test110720_block_20
  test110720_block_21)
  (interval_append test110720 352 368 400
  test110720_block_22
  (interval_append test110720 368 384 400
  test110720_block_23
  test110720_block_24)))
  (interval_append test110720 400 432 480
  (interval_append test110720 400 416 432
  test110720_block_25
  test110720_block_26)
  (interval_append test110720 432 448 480
  test110720_block_27
  (interval_append test110720 448 464 480
  test110720_block_28
  test110720_block_29))))
  (interval_append test110720 480 560 640
  (interval_append test110720 480 512 560
  (interval_append test110720 480 496 512
  test110720_block_30
  test110720_block_31)
  (interval_append test110720 512 528 560
  test110720_block_32
  (interval_append test110720 528 544 560
  test110720_block_33
  test110720_block_34)))
  (interval_append test110720 560 592 640
  (interval_append test110720 560 576 592
  test110720_block_35
  test110720_block_36)
  (interval_append test110720 592 608 640
  test110720_block_37
  (interval_append test110720 608 624 640
  test110720_block_38
  test110720_block_39))))))
theorem nodeInterval110720 : Interval nodeTest 110720 111360 := by
  intro i hlo hhi
  have h := test110720_complete (i-110720) (Nat.zero_le _) (by omega)
  simpa only [test110720, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
