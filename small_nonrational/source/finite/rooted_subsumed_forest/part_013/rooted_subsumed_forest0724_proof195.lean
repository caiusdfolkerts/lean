module
prelude
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test124800 (i : Nat) := nodeTest (i+124800)
theorem test124800_block_0 : Interval test124800 0 16 :=
  interval_of_check test124800 0 16 (by decide +kernel)

theorem test124800_block_1 : Interval test124800 16 32 :=
  interval_of_check test124800 16 16 (by decide +kernel)

theorem test124800_block_2 : Interval test124800 32 48 :=
  interval_of_check test124800 32 16 (by decide +kernel)

theorem test124800_block_3 : Interval test124800 48 64 :=
  interval_of_check test124800 48 16 (by decide +kernel)

theorem test124800_block_4 : Interval test124800 64 80 :=
  interval_of_check test124800 64 16 (by decide +kernel)

theorem test124800_block_5 : Interval test124800 80 96 :=
  interval_of_check test124800 80 16 (by decide +kernel)

theorem test124800_block_6 : Interval test124800 96 112 :=
  interval_of_check test124800 96 16 (by decide +kernel)

theorem test124800_block_7 : Interval test124800 112 128 :=
  interval_of_check test124800 112 16 (by decide +kernel)

theorem test124800_block_8 : Interval test124800 128 144 :=
  interval_of_check test124800 128 16 (by decide +kernel)

theorem test124800_block_9 : Interval test124800 144 160 :=
  interval_of_check test124800 144 16 (by decide +kernel)

theorem test124800_block_10 : Interval test124800 160 176 :=
  interval_of_check test124800 160 16 (by decide +kernel)

theorem test124800_block_11 : Interval test124800 176 192 :=
  interval_of_check test124800 176 16 (by decide +kernel)

theorem test124800_block_12 : Interval test124800 192 208 :=
  interval_of_check test124800 192 16 (by decide +kernel)

theorem test124800_block_13 : Interval test124800 208 224 :=
  interval_of_check test124800 208 16 (by decide +kernel)

theorem test124800_block_14 : Interval test124800 224 240 :=
  interval_of_check test124800 224 16 (by decide +kernel)

theorem test124800_block_15 : Interval test124800 240 256 :=
  interval_of_check test124800 240 16 (by decide +kernel)

theorem test124800_block_16 : Interval test124800 256 272 :=
  interval_of_check test124800 256 16 (by decide +kernel)

theorem test124800_block_17 : Interval test124800 272 288 :=
  interval_of_check test124800 272 16 (by decide +kernel)

theorem test124800_block_18 : Interval test124800 288 304 :=
  interval_of_check test124800 288 16 (by decide +kernel)

theorem test124800_block_19 : Interval test124800 304 320 :=
  interval_of_check test124800 304 16 (by decide +kernel)

theorem test124800_block_20 : Interval test124800 320 336 :=
  interval_of_check test124800 320 16 (by decide +kernel)

theorem test124800_block_21 : Interval test124800 336 352 :=
  interval_of_check test124800 336 16 (by decide +kernel)

theorem test124800_block_22 : Interval test124800 352 368 :=
  interval_of_check test124800 352 16 (by decide +kernel)

theorem test124800_block_23 : Interval test124800 368 384 :=
  interval_of_check test124800 368 16 (by decide +kernel)

theorem test124800_block_24 : Interval test124800 384 400 :=
  interval_of_check test124800 384 16 (by decide +kernel)

theorem test124800_block_25 : Interval test124800 400 416 :=
  interval_of_check test124800 400 16 (by decide +kernel)

theorem test124800_block_26 : Interval test124800 416 432 :=
  interval_of_check test124800 416 16 (by decide +kernel)

theorem test124800_block_27 : Interval test124800 432 448 :=
  interval_of_check test124800 432 16 (by decide +kernel)

theorem test124800_block_28 : Interval test124800 448 464 :=
  interval_of_check test124800 448 16 (by decide +kernel)

theorem test124800_block_29 : Interval test124800 464 480 :=
  interval_of_check test124800 464 16 (by decide +kernel)

theorem test124800_block_30 : Interval test124800 480 496 :=
  interval_of_check test124800 480 16 (by decide +kernel)

theorem test124800_block_31 : Interval test124800 496 512 :=
  interval_of_check test124800 496 16 (by decide +kernel)

theorem test124800_block_32 : Interval test124800 512 528 :=
  interval_of_check test124800 512 16 (by decide +kernel)

theorem test124800_block_33 : Interval test124800 528 544 :=
  interval_of_check test124800 528 16 (by decide +kernel)

theorem test124800_block_34 : Interval test124800 544 560 :=
  interval_of_check test124800 544 16 (by decide +kernel)

theorem test124800_block_35 : Interval test124800 560 576 :=
  interval_of_check test124800 560 16 (by decide +kernel)

theorem test124800_block_36 : Interval test124800 576 592 :=
  interval_of_check test124800 576 16 (by decide +kernel)

theorem test124800_block_37 : Interval test124800 592 608 :=
  interval_of_check test124800 592 16 (by decide +kernel)

theorem test124800_block_38 : Interval test124800 608 624 :=
  interval_of_check test124800 608 16 (by decide +kernel)

theorem test124800_block_39 : Interval test124800 624 640 :=
  interval_of_check test124800 624 16 (by decide +kernel)

theorem test124800_complete : Interval test124800 0 640 :=
  (interval_append test124800 0 320 640
  (interval_append test124800 0 160 320
  (interval_append test124800 0 80 160
  (interval_append test124800 0 32 80
  (interval_append test124800 0 16 32
  test124800_block_0
  test124800_block_1)
  (interval_append test124800 32 48 80
  test124800_block_2
  (interval_append test124800 48 64 80
  test124800_block_3
  test124800_block_4)))
  (interval_append test124800 80 112 160
  (interval_append test124800 80 96 112
  test124800_block_5
  test124800_block_6)
  (interval_append test124800 112 128 160
  test124800_block_7
  (interval_append test124800 128 144 160
  test124800_block_8
  test124800_block_9))))
  (interval_append test124800 160 240 320
  (interval_append test124800 160 192 240
  (interval_append test124800 160 176 192
  test124800_block_10
  test124800_block_11)
  (interval_append test124800 192 208 240
  test124800_block_12
  (interval_append test124800 208 224 240
  test124800_block_13
  test124800_block_14)))
  (interval_append test124800 240 272 320
  (interval_append test124800 240 256 272
  test124800_block_15
  test124800_block_16)
  (interval_append test124800 272 288 320
  test124800_block_17
  (interval_append test124800 288 304 320
  test124800_block_18
  test124800_block_19)))))
  (interval_append test124800 320 480 640
  (interval_append test124800 320 400 480
  (interval_append test124800 320 352 400
  (interval_append test124800 320 336 352
  test124800_block_20
  test124800_block_21)
  (interval_append test124800 352 368 400
  test124800_block_22
  (interval_append test124800 368 384 400
  test124800_block_23
  test124800_block_24)))
  (interval_append test124800 400 432 480
  (interval_append test124800 400 416 432
  test124800_block_25
  test124800_block_26)
  (interval_append test124800 432 448 480
  test124800_block_27
  (interval_append test124800 448 464 480
  test124800_block_28
  test124800_block_29))))
  (interval_append test124800 480 560 640
  (interval_append test124800 480 512 560
  (interval_append test124800 480 496 512
  test124800_block_30
  test124800_block_31)
  (interval_append test124800 512 528 560
  test124800_block_32
  (interval_append test124800 528 544 560
  test124800_block_33
  test124800_block_34)))
  (interval_append test124800 560 592 640
  (interval_append test124800 560 576 592
  test124800_block_35
  test124800_block_36)
  (interval_append test124800 592 608 640
  test124800_block_37
  (interval_append test124800 608 624 640
  test124800_block_38
  test124800_block_39))))))
theorem nodeInterval124800 : Interval nodeTest 124800 125440 := by
  intro i hlo hhi
  have h := test124800_complete (i-124800) (Nat.zero_le _) (by omega)
  simpa only [test124800, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
