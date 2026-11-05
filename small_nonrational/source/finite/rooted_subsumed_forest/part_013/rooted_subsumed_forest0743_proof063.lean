module
prelude
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test40320 (i : Nat) := nodeTest (i+40320)
theorem test40320_block_0 : Interval test40320 0 16 :=
  interval_of_check test40320 0 16 (by decide +kernel)

theorem test40320_block_1 : Interval test40320 16 32 :=
  interval_of_check test40320 16 16 (by decide +kernel)

theorem test40320_block_2 : Interval test40320 32 48 :=
  interval_of_check test40320 32 16 (by decide +kernel)

theorem test40320_block_3 : Interval test40320 48 64 :=
  interval_of_check test40320 48 16 (by decide +kernel)

theorem test40320_block_4 : Interval test40320 64 80 :=
  interval_of_check test40320 64 16 (by decide +kernel)

theorem test40320_block_5 : Interval test40320 80 96 :=
  interval_of_check test40320 80 16 (by decide +kernel)

theorem test40320_block_6 : Interval test40320 96 112 :=
  interval_of_check test40320 96 16 (by decide +kernel)

theorem test40320_block_7 : Interval test40320 112 128 :=
  interval_of_check test40320 112 16 (by decide +kernel)

theorem test40320_block_8 : Interval test40320 128 144 :=
  interval_of_check test40320 128 16 (by decide +kernel)

theorem test40320_block_9 : Interval test40320 144 160 :=
  interval_of_check test40320 144 16 (by decide +kernel)

theorem test40320_block_10 : Interval test40320 160 176 :=
  interval_of_check test40320 160 16 (by decide +kernel)

theorem test40320_block_11 : Interval test40320 176 192 :=
  interval_of_check test40320 176 16 (by decide +kernel)

theorem test40320_block_12 : Interval test40320 192 208 :=
  interval_of_check test40320 192 16 (by decide +kernel)

theorem test40320_block_13 : Interval test40320 208 224 :=
  interval_of_check test40320 208 16 (by decide +kernel)

theorem test40320_block_14 : Interval test40320 224 240 :=
  interval_of_check test40320 224 16 (by decide +kernel)

theorem test40320_block_15 : Interval test40320 240 256 :=
  interval_of_check test40320 240 16 (by decide +kernel)

theorem test40320_block_16 : Interval test40320 256 272 :=
  interval_of_check test40320 256 16 (by decide +kernel)

theorem test40320_block_17 : Interval test40320 272 288 :=
  interval_of_check test40320 272 16 (by decide +kernel)

theorem test40320_block_18 : Interval test40320 288 304 :=
  interval_of_check test40320 288 16 (by decide +kernel)

theorem test40320_block_19 : Interval test40320 304 320 :=
  interval_of_check test40320 304 16 (by decide +kernel)

theorem test40320_block_20 : Interval test40320 320 336 :=
  interval_of_check test40320 320 16 (by decide +kernel)

theorem test40320_block_21 : Interval test40320 336 352 :=
  interval_of_check test40320 336 16 (by decide +kernel)

theorem test40320_block_22 : Interval test40320 352 368 :=
  interval_of_check test40320 352 16 (by decide +kernel)

theorem test40320_block_23 : Interval test40320 368 384 :=
  interval_of_check test40320 368 16 (by decide +kernel)

theorem test40320_block_24 : Interval test40320 384 400 :=
  interval_of_check test40320 384 16 (by decide +kernel)

theorem test40320_block_25 : Interval test40320 400 416 :=
  interval_of_check test40320 400 16 (by decide +kernel)

theorem test40320_block_26 : Interval test40320 416 432 :=
  interval_of_check test40320 416 16 (by decide +kernel)

theorem test40320_block_27 : Interval test40320 432 448 :=
  interval_of_check test40320 432 16 (by decide +kernel)

theorem test40320_block_28 : Interval test40320 448 464 :=
  interval_of_check test40320 448 16 (by decide +kernel)

theorem test40320_block_29 : Interval test40320 464 480 :=
  interval_of_check test40320 464 16 (by decide +kernel)

theorem test40320_block_30 : Interval test40320 480 496 :=
  interval_of_check test40320 480 16 (by decide +kernel)

theorem test40320_block_31 : Interval test40320 496 512 :=
  interval_of_check test40320 496 16 (by decide +kernel)

theorem test40320_block_32 : Interval test40320 512 528 :=
  interval_of_check test40320 512 16 (by decide +kernel)

theorem test40320_block_33 : Interval test40320 528 544 :=
  interval_of_check test40320 528 16 (by decide +kernel)

theorem test40320_block_34 : Interval test40320 544 560 :=
  interval_of_check test40320 544 16 (by decide +kernel)

theorem test40320_block_35 : Interval test40320 560 576 :=
  interval_of_check test40320 560 16 (by decide +kernel)

theorem test40320_block_36 : Interval test40320 576 592 :=
  interval_of_check test40320 576 16 (by decide +kernel)

theorem test40320_block_37 : Interval test40320 592 608 :=
  interval_of_check test40320 592 16 (by decide +kernel)

theorem test40320_block_38 : Interval test40320 608 624 :=
  interval_of_check test40320 608 16 (by decide +kernel)

theorem test40320_block_39 : Interval test40320 624 640 :=
  interval_of_check test40320 624 16 (by decide +kernel)

theorem test40320_complete : Interval test40320 0 640 :=
  (interval_append test40320 0 320 640
  (interval_append test40320 0 160 320
  (interval_append test40320 0 80 160
  (interval_append test40320 0 32 80
  (interval_append test40320 0 16 32
  test40320_block_0
  test40320_block_1)
  (interval_append test40320 32 48 80
  test40320_block_2
  (interval_append test40320 48 64 80
  test40320_block_3
  test40320_block_4)))
  (interval_append test40320 80 112 160
  (interval_append test40320 80 96 112
  test40320_block_5
  test40320_block_6)
  (interval_append test40320 112 128 160
  test40320_block_7
  (interval_append test40320 128 144 160
  test40320_block_8
  test40320_block_9))))
  (interval_append test40320 160 240 320
  (interval_append test40320 160 192 240
  (interval_append test40320 160 176 192
  test40320_block_10
  test40320_block_11)
  (interval_append test40320 192 208 240
  test40320_block_12
  (interval_append test40320 208 224 240
  test40320_block_13
  test40320_block_14)))
  (interval_append test40320 240 272 320
  (interval_append test40320 240 256 272
  test40320_block_15
  test40320_block_16)
  (interval_append test40320 272 288 320
  test40320_block_17
  (interval_append test40320 288 304 320
  test40320_block_18
  test40320_block_19)))))
  (interval_append test40320 320 480 640
  (interval_append test40320 320 400 480
  (interval_append test40320 320 352 400
  (interval_append test40320 320 336 352
  test40320_block_20
  test40320_block_21)
  (interval_append test40320 352 368 400
  test40320_block_22
  (interval_append test40320 368 384 400
  test40320_block_23
  test40320_block_24)))
  (interval_append test40320 400 432 480
  (interval_append test40320 400 416 432
  test40320_block_25
  test40320_block_26)
  (interval_append test40320 432 448 480
  test40320_block_27
  (interval_append test40320 448 464 480
  test40320_block_28
  test40320_block_29))))
  (interval_append test40320 480 560 640
  (interval_append test40320 480 512 560
  (interval_append test40320 480 496 512
  test40320_block_30
  test40320_block_31)
  (interval_append test40320 512 528 560
  test40320_block_32
  (interval_append test40320 528 544 560
  test40320_block_33
  test40320_block_34)))
  (interval_append test40320 560 592 640
  (interval_append test40320 560 576 592
  test40320_block_35
  test40320_block_36)
  (interval_append test40320 592 608 640
  test40320_block_37
  (interval_append test40320 608 624 640
  test40320_block_38
  test40320_block_39))))))
theorem nodeInterval40320 : Interval nodeTest 40320 40960 := by
  intro i hlo hhi
  have h := test40320_complete (i-40320) (Nat.zero_le _) (by omega)
  simpa only [test40320, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
