module
prelude
public import RootedSubsumedForest0303Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test7680 (i : Nat) := nodeTest (i+7680)
theorem test7680_block_0 : Interval test7680 0 16 :=
  interval_of_check test7680 0 16 (by decide +kernel)

theorem test7680_block_1 : Interval test7680 16 32 :=
  interval_of_check test7680 16 16 (by decide +kernel)

theorem test7680_block_2 : Interval test7680 32 48 :=
  interval_of_check test7680 32 16 (by decide +kernel)

theorem test7680_block_3 : Interval test7680 48 64 :=
  interval_of_check test7680 48 16 (by decide +kernel)

theorem test7680_block_4 : Interval test7680 64 80 :=
  interval_of_check test7680 64 16 (by decide +kernel)

theorem test7680_block_5 : Interval test7680 80 96 :=
  interval_of_check test7680 80 16 (by decide +kernel)

theorem test7680_block_6 : Interval test7680 96 112 :=
  interval_of_check test7680 96 16 (by decide +kernel)

theorem test7680_block_7 : Interval test7680 112 128 :=
  interval_of_check test7680 112 16 (by decide +kernel)

theorem test7680_block_8 : Interval test7680 128 144 :=
  interval_of_check test7680 128 16 (by decide +kernel)

theorem test7680_block_9 : Interval test7680 144 160 :=
  interval_of_check test7680 144 16 (by decide +kernel)

theorem test7680_block_10 : Interval test7680 160 176 :=
  interval_of_check test7680 160 16 (by decide +kernel)

theorem test7680_block_11 : Interval test7680 176 192 :=
  interval_of_check test7680 176 16 (by decide +kernel)

theorem test7680_block_12 : Interval test7680 192 208 :=
  interval_of_check test7680 192 16 (by decide +kernel)

theorem test7680_block_13 : Interval test7680 208 224 :=
  interval_of_check test7680 208 16 (by decide +kernel)

theorem test7680_block_14 : Interval test7680 224 240 :=
  interval_of_check test7680 224 16 (by decide +kernel)

theorem test7680_block_15 : Interval test7680 240 256 :=
  interval_of_check test7680 240 16 (by decide +kernel)

theorem test7680_block_16 : Interval test7680 256 272 :=
  interval_of_check test7680 256 16 (by decide +kernel)

theorem test7680_block_17 : Interval test7680 272 288 :=
  interval_of_check test7680 272 16 (by decide +kernel)

theorem test7680_block_18 : Interval test7680 288 304 :=
  interval_of_check test7680 288 16 (by decide +kernel)

theorem test7680_block_19 : Interval test7680 304 320 :=
  interval_of_check test7680 304 16 (by decide +kernel)

theorem test7680_block_20 : Interval test7680 320 336 :=
  interval_of_check test7680 320 16 (by decide +kernel)

theorem test7680_block_21 : Interval test7680 336 352 :=
  interval_of_check test7680 336 16 (by decide +kernel)

theorem test7680_block_22 : Interval test7680 352 368 :=
  interval_of_check test7680 352 16 (by decide +kernel)

theorem test7680_block_23 : Interval test7680 368 384 :=
  interval_of_check test7680 368 16 (by decide +kernel)

theorem test7680_block_24 : Interval test7680 384 400 :=
  interval_of_check test7680 384 16 (by decide +kernel)

theorem test7680_block_25 : Interval test7680 400 416 :=
  interval_of_check test7680 400 16 (by decide +kernel)

theorem test7680_block_26 : Interval test7680 416 432 :=
  interval_of_check test7680 416 16 (by decide +kernel)

theorem test7680_block_27 : Interval test7680 432 448 :=
  interval_of_check test7680 432 16 (by decide +kernel)

theorem test7680_block_28 : Interval test7680 448 464 :=
  interval_of_check test7680 448 16 (by decide +kernel)

theorem test7680_block_29 : Interval test7680 464 480 :=
  interval_of_check test7680 464 16 (by decide +kernel)

theorem test7680_block_30 : Interval test7680 480 496 :=
  interval_of_check test7680 480 16 (by decide +kernel)

theorem test7680_block_31 : Interval test7680 496 512 :=
  interval_of_check test7680 496 16 (by decide +kernel)

theorem test7680_block_32 : Interval test7680 512 528 :=
  interval_of_check test7680 512 16 (by decide +kernel)

theorem test7680_block_33 : Interval test7680 528 544 :=
  interval_of_check test7680 528 16 (by decide +kernel)

theorem test7680_block_34 : Interval test7680 544 560 :=
  interval_of_check test7680 544 16 (by decide +kernel)

theorem test7680_block_35 : Interval test7680 560 576 :=
  interval_of_check test7680 560 16 (by decide +kernel)

theorem test7680_block_36 : Interval test7680 576 592 :=
  interval_of_check test7680 576 16 (by decide +kernel)

theorem test7680_block_37 : Interval test7680 592 608 :=
  interval_of_check test7680 592 16 (by decide +kernel)

theorem test7680_block_38 : Interval test7680 608 624 :=
  interval_of_check test7680 608 16 (by decide +kernel)

theorem test7680_block_39 : Interval test7680 624 640 :=
  interval_of_check test7680 624 16 (by decide +kernel)

theorem test7680_complete : Interval test7680 0 640 :=
  (interval_append test7680 0 320 640
  (interval_append test7680 0 160 320
  (interval_append test7680 0 80 160
  (interval_append test7680 0 32 80
  (interval_append test7680 0 16 32
  test7680_block_0
  test7680_block_1)
  (interval_append test7680 32 48 80
  test7680_block_2
  (interval_append test7680 48 64 80
  test7680_block_3
  test7680_block_4)))
  (interval_append test7680 80 112 160
  (interval_append test7680 80 96 112
  test7680_block_5
  test7680_block_6)
  (interval_append test7680 112 128 160
  test7680_block_7
  (interval_append test7680 128 144 160
  test7680_block_8
  test7680_block_9))))
  (interval_append test7680 160 240 320
  (interval_append test7680 160 192 240
  (interval_append test7680 160 176 192
  test7680_block_10
  test7680_block_11)
  (interval_append test7680 192 208 240
  test7680_block_12
  (interval_append test7680 208 224 240
  test7680_block_13
  test7680_block_14)))
  (interval_append test7680 240 272 320
  (interval_append test7680 240 256 272
  test7680_block_15
  test7680_block_16)
  (interval_append test7680 272 288 320
  test7680_block_17
  (interval_append test7680 288 304 320
  test7680_block_18
  test7680_block_19)))))
  (interval_append test7680 320 480 640
  (interval_append test7680 320 400 480
  (interval_append test7680 320 352 400
  (interval_append test7680 320 336 352
  test7680_block_20
  test7680_block_21)
  (interval_append test7680 352 368 400
  test7680_block_22
  (interval_append test7680 368 384 400
  test7680_block_23
  test7680_block_24)))
  (interval_append test7680 400 432 480
  (interval_append test7680 400 416 432
  test7680_block_25
  test7680_block_26)
  (interval_append test7680 432 448 480
  test7680_block_27
  (interval_append test7680 448 464 480
  test7680_block_28
  test7680_block_29))))
  (interval_append test7680 480 560 640
  (interval_append test7680 480 512 560
  (interval_append test7680 480 496 512
  test7680_block_30
  test7680_block_31)
  (interval_append test7680 512 528 560
  test7680_block_32
  (interval_append test7680 528 544 560
  test7680_block_33
  test7680_block_34)))
  (interval_append test7680 560 592 640
  (interval_append test7680 560 576 592
  test7680_block_35
  test7680_block_36)
  (interval_append test7680 592 608 640
  test7680_block_37
  (interval_append test7680 608 624 640
  test7680_block_38
  test7680_block_39))))))
theorem nodeInterval7680 : Interval nodeTest 7680 8320 := by
  intro i hlo hhi
  have h := test7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [test7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
