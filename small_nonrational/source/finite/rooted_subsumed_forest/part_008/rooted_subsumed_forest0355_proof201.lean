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
def test128640 (i : Nat) := nodeTest (i+128640)
theorem test128640_block_0 : Interval test128640 0 16 :=
  interval_of_check test128640 0 16 (by decide +kernel)

theorem test128640_block_1 : Interval test128640 16 32 :=
  interval_of_check test128640 16 16 (by decide +kernel)

theorem test128640_block_2 : Interval test128640 32 48 :=
  interval_of_check test128640 32 16 (by decide +kernel)

theorem test128640_block_3 : Interval test128640 48 64 :=
  interval_of_check test128640 48 16 (by decide +kernel)

theorem test128640_block_4 : Interval test128640 64 80 :=
  interval_of_check test128640 64 16 (by decide +kernel)

theorem test128640_block_5 : Interval test128640 80 96 :=
  interval_of_check test128640 80 16 (by decide +kernel)

theorem test128640_block_6 : Interval test128640 96 112 :=
  interval_of_check test128640 96 16 (by decide +kernel)

theorem test128640_block_7 : Interval test128640 112 128 :=
  interval_of_check test128640 112 16 (by decide +kernel)

theorem test128640_block_8 : Interval test128640 128 144 :=
  interval_of_check test128640 128 16 (by decide +kernel)

theorem test128640_block_9 : Interval test128640 144 160 :=
  interval_of_check test128640 144 16 (by decide +kernel)

theorem test128640_block_10 : Interval test128640 160 176 :=
  interval_of_check test128640 160 16 (by decide +kernel)

theorem test128640_block_11 : Interval test128640 176 192 :=
  interval_of_check test128640 176 16 (by decide +kernel)

theorem test128640_block_12 : Interval test128640 192 208 :=
  interval_of_check test128640 192 16 (by decide +kernel)

theorem test128640_block_13 : Interval test128640 208 224 :=
  interval_of_check test128640 208 16 (by decide +kernel)

theorem test128640_block_14 : Interval test128640 224 240 :=
  interval_of_check test128640 224 16 (by decide +kernel)

theorem test128640_block_15 : Interval test128640 240 256 :=
  interval_of_check test128640 240 16 (by decide +kernel)

theorem test128640_block_16 : Interval test128640 256 272 :=
  interval_of_check test128640 256 16 (by decide +kernel)

theorem test128640_block_17 : Interval test128640 272 288 :=
  interval_of_check test128640 272 16 (by decide +kernel)

theorem test128640_block_18 : Interval test128640 288 304 :=
  interval_of_check test128640 288 16 (by decide +kernel)

theorem test128640_block_19 : Interval test128640 304 320 :=
  interval_of_check test128640 304 16 (by decide +kernel)

theorem test128640_block_20 : Interval test128640 320 336 :=
  interval_of_check test128640 320 16 (by decide +kernel)

theorem test128640_block_21 : Interval test128640 336 352 :=
  interval_of_check test128640 336 16 (by decide +kernel)

theorem test128640_block_22 : Interval test128640 352 368 :=
  interval_of_check test128640 352 16 (by decide +kernel)

theorem test128640_block_23 : Interval test128640 368 384 :=
  interval_of_check test128640 368 16 (by decide +kernel)

theorem test128640_block_24 : Interval test128640 384 400 :=
  interval_of_check test128640 384 16 (by decide +kernel)

theorem test128640_block_25 : Interval test128640 400 416 :=
  interval_of_check test128640 400 16 (by decide +kernel)

theorem test128640_block_26 : Interval test128640 416 432 :=
  interval_of_check test128640 416 16 (by decide +kernel)

theorem test128640_block_27 : Interval test128640 432 448 :=
  interval_of_check test128640 432 16 (by decide +kernel)

theorem test128640_block_28 : Interval test128640 448 464 :=
  interval_of_check test128640 448 16 (by decide +kernel)

theorem test128640_block_29 : Interval test128640 464 480 :=
  interval_of_check test128640 464 16 (by decide +kernel)

theorem test128640_block_30 : Interval test128640 480 496 :=
  interval_of_check test128640 480 16 (by decide +kernel)

theorem test128640_block_31 : Interval test128640 496 512 :=
  interval_of_check test128640 496 16 (by decide +kernel)

theorem test128640_block_32 : Interval test128640 512 528 :=
  interval_of_check test128640 512 16 (by decide +kernel)

theorem test128640_block_33 : Interval test128640 528 544 :=
  interval_of_check test128640 528 16 (by decide +kernel)

theorem test128640_block_34 : Interval test128640 544 560 :=
  interval_of_check test128640 544 16 (by decide +kernel)

theorem test128640_block_35 : Interval test128640 560 576 :=
  interval_of_check test128640 560 16 (by decide +kernel)

theorem test128640_block_36 : Interval test128640 576 592 :=
  interval_of_check test128640 576 16 (by decide +kernel)

theorem test128640_block_37 : Interval test128640 592 608 :=
  interval_of_check test128640 592 16 (by decide +kernel)

theorem test128640_block_38 : Interval test128640 608 624 :=
  interval_of_check test128640 608 16 (by decide +kernel)

theorem test128640_block_39 : Interval test128640 624 640 :=
  interval_of_check test128640 624 16 (by decide +kernel)

theorem test128640_complete : Interval test128640 0 640 :=
  (interval_append test128640 0 320 640
  (interval_append test128640 0 160 320
  (interval_append test128640 0 80 160
  (interval_append test128640 0 32 80
  (interval_append test128640 0 16 32
  test128640_block_0
  test128640_block_1)
  (interval_append test128640 32 48 80
  test128640_block_2
  (interval_append test128640 48 64 80
  test128640_block_3
  test128640_block_4)))
  (interval_append test128640 80 112 160
  (interval_append test128640 80 96 112
  test128640_block_5
  test128640_block_6)
  (interval_append test128640 112 128 160
  test128640_block_7
  (interval_append test128640 128 144 160
  test128640_block_8
  test128640_block_9))))
  (interval_append test128640 160 240 320
  (interval_append test128640 160 192 240
  (interval_append test128640 160 176 192
  test128640_block_10
  test128640_block_11)
  (interval_append test128640 192 208 240
  test128640_block_12
  (interval_append test128640 208 224 240
  test128640_block_13
  test128640_block_14)))
  (interval_append test128640 240 272 320
  (interval_append test128640 240 256 272
  test128640_block_15
  test128640_block_16)
  (interval_append test128640 272 288 320
  test128640_block_17
  (interval_append test128640 288 304 320
  test128640_block_18
  test128640_block_19)))))
  (interval_append test128640 320 480 640
  (interval_append test128640 320 400 480
  (interval_append test128640 320 352 400
  (interval_append test128640 320 336 352
  test128640_block_20
  test128640_block_21)
  (interval_append test128640 352 368 400
  test128640_block_22
  (interval_append test128640 368 384 400
  test128640_block_23
  test128640_block_24)))
  (interval_append test128640 400 432 480
  (interval_append test128640 400 416 432
  test128640_block_25
  test128640_block_26)
  (interval_append test128640 432 448 480
  test128640_block_27
  (interval_append test128640 448 464 480
  test128640_block_28
  test128640_block_29))))
  (interval_append test128640 480 560 640
  (interval_append test128640 480 512 560
  (interval_append test128640 480 496 512
  test128640_block_30
  test128640_block_31)
  (interval_append test128640 512 528 560
  test128640_block_32
  (interval_append test128640 528 544 560
  test128640_block_33
  test128640_block_34)))
  (interval_append test128640 560 592 640
  (interval_append test128640 560 576 592
  test128640_block_35
  test128640_block_36)
  (interval_append test128640 592 608 640
  test128640_block_37
  (interval_append test128640 608 624 640
  test128640_block_38
  test128640_block_39))))))
theorem nodeInterval128640 : Interval nodeTest 128640 129280 := by
  intro i hlo hhi
  have h := test128640_complete (i-128640) (Nat.zero_le _) (by omega)
  simpa only [test128640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
