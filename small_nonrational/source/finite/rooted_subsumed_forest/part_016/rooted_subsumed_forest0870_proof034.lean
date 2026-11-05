module
prelude
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test21760 (i : Nat) := nodeTest (i+21760)
theorem test21760_block_0 : Interval test21760 0 16 :=
  interval_of_check test21760 0 16 (by decide +kernel)

theorem test21760_block_1 : Interval test21760 16 32 :=
  interval_of_check test21760 16 16 (by decide +kernel)

theorem test21760_block_2 : Interval test21760 32 48 :=
  interval_of_check test21760 32 16 (by decide +kernel)

theorem test21760_block_3 : Interval test21760 48 64 :=
  interval_of_check test21760 48 16 (by decide +kernel)

theorem test21760_block_4 : Interval test21760 64 80 :=
  interval_of_check test21760 64 16 (by decide +kernel)

theorem test21760_block_5 : Interval test21760 80 96 :=
  interval_of_check test21760 80 16 (by decide +kernel)

theorem test21760_block_6 : Interval test21760 96 112 :=
  interval_of_check test21760 96 16 (by decide +kernel)

theorem test21760_block_7 : Interval test21760 112 128 :=
  interval_of_check test21760 112 16 (by decide +kernel)

theorem test21760_block_8 : Interval test21760 128 144 :=
  interval_of_check test21760 128 16 (by decide +kernel)

theorem test21760_block_9 : Interval test21760 144 160 :=
  interval_of_check test21760 144 16 (by decide +kernel)

theorem test21760_block_10 : Interval test21760 160 176 :=
  interval_of_check test21760 160 16 (by decide +kernel)

theorem test21760_block_11 : Interval test21760 176 192 :=
  interval_of_check test21760 176 16 (by decide +kernel)

theorem test21760_block_12 : Interval test21760 192 208 :=
  interval_of_check test21760 192 16 (by decide +kernel)

theorem test21760_block_13 : Interval test21760 208 224 :=
  interval_of_check test21760 208 16 (by decide +kernel)

theorem test21760_block_14 : Interval test21760 224 240 :=
  interval_of_check test21760 224 16 (by decide +kernel)

theorem test21760_block_15 : Interval test21760 240 256 :=
  interval_of_check test21760 240 16 (by decide +kernel)

theorem test21760_block_16 : Interval test21760 256 272 :=
  interval_of_check test21760 256 16 (by decide +kernel)

theorem test21760_block_17 : Interval test21760 272 288 :=
  interval_of_check test21760 272 16 (by decide +kernel)

theorem test21760_block_18 : Interval test21760 288 304 :=
  interval_of_check test21760 288 16 (by decide +kernel)

theorem test21760_block_19 : Interval test21760 304 320 :=
  interval_of_check test21760 304 16 (by decide +kernel)

theorem test21760_block_20 : Interval test21760 320 336 :=
  interval_of_check test21760 320 16 (by decide +kernel)

theorem test21760_block_21 : Interval test21760 336 352 :=
  interval_of_check test21760 336 16 (by decide +kernel)

theorem test21760_block_22 : Interval test21760 352 368 :=
  interval_of_check test21760 352 16 (by decide +kernel)

theorem test21760_block_23 : Interval test21760 368 384 :=
  interval_of_check test21760 368 16 (by decide +kernel)

theorem test21760_block_24 : Interval test21760 384 400 :=
  interval_of_check test21760 384 16 (by decide +kernel)

theorem test21760_block_25 : Interval test21760 400 416 :=
  interval_of_check test21760 400 16 (by decide +kernel)

theorem test21760_block_26 : Interval test21760 416 432 :=
  interval_of_check test21760 416 16 (by decide +kernel)

theorem test21760_block_27 : Interval test21760 432 448 :=
  interval_of_check test21760 432 16 (by decide +kernel)

theorem test21760_block_28 : Interval test21760 448 464 :=
  interval_of_check test21760 448 16 (by decide +kernel)

theorem test21760_block_29 : Interval test21760 464 480 :=
  interval_of_check test21760 464 16 (by decide +kernel)

theorem test21760_block_30 : Interval test21760 480 496 :=
  interval_of_check test21760 480 16 (by decide +kernel)

theorem test21760_block_31 : Interval test21760 496 512 :=
  interval_of_check test21760 496 16 (by decide +kernel)

theorem test21760_block_32 : Interval test21760 512 528 :=
  interval_of_check test21760 512 16 (by decide +kernel)

theorem test21760_block_33 : Interval test21760 528 544 :=
  interval_of_check test21760 528 16 (by decide +kernel)

theorem test21760_block_34 : Interval test21760 544 560 :=
  interval_of_check test21760 544 16 (by decide +kernel)

theorem test21760_block_35 : Interval test21760 560 576 :=
  interval_of_check test21760 560 16 (by decide +kernel)

theorem test21760_block_36 : Interval test21760 576 592 :=
  interval_of_check test21760 576 16 (by decide +kernel)

theorem test21760_block_37 : Interval test21760 592 608 :=
  interval_of_check test21760 592 16 (by decide +kernel)

theorem test21760_block_38 : Interval test21760 608 624 :=
  interval_of_check test21760 608 16 (by decide +kernel)

theorem test21760_block_39 : Interval test21760 624 640 :=
  interval_of_check test21760 624 16 (by decide +kernel)

theorem test21760_complete : Interval test21760 0 640 :=
  (interval_append test21760 0 320 640
  (interval_append test21760 0 160 320
  (interval_append test21760 0 80 160
  (interval_append test21760 0 32 80
  (interval_append test21760 0 16 32
  test21760_block_0
  test21760_block_1)
  (interval_append test21760 32 48 80
  test21760_block_2
  (interval_append test21760 48 64 80
  test21760_block_3
  test21760_block_4)))
  (interval_append test21760 80 112 160
  (interval_append test21760 80 96 112
  test21760_block_5
  test21760_block_6)
  (interval_append test21760 112 128 160
  test21760_block_7
  (interval_append test21760 128 144 160
  test21760_block_8
  test21760_block_9))))
  (interval_append test21760 160 240 320
  (interval_append test21760 160 192 240
  (interval_append test21760 160 176 192
  test21760_block_10
  test21760_block_11)
  (interval_append test21760 192 208 240
  test21760_block_12
  (interval_append test21760 208 224 240
  test21760_block_13
  test21760_block_14)))
  (interval_append test21760 240 272 320
  (interval_append test21760 240 256 272
  test21760_block_15
  test21760_block_16)
  (interval_append test21760 272 288 320
  test21760_block_17
  (interval_append test21760 288 304 320
  test21760_block_18
  test21760_block_19)))))
  (interval_append test21760 320 480 640
  (interval_append test21760 320 400 480
  (interval_append test21760 320 352 400
  (interval_append test21760 320 336 352
  test21760_block_20
  test21760_block_21)
  (interval_append test21760 352 368 400
  test21760_block_22
  (interval_append test21760 368 384 400
  test21760_block_23
  test21760_block_24)))
  (interval_append test21760 400 432 480
  (interval_append test21760 400 416 432
  test21760_block_25
  test21760_block_26)
  (interval_append test21760 432 448 480
  test21760_block_27
  (interval_append test21760 448 464 480
  test21760_block_28
  test21760_block_29))))
  (interval_append test21760 480 560 640
  (interval_append test21760 480 512 560
  (interval_append test21760 480 496 512
  test21760_block_30
  test21760_block_31)
  (interval_append test21760 512 528 560
  test21760_block_32
  (interval_append test21760 528 544 560
  test21760_block_33
  test21760_block_34)))
  (interval_append test21760 560 592 640
  (interval_append test21760 560 576 592
  test21760_block_35
  test21760_block_36)
  (interval_append test21760 592 608 640
  test21760_block_37
  (interval_append test21760 608 624 640
  test21760_block_38
  test21760_block_39))))))
theorem nodeInterval21760 : Interval nodeTest 21760 22400 := by
  intro i hlo hhi
  have h := test21760_complete (i-21760) (Nat.zero_le _) (by omega)
  simpa only [test21760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
