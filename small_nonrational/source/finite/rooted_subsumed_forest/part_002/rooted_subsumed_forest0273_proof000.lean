module
prelude
public import RootedSubsumedForest0273Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0273
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_block_8 : Interval test0 128 144 :=
  interval_of_check test0 128 16 (by decide +kernel)

theorem test0_block_9 : Interval test0 144 160 :=
  interval_of_check test0 144 16 (by decide +kernel)

theorem test0_block_10 : Interval test0 160 176 :=
  interval_of_check test0 160 16 (by decide +kernel)

theorem test0_block_11 : Interval test0 176 192 :=
  interval_of_check test0 176 16 (by decide +kernel)

theorem test0_block_12 : Interval test0 192 208 :=
  interval_of_check test0 192 16 (by decide +kernel)

theorem test0_block_13 : Interval test0 208 224 :=
  interval_of_check test0 208 16 (by decide +kernel)

theorem test0_block_14 : Interval test0 224 240 :=
  interval_of_check test0 224 16 (by decide +kernel)

theorem test0_block_15 : Interval test0 240 256 :=
  interval_of_check test0 240 16 (by decide +kernel)

theorem test0_block_16 : Interval test0 256 272 :=
  interval_of_check test0 256 16 (by decide +kernel)

theorem test0_block_17 : Interval test0 272 288 :=
  interval_of_check test0 272 16 (by decide +kernel)

theorem test0_block_18 : Interval test0 288 304 :=
  interval_of_check test0 288 16 (by decide +kernel)

theorem test0_block_19 : Interval test0 304 320 :=
  interval_of_check test0 304 16 (by decide +kernel)

theorem test0_block_20 : Interval test0 320 336 :=
  interval_of_check test0 320 16 (by decide +kernel)

theorem test0_block_21 : Interval test0 336 352 :=
  interval_of_check test0 336 16 (by decide +kernel)

theorem test0_block_22 : Interval test0 352 368 :=
  interval_of_check test0 352 16 (by decide +kernel)

theorem test0_block_23 : Interval test0 368 384 :=
  interval_of_check test0 368 16 (by decide +kernel)

theorem test0_block_24 : Interval test0 384 400 :=
  interval_of_check test0 384 16 (by decide +kernel)

theorem test0_block_25 : Interval test0 400 416 :=
  interval_of_check test0 400 16 (by decide +kernel)

theorem test0_block_26 : Interval test0 416 432 :=
  interval_of_check test0 416 16 (by decide +kernel)

theorem test0_block_27 : Interval test0 432 448 :=
  interval_of_check test0 432 16 (by decide +kernel)

theorem test0_block_28 : Interval test0 448 464 :=
  interval_of_check test0 448 16 (by decide +kernel)

theorem test0_block_29 : Interval test0 464 479 :=
  interval_of_check test0 464 15 (by decide +kernel)

theorem test0_complete : Interval test0 0 479 :=
  (interval_append test0 0 240 479
  (interval_append test0 0 112 240
  (interval_append test0 0 48 112
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 80 112
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)
  (interval_append test0 80 96 112
  test0_block_5
  test0_block_6)))
  (interval_append test0 112 176 240
  (interval_append test0 112 144 176
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8)
  (interval_append test0 144 160 176
  test0_block_9
  test0_block_10))
  (interval_append test0 176 208 240
  (interval_append test0 176 192 208
  test0_block_11
  test0_block_12)
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14))))
  (interval_append test0 240 352 479
  (interval_append test0 240 288 352
  (interval_append test0 240 256 288
  test0_block_15
  (interval_append test0 256 272 288
  test0_block_16
  test0_block_17))
  (interval_append test0 288 320 352
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19)
  (interval_append test0 320 336 352
  test0_block_20
  test0_block_21)))
  (interval_append test0 352 416 479
  (interval_append test0 352 384 416
  (interval_append test0 352 368 384
  test0_block_22
  test0_block_23)
  (interval_append test0 384 400 416
  test0_block_24
  test0_block_25))
  (interval_append test0 416 448 479
  (interval_append test0 416 432 448
  test0_block_26
  test0_block_27)
  (interval_append test0 448 464 479
  test0_block_28
  test0_block_29)))))
theorem nodeInterval0 : Interval nodeTest 0 479 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0273
