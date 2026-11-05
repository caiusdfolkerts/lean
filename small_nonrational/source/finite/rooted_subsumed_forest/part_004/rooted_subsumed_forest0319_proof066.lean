module
prelude
public import RootedSubsumedForest0319Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test42240 (i : Nat) := nodeTest (i+42240)
theorem test42240_block_0 : Interval test42240 0 16 :=
  interval_of_check test42240 0 16 (by decide +kernel)

theorem test42240_block_1 : Interval test42240 16 32 :=
  interval_of_check test42240 16 16 (by decide +kernel)

theorem test42240_block_2 : Interval test42240 32 48 :=
  interval_of_check test42240 32 16 (by decide +kernel)

theorem test42240_block_3 : Interval test42240 48 64 :=
  interval_of_check test42240 48 16 (by decide +kernel)

theorem test42240_block_4 : Interval test42240 64 80 :=
  interval_of_check test42240 64 16 (by decide +kernel)

theorem test42240_block_5 : Interval test42240 80 96 :=
  interval_of_check test42240 80 16 (by decide +kernel)

theorem test42240_block_6 : Interval test42240 96 112 :=
  interval_of_check test42240 96 16 (by decide +kernel)

theorem test42240_block_7 : Interval test42240 112 128 :=
  interval_of_check test42240 112 16 (by decide +kernel)

theorem test42240_block_8 : Interval test42240 128 144 :=
  interval_of_check test42240 128 16 (by decide +kernel)

theorem test42240_block_9 : Interval test42240 144 160 :=
  interval_of_check test42240 144 16 (by decide +kernel)

theorem test42240_block_10 : Interval test42240 160 176 :=
  interval_of_check test42240 160 16 (by decide +kernel)

theorem test42240_block_11 : Interval test42240 176 192 :=
  interval_of_check test42240 176 16 (by decide +kernel)

theorem test42240_block_12 : Interval test42240 192 208 :=
  interval_of_check test42240 192 16 (by decide +kernel)

theorem test42240_block_13 : Interval test42240 208 224 :=
  interval_of_check test42240 208 16 (by decide +kernel)

theorem test42240_block_14 : Interval test42240 224 240 :=
  interval_of_check test42240 224 16 (by decide +kernel)

theorem test42240_block_15 : Interval test42240 240 256 :=
  interval_of_check test42240 240 16 (by decide +kernel)

theorem test42240_block_16 : Interval test42240 256 272 :=
  interval_of_check test42240 256 16 (by decide +kernel)

theorem test42240_block_17 : Interval test42240 272 288 :=
  interval_of_check test42240 272 16 (by decide +kernel)

theorem test42240_block_18 : Interval test42240 288 304 :=
  interval_of_check test42240 288 16 (by decide +kernel)

theorem test42240_block_19 : Interval test42240 304 320 :=
  interval_of_check test42240 304 16 (by decide +kernel)

theorem test42240_block_20 : Interval test42240 320 336 :=
  interval_of_check test42240 320 16 (by decide +kernel)

theorem test42240_block_21 : Interval test42240 336 352 :=
  interval_of_check test42240 336 16 (by decide +kernel)

theorem test42240_block_22 : Interval test42240 352 368 :=
  interval_of_check test42240 352 16 (by decide +kernel)

theorem test42240_block_23 : Interval test42240 368 384 :=
  interval_of_check test42240 368 16 (by decide +kernel)

theorem test42240_block_24 : Interval test42240 384 400 :=
  interval_of_check test42240 384 16 (by decide +kernel)

theorem test42240_block_25 : Interval test42240 400 416 :=
  interval_of_check test42240 400 16 (by decide +kernel)

theorem test42240_block_26 : Interval test42240 416 432 :=
  interval_of_check test42240 416 16 (by decide +kernel)

theorem test42240_block_27 : Interval test42240 432 448 :=
  interval_of_check test42240 432 16 (by decide +kernel)

theorem test42240_block_28 : Interval test42240 448 464 :=
  interval_of_check test42240 448 16 (by decide +kernel)

theorem test42240_block_29 : Interval test42240 464 467 :=
  interval_of_check test42240 464 3 (by decide +kernel)

theorem test42240_complete : Interval test42240 0 467 :=
  (interval_append test42240 0 240 467
  (interval_append test42240 0 112 240
  (interval_append test42240 0 48 112
  (interval_append test42240 0 16 48
  test42240_block_0
  (interval_append test42240 16 32 48
  test42240_block_1
  test42240_block_2))
  (interval_append test42240 48 80 112
  (interval_append test42240 48 64 80
  test42240_block_3
  test42240_block_4)
  (interval_append test42240 80 96 112
  test42240_block_5
  test42240_block_6)))
  (interval_append test42240 112 176 240
  (interval_append test42240 112 144 176
  (interval_append test42240 112 128 144
  test42240_block_7
  test42240_block_8)
  (interval_append test42240 144 160 176
  test42240_block_9
  test42240_block_10))
  (interval_append test42240 176 208 240
  (interval_append test42240 176 192 208
  test42240_block_11
  test42240_block_12)
  (interval_append test42240 208 224 240
  test42240_block_13
  test42240_block_14))))
  (interval_append test42240 240 352 467
  (interval_append test42240 240 288 352
  (interval_append test42240 240 256 288
  test42240_block_15
  (interval_append test42240 256 272 288
  test42240_block_16
  test42240_block_17))
  (interval_append test42240 288 320 352
  (interval_append test42240 288 304 320
  test42240_block_18
  test42240_block_19)
  (interval_append test42240 320 336 352
  test42240_block_20
  test42240_block_21)))
  (interval_append test42240 352 416 467
  (interval_append test42240 352 384 416
  (interval_append test42240 352 368 384
  test42240_block_22
  test42240_block_23)
  (interval_append test42240 384 400 416
  test42240_block_24
  test42240_block_25))
  (interval_append test42240 416 448 467
  (interval_append test42240 416 432 448
  test42240_block_26
  test42240_block_27)
  (interval_append test42240 448 464 467
  test42240_block_28
  test42240_block_29)))))
theorem nodeInterval42240 : Interval nodeTest 42240 42707 := by
  intro i hlo hhi
  have h := test42240_complete (i-42240) (Nat.zero_le _) (by omega)
  simpa only [test42240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
