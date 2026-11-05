module
prelude
public import RootedSubsumedForest0232Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test2560 (i : Nat) := nodeTest (i+2560)
theorem test2560_block_0 : Interval test2560 0 16 :=
  interval_of_check test2560 0 16 (by decide +kernel)

theorem test2560_block_1 : Interval test2560 16 32 :=
  interval_of_check test2560 16 16 (by decide +kernel)

theorem test2560_block_2 : Interval test2560 32 48 :=
  interval_of_check test2560 32 16 (by decide +kernel)

theorem test2560_block_3 : Interval test2560 48 64 :=
  interval_of_check test2560 48 16 (by decide +kernel)

theorem test2560_block_4 : Interval test2560 64 80 :=
  interval_of_check test2560 64 16 (by decide +kernel)

theorem test2560_block_5 : Interval test2560 80 96 :=
  interval_of_check test2560 80 16 (by decide +kernel)

theorem test2560_block_6 : Interval test2560 96 112 :=
  interval_of_check test2560 96 16 (by decide +kernel)

theorem test2560_block_7 : Interval test2560 112 128 :=
  interval_of_check test2560 112 16 (by decide +kernel)

theorem test2560_block_8 : Interval test2560 128 144 :=
  interval_of_check test2560 128 16 (by decide +kernel)

theorem test2560_block_9 : Interval test2560 144 160 :=
  interval_of_check test2560 144 16 (by decide +kernel)

theorem test2560_block_10 : Interval test2560 160 176 :=
  interval_of_check test2560 160 16 (by decide +kernel)

theorem test2560_block_11 : Interval test2560 176 192 :=
  interval_of_check test2560 176 16 (by decide +kernel)

theorem test2560_block_12 : Interval test2560 192 208 :=
  interval_of_check test2560 192 16 (by decide +kernel)

theorem test2560_block_13 : Interval test2560 208 224 :=
  interval_of_check test2560 208 16 (by decide +kernel)

theorem test2560_block_14 : Interval test2560 224 240 :=
  interval_of_check test2560 224 16 (by decide +kernel)

theorem test2560_block_15 : Interval test2560 240 256 :=
  interval_of_check test2560 240 16 (by decide +kernel)

theorem test2560_block_16 : Interval test2560 256 272 :=
  interval_of_check test2560 256 16 (by decide +kernel)

theorem test2560_block_17 : Interval test2560 272 288 :=
  interval_of_check test2560 272 16 (by decide +kernel)

theorem test2560_block_18 : Interval test2560 288 304 :=
  interval_of_check test2560 288 16 (by decide +kernel)

theorem test2560_block_19 : Interval test2560 304 320 :=
  interval_of_check test2560 304 16 (by decide +kernel)

theorem test2560_block_20 : Interval test2560 320 336 :=
  interval_of_check test2560 320 16 (by decide +kernel)

theorem test2560_block_21 : Interval test2560 336 352 :=
  interval_of_check test2560 336 16 (by decide +kernel)

theorem test2560_block_22 : Interval test2560 352 368 :=
  interval_of_check test2560 352 16 (by decide +kernel)

theorem test2560_block_23 : Interval test2560 368 384 :=
  interval_of_check test2560 368 16 (by decide +kernel)

theorem test2560_block_24 : Interval test2560 384 400 :=
  interval_of_check test2560 384 16 (by decide +kernel)

theorem test2560_block_25 : Interval test2560 400 416 :=
  interval_of_check test2560 400 16 (by decide +kernel)

theorem test2560_complete : Interval test2560 0 416 :=
  (interval_append test2560 0 208 416
  (interval_append test2560 0 96 208
  (interval_append test2560 0 48 96
  (interval_append test2560 0 16 48
  test2560_block_0
  (interval_append test2560 16 32 48
  test2560_block_1
  test2560_block_2))
  (interval_append test2560 48 64 96
  test2560_block_3
  (interval_append test2560 64 80 96
  test2560_block_4
  test2560_block_5)))
  (interval_append test2560 96 144 208
  (interval_append test2560 96 112 144
  test2560_block_6
  (interval_append test2560 112 128 144
  test2560_block_7
  test2560_block_8))
  (interval_append test2560 144 176 208
  (interval_append test2560 144 160 176
  test2560_block_9
  test2560_block_10)
  (interval_append test2560 176 192 208
  test2560_block_11
  test2560_block_12))))
  (interval_append test2560 208 304 416
  (interval_append test2560 208 256 304
  (interval_append test2560 208 224 256
  test2560_block_13
  (interval_append test2560 224 240 256
  test2560_block_14
  test2560_block_15))
  (interval_append test2560 256 272 304
  test2560_block_16
  (interval_append test2560 272 288 304
  test2560_block_17
  test2560_block_18)))
  (interval_append test2560 304 352 416
  (interval_append test2560 304 320 352
  test2560_block_19
  (interval_append test2560 320 336 352
  test2560_block_20
  test2560_block_21))
  (interval_append test2560 352 384 416
  (interval_append test2560 352 368 384
  test2560_block_22
  test2560_block_23)
  (interval_append test2560 384 400 416
  test2560_block_24
  test2560_block_25)))))
theorem nodeInterval2560 : Interval nodeTest 2560 2976 := by
  intro i hlo hhi
  have h := test2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [test2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0232
