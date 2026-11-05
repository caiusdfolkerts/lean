module
prelude
public import RootedSubsumedForest0699Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0699
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

theorem test2560_block_22 : Interval test2560 352 353 :=
  interval_of_check test2560 352 1 (by decide +kernel)

theorem test2560_complete : Interval test2560 0 353 :=
  (interval_append test2560 0 176 353
  (interval_append test2560 0 80 176
  (interval_append test2560 0 32 80
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 80
  test2560_block_2
  (interval_append test2560 48 64 80
  test2560_block_3
  test2560_block_4)))
  (interval_append test2560 80 128 176
  (interval_append test2560 80 96 128
  test2560_block_5
  (interval_append test2560 96 112 128
  test2560_block_6
  test2560_block_7))
  (interval_append test2560 128 144 176
  test2560_block_8
  (interval_append test2560 144 160 176
  test2560_block_9
  test2560_block_10))))
  (interval_append test2560 176 272 353
  (interval_append test2560 176 224 272
  (interval_append test2560 176 192 224
  test2560_block_11
  (interval_append test2560 192 208 224
  test2560_block_12
  test2560_block_13))
  (interval_append test2560 224 240 272
  test2560_block_14
  (interval_append test2560 240 256 272
  test2560_block_15
  test2560_block_16)))
  (interval_append test2560 272 320 353
  (interval_append test2560 272 288 320
  test2560_block_17
  (interval_append test2560 288 304 320
  test2560_block_18
  test2560_block_19))
  (interval_append test2560 320 336 353
  test2560_block_20
  (interval_append test2560 336 352 353
  test2560_block_21
  test2560_block_22)))))
theorem nodeInterval2560 : Interval nodeTest 2560 2913 := by
  intro i hlo hhi
  have h := test2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [test2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0699
