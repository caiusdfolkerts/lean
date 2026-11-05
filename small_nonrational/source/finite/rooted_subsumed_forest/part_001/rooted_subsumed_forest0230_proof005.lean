module
prelude
public import RootedSubsumedForest0230Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0230
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3200 (i : Nat) := nodeTest (i+3200)
theorem test3200_block_0 : Interval test3200 0 16 :=
  interval_of_check test3200 0 16 (by decide +kernel)

theorem test3200_block_1 : Interval test3200 16 32 :=
  interval_of_check test3200 16 16 (by decide +kernel)

theorem test3200_block_2 : Interval test3200 32 48 :=
  interval_of_check test3200 32 16 (by decide +kernel)

theorem test3200_block_3 : Interval test3200 48 64 :=
  interval_of_check test3200 48 16 (by decide +kernel)

theorem test3200_block_4 : Interval test3200 64 80 :=
  interval_of_check test3200 64 16 (by decide +kernel)

theorem test3200_block_5 : Interval test3200 80 96 :=
  interval_of_check test3200 80 16 (by decide +kernel)

theorem test3200_block_6 : Interval test3200 96 112 :=
  interval_of_check test3200 96 16 (by decide +kernel)

theorem test3200_block_7 : Interval test3200 112 128 :=
  interval_of_check test3200 112 16 (by decide +kernel)

theorem test3200_block_8 : Interval test3200 128 144 :=
  interval_of_check test3200 128 16 (by decide +kernel)

theorem test3200_block_9 : Interval test3200 144 160 :=
  interval_of_check test3200 144 16 (by decide +kernel)

theorem test3200_block_10 : Interval test3200 160 176 :=
  interval_of_check test3200 160 16 (by decide +kernel)

theorem test3200_block_11 : Interval test3200 176 192 :=
  interval_of_check test3200 176 16 (by decide +kernel)

theorem test3200_block_12 : Interval test3200 192 208 :=
  interval_of_check test3200 192 16 (by decide +kernel)

theorem test3200_block_13 : Interval test3200 208 224 :=
  interval_of_check test3200 208 16 (by decide +kernel)

theorem test3200_block_14 : Interval test3200 224 240 :=
  interval_of_check test3200 224 16 (by decide +kernel)

theorem test3200_block_15 : Interval test3200 240 244 :=
  interval_of_check test3200 240 4 (by decide +kernel)

theorem test3200_complete : Interval test3200 0 244 :=
  (interval_append test3200 0 128 244
  (interval_append test3200 0 64 128
  (interval_append test3200 0 32 64
  (interval_append test3200 0 16 32
  test3200_block_0
  test3200_block_1)
  (interval_append test3200 32 48 64
  test3200_block_2
  test3200_block_3))
  (interval_append test3200 64 96 128
  (interval_append test3200 64 80 96
  test3200_block_4
  test3200_block_5)
  (interval_append test3200 96 112 128
  test3200_block_6
  test3200_block_7)))
  (interval_append test3200 128 192 244
  (interval_append test3200 128 160 192
  (interval_append test3200 128 144 160
  test3200_block_8
  test3200_block_9)
  (interval_append test3200 160 176 192
  test3200_block_10
  test3200_block_11))
  (interval_append test3200 192 224 244
  (interval_append test3200 192 208 224
  test3200_block_12
  test3200_block_13)
  (interval_append test3200 224 240 244
  test3200_block_14
  test3200_block_15))))
theorem nodeInterval3200 : Interval nodeTest 3200 3444 := by
  intro i hlo hhi
  have h := test3200_complete (i-3200) (Nat.zero_le _) (by omega)
  simpa only [test3200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0230
