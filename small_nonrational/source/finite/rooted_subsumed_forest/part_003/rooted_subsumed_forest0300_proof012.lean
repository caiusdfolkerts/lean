module
prelude
public import RootedSubsumedForest0300Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
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

theorem test7680_block_14 : Interval test7680 224 237 :=
  interval_of_check test7680 224 13 (by decide +kernel)

theorem test7680_complete : Interval test7680 0 237 :=
  (interval_append test7680 0 112 237
  (interval_append test7680 0 48 112
  (interval_append test7680 0 16 48
  test7680_block_0
  (interval_append test7680 16 32 48
  test7680_block_1
  test7680_block_2))
  (interval_append test7680 48 80 112
  (interval_append test7680 48 64 80
  test7680_block_3
  test7680_block_4)
  (interval_append test7680 80 96 112
  test7680_block_5
  test7680_block_6)))
  (interval_append test7680 112 176 237
  (interval_append test7680 112 144 176
  (interval_append test7680 112 128 144
  test7680_block_7
  test7680_block_8)
  (interval_append test7680 144 160 176
  test7680_block_9
  test7680_block_10))
  (interval_append test7680 176 208 237
  (interval_append test7680 176 192 208
  test7680_block_11
  test7680_block_12)
  (interval_append test7680 208 224 237
  test7680_block_13
  test7680_block_14))))
theorem nodeInterval7680 : Interval nodeTest 7680 7917 := by
  intro i hlo hhi
  have h := test7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [test7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0300
