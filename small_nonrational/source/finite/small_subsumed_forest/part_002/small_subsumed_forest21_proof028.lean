module
prelude
public import SmallSubsumedForest21Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test17920 (i : Nat) := nodeTest (i+17920)
theorem test17920_block_0 : Interval test17920 0 16 :=
  interval_of_check test17920 0 16 (by decide +kernel)

theorem test17920_block_1 : Interval test17920 16 32 :=
  interval_of_check test17920 16 16 (by decide +kernel)

theorem test17920_block_2 : Interval test17920 32 48 :=
  interval_of_check test17920 32 16 (by decide +kernel)

theorem test17920_block_3 : Interval test17920 48 64 :=
  interval_of_check test17920 48 16 (by decide +kernel)

theorem test17920_block_4 : Interval test17920 64 80 :=
  interval_of_check test17920 64 16 (by decide +kernel)

theorem test17920_block_5 : Interval test17920 80 96 :=
  interval_of_check test17920 80 16 (by decide +kernel)

theorem test17920_block_6 : Interval test17920 96 112 :=
  interval_of_check test17920 96 16 (by decide +kernel)

theorem test17920_block_7 : Interval test17920 112 128 :=
  interval_of_check test17920 112 16 (by decide +kernel)

theorem test17920_block_8 : Interval test17920 128 144 :=
  interval_of_check test17920 128 16 (by decide +kernel)

theorem test17920_block_9 : Interval test17920 144 160 :=
  interval_of_check test17920 144 16 (by decide +kernel)

theorem test17920_block_10 : Interval test17920 160 176 :=
  interval_of_check test17920 160 16 (by decide +kernel)

theorem test17920_block_11 : Interval test17920 176 192 :=
  interval_of_check test17920 176 16 (by decide +kernel)

theorem test17920_block_12 : Interval test17920 192 208 :=
  interval_of_check test17920 192 16 (by decide +kernel)

theorem test17920_block_13 : Interval test17920 208 224 :=
  interval_of_check test17920 208 16 (by decide +kernel)

theorem test17920_block_14 : Interval test17920 224 234 :=
  interval_of_check test17920 224 10 (by decide +kernel)

theorem test17920_complete : Interval test17920 0 234 :=
  (interval_append test17920 0 112 234
  (interval_append test17920 0 48 112
  (interval_append test17920 0 16 48
  test17920_block_0
  (interval_append test17920 16 32 48
  test17920_block_1
  test17920_block_2))
  (interval_append test17920 48 80 112
  (interval_append test17920 48 64 80
  test17920_block_3
  test17920_block_4)
  (interval_append test17920 80 96 112
  test17920_block_5
  test17920_block_6)))
  (interval_append test17920 112 176 234
  (interval_append test17920 112 144 176
  (interval_append test17920 112 128 144
  test17920_block_7
  test17920_block_8)
  (interval_append test17920 144 160 176
  test17920_block_9
  test17920_block_10))
  (interval_append test17920 176 208 234
  (interval_append test17920 176 192 208
  test17920_block_11
  test17920_block_12)
  (interval_append test17920 208 224 234
  test17920_block_13
  test17920_block_14))))
theorem nodeInterval17920 : Interval nodeTest 17920 18154 := by
  intro i hlo hhi
  have h := test17920_complete (i-17920) (Nat.zero_le _) (by omega)
  simpa only [test17920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest21
