module
prelude
public import SmallSubsumedForest22Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 16 :=
  interval_of_check test1920 0 16 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 16 32 :=
  interval_of_check test1920 16 16 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 32 48 :=
  interval_of_check test1920 32 16 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 48 64 :=
  interval_of_check test1920 48 16 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 64 69 :=
  interval_of_check test1920 64 5 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 69 :=
  (interval_append test1920 0 32 69
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 69
  test1920_block_2
  (interval_append test1920 48 64 69
  test1920_block_3
  test1920_block_4)))
theorem nodeInterval1920 : Interval nodeTest 1920 1989 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest22
