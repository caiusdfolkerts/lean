module
prelude
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test62720 (i : Nat) := nodeTest (i+62720)
theorem test62720_block_0 : Interval test62720 0 16 :=
  interval_of_check test62720 0 16 (by decide +kernel)

theorem test62720_block_1 : Interval test62720 16 32 :=
  interval_of_check test62720 16 16 (by decide +kernel)

theorem test62720_block_2 : Interval test62720 32 48 :=
  interval_of_check test62720 32 16 (by decide +kernel)

theorem test62720_block_3 : Interval test62720 48 49 :=
  interval_of_check test62720 48 1 (by decide +kernel)

theorem test62720_complete : Interval test62720 0 49 :=
  (interval_append test62720 0 32 49
  (interval_append test62720 0 16 32
  test62720_block_0
  test62720_block_1)
  (interval_append test62720 32 48 49
  test62720_block_2
  test62720_block_3))
theorem nodeInterval62720 : Interval nodeTest 62720 62769 := by
  intro i hlo hhi
  have h := test62720_complete (i-62720) (Nat.zero_le _) (by omega)
  simpa only [test62720, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
