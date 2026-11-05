module
prelude
public import RootedSubsumedForest0314Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0314
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3200 (i : Nat) := nodeTest (i+3200)
theorem test3200_block_0 : Interval test3200 0 16 :=
  interval_of_check test3200 0 16 (by decide +kernel)

theorem test3200_block_1 : Interval test3200 16 29 :=
  interval_of_check test3200 16 13 (by decide +kernel)

theorem test3200_complete : Interval test3200 0 29 :=
  (interval_append test3200 0 16 29
  test3200_block_0
  test3200_block_1)
theorem nodeInterval3200 : Interval nodeTest 3200 3229 := by
  intro i hlo hhi
  have h := test3200_complete (i-3200) (Nat.zero_le _) (by omega)
  simpa only [test3200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0314
