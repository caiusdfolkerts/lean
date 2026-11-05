module
prelude
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test157440 (i : Nat) := nodeTest (i+157440)
theorem test157440_block_0 : Interval test157440 0 16 :=
  interval_of_check test157440 0 16 (by decide +kernel)

theorem test157440_block_1 : Interval test157440 16 32 :=
  interval_of_check test157440 16 16 (by decide +kernel)

theorem test157440_block_2 : Interval test157440 32 48 :=
  interval_of_check test157440 32 16 (by decide +kernel)

theorem test157440_block_3 : Interval test157440 48 64 :=
  interval_of_check test157440 48 16 (by decide +kernel)

theorem test157440_block_4 : Interval test157440 64 74 :=
  interval_of_check test157440 64 10 (by decide +kernel)

theorem test157440_complete : Interval test157440 0 74 :=
  (interval_append test157440 0 32 74
  (interval_append test157440 0 16 32
  test157440_block_0
  test157440_block_1)
  (interval_append test157440 32 48 74
  test157440_block_2
  (interval_append test157440 48 64 74
  test157440_block_3
  test157440_block_4)))
theorem nodeInterval157440 : Interval nodeTest 157440 157514 := by
  intro i hlo hhi
  have h := test157440_complete (i-157440) (Nat.zero_le _) (by omega)
  simpa only [test157440, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
