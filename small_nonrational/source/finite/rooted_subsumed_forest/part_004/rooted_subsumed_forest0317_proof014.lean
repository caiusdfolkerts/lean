module
prelude
public import RootedSubsumedForest0317Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test8960 (i : Nat) := nodeTest (i+8960)
theorem test8960_block_0 : Interval test8960 0 16 :=
  interval_of_check test8960 0 16 (by decide +kernel)

theorem test8960_block_1 : Interval test8960 16 32 :=
  interval_of_check test8960 16 16 (by decide +kernel)

theorem test8960_block_2 : Interval test8960 32 43 :=
  interval_of_check test8960 32 11 (by decide +kernel)

theorem test8960_complete : Interval test8960 0 43 :=
  (interval_append test8960 0 16 43
  test8960_block_0
  (interval_append test8960 16 32 43
  test8960_block_1
  test8960_block_2))
theorem nodeInterval8960 : Interval nodeTest 8960 9003 := by
  intro i hlo hhi
  have h := test8960_complete (i-8960) (Nat.zero_le _) (by omega)
  simpa only [test8960, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0317
