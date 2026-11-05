module
prelude
public import RootedSubsumedForest0233Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0233
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1280 (i : Nat) := nodeTest (i+1280)
theorem test1280_block_0 : Interval test1280 0 16 :=
  interval_of_check test1280 0 16 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 16 26 :=
  interval_of_check test1280 16 10 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 26 :=
  (interval_append test1280 0 16 26
  test1280_block_0
  test1280_block_1)
theorem nodeInterval1280 : Interval nodeTest 1280 1306 := by
  intro i hlo hhi
  have h := test1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0233
