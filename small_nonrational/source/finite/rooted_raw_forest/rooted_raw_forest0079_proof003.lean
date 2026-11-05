module
prelude
public import RootedRawForest0079Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0079
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 32 :=
  interval_of_check test1920 0 32 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 32 64 :=
  interval_of_check test1920 32 32 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 64 96 :=
  interval_of_check test1920 64 32 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 96 97 :=
  interval_of_check test1920 96 1 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 97 :=
  (interval_append test1920 0 64 97
  (interval_append test1920 0 32 64
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 64 96 97
  test1920_block_2
  test1920_block_3))
theorem nodeInterval1920 : Interval nodeTest 1920 2017 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0079
