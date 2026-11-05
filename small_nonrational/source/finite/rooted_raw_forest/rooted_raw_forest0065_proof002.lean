module
prelude
public import RootedRawForest0065Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0065
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1280 (i : Nat) := nodeTest (i+1280)
theorem test1280_block_0 : Interval test1280 0 32 :=
  interval_of_check test1280 0 32 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 32 64 :=
  interval_of_check test1280 32 32 (by decide +kernel)

theorem test1280_block_2 : Interval test1280 64 96 :=
  interval_of_check test1280 64 32 (by decide +kernel)

theorem test1280_block_3 : Interval test1280 96 121 :=
  interval_of_check test1280 96 25 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 121 :=
  (interval_append test1280 0 64 121
  (interval_append test1280 0 32 64
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 64 96 121
  test1280_block_2
  test1280_block_3))
theorem nodeInterval1280 : Interval nodeTest 1280 1401 := by
  intro i hlo hhi
  have h := test1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0065
