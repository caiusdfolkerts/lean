module
prelude
public import RootedRawForest0088Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0088
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

theorem test1280_block_3 : Interval test1280 96 128 :=
  interval_of_check test1280 96 32 (by decide +kernel)

theorem test1280_block_4 : Interval test1280 128 160 :=
  interval_of_check test1280 128 32 (by decide +kernel)

theorem test1280_block_5 : Interval test1280 160 188 :=
  interval_of_check test1280 160 28 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 188 :=
  (interval_append test1280 0 96 188
  (interval_append test1280 0 32 96
  test1280_block_0
  (interval_append test1280 32 64 96
  test1280_block_1
  test1280_block_2))
  (interval_append test1280 96 128 188
  test1280_block_3
  (interval_append test1280 128 160 188
  test1280_block_4
  test1280_block_5)))
theorem nodeInterval1280 : Interval nodeTest 1280 1468 := by
  intro i hlo hhi
  have h := test1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0088
