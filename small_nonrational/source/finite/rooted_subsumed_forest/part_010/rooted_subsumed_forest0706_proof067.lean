module
prelude
public import RootedSubsumedForest0706Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test42880 (i : Nat) := nodeTest (i+42880)
theorem test42880_block_0 : Interval test42880 0 16 :=
  interval_of_check test42880 0 16 (by decide +kernel)

theorem test42880_block_1 : Interval test42880 16 31 :=
  interval_of_check test42880 16 15 (by decide +kernel)

theorem test42880_complete : Interval test42880 0 31 :=
  (interval_append test42880 0 16 31
  test42880_block_0
  test42880_block_1)
theorem nodeInterval42880 : Interval nodeTest 42880 42911 := by
  intro i hlo hhi
  have h := test42880_complete (i-42880) (Nat.zero_le _) (by omega)
  simpa only [test42880, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0706
