module
prelude
public import RootedSubsumedForest0740Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test10240 (i : Nat) := nodeTest (i+10240)
theorem test10240_block_0 : Interval test10240 0 16 :=
  interval_of_check test10240 0 16 (by decide +kernel)

theorem test10240_block_1 : Interval test10240 16 32 :=
  interval_of_check test10240 16 16 (by decide +kernel)

theorem test10240_block_2 : Interval test10240 32 41 :=
  interval_of_check test10240 32 9 (by decide +kernel)

theorem test10240_complete : Interval test10240 0 41 :=
  (interval_append test10240 0 16 41
  test10240_block_0
  (interval_append test10240 16 32 41
  test10240_block_1
  test10240_block_2))
theorem nodeInterval10240 : Interval nodeTest 10240 10281 := by
  intro i hlo hhi
  have h := test10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [test10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0740
