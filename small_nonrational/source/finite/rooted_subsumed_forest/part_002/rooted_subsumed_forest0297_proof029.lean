module
prelude
public import RootedSubsumedForest0297Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test18560 (i : Nat) := nodeTest (i+18560)
theorem test18560_block_0 : Interval test18560 0 16 :=
  interval_of_check test18560 0 16 (by decide +kernel)

theorem test18560_block_1 : Interval test18560 16 32 :=
  interval_of_check test18560 16 16 (by decide +kernel)

theorem test18560_block_2 : Interval test18560 32 48 :=
  interval_of_check test18560 32 16 (by decide +kernel)

theorem test18560_block_3 : Interval test18560 48 56 :=
  interval_of_check test18560 48 8 (by decide +kernel)

theorem test18560_complete : Interval test18560 0 56 :=
  (interval_append test18560 0 32 56
  (interval_append test18560 0 16 32
  test18560_block_0
  test18560_block_1)
  (interval_append test18560 32 48 56
  test18560_block_2
  test18560_block_3))
theorem nodeInterval18560 : Interval nodeTest 18560 18616 := by
  intro i hlo hhi
  have h := test18560_complete (i-18560) (Nat.zero_le _) (by omega)
  simpa only [test18560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0297
