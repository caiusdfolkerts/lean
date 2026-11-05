module
prelude
public import RootedSubsumedForest0282Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3840 (i : Nat) := nodeTest (i+3840)
theorem test3840_block_0 : Interval test3840 0 16 :=
  interval_of_check test3840 0 16 (by decide +kernel)

theorem test3840_block_1 : Interval test3840 16 32 :=
  interval_of_check test3840 16 16 (by decide +kernel)

theorem test3840_block_2 : Interval test3840 32 48 :=
  interval_of_check test3840 32 16 (by decide +kernel)

theorem test3840_block_3 : Interval test3840 48 64 :=
  interval_of_check test3840 48 16 (by decide +kernel)

theorem test3840_complete : Interval test3840 0 64 :=
  (interval_append test3840 0 32 64
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 64
  test3840_block_2
  test3840_block_3))
theorem nodeInterval3840 : Interval nodeTest 3840 3904 := by
  intro i hlo hhi
  have h := test3840_complete (i-3840) (Nat.zero_le _) (by omega)
  simpa only [test3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0282
