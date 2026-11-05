module
prelude
public import RootedSubsumedForest0721Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test15360 (i : Nat) := nodeTest (i+15360)
theorem test15360_block_0 : Interval test15360 0 16 :=
  interval_of_check test15360 0 16 (by decide +kernel)

theorem test15360_block_1 : Interval test15360 16 32 :=
  interval_of_check test15360 16 16 (by decide +kernel)

theorem test15360_block_2 : Interval test15360 32 48 :=
  interval_of_check test15360 32 16 (by decide +kernel)

theorem test15360_block_3 : Interval test15360 48 64 :=
  interval_of_check test15360 48 16 (by decide +kernel)

theorem test15360_block_4 : Interval test15360 64 67 :=
  interval_of_check test15360 64 3 (by decide +kernel)

theorem test15360_complete : Interval test15360 0 67 :=
  (interval_append test15360 0 32 67
  (interval_append test15360 0 16 32
  test15360_block_0
  test15360_block_1)
  (interval_append test15360 32 48 67
  test15360_block_2
  (interval_append test15360 48 64 67
  test15360_block_3
  test15360_block_4)))
theorem nodeInterval15360 : Interval nodeTest 15360 15427 := by
  intro i hlo hhi
  have h := test15360_complete (i-15360) (Nat.zero_le _) (by omega)
  simpa only [test15360, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0721
