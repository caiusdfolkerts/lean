module
prelude
public import RootedSubsumedForest0301Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test23040 (i : Nat) := nodeTest (i+23040)
theorem test23040_block_0 : Interval test23040 0 16 :=
  interval_of_check test23040 0 16 (by decide +kernel)

theorem test23040_block_1 : Interval test23040 16 32 :=
  interval_of_check test23040 16 16 (by decide +kernel)

theorem test23040_block_2 : Interval test23040 32 48 :=
  interval_of_check test23040 32 16 (by decide +kernel)

theorem test23040_block_3 : Interval test23040 48 52 :=
  interval_of_check test23040 48 4 (by decide +kernel)

theorem test23040_complete : Interval test23040 0 52 :=
  (interval_append test23040 0 32 52
  (interval_append test23040 0 16 32
  test23040_block_0
  test23040_block_1)
  (interval_append test23040 32 48 52
  test23040_block_2
  test23040_block_3))
theorem nodeInterval23040 : Interval nodeTest 23040 23092 := by
  intro i hlo hhi
  have h := test23040_complete (i-23040) (Nat.zero_le _) (by omega)
  simpa only [test23040, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
