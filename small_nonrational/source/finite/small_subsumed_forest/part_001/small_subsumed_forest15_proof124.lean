module
prelude
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test79360 (i : Nat) := nodeTest (i+79360)
theorem test79360_block_0 : Interval test79360 0 16 :=
  interval_of_check test79360 0 16 (by decide +kernel)

theorem test79360_block_1 : Interval test79360 16 32 :=
  interval_of_check test79360 16 16 (by decide +kernel)

theorem test79360_block_2 : Interval test79360 32 48 :=
  interval_of_check test79360 32 16 (by decide +kernel)

theorem test79360_block_3 : Interval test79360 48 57 :=
  interval_of_check test79360 48 9 (by decide +kernel)

theorem test79360_complete : Interval test79360 0 57 :=
  (interval_append test79360 0 32 57
  (interval_append test79360 0 16 32
  test79360_block_0
  test79360_block_1)
  (interval_append test79360 32 48 57
  test79360_block_2
  test79360_block_3))
theorem nodeInterval79360 : Interval nodeTest 79360 79417 := by
  intro i hlo hhi
  have h := test79360_complete (i-79360) (Nat.zero_le _) (by omega)
  simpa only [test79360, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
