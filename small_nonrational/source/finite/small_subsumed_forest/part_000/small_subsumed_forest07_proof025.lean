module
prelude
public import SmallSubsumedForest07Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test16000 (i : Nat) := nodeTest (i+16000)
theorem test16000_block_0 : Interval test16000 0 16 :=
  interval_of_check test16000 0 16 (by decide +kernel)

theorem test16000_block_1 : Interval test16000 16 21 :=
  interval_of_check test16000 16 5 (by decide +kernel)

theorem test16000_complete : Interval test16000 0 21 :=
  (interval_append test16000 0 16 21
  test16000_block_0
  test16000_block_1)
theorem nodeInterval16000 : Interval nodeTest 16000 16021 := by
  intro i hlo hhi
  have h := test16000_complete (i-16000) (Nat.zero_le _) (by omega)
  simpa only [test16000, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
