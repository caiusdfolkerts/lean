module
prelude
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt256 (i : Nat) := leafTest (i+256)
theorem leafTestAt256_block_0 : Interval leafTestAt256 0 1 :=
  interval_of_check leafTestAt256 0 1 (by decide +kernel)

theorem leafTestAt256_complete : Interval leafTestAt256 0 1 :=
  leafTestAt256_block_0
theorem leafInterval256 : Interval leafTest 256 257 := by
  intro i hlo hhi
  have h := leafTestAt256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
