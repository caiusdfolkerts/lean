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
def leafTestAt576 (i : Nat) := leafTest (i+576)
theorem leafTestAt576_block_0 : Interval leafTestAt576 0 1 :=
  interval_of_check leafTestAt576 0 1 (by decide +kernel)

theorem leafTestAt576_block_1 : Interval leafTestAt576 1 2 :=
  interval_of_check leafTestAt576 1 1 (by decide +kernel)

theorem leafTestAt576_complete : Interval leafTestAt576 0 2 :=
  (interval_append leafTestAt576 0 1 2
  leafTestAt576_block_0
  leafTestAt576_block_1)
theorem leafInterval576 : Interval leafTest 576 578 := by
  intro i hlo hhi
  have h := leafTestAt576_complete (i-576) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt576, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
