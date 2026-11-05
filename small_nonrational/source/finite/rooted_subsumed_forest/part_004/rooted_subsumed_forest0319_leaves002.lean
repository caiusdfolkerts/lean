module
prelude
public import RootedSubsumedForest0319Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt64 (i : Nat) := leafTest (i+64)
theorem leafTestAt64_block_0 : Interval leafTestAt64 0 1 :=
  interval_of_check leafTestAt64 0 1 (by decide +kernel)

theorem leafTestAt64_block_1 : Interval leafTestAt64 1 2 :=
  interval_of_check leafTestAt64 1 1 (by decide +kernel)

theorem leafTestAt64_block_2 : Interval leafTestAt64 2 3 :=
  interval_of_check leafTestAt64 2 1 (by decide +kernel)

theorem leafTestAt64_block_3 : Interval leafTestAt64 3 4 :=
  interval_of_check leafTestAt64 3 1 (by decide +kernel)

theorem leafTestAt64_block_4 : Interval leafTestAt64 4 5 :=
  interval_of_check leafTestAt64 4 1 (by decide +kernel)

theorem leafTestAt64_complete : Interval leafTestAt64 0 5 :=
  (interval_append leafTestAt64 0 2 5
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 5
  leafTestAt64_block_2
  (interval_append leafTestAt64 3 4 5
  leafTestAt64_block_3
  leafTestAt64_block_4)))
theorem leafInterval64 : Interval leafTest 64 69 := by
  intro i hlo hhi
  have h := leafTestAt64_complete (i-64) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt64, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0319
