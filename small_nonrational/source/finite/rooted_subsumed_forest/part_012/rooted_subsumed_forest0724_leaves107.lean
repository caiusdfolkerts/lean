module
prelude
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt3424 (i : Nat) := leafTest (i+3424)
theorem leafTestAt3424_block_0 : Interval leafTestAt3424 0 1 :=
  interval_of_check leafTestAt3424 0 1 (by decide +kernel)

theorem leafTestAt3424_block_1 : Interval leafTestAt3424 1 2 :=
  interval_of_check leafTestAt3424 1 1 (by decide +kernel)

theorem leafTestAt3424_block_2 : Interval leafTestAt3424 2 3 :=
  interval_of_check leafTestAt3424 2 1 (by decide +kernel)

theorem leafTestAt3424_block_3 : Interval leafTestAt3424 3 4 :=
  interval_of_check leafTestAt3424 3 1 (by decide +kernel)

theorem leafTestAt3424_complete : Interval leafTestAt3424 0 4 :=
  (interval_append leafTestAt3424 0 2 4
  (interval_append leafTestAt3424 0 1 2
  leafTestAt3424_block_0
  leafTestAt3424_block_1)
  (interval_append leafTestAt3424 2 3 4
  leafTestAt3424_block_2
  leafTestAt3424_block_3))
theorem leafInterval3424 : Interval leafTest 3424 3428 := by
  intro i hlo hhi
  have h := leafTestAt3424_complete (i-3424) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt3424, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
