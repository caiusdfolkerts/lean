module
prelude
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt128 (i : Nat) := leafTest (i+128)
theorem leafTestAt128_block_0 : Interval leafTestAt128 0 1 :=
  interval_of_check leafTestAt128 0 1 (by decide +kernel)

theorem leafTestAt128_block_1 : Interval leafTestAt128 1 2 :=
  interval_of_check leafTestAt128 1 1 (by decide +kernel)

theorem leafTestAt128_block_2 : Interval leafTestAt128 2 3 :=
  interval_of_check leafTestAt128 2 1 (by decide +kernel)

theorem leafTestAt128_block_3 : Interval leafTestAt128 3 4 :=
  interval_of_check leafTestAt128 3 1 (by decide +kernel)

theorem leafTestAt128_block_4 : Interval leafTestAt128 4 5 :=
  interval_of_check leafTestAt128 4 1 (by decide +kernel)

theorem leafTestAt128_complete : Interval leafTestAt128 0 5 :=
  (interval_append leafTestAt128 0 2 5
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 5
  leafTestAt128_block_2
  (interval_append leafTestAt128 3 4 5
  leafTestAt128_block_3
  leafTestAt128_block_4)))
theorem leafInterval128 : Interval leafTest 128 133 := by
  intro i hlo hhi
  have h := leafTestAt128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
