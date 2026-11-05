module
prelude
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt4064 (i : Nat) := leafTest (i+4064)
theorem leafTestAt4064_block_0 : Interval leafTestAt4064 0 1 :=
  interval_of_check leafTestAt4064 0 1 (by decide +kernel)

theorem leafTestAt4064_block_1 : Interval leafTestAt4064 1 2 :=
  interval_of_check leafTestAt4064 1 1 (by decide +kernel)

theorem leafTestAt4064_block_2 : Interval leafTestAt4064 2 3 :=
  interval_of_check leafTestAt4064 2 1 (by decide +kernel)

theorem leafTestAt4064_block_3 : Interval leafTestAt4064 3 4 :=
  interval_of_check leafTestAt4064 3 1 (by decide +kernel)

theorem leafTestAt4064_block_4 : Interval leafTestAt4064 4 5 :=
  interval_of_check leafTestAt4064 4 1 (by decide +kernel)

theorem leafTestAt4064_block_5 : Interval leafTestAt4064 5 6 :=
  interval_of_check leafTestAt4064 5 1 (by decide +kernel)

theorem leafTestAt4064_block_6 : Interval leafTestAt4064 6 7 :=
  interval_of_check leafTestAt4064 6 1 (by decide +kernel)

theorem leafTestAt4064_block_7 : Interval leafTestAt4064 7 8 :=
  interval_of_check leafTestAt4064 7 1 (by decide +kernel)

theorem leafTestAt4064_block_8 : Interval leafTestAt4064 8 9 :=
  interval_of_check leafTestAt4064 8 1 (by decide +kernel)

theorem leafTestAt4064_block_9 : Interval leafTestAt4064 9 10 :=
  interval_of_check leafTestAt4064 9 1 (by decide +kernel)

theorem leafTestAt4064_block_10 : Interval leafTestAt4064 10 11 :=
  interval_of_check leafTestAt4064 10 1 (by decide +kernel)

theorem leafTestAt4064_block_11 : Interval leafTestAt4064 11 12 :=
  interval_of_check leafTestAt4064 11 1 (by decide +kernel)

theorem leafTestAt4064_block_12 : Interval leafTestAt4064 12 13 :=
  interval_of_check leafTestAt4064 12 1 (by decide +kernel)

theorem leafTestAt4064_block_13 : Interval leafTestAt4064 13 14 :=
  interval_of_check leafTestAt4064 13 1 (by decide +kernel)

theorem leafTestAt4064_block_14 : Interval leafTestAt4064 14 15 :=
  interval_of_check leafTestAt4064 14 1 (by decide +kernel)

theorem leafTestAt4064_block_15 : Interval leafTestAt4064 15 16 :=
  interval_of_check leafTestAt4064 15 1 (by decide +kernel)

theorem leafTestAt4064_block_16 : Interval leafTestAt4064 16 17 :=
  interval_of_check leafTestAt4064 16 1 (by decide +kernel)

theorem leafTestAt4064_block_17 : Interval leafTestAt4064 17 18 :=
  interval_of_check leafTestAt4064 17 1 (by decide +kernel)

theorem leafTestAt4064_block_18 : Interval leafTestAt4064 18 19 :=
  interval_of_check leafTestAt4064 18 1 (by decide +kernel)

theorem leafTestAt4064_block_19 : Interval leafTestAt4064 19 20 :=
  interval_of_check leafTestAt4064 19 1 (by decide +kernel)

theorem leafTestAt4064_complete : Interval leafTestAt4064 0 20 :=
  (interval_append leafTestAt4064 0 10 20
  (interval_append leafTestAt4064 0 5 10
  (interval_append leafTestAt4064 0 2 5
  (interval_append leafTestAt4064 0 1 2
  leafTestAt4064_block_0
  leafTestAt4064_block_1)
  (interval_append leafTestAt4064 2 3 5
  leafTestAt4064_block_2
  (interval_append leafTestAt4064 3 4 5
  leafTestAt4064_block_3
  leafTestAt4064_block_4)))
  (interval_append leafTestAt4064 5 7 10
  (interval_append leafTestAt4064 5 6 7
  leafTestAt4064_block_5
  leafTestAt4064_block_6)
  (interval_append leafTestAt4064 7 8 10
  leafTestAt4064_block_7
  (interval_append leafTestAt4064 8 9 10
  leafTestAt4064_block_8
  leafTestAt4064_block_9))))
  (interval_append leafTestAt4064 10 15 20
  (interval_append leafTestAt4064 10 12 15
  (interval_append leafTestAt4064 10 11 12
  leafTestAt4064_block_10
  leafTestAt4064_block_11)
  (interval_append leafTestAt4064 12 13 15
  leafTestAt4064_block_12
  (interval_append leafTestAt4064 13 14 15
  leafTestAt4064_block_13
  leafTestAt4064_block_14)))
  (interval_append leafTestAt4064 15 17 20
  (interval_append leafTestAt4064 15 16 17
  leafTestAt4064_block_15
  leafTestAt4064_block_16)
  (interval_append leafTestAt4064 17 18 20
  leafTestAt4064_block_17
  (interval_append leafTestAt4064 18 19 20
  leafTestAt4064_block_18
  leafTestAt4064_block_19)))))
theorem leafInterval4064 : Interval leafTest 4064 4084 := by
  intro i hlo hhi
  have h := leafTestAt4064_complete (i-4064) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt4064, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
