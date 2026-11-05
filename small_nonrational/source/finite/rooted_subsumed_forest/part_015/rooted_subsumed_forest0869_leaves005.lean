module
prelude
public import RootedSubsumedForest0869Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt160 (i : Nat) := leafTest (i+160)
theorem leafTestAt160_block_0 : Interval leafTestAt160 0 1 :=
  interval_of_check leafTestAt160 0 1 (by decide +kernel)

theorem leafTestAt160_block_1 : Interval leafTestAt160 1 2 :=
  interval_of_check leafTestAt160 1 1 (by decide +kernel)

theorem leafTestAt160_block_2 : Interval leafTestAt160 2 3 :=
  interval_of_check leafTestAt160 2 1 (by decide +kernel)

theorem leafTestAt160_block_3 : Interval leafTestAt160 3 4 :=
  interval_of_check leafTestAt160 3 1 (by decide +kernel)

theorem leafTestAt160_block_4 : Interval leafTestAt160 4 5 :=
  interval_of_check leafTestAt160 4 1 (by decide +kernel)

theorem leafTestAt160_block_5 : Interval leafTestAt160 5 6 :=
  interval_of_check leafTestAt160 5 1 (by decide +kernel)

theorem leafTestAt160_block_6 : Interval leafTestAt160 6 7 :=
  interval_of_check leafTestAt160 6 1 (by decide +kernel)

theorem leafTestAt160_block_7 : Interval leafTestAt160 7 8 :=
  interval_of_check leafTestAt160 7 1 (by decide +kernel)

theorem leafTestAt160_block_8 : Interval leafTestAt160 8 9 :=
  interval_of_check leafTestAt160 8 1 (by decide +kernel)

theorem leafTestAt160_block_9 : Interval leafTestAt160 9 10 :=
  interval_of_check leafTestAt160 9 1 (by decide +kernel)

theorem leafTestAt160_block_10 : Interval leafTestAt160 10 11 :=
  interval_of_check leafTestAt160 10 1 (by decide +kernel)

theorem leafTestAt160_block_11 : Interval leafTestAt160 11 12 :=
  interval_of_check leafTestAt160 11 1 (by decide +kernel)

theorem leafTestAt160_block_12 : Interval leafTestAt160 12 13 :=
  interval_of_check leafTestAt160 12 1 (by decide +kernel)

theorem leafTestAt160_block_13 : Interval leafTestAt160 13 14 :=
  interval_of_check leafTestAt160 13 1 (by decide +kernel)

theorem leafTestAt160_block_14 : Interval leafTestAt160 14 15 :=
  interval_of_check leafTestAt160 14 1 (by decide +kernel)

theorem leafTestAt160_block_15 : Interval leafTestAt160 15 16 :=
  interval_of_check leafTestAt160 15 1 (by decide +kernel)

theorem leafTestAt160_block_16 : Interval leafTestAt160 16 17 :=
  interval_of_check leafTestAt160 16 1 (by decide +kernel)

theorem leafTestAt160_block_17 : Interval leafTestAt160 17 18 :=
  interval_of_check leafTestAt160 17 1 (by decide +kernel)

theorem leafTestAt160_block_18 : Interval leafTestAt160 18 19 :=
  interval_of_check leafTestAt160 18 1 (by decide +kernel)

theorem leafTestAt160_block_19 : Interval leafTestAt160 19 20 :=
  interval_of_check leafTestAt160 19 1 (by decide +kernel)

theorem leafTestAt160_block_20 : Interval leafTestAt160 20 21 :=
  interval_of_check leafTestAt160 20 1 (by decide +kernel)

theorem leafTestAt160_complete : Interval leafTestAt160 0 21 :=
  (interval_append leafTestAt160 0 10 21
  (interval_append leafTestAt160 0 5 10
  (interval_append leafTestAt160 0 2 5
  (interval_append leafTestAt160 0 1 2
  leafTestAt160_block_0
  leafTestAt160_block_1)
  (interval_append leafTestAt160 2 3 5
  leafTestAt160_block_2
  (interval_append leafTestAt160 3 4 5
  leafTestAt160_block_3
  leafTestAt160_block_4)))
  (interval_append leafTestAt160 5 7 10
  (interval_append leafTestAt160 5 6 7
  leafTestAt160_block_5
  leafTestAt160_block_6)
  (interval_append leafTestAt160 7 8 10
  leafTestAt160_block_7
  (interval_append leafTestAt160 8 9 10
  leafTestAt160_block_8
  leafTestAt160_block_9))))
  (interval_append leafTestAt160 10 15 21
  (interval_append leafTestAt160 10 12 15
  (interval_append leafTestAt160 10 11 12
  leafTestAt160_block_10
  leafTestAt160_block_11)
  (interval_append leafTestAt160 12 13 15
  leafTestAt160_block_12
  (interval_append leafTestAt160 13 14 15
  leafTestAt160_block_13
  leafTestAt160_block_14)))
  (interval_append leafTestAt160 15 18 21
  (interval_append leafTestAt160 15 16 18
  leafTestAt160_block_15
  (interval_append leafTestAt160 16 17 18
  leafTestAt160_block_16
  leafTestAt160_block_17))
  (interval_append leafTestAt160 18 19 21
  leafTestAt160_block_18
  (interval_append leafTestAt160 19 20 21
  leafTestAt160_block_19
  leafTestAt160_block_20)))))
theorem leafInterval160 : Interval leafTest 160 181 := by
  intro i hlo hhi
  have h := leafTestAt160_complete (i-160) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt160, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
