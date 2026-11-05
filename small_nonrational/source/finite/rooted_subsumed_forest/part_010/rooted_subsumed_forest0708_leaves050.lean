module
prelude
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt1600 (i : Nat) := leafTest (i+1600)
theorem leafTestAt1600_block_0 : Interval leafTestAt1600 0 1 :=
  interval_of_check leafTestAt1600 0 1 (by decide +kernel)

theorem leafTestAt1600_block_1 : Interval leafTestAt1600 1 2 :=
  interval_of_check leafTestAt1600 1 1 (by decide +kernel)

theorem leafTestAt1600_block_2 : Interval leafTestAt1600 2 3 :=
  interval_of_check leafTestAt1600 2 1 (by decide +kernel)

theorem leafTestAt1600_block_3 : Interval leafTestAt1600 3 4 :=
  interval_of_check leafTestAt1600 3 1 (by decide +kernel)

theorem leafTestAt1600_block_4 : Interval leafTestAt1600 4 5 :=
  interval_of_check leafTestAt1600 4 1 (by decide +kernel)

theorem leafTestAt1600_block_5 : Interval leafTestAt1600 5 6 :=
  interval_of_check leafTestAt1600 5 1 (by decide +kernel)

theorem leafTestAt1600_block_6 : Interval leafTestAt1600 6 7 :=
  interval_of_check leafTestAt1600 6 1 (by decide +kernel)

theorem leafTestAt1600_block_7 : Interval leafTestAt1600 7 8 :=
  interval_of_check leafTestAt1600 7 1 (by decide +kernel)

theorem leafTestAt1600_block_8 : Interval leafTestAt1600 8 9 :=
  interval_of_check leafTestAt1600 8 1 (by decide +kernel)

theorem leafTestAt1600_block_9 : Interval leafTestAt1600 9 10 :=
  interval_of_check leafTestAt1600 9 1 (by decide +kernel)

theorem leafTestAt1600_block_10 : Interval leafTestAt1600 10 11 :=
  interval_of_check leafTestAt1600 10 1 (by decide +kernel)

theorem leafTestAt1600_block_11 : Interval leafTestAt1600 11 12 :=
  interval_of_check leafTestAt1600 11 1 (by decide +kernel)

theorem leafTestAt1600_block_12 : Interval leafTestAt1600 12 13 :=
  interval_of_check leafTestAt1600 12 1 (by decide +kernel)

theorem leafTestAt1600_block_13 : Interval leafTestAt1600 13 14 :=
  interval_of_check leafTestAt1600 13 1 (by decide +kernel)

theorem leafTestAt1600_block_14 : Interval leafTestAt1600 14 15 :=
  interval_of_check leafTestAt1600 14 1 (by decide +kernel)

theorem leafTestAt1600_block_15 : Interval leafTestAt1600 15 16 :=
  interval_of_check leafTestAt1600 15 1 (by decide +kernel)

theorem leafTestAt1600_block_16 : Interval leafTestAt1600 16 17 :=
  interval_of_check leafTestAt1600 16 1 (by decide +kernel)

theorem leafTestAt1600_block_17 : Interval leafTestAt1600 17 18 :=
  interval_of_check leafTestAt1600 17 1 (by decide +kernel)

theorem leafTestAt1600_block_18 : Interval leafTestAt1600 18 19 :=
  interval_of_check leafTestAt1600 18 1 (by decide +kernel)

theorem leafTestAt1600_block_19 : Interval leafTestAt1600 19 20 :=
  interval_of_check leafTestAt1600 19 1 (by decide +kernel)

theorem leafTestAt1600_block_20 : Interval leafTestAt1600 20 21 :=
  interval_of_check leafTestAt1600 20 1 (by decide +kernel)

theorem leafTestAt1600_block_21 : Interval leafTestAt1600 21 22 :=
  interval_of_check leafTestAt1600 21 1 (by decide +kernel)

theorem leafTestAt1600_block_22 : Interval leafTestAt1600 22 23 :=
  interval_of_check leafTestAt1600 22 1 (by decide +kernel)

theorem leafTestAt1600_block_23 : Interval leafTestAt1600 23 24 :=
  interval_of_check leafTestAt1600 23 1 (by decide +kernel)

theorem leafTestAt1600_block_24 : Interval leafTestAt1600 24 25 :=
  interval_of_check leafTestAt1600 24 1 (by decide +kernel)

theorem leafTestAt1600_block_25 : Interval leafTestAt1600 25 26 :=
  interval_of_check leafTestAt1600 25 1 (by decide +kernel)

theorem leafTestAt1600_block_26 : Interval leafTestAt1600 26 27 :=
  interval_of_check leafTestAt1600 26 1 (by decide +kernel)

theorem leafTestAt1600_block_27 : Interval leafTestAt1600 27 28 :=
  interval_of_check leafTestAt1600 27 1 (by decide +kernel)

theorem leafTestAt1600_block_28 : Interval leafTestAt1600 28 29 :=
  interval_of_check leafTestAt1600 28 1 (by decide +kernel)

theorem leafTestAt1600_block_29 : Interval leafTestAt1600 29 30 :=
  interval_of_check leafTestAt1600 29 1 (by decide +kernel)

theorem leafTestAt1600_block_30 : Interval leafTestAt1600 30 31 :=
  interval_of_check leafTestAt1600 30 1 (by decide +kernel)

theorem leafTestAt1600_complete : Interval leafTestAt1600 0 31 :=
  (interval_append leafTestAt1600 0 15 31
  (interval_append leafTestAt1600 0 7 15
  (interval_append leafTestAt1600 0 3 7
  (interval_append leafTestAt1600 0 1 3
  leafTestAt1600_block_0
  (interval_append leafTestAt1600 1 2 3
  leafTestAt1600_block_1
  leafTestAt1600_block_2))
  (interval_append leafTestAt1600 3 5 7
  (interval_append leafTestAt1600 3 4 5
  leafTestAt1600_block_3
  leafTestAt1600_block_4)
  (interval_append leafTestAt1600 5 6 7
  leafTestAt1600_block_5
  leafTestAt1600_block_6)))
  (interval_append leafTestAt1600 7 11 15
  (interval_append leafTestAt1600 7 9 11
  (interval_append leafTestAt1600 7 8 9
  leafTestAt1600_block_7
  leafTestAt1600_block_8)
  (interval_append leafTestAt1600 9 10 11
  leafTestAt1600_block_9
  leafTestAt1600_block_10))
  (interval_append leafTestAt1600 11 13 15
  (interval_append leafTestAt1600 11 12 13
  leafTestAt1600_block_11
  leafTestAt1600_block_12)
  (interval_append leafTestAt1600 13 14 15
  leafTestAt1600_block_13
  leafTestAt1600_block_14))))
  (interval_append leafTestAt1600 15 23 31
  (interval_append leafTestAt1600 15 19 23
  (interval_append leafTestAt1600 15 17 19
  (interval_append leafTestAt1600 15 16 17
  leafTestAt1600_block_15
  leafTestAt1600_block_16)
  (interval_append leafTestAt1600 17 18 19
  leafTestAt1600_block_17
  leafTestAt1600_block_18))
  (interval_append leafTestAt1600 19 21 23
  (interval_append leafTestAt1600 19 20 21
  leafTestAt1600_block_19
  leafTestAt1600_block_20)
  (interval_append leafTestAt1600 21 22 23
  leafTestAt1600_block_21
  leafTestAt1600_block_22)))
  (interval_append leafTestAt1600 23 27 31
  (interval_append leafTestAt1600 23 25 27
  (interval_append leafTestAt1600 23 24 25
  leafTestAt1600_block_23
  leafTestAt1600_block_24)
  (interval_append leafTestAt1600 25 26 27
  leafTestAt1600_block_25
  leafTestAt1600_block_26))
  (interval_append leafTestAt1600 27 29 31
  (interval_append leafTestAt1600 27 28 29
  leafTestAt1600_block_27
  leafTestAt1600_block_28)
  (interval_append leafTestAt1600 29 30 31
  leafTestAt1600_block_29
  leafTestAt1600_block_30)))))
theorem leafInterval1600 : Interval leafTest 1600 1631 := by
  intro i hlo hhi
  have h := leafTestAt1600_complete (i-1600) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt1600, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
