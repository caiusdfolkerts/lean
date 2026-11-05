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
def leafTestAt3520 (i : Nat) := leafTest (i+3520)
theorem leafTestAt3520_block_0 : Interval leafTestAt3520 0 1 :=
  interval_of_check leafTestAt3520 0 1 (by decide +kernel)

theorem leafTestAt3520_block_1 : Interval leafTestAt3520 1 2 :=
  interval_of_check leafTestAt3520 1 1 (by decide +kernel)

theorem leafTestAt3520_block_2 : Interval leafTestAt3520 2 3 :=
  interval_of_check leafTestAt3520 2 1 (by decide +kernel)

theorem leafTestAt3520_block_3 : Interval leafTestAt3520 3 4 :=
  interval_of_check leafTestAt3520 3 1 (by decide +kernel)

theorem leafTestAt3520_block_4 : Interval leafTestAt3520 4 5 :=
  interval_of_check leafTestAt3520 4 1 (by decide +kernel)

theorem leafTestAt3520_block_5 : Interval leafTestAt3520 5 6 :=
  interval_of_check leafTestAt3520 5 1 (by decide +kernel)

theorem leafTestAt3520_block_6 : Interval leafTestAt3520 6 7 :=
  interval_of_check leafTestAt3520 6 1 (by decide +kernel)

theorem leafTestAt3520_block_7 : Interval leafTestAt3520 7 8 :=
  interval_of_check leafTestAt3520 7 1 (by decide +kernel)

theorem leafTestAt3520_block_8 : Interval leafTestAt3520 8 9 :=
  interval_of_check leafTestAt3520 8 1 (by decide +kernel)

theorem leafTestAt3520_block_9 : Interval leafTestAt3520 9 10 :=
  interval_of_check leafTestAt3520 9 1 (by decide +kernel)

theorem leafTestAt3520_block_10 : Interval leafTestAt3520 10 11 :=
  interval_of_check leafTestAt3520 10 1 (by decide +kernel)

theorem leafTestAt3520_block_11 : Interval leafTestAt3520 11 12 :=
  interval_of_check leafTestAt3520 11 1 (by decide +kernel)

theorem leafTestAt3520_block_12 : Interval leafTestAt3520 12 13 :=
  interval_of_check leafTestAt3520 12 1 (by decide +kernel)

theorem leafTestAt3520_block_13 : Interval leafTestAt3520 13 14 :=
  interval_of_check leafTestAt3520 13 1 (by decide +kernel)

theorem leafTestAt3520_block_14 : Interval leafTestAt3520 14 15 :=
  interval_of_check leafTestAt3520 14 1 (by decide +kernel)

theorem leafTestAt3520_block_15 : Interval leafTestAt3520 15 16 :=
  interval_of_check leafTestAt3520 15 1 (by decide +kernel)

theorem leafTestAt3520_block_16 : Interval leafTestAt3520 16 17 :=
  interval_of_check leafTestAt3520 16 1 (by decide +kernel)

theorem leafTestAt3520_block_17 : Interval leafTestAt3520 17 18 :=
  interval_of_check leafTestAt3520 17 1 (by decide +kernel)

theorem leafTestAt3520_block_18 : Interval leafTestAt3520 18 19 :=
  interval_of_check leafTestAt3520 18 1 (by decide +kernel)

theorem leafTestAt3520_block_19 : Interval leafTestAt3520 19 20 :=
  interval_of_check leafTestAt3520 19 1 (by decide +kernel)

theorem leafTestAt3520_block_20 : Interval leafTestAt3520 20 21 :=
  interval_of_check leafTestAt3520 20 1 (by decide +kernel)

theorem leafTestAt3520_block_21 : Interval leafTestAt3520 21 22 :=
  interval_of_check leafTestAt3520 21 1 (by decide +kernel)

theorem leafTestAt3520_block_22 : Interval leafTestAt3520 22 23 :=
  interval_of_check leafTestAt3520 22 1 (by decide +kernel)

theorem leafTestAt3520_block_23 : Interval leafTestAt3520 23 24 :=
  interval_of_check leafTestAt3520 23 1 (by decide +kernel)

theorem leafTestAt3520_block_24 : Interval leafTestAt3520 24 25 :=
  interval_of_check leafTestAt3520 24 1 (by decide +kernel)

theorem leafTestAt3520_block_25 : Interval leafTestAt3520 25 26 :=
  interval_of_check leafTestAt3520 25 1 (by decide +kernel)

theorem leafTestAt3520_block_26 : Interval leafTestAt3520 26 27 :=
  interval_of_check leafTestAt3520 26 1 (by decide +kernel)

theorem leafTestAt3520_block_27 : Interval leafTestAt3520 27 28 :=
  interval_of_check leafTestAt3520 27 1 (by decide +kernel)

theorem leafTestAt3520_block_28 : Interval leafTestAt3520 28 29 :=
  interval_of_check leafTestAt3520 28 1 (by decide +kernel)

theorem leafTestAt3520_block_29 : Interval leafTestAt3520 29 30 :=
  interval_of_check leafTestAt3520 29 1 (by decide +kernel)

theorem leafTestAt3520_block_30 : Interval leafTestAt3520 30 31 :=
  interval_of_check leafTestAt3520 30 1 (by decide +kernel)

theorem leafTestAt3520_block_31 : Interval leafTestAt3520 31 32 :=
  interval_of_check leafTestAt3520 31 1 (by decide +kernel)

theorem leafTestAt3520_complete : Interval leafTestAt3520 0 32 :=
  (interval_append leafTestAt3520 0 16 32
  (interval_append leafTestAt3520 0 8 16
  (interval_append leafTestAt3520 0 4 8
  (interval_append leafTestAt3520 0 2 4
  (interval_append leafTestAt3520 0 1 2
  leafTestAt3520_block_0
  leafTestAt3520_block_1)
  (interval_append leafTestAt3520 2 3 4
  leafTestAt3520_block_2
  leafTestAt3520_block_3))
  (interval_append leafTestAt3520 4 6 8
  (interval_append leafTestAt3520 4 5 6
  leafTestAt3520_block_4
  leafTestAt3520_block_5)
  (interval_append leafTestAt3520 6 7 8
  leafTestAt3520_block_6
  leafTestAt3520_block_7)))
  (interval_append leafTestAt3520 8 12 16
  (interval_append leafTestAt3520 8 10 12
  (interval_append leafTestAt3520 8 9 10
  leafTestAt3520_block_8
  leafTestAt3520_block_9)
  (interval_append leafTestAt3520 10 11 12
  leafTestAt3520_block_10
  leafTestAt3520_block_11))
  (interval_append leafTestAt3520 12 14 16
  (interval_append leafTestAt3520 12 13 14
  leafTestAt3520_block_12
  leafTestAt3520_block_13)
  (interval_append leafTestAt3520 14 15 16
  leafTestAt3520_block_14
  leafTestAt3520_block_15))))
  (interval_append leafTestAt3520 16 24 32
  (interval_append leafTestAt3520 16 20 24
  (interval_append leafTestAt3520 16 18 20
  (interval_append leafTestAt3520 16 17 18
  leafTestAt3520_block_16
  leafTestAt3520_block_17)
  (interval_append leafTestAt3520 18 19 20
  leafTestAt3520_block_18
  leafTestAt3520_block_19))
  (interval_append leafTestAt3520 20 22 24
  (interval_append leafTestAt3520 20 21 22
  leafTestAt3520_block_20
  leafTestAt3520_block_21)
  (interval_append leafTestAt3520 22 23 24
  leafTestAt3520_block_22
  leafTestAt3520_block_23)))
  (interval_append leafTestAt3520 24 28 32
  (interval_append leafTestAt3520 24 26 28
  (interval_append leafTestAt3520 24 25 26
  leafTestAt3520_block_24
  leafTestAt3520_block_25)
  (interval_append leafTestAt3520 26 27 28
  leafTestAt3520_block_26
  leafTestAt3520_block_27))
  (interval_append leafTestAt3520 28 30 32
  (interval_append leafTestAt3520 28 29 30
  leafTestAt3520_block_28
  leafTestAt3520_block_29)
  (interval_append leafTestAt3520 30 31 32
  leafTestAt3520_block_30
  leafTestAt3520_block_31)))))
theorem leafInterval3520 : Interval leafTest 3520 3552 := by
  intro i hlo hhi
  have h := leafTestAt3520_complete (i-3520) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt3520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
