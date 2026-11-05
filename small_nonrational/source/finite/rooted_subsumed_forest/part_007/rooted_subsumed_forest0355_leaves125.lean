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
def leafTestAt4000 (i : Nat) := leafTest (i+4000)
theorem leafTestAt4000_block_0 : Interval leafTestAt4000 0 1 :=
  interval_of_check leafTestAt4000 0 1 (by decide +kernel)

theorem leafTestAt4000_block_1 : Interval leafTestAt4000 1 2 :=
  interval_of_check leafTestAt4000 1 1 (by decide +kernel)

theorem leafTestAt4000_block_2 : Interval leafTestAt4000 2 3 :=
  interval_of_check leafTestAt4000 2 1 (by decide +kernel)

theorem leafTestAt4000_block_3 : Interval leafTestAt4000 3 4 :=
  interval_of_check leafTestAt4000 3 1 (by decide +kernel)

theorem leafTestAt4000_block_4 : Interval leafTestAt4000 4 5 :=
  interval_of_check leafTestAt4000 4 1 (by decide +kernel)

theorem leafTestAt4000_block_5 : Interval leafTestAt4000 5 6 :=
  interval_of_check leafTestAt4000 5 1 (by decide +kernel)

theorem leafTestAt4000_block_6 : Interval leafTestAt4000 6 7 :=
  interval_of_check leafTestAt4000 6 1 (by decide +kernel)

theorem leafTestAt4000_block_7 : Interval leafTestAt4000 7 8 :=
  interval_of_check leafTestAt4000 7 1 (by decide +kernel)

theorem leafTestAt4000_block_8 : Interval leafTestAt4000 8 9 :=
  interval_of_check leafTestAt4000 8 1 (by decide +kernel)

theorem leafTestAt4000_block_9 : Interval leafTestAt4000 9 10 :=
  interval_of_check leafTestAt4000 9 1 (by decide +kernel)

theorem leafTestAt4000_block_10 : Interval leafTestAt4000 10 11 :=
  interval_of_check leafTestAt4000 10 1 (by decide +kernel)

theorem leafTestAt4000_block_11 : Interval leafTestAt4000 11 12 :=
  interval_of_check leafTestAt4000 11 1 (by decide +kernel)

theorem leafTestAt4000_block_12 : Interval leafTestAt4000 12 13 :=
  interval_of_check leafTestAt4000 12 1 (by decide +kernel)

theorem leafTestAt4000_block_13 : Interval leafTestAt4000 13 14 :=
  interval_of_check leafTestAt4000 13 1 (by decide +kernel)

theorem leafTestAt4000_block_14 : Interval leafTestAt4000 14 15 :=
  interval_of_check leafTestAt4000 14 1 (by decide +kernel)

theorem leafTestAt4000_block_15 : Interval leafTestAt4000 15 16 :=
  interval_of_check leafTestAt4000 15 1 (by decide +kernel)

theorem leafTestAt4000_block_16 : Interval leafTestAt4000 16 17 :=
  interval_of_check leafTestAt4000 16 1 (by decide +kernel)

theorem leafTestAt4000_block_17 : Interval leafTestAt4000 17 18 :=
  interval_of_check leafTestAt4000 17 1 (by decide +kernel)

theorem leafTestAt4000_block_18 : Interval leafTestAt4000 18 19 :=
  interval_of_check leafTestAt4000 18 1 (by decide +kernel)

theorem leafTestAt4000_block_19 : Interval leafTestAt4000 19 20 :=
  interval_of_check leafTestAt4000 19 1 (by decide +kernel)

theorem leafTestAt4000_block_20 : Interval leafTestAt4000 20 21 :=
  interval_of_check leafTestAt4000 20 1 (by decide +kernel)

theorem leafTestAt4000_block_21 : Interval leafTestAt4000 21 22 :=
  interval_of_check leafTestAt4000 21 1 (by decide +kernel)

theorem leafTestAt4000_block_22 : Interval leafTestAt4000 22 23 :=
  interval_of_check leafTestAt4000 22 1 (by decide +kernel)

theorem leafTestAt4000_block_23 : Interval leafTestAt4000 23 24 :=
  interval_of_check leafTestAt4000 23 1 (by decide +kernel)

theorem leafTestAt4000_block_24 : Interval leafTestAt4000 24 25 :=
  interval_of_check leafTestAt4000 24 1 (by decide +kernel)

theorem leafTestAt4000_block_25 : Interval leafTestAt4000 25 26 :=
  interval_of_check leafTestAt4000 25 1 (by decide +kernel)

theorem leafTestAt4000_block_26 : Interval leafTestAt4000 26 27 :=
  interval_of_check leafTestAt4000 26 1 (by decide +kernel)

theorem leafTestAt4000_block_27 : Interval leafTestAt4000 27 28 :=
  interval_of_check leafTestAt4000 27 1 (by decide +kernel)

theorem leafTestAt4000_block_28 : Interval leafTestAt4000 28 29 :=
  interval_of_check leafTestAt4000 28 1 (by decide +kernel)

theorem leafTestAt4000_block_29 : Interval leafTestAt4000 29 30 :=
  interval_of_check leafTestAt4000 29 1 (by decide +kernel)

theorem leafTestAt4000_block_30 : Interval leafTestAt4000 30 31 :=
  interval_of_check leafTestAt4000 30 1 (by decide +kernel)

theorem leafTestAt4000_block_31 : Interval leafTestAt4000 31 32 :=
  interval_of_check leafTestAt4000 31 1 (by decide +kernel)

theorem leafTestAt4000_complete : Interval leafTestAt4000 0 32 :=
  (interval_append leafTestAt4000 0 16 32
  (interval_append leafTestAt4000 0 8 16
  (interval_append leafTestAt4000 0 4 8
  (interval_append leafTestAt4000 0 2 4
  (interval_append leafTestAt4000 0 1 2
  leafTestAt4000_block_0
  leafTestAt4000_block_1)
  (interval_append leafTestAt4000 2 3 4
  leafTestAt4000_block_2
  leafTestAt4000_block_3))
  (interval_append leafTestAt4000 4 6 8
  (interval_append leafTestAt4000 4 5 6
  leafTestAt4000_block_4
  leafTestAt4000_block_5)
  (interval_append leafTestAt4000 6 7 8
  leafTestAt4000_block_6
  leafTestAt4000_block_7)))
  (interval_append leafTestAt4000 8 12 16
  (interval_append leafTestAt4000 8 10 12
  (interval_append leafTestAt4000 8 9 10
  leafTestAt4000_block_8
  leafTestAt4000_block_9)
  (interval_append leafTestAt4000 10 11 12
  leafTestAt4000_block_10
  leafTestAt4000_block_11))
  (interval_append leafTestAt4000 12 14 16
  (interval_append leafTestAt4000 12 13 14
  leafTestAt4000_block_12
  leafTestAt4000_block_13)
  (interval_append leafTestAt4000 14 15 16
  leafTestAt4000_block_14
  leafTestAt4000_block_15))))
  (interval_append leafTestAt4000 16 24 32
  (interval_append leafTestAt4000 16 20 24
  (interval_append leafTestAt4000 16 18 20
  (interval_append leafTestAt4000 16 17 18
  leafTestAt4000_block_16
  leafTestAt4000_block_17)
  (interval_append leafTestAt4000 18 19 20
  leafTestAt4000_block_18
  leafTestAt4000_block_19))
  (interval_append leafTestAt4000 20 22 24
  (interval_append leafTestAt4000 20 21 22
  leafTestAt4000_block_20
  leafTestAt4000_block_21)
  (interval_append leafTestAt4000 22 23 24
  leafTestAt4000_block_22
  leafTestAt4000_block_23)))
  (interval_append leafTestAt4000 24 28 32
  (interval_append leafTestAt4000 24 26 28
  (interval_append leafTestAt4000 24 25 26
  leafTestAt4000_block_24
  leafTestAt4000_block_25)
  (interval_append leafTestAt4000 26 27 28
  leafTestAt4000_block_26
  leafTestAt4000_block_27))
  (interval_append leafTestAt4000 28 30 32
  (interval_append leafTestAt4000 28 29 30
  leafTestAt4000_block_28
  leafTestAt4000_block_29)
  (interval_append leafTestAt4000 30 31 32
  leafTestAt4000_block_30
  leafTestAt4000_block_31)))))
theorem leafInterval4000 : Interval leafTest 4000 4032 := by
  intro i hlo hhi
  have h := leafTestAt4000_complete (i-4000) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt4000, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
