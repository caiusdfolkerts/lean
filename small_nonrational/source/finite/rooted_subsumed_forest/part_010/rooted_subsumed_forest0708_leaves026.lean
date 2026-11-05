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
def leafTestAt832 (i : Nat) := leafTest (i+832)
theorem leafTestAt832_block_0 : Interval leafTestAt832 0 1 :=
  interval_of_check leafTestAt832 0 1 (by decide +kernel)

theorem leafTestAt832_block_1 : Interval leafTestAt832 1 2 :=
  interval_of_check leafTestAt832 1 1 (by decide +kernel)

theorem leafTestAt832_block_2 : Interval leafTestAt832 2 3 :=
  interval_of_check leafTestAt832 2 1 (by decide +kernel)

theorem leafTestAt832_block_3 : Interval leafTestAt832 3 4 :=
  interval_of_check leafTestAt832 3 1 (by decide +kernel)

theorem leafTestAt832_block_4 : Interval leafTestAt832 4 5 :=
  interval_of_check leafTestAt832 4 1 (by decide +kernel)

theorem leafTestAt832_block_5 : Interval leafTestAt832 5 6 :=
  interval_of_check leafTestAt832 5 1 (by decide +kernel)

theorem leafTestAt832_block_6 : Interval leafTestAt832 6 7 :=
  interval_of_check leafTestAt832 6 1 (by decide +kernel)

theorem leafTestAt832_block_7 : Interval leafTestAt832 7 8 :=
  interval_of_check leafTestAt832 7 1 (by decide +kernel)

theorem leafTestAt832_block_8 : Interval leafTestAt832 8 9 :=
  interval_of_check leafTestAt832 8 1 (by decide +kernel)

theorem leafTestAt832_block_9 : Interval leafTestAt832 9 10 :=
  interval_of_check leafTestAt832 9 1 (by decide +kernel)

theorem leafTestAt832_block_10 : Interval leafTestAt832 10 11 :=
  interval_of_check leafTestAt832 10 1 (by decide +kernel)

theorem leafTestAt832_block_11 : Interval leafTestAt832 11 12 :=
  interval_of_check leafTestAt832 11 1 (by decide +kernel)

theorem leafTestAt832_block_12 : Interval leafTestAt832 12 13 :=
  interval_of_check leafTestAt832 12 1 (by decide +kernel)

theorem leafTestAt832_block_13 : Interval leafTestAt832 13 14 :=
  interval_of_check leafTestAt832 13 1 (by decide +kernel)

theorem leafTestAt832_block_14 : Interval leafTestAt832 14 15 :=
  interval_of_check leafTestAt832 14 1 (by decide +kernel)

theorem leafTestAt832_block_15 : Interval leafTestAt832 15 16 :=
  interval_of_check leafTestAt832 15 1 (by decide +kernel)

theorem leafTestAt832_block_16 : Interval leafTestAt832 16 17 :=
  interval_of_check leafTestAt832 16 1 (by decide +kernel)

theorem leafTestAt832_block_17 : Interval leafTestAt832 17 18 :=
  interval_of_check leafTestAt832 17 1 (by decide +kernel)

theorem leafTestAt832_block_18 : Interval leafTestAt832 18 19 :=
  interval_of_check leafTestAt832 18 1 (by decide +kernel)

theorem leafTestAt832_block_19 : Interval leafTestAt832 19 20 :=
  interval_of_check leafTestAt832 19 1 (by decide +kernel)

theorem leafTestAt832_block_20 : Interval leafTestAt832 20 21 :=
  interval_of_check leafTestAt832 20 1 (by decide +kernel)

theorem leafTestAt832_block_21 : Interval leafTestAt832 21 22 :=
  interval_of_check leafTestAt832 21 1 (by decide +kernel)

theorem leafTestAt832_block_22 : Interval leafTestAt832 22 23 :=
  interval_of_check leafTestAt832 22 1 (by decide +kernel)

theorem leafTestAt832_block_23 : Interval leafTestAt832 23 24 :=
  interval_of_check leafTestAt832 23 1 (by decide +kernel)

theorem leafTestAt832_block_24 : Interval leafTestAt832 24 25 :=
  interval_of_check leafTestAt832 24 1 (by decide +kernel)

theorem leafTestAt832_block_25 : Interval leafTestAt832 25 26 :=
  interval_of_check leafTestAt832 25 1 (by decide +kernel)

theorem leafTestAt832_block_26 : Interval leafTestAt832 26 27 :=
  interval_of_check leafTestAt832 26 1 (by decide +kernel)

theorem leafTestAt832_block_27 : Interval leafTestAt832 27 28 :=
  interval_of_check leafTestAt832 27 1 (by decide +kernel)

theorem leafTestAt832_block_28 : Interval leafTestAt832 28 29 :=
  interval_of_check leafTestAt832 28 1 (by decide +kernel)

theorem leafTestAt832_block_29 : Interval leafTestAt832 29 30 :=
  interval_of_check leafTestAt832 29 1 (by decide +kernel)

theorem leafTestAt832_block_30 : Interval leafTestAt832 30 31 :=
  interval_of_check leafTestAt832 30 1 (by decide +kernel)

theorem leafTestAt832_block_31 : Interval leafTestAt832 31 32 :=
  interval_of_check leafTestAt832 31 1 (by decide +kernel)

theorem leafTestAt832_complete : Interval leafTestAt832 0 32 :=
  (interval_append leafTestAt832 0 16 32
  (interval_append leafTestAt832 0 8 16
  (interval_append leafTestAt832 0 4 8
  (interval_append leafTestAt832 0 2 4
  (interval_append leafTestAt832 0 1 2
  leafTestAt832_block_0
  leafTestAt832_block_1)
  (interval_append leafTestAt832 2 3 4
  leafTestAt832_block_2
  leafTestAt832_block_3))
  (interval_append leafTestAt832 4 6 8
  (interval_append leafTestAt832 4 5 6
  leafTestAt832_block_4
  leafTestAt832_block_5)
  (interval_append leafTestAt832 6 7 8
  leafTestAt832_block_6
  leafTestAt832_block_7)))
  (interval_append leafTestAt832 8 12 16
  (interval_append leafTestAt832 8 10 12
  (interval_append leafTestAt832 8 9 10
  leafTestAt832_block_8
  leafTestAt832_block_9)
  (interval_append leafTestAt832 10 11 12
  leafTestAt832_block_10
  leafTestAt832_block_11))
  (interval_append leafTestAt832 12 14 16
  (interval_append leafTestAt832 12 13 14
  leafTestAt832_block_12
  leafTestAt832_block_13)
  (interval_append leafTestAt832 14 15 16
  leafTestAt832_block_14
  leafTestAt832_block_15))))
  (interval_append leafTestAt832 16 24 32
  (interval_append leafTestAt832 16 20 24
  (interval_append leafTestAt832 16 18 20
  (interval_append leafTestAt832 16 17 18
  leafTestAt832_block_16
  leafTestAt832_block_17)
  (interval_append leafTestAt832 18 19 20
  leafTestAt832_block_18
  leafTestAt832_block_19))
  (interval_append leafTestAt832 20 22 24
  (interval_append leafTestAt832 20 21 22
  leafTestAt832_block_20
  leafTestAt832_block_21)
  (interval_append leafTestAt832 22 23 24
  leafTestAt832_block_22
  leafTestAt832_block_23)))
  (interval_append leafTestAt832 24 28 32
  (interval_append leafTestAt832 24 26 28
  (interval_append leafTestAt832 24 25 26
  leafTestAt832_block_24
  leafTestAt832_block_25)
  (interval_append leafTestAt832 26 27 28
  leafTestAt832_block_26
  leafTestAt832_block_27))
  (interval_append leafTestAt832 28 30 32
  (interval_append leafTestAt832 28 29 30
  leafTestAt832_block_28
  leafTestAt832_block_29)
  (interval_append leafTestAt832 30 31 32
  leafTestAt832_block_30
  leafTestAt832_block_31)))))
theorem leafInterval832 : Interval leafTest 832 864 := by
  intro i hlo hhi
  have h := leafTestAt832_complete (i-832) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt832, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
