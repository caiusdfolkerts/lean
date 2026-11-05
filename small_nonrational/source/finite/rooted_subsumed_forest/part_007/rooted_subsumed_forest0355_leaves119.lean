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
def leafTestAt3808 (i : Nat) := leafTest (i+3808)
theorem leafTestAt3808_block_0 : Interval leafTestAt3808 0 1 :=
  interval_of_check leafTestAt3808 0 1 (by decide +kernel)

theorem leafTestAt3808_block_1 : Interval leafTestAt3808 1 2 :=
  interval_of_check leafTestAt3808 1 1 (by decide +kernel)

theorem leafTestAt3808_block_2 : Interval leafTestAt3808 2 3 :=
  interval_of_check leafTestAt3808 2 1 (by decide +kernel)

theorem leafTestAt3808_block_3 : Interval leafTestAt3808 3 4 :=
  interval_of_check leafTestAt3808 3 1 (by decide +kernel)

theorem leafTestAt3808_block_4 : Interval leafTestAt3808 4 5 :=
  interval_of_check leafTestAt3808 4 1 (by decide +kernel)

theorem leafTestAt3808_block_5 : Interval leafTestAt3808 5 6 :=
  interval_of_check leafTestAt3808 5 1 (by decide +kernel)

theorem leafTestAt3808_block_6 : Interval leafTestAt3808 6 7 :=
  interval_of_check leafTestAt3808 6 1 (by decide +kernel)

theorem leafTestAt3808_block_7 : Interval leafTestAt3808 7 8 :=
  interval_of_check leafTestAt3808 7 1 (by decide +kernel)

theorem leafTestAt3808_block_8 : Interval leafTestAt3808 8 9 :=
  interval_of_check leafTestAt3808 8 1 (by decide +kernel)

theorem leafTestAt3808_block_9 : Interval leafTestAt3808 9 10 :=
  interval_of_check leafTestAt3808 9 1 (by decide +kernel)

theorem leafTestAt3808_block_10 : Interval leafTestAt3808 10 11 :=
  interval_of_check leafTestAt3808 10 1 (by decide +kernel)

theorem leafTestAt3808_block_11 : Interval leafTestAt3808 11 12 :=
  interval_of_check leafTestAt3808 11 1 (by decide +kernel)

theorem leafTestAt3808_block_12 : Interval leafTestAt3808 12 13 :=
  interval_of_check leafTestAt3808 12 1 (by decide +kernel)

theorem leafTestAt3808_block_13 : Interval leafTestAt3808 13 14 :=
  interval_of_check leafTestAt3808 13 1 (by decide +kernel)

theorem leafTestAt3808_block_14 : Interval leafTestAt3808 14 15 :=
  interval_of_check leafTestAt3808 14 1 (by decide +kernel)

theorem leafTestAt3808_block_15 : Interval leafTestAt3808 15 16 :=
  interval_of_check leafTestAt3808 15 1 (by decide +kernel)

theorem leafTestAt3808_block_16 : Interval leafTestAt3808 16 17 :=
  interval_of_check leafTestAt3808 16 1 (by decide +kernel)

theorem leafTestAt3808_block_17 : Interval leafTestAt3808 17 18 :=
  interval_of_check leafTestAt3808 17 1 (by decide +kernel)

theorem leafTestAt3808_block_18 : Interval leafTestAt3808 18 19 :=
  interval_of_check leafTestAt3808 18 1 (by decide +kernel)

theorem leafTestAt3808_block_19 : Interval leafTestAt3808 19 20 :=
  interval_of_check leafTestAt3808 19 1 (by decide +kernel)

theorem leafTestAt3808_block_20 : Interval leafTestAt3808 20 21 :=
  interval_of_check leafTestAt3808 20 1 (by decide +kernel)

theorem leafTestAt3808_block_21 : Interval leafTestAt3808 21 22 :=
  interval_of_check leafTestAt3808 21 1 (by decide +kernel)

theorem leafTestAt3808_block_22 : Interval leafTestAt3808 22 23 :=
  interval_of_check leafTestAt3808 22 1 (by decide +kernel)

theorem leafTestAt3808_block_23 : Interval leafTestAt3808 23 24 :=
  interval_of_check leafTestAt3808 23 1 (by decide +kernel)

theorem leafTestAt3808_block_24 : Interval leafTestAt3808 24 25 :=
  interval_of_check leafTestAt3808 24 1 (by decide +kernel)

theorem leafTestAt3808_block_25 : Interval leafTestAt3808 25 26 :=
  interval_of_check leafTestAt3808 25 1 (by decide +kernel)

theorem leafTestAt3808_block_26 : Interval leafTestAt3808 26 27 :=
  interval_of_check leafTestAt3808 26 1 (by decide +kernel)

theorem leafTestAt3808_block_27 : Interval leafTestAt3808 27 28 :=
  interval_of_check leafTestAt3808 27 1 (by decide +kernel)

theorem leafTestAt3808_block_28 : Interval leafTestAt3808 28 29 :=
  interval_of_check leafTestAt3808 28 1 (by decide +kernel)

theorem leafTestAt3808_block_29 : Interval leafTestAt3808 29 30 :=
  interval_of_check leafTestAt3808 29 1 (by decide +kernel)

theorem leafTestAt3808_block_30 : Interval leafTestAt3808 30 31 :=
  interval_of_check leafTestAt3808 30 1 (by decide +kernel)

theorem leafTestAt3808_block_31 : Interval leafTestAt3808 31 32 :=
  interval_of_check leafTestAt3808 31 1 (by decide +kernel)

theorem leafTestAt3808_complete : Interval leafTestAt3808 0 32 :=
  (interval_append leafTestAt3808 0 16 32
  (interval_append leafTestAt3808 0 8 16
  (interval_append leafTestAt3808 0 4 8
  (interval_append leafTestAt3808 0 2 4
  (interval_append leafTestAt3808 0 1 2
  leafTestAt3808_block_0
  leafTestAt3808_block_1)
  (interval_append leafTestAt3808 2 3 4
  leafTestAt3808_block_2
  leafTestAt3808_block_3))
  (interval_append leafTestAt3808 4 6 8
  (interval_append leafTestAt3808 4 5 6
  leafTestAt3808_block_4
  leafTestAt3808_block_5)
  (interval_append leafTestAt3808 6 7 8
  leafTestAt3808_block_6
  leafTestAt3808_block_7)))
  (interval_append leafTestAt3808 8 12 16
  (interval_append leafTestAt3808 8 10 12
  (interval_append leafTestAt3808 8 9 10
  leafTestAt3808_block_8
  leafTestAt3808_block_9)
  (interval_append leafTestAt3808 10 11 12
  leafTestAt3808_block_10
  leafTestAt3808_block_11))
  (interval_append leafTestAt3808 12 14 16
  (interval_append leafTestAt3808 12 13 14
  leafTestAt3808_block_12
  leafTestAt3808_block_13)
  (interval_append leafTestAt3808 14 15 16
  leafTestAt3808_block_14
  leafTestAt3808_block_15))))
  (interval_append leafTestAt3808 16 24 32
  (interval_append leafTestAt3808 16 20 24
  (interval_append leafTestAt3808 16 18 20
  (interval_append leafTestAt3808 16 17 18
  leafTestAt3808_block_16
  leafTestAt3808_block_17)
  (interval_append leafTestAt3808 18 19 20
  leafTestAt3808_block_18
  leafTestAt3808_block_19))
  (interval_append leafTestAt3808 20 22 24
  (interval_append leafTestAt3808 20 21 22
  leafTestAt3808_block_20
  leafTestAt3808_block_21)
  (interval_append leafTestAt3808 22 23 24
  leafTestAt3808_block_22
  leafTestAt3808_block_23)))
  (interval_append leafTestAt3808 24 28 32
  (interval_append leafTestAt3808 24 26 28
  (interval_append leafTestAt3808 24 25 26
  leafTestAt3808_block_24
  leafTestAt3808_block_25)
  (interval_append leafTestAt3808 26 27 28
  leafTestAt3808_block_26
  leafTestAt3808_block_27))
  (interval_append leafTestAt3808 28 30 32
  (interval_append leafTestAt3808 28 29 30
  leafTestAt3808_block_28
  leafTestAt3808_block_29)
  (interval_append leafTestAt3808 30 31 32
  leafTestAt3808_block_30
  leafTestAt3808_block_31)))))
theorem leafInterval3808 : Interval leafTest 3808 3840 := by
  intro i hlo hhi
  have h := leafTestAt3808_complete (i-3808) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt3808, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
