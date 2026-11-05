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
def leafTestAt3072 (i : Nat) := leafTest (i+3072)
theorem leafTestAt3072_block_0 : Interval leafTestAt3072 0 1 :=
  interval_of_check leafTestAt3072 0 1 (by decide +kernel)

theorem leafTestAt3072_block_1 : Interval leafTestAt3072 1 2 :=
  interval_of_check leafTestAt3072 1 1 (by decide +kernel)

theorem leafTestAt3072_block_2 : Interval leafTestAt3072 2 3 :=
  interval_of_check leafTestAt3072 2 1 (by decide +kernel)

theorem leafTestAt3072_block_3 : Interval leafTestAt3072 3 4 :=
  interval_of_check leafTestAt3072 3 1 (by decide +kernel)

theorem leafTestAt3072_block_4 : Interval leafTestAt3072 4 5 :=
  interval_of_check leafTestAt3072 4 1 (by decide +kernel)

theorem leafTestAt3072_block_5 : Interval leafTestAt3072 5 6 :=
  interval_of_check leafTestAt3072 5 1 (by decide +kernel)

theorem leafTestAt3072_block_6 : Interval leafTestAt3072 6 7 :=
  interval_of_check leafTestAt3072 6 1 (by decide +kernel)

theorem leafTestAt3072_block_7 : Interval leafTestAt3072 7 8 :=
  interval_of_check leafTestAt3072 7 1 (by decide +kernel)

theorem leafTestAt3072_block_8 : Interval leafTestAt3072 8 9 :=
  interval_of_check leafTestAt3072 8 1 (by decide +kernel)

theorem leafTestAt3072_block_9 : Interval leafTestAt3072 9 10 :=
  interval_of_check leafTestAt3072 9 1 (by decide +kernel)

theorem leafTestAt3072_block_10 : Interval leafTestAt3072 10 11 :=
  interval_of_check leafTestAt3072 10 1 (by decide +kernel)

theorem leafTestAt3072_block_11 : Interval leafTestAt3072 11 12 :=
  interval_of_check leafTestAt3072 11 1 (by decide +kernel)

theorem leafTestAt3072_block_12 : Interval leafTestAt3072 12 13 :=
  interval_of_check leafTestAt3072 12 1 (by decide +kernel)

theorem leafTestAt3072_block_13 : Interval leafTestAt3072 13 14 :=
  interval_of_check leafTestAt3072 13 1 (by decide +kernel)

theorem leafTestAt3072_block_14 : Interval leafTestAt3072 14 15 :=
  interval_of_check leafTestAt3072 14 1 (by decide +kernel)

theorem leafTestAt3072_block_15 : Interval leafTestAt3072 15 16 :=
  interval_of_check leafTestAt3072 15 1 (by decide +kernel)

theorem leafTestAt3072_block_16 : Interval leafTestAt3072 16 17 :=
  interval_of_check leafTestAt3072 16 1 (by decide +kernel)

theorem leafTestAt3072_block_17 : Interval leafTestAt3072 17 18 :=
  interval_of_check leafTestAt3072 17 1 (by decide +kernel)

theorem leafTestAt3072_block_18 : Interval leafTestAt3072 18 19 :=
  interval_of_check leafTestAt3072 18 1 (by decide +kernel)

theorem leafTestAt3072_block_19 : Interval leafTestAt3072 19 20 :=
  interval_of_check leafTestAt3072 19 1 (by decide +kernel)

theorem leafTestAt3072_block_20 : Interval leafTestAt3072 20 21 :=
  interval_of_check leafTestAt3072 20 1 (by decide +kernel)

theorem leafTestAt3072_block_21 : Interval leafTestAt3072 21 22 :=
  interval_of_check leafTestAt3072 21 1 (by decide +kernel)

theorem leafTestAt3072_block_22 : Interval leafTestAt3072 22 23 :=
  interval_of_check leafTestAt3072 22 1 (by decide +kernel)

theorem leafTestAt3072_block_23 : Interval leafTestAt3072 23 24 :=
  interval_of_check leafTestAt3072 23 1 (by decide +kernel)

theorem leafTestAt3072_block_24 : Interval leafTestAt3072 24 25 :=
  interval_of_check leafTestAt3072 24 1 (by decide +kernel)

theorem leafTestAt3072_block_25 : Interval leafTestAt3072 25 26 :=
  interval_of_check leafTestAt3072 25 1 (by decide +kernel)

theorem leafTestAt3072_block_26 : Interval leafTestAt3072 26 27 :=
  interval_of_check leafTestAt3072 26 1 (by decide +kernel)

theorem leafTestAt3072_block_27 : Interval leafTestAt3072 27 28 :=
  interval_of_check leafTestAt3072 27 1 (by decide +kernel)

theorem leafTestAt3072_block_28 : Interval leafTestAt3072 28 29 :=
  interval_of_check leafTestAt3072 28 1 (by decide +kernel)

theorem leafTestAt3072_block_29 : Interval leafTestAt3072 29 30 :=
  interval_of_check leafTestAt3072 29 1 (by decide +kernel)

theorem leafTestAt3072_block_30 : Interval leafTestAt3072 30 31 :=
  interval_of_check leafTestAt3072 30 1 (by decide +kernel)

theorem leafTestAt3072_block_31 : Interval leafTestAt3072 31 32 :=
  interval_of_check leafTestAt3072 31 1 (by decide +kernel)

theorem leafTestAt3072_complete : Interval leafTestAt3072 0 32 :=
  (interval_append leafTestAt3072 0 16 32
  (interval_append leafTestAt3072 0 8 16
  (interval_append leafTestAt3072 0 4 8
  (interval_append leafTestAt3072 0 2 4
  (interval_append leafTestAt3072 0 1 2
  leafTestAt3072_block_0
  leafTestAt3072_block_1)
  (interval_append leafTestAt3072 2 3 4
  leafTestAt3072_block_2
  leafTestAt3072_block_3))
  (interval_append leafTestAt3072 4 6 8
  (interval_append leafTestAt3072 4 5 6
  leafTestAt3072_block_4
  leafTestAt3072_block_5)
  (interval_append leafTestAt3072 6 7 8
  leafTestAt3072_block_6
  leafTestAt3072_block_7)))
  (interval_append leafTestAt3072 8 12 16
  (interval_append leafTestAt3072 8 10 12
  (interval_append leafTestAt3072 8 9 10
  leafTestAt3072_block_8
  leafTestAt3072_block_9)
  (interval_append leafTestAt3072 10 11 12
  leafTestAt3072_block_10
  leafTestAt3072_block_11))
  (interval_append leafTestAt3072 12 14 16
  (interval_append leafTestAt3072 12 13 14
  leafTestAt3072_block_12
  leafTestAt3072_block_13)
  (interval_append leafTestAt3072 14 15 16
  leafTestAt3072_block_14
  leafTestAt3072_block_15))))
  (interval_append leafTestAt3072 16 24 32
  (interval_append leafTestAt3072 16 20 24
  (interval_append leafTestAt3072 16 18 20
  (interval_append leafTestAt3072 16 17 18
  leafTestAt3072_block_16
  leafTestAt3072_block_17)
  (interval_append leafTestAt3072 18 19 20
  leafTestAt3072_block_18
  leafTestAt3072_block_19))
  (interval_append leafTestAt3072 20 22 24
  (interval_append leafTestAt3072 20 21 22
  leafTestAt3072_block_20
  leafTestAt3072_block_21)
  (interval_append leafTestAt3072 22 23 24
  leafTestAt3072_block_22
  leafTestAt3072_block_23)))
  (interval_append leafTestAt3072 24 28 32
  (interval_append leafTestAt3072 24 26 28
  (interval_append leafTestAt3072 24 25 26
  leafTestAt3072_block_24
  leafTestAt3072_block_25)
  (interval_append leafTestAt3072 26 27 28
  leafTestAt3072_block_26
  leafTestAt3072_block_27))
  (interval_append leafTestAt3072 28 30 32
  (interval_append leafTestAt3072 28 29 30
  leafTestAt3072_block_28
  leafTestAt3072_block_29)
  (interval_append leafTestAt3072 30 31 32
  leafTestAt3072_block_30
  leafTestAt3072_block_31)))))
theorem leafInterval3072 : Interval leafTest 3072 3104 := by
  intro i hlo hhi
  have h := leafTestAt3072_complete (i-3072) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt3072, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
