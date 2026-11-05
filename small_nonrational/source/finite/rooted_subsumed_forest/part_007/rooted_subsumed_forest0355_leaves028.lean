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
def leafTestAt896 (i : Nat) := leafTest (i+896)
theorem leafTestAt896_block_0 : Interval leafTestAt896 0 1 :=
  interval_of_check leafTestAt896 0 1 (by decide +kernel)

theorem leafTestAt896_block_1 : Interval leafTestAt896 1 2 :=
  interval_of_check leafTestAt896 1 1 (by decide +kernel)

theorem leafTestAt896_block_2 : Interval leafTestAt896 2 3 :=
  interval_of_check leafTestAt896 2 1 (by decide +kernel)

theorem leafTestAt896_block_3 : Interval leafTestAt896 3 4 :=
  interval_of_check leafTestAt896 3 1 (by decide +kernel)

theorem leafTestAt896_block_4 : Interval leafTestAt896 4 5 :=
  interval_of_check leafTestAt896 4 1 (by decide +kernel)

theorem leafTestAt896_block_5 : Interval leafTestAt896 5 6 :=
  interval_of_check leafTestAt896 5 1 (by decide +kernel)

theorem leafTestAt896_block_6 : Interval leafTestAt896 6 7 :=
  interval_of_check leafTestAt896 6 1 (by decide +kernel)

theorem leafTestAt896_block_7 : Interval leafTestAt896 7 8 :=
  interval_of_check leafTestAt896 7 1 (by decide +kernel)

theorem leafTestAt896_block_8 : Interval leafTestAt896 8 9 :=
  interval_of_check leafTestAt896 8 1 (by decide +kernel)

theorem leafTestAt896_block_9 : Interval leafTestAt896 9 10 :=
  interval_of_check leafTestAt896 9 1 (by decide +kernel)

theorem leafTestAt896_block_10 : Interval leafTestAt896 10 11 :=
  interval_of_check leafTestAt896 10 1 (by decide +kernel)

theorem leafTestAt896_block_11 : Interval leafTestAt896 11 12 :=
  interval_of_check leafTestAt896 11 1 (by decide +kernel)

theorem leafTestAt896_block_12 : Interval leafTestAt896 12 13 :=
  interval_of_check leafTestAt896 12 1 (by decide +kernel)

theorem leafTestAt896_block_13 : Interval leafTestAt896 13 14 :=
  interval_of_check leafTestAt896 13 1 (by decide +kernel)

theorem leafTestAt896_block_14 : Interval leafTestAt896 14 15 :=
  interval_of_check leafTestAt896 14 1 (by decide +kernel)

theorem leafTestAt896_block_15 : Interval leafTestAt896 15 16 :=
  interval_of_check leafTestAt896 15 1 (by decide +kernel)

theorem leafTestAt896_block_16 : Interval leafTestAt896 16 17 :=
  interval_of_check leafTestAt896 16 1 (by decide +kernel)

theorem leafTestAt896_block_17 : Interval leafTestAt896 17 18 :=
  interval_of_check leafTestAt896 17 1 (by decide +kernel)

theorem leafTestAt896_block_18 : Interval leafTestAt896 18 19 :=
  interval_of_check leafTestAt896 18 1 (by decide +kernel)

theorem leafTestAt896_block_19 : Interval leafTestAt896 19 20 :=
  interval_of_check leafTestAt896 19 1 (by decide +kernel)

theorem leafTestAt896_block_20 : Interval leafTestAt896 20 21 :=
  interval_of_check leafTestAt896 20 1 (by decide +kernel)

theorem leafTestAt896_block_21 : Interval leafTestAt896 21 22 :=
  interval_of_check leafTestAt896 21 1 (by decide +kernel)

theorem leafTestAt896_block_22 : Interval leafTestAt896 22 23 :=
  interval_of_check leafTestAt896 22 1 (by decide +kernel)

theorem leafTestAt896_block_23 : Interval leafTestAt896 23 24 :=
  interval_of_check leafTestAt896 23 1 (by decide +kernel)

theorem leafTestAt896_block_24 : Interval leafTestAt896 24 25 :=
  interval_of_check leafTestAt896 24 1 (by decide +kernel)

theorem leafTestAt896_block_25 : Interval leafTestAt896 25 26 :=
  interval_of_check leafTestAt896 25 1 (by decide +kernel)

theorem leafTestAt896_block_26 : Interval leafTestAt896 26 27 :=
  interval_of_check leafTestAt896 26 1 (by decide +kernel)

theorem leafTestAt896_block_27 : Interval leafTestAt896 27 28 :=
  interval_of_check leafTestAt896 27 1 (by decide +kernel)

theorem leafTestAt896_block_28 : Interval leafTestAt896 28 29 :=
  interval_of_check leafTestAt896 28 1 (by decide +kernel)

theorem leafTestAt896_block_29 : Interval leafTestAt896 29 30 :=
  interval_of_check leafTestAt896 29 1 (by decide +kernel)

theorem leafTestAt896_block_30 : Interval leafTestAt896 30 31 :=
  interval_of_check leafTestAt896 30 1 (by decide +kernel)

theorem leafTestAt896_block_31 : Interval leafTestAt896 31 32 :=
  interval_of_check leafTestAt896 31 1 (by decide +kernel)

theorem leafTestAt896_complete : Interval leafTestAt896 0 32 :=
  (interval_append leafTestAt896 0 16 32
  (interval_append leafTestAt896 0 8 16
  (interval_append leafTestAt896 0 4 8
  (interval_append leafTestAt896 0 2 4
  (interval_append leafTestAt896 0 1 2
  leafTestAt896_block_0
  leafTestAt896_block_1)
  (interval_append leafTestAt896 2 3 4
  leafTestAt896_block_2
  leafTestAt896_block_3))
  (interval_append leafTestAt896 4 6 8
  (interval_append leafTestAt896 4 5 6
  leafTestAt896_block_4
  leafTestAt896_block_5)
  (interval_append leafTestAt896 6 7 8
  leafTestAt896_block_6
  leafTestAt896_block_7)))
  (interval_append leafTestAt896 8 12 16
  (interval_append leafTestAt896 8 10 12
  (interval_append leafTestAt896 8 9 10
  leafTestAt896_block_8
  leafTestAt896_block_9)
  (interval_append leafTestAt896 10 11 12
  leafTestAt896_block_10
  leafTestAt896_block_11))
  (interval_append leafTestAt896 12 14 16
  (interval_append leafTestAt896 12 13 14
  leafTestAt896_block_12
  leafTestAt896_block_13)
  (interval_append leafTestAt896 14 15 16
  leafTestAt896_block_14
  leafTestAt896_block_15))))
  (interval_append leafTestAt896 16 24 32
  (interval_append leafTestAt896 16 20 24
  (interval_append leafTestAt896 16 18 20
  (interval_append leafTestAt896 16 17 18
  leafTestAt896_block_16
  leafTestAt896_block_17)
  (interval_append leafTestAt896 18 19 20
  leafTestAt896_block_18
  leafTestAt896_block_19))
  (interval_append leafTestAt896 20 22 24
  (interval_append leafTestAt896 20 21 22
  leafTestAt896_block_20
  leafTestAt896_block_21)
  (interval_append leafTestAt896 22 23 24
  leafTestAt896_block_22
  leafTestAt896_block_23)))
  (interval_append leafTestAt896 24 28 32
  (interval_append leafTestAt896 24 26 28
  (interval_append leafTestAt896 24 25 26
  leafTestAt896_block_24
  leafTestAt896_block_25)
  (interval_append leafTestAt896 26 27 28
  leafTestAt896_block_26
  leafTestAt896_block_27))
  (interval_append leafTestAt896 28 30 32
  (interval_append leafTestAt896 28 29 30
  leafTestAt896_block_28
  leafTestAt896_block_29)
  (interval_append leafTestAt896 30 31 32
  leafTestAt896_block_30
  leafTestAt896_block_31)))))
theorem leafInterval896 : Interval leafTest 896 928 := by
  intro i hlo hhi
  have h := leafTestAt896_complete (i-896) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt896, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
