module
prelude
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt2208 (i : Nat) := leafTest (i+2208)
theorem leafTestAt2208_block_0 : Interval leafTestAt2208 0 1 :=
  interval_of_check leafTestAt2208 0 1 (by decide +kernel)

theorem leafTestAt2208_block_1 : Interval leafTestAt2208 1 2 :=
  interval_of_check leafTestAt2208 1 1 (by decide +kernel)

theorem leafTestAt2208_block_2 : Interval leafTestAt2208 2 3 :=
  interval_of_check leafTestAt2208 2 1 (by decide +kernel)

theorem leafTestAt2208_block_3 : Interval leafTestAt2208 3 4 :=
  interval_of_check leafTestAt2208 3 1 (by decide +kernel)

theorem leafTestAt2208_block_4 : Interval leafTestAt2208 4 5 :=
  interval_of_check leafTestAt2208 4 1 (by decide +kernel)

theorem leafTestAt2208_block_5 : Interval leafTestAt2208 5 6 :=
  interval_of_check leafTestAt2208 5 1 (by decide +kernel)

theorem leafTestAt2208_block_6 : Interval leafTestAt2208 6 7 :=
  interval_of_check leafTestAt2208 6 1 (by decide +kernel)

theorem leafTestAt2208_block_7 : Interval leafTestAt2208 7 8 :=
  interval_of_check leafTestAt2208 7 1 (by decide +kernel)

theorem leafTestAt2208_block_8 : Interval leafTestAt2208 8 9 :=
  interval_of_check leafTestAt2208 8 1 (by decide +kernel)

theorem leafTestAt2208_block_9 : Interval leafTestAt2208 9 10 :=
  interval_of_check leafTestAt2208 9 1 (by decide +kernel)

theorem leafTestAt2208_block_10 : Interval leafTestAt2208 10 11 :=
  interval_of_check leafTestAt2208 10 1 (by decide +kernel)

theorem leafTestAt2208_block_11 : Interval leafTestAt2208 11 12 :=
  interval_of_check leafTestAt2208 11 1 (by decide +kernel)

theorem leafTestAt2208_block_12 : Interval leafTestAt2208 12 13 :=
  interval_of_check leafTestAt2208 12 1 (by decide +kernel)

theorem leafTestAt2208_block_13 : Interval leafTestAt2208 13 14 :=
  interval_of_check leafTestAt2208 13 1 (by decide +kernel)

theorem leafTestAt2208_block_14 : Interval leafTestAt2208 14 15 :=
  interval_of_check leafTestAt2208 14 1 (by decide +kernel)

theorem leafTestAt2208_block_15 : Interval leafTestAt2208 15 16 :=
  interval_of_check leafTestAt2208 15 1 (by decide +kernel)

theorem leafTestAt2208_block_16 : Interval leafTestAt2208 16 17 :=
  interval_of_check leafTestAt2208 16 1 (by decide +kernel)

theorem leafTestAt2208_block_17 : Interval leafTestAt2208 17 18 :=
  interval_of_check leafTestAt2208 17 1 (by decide +kernel)

theorem leafTestAt2208_block_18 : Interval leafTestAt2208 18 19 :=
  interval_of_check leafTestAt2208 18 1 (by decide +kernel)

theorem leafTestAt2208_block_19 : Interval leafTestAt2208 19 20 :=
  interval_of_check leafTestAt2208 19 1 (by decide +kernel)

theorem leafTestAt2208_block_20 : Interval leafTestAt2208 20 21 :=
  interval_of_check leafTestAt2208 20 1 (by decide +kernel)

theorem leafTestAt2208_block_21 : Interval leafTestAt2208 21 22 :=
  interval_of_check leafTestAt2208 21 1 (by decide +kernel)

theorem leafTestAt2208_block_22 : Interval leafTestAt2208 22 23 :=
  interval_of_check leafTestAt2208 22 1 (by decide +kernel)

theorem leafTestAt2208_block_23 : Interval leafTestAt2208 23 24 :=
  interval_of_check leafTestAt2208 23 1 (by decide +kernel)

theorem leafTestAt2208_block_24 : Interval leafTestAt2208 24 25 :=
  interval_of_check leafTestAt2208 24 1 (by decide +kernel)

theorem leafTestAt2208_block_25 : Interval leafTestAt2208 25 26 :=
  interval_of_check leafTestAt2208 25 1 (by decide +kernel)

theorem leafTestAt2208_block_26 : Interval leafTestAt2208 26 27 :=
  interval_of_check leafTestAt2208 26 1 (by decide +kernel)

theorem leafTestAt2208_block_27 : Interval leafTestAt2208 27 28 :=
  interval_of_check leafTestAt2208 27 1 (by decide +kernel)

theorem leafTestAt2208_block_28 : Interval leafTestAt2208 28 29 :=
  interval_of_check leafTestAt2208 28 1 (by decide +kernel)

theorem leafTestAt2208_block_29 : Interval leafTestAt2208 29 30 :=
  interval_of_check leafTestAt2208 29 1 (by decide +kernel)

theorem leafTestAt2208_block_30 : Interval leafTestAt2208 30 31 :=
  interval_of_check leafTestAt2208 30 1 (by decide +kernel)

theorem leafTestAt2208_block_31 : Interval leafTestAt2208 31 32 :=
  interval_of_check leafTestAt2208 31 1 (by decide +kernel)

theorem leafTestAt2208_complete : Interval leafTestAt2208 0 32 :=
  (interval_append leafTestAt2208 0 16 32
  (interval_append leafTestAt2208 0 8 16
  (interval_append leafTestAt2208 0 4 8
  (interval_append leafTestAt2208 0 2 4
  (interval_append leafTestAt2208 0 1 2
  leafTestAt2208_block_0
  leafTestAt2208_block_1)
  (interval_append leafTestAt2208 2 3 4
  leafTestAt2208_block_2
  leafTestAt2208_block_3))
  (interval_append leafTestAt2208 4 6 8
  (interval_append leafTestAt2208 4 5 6
  leafTestAt2208_block_4
  leafTestAt2208_block_5)
  (interval_append leafTestAt2208 6 7 8
  leafTestAt2208_block_6
  leafTestAt2208_block_7)))
  (interval_append leafTestAt2208 8 12 16
  (interval_append leafTestAt2208 8 10 12
  (interval_append leafTestAt2208 8 9 10
  leafTestAt2208_block_8
  leafTestAt2208_block_9)
  (interval_append leafTestAt2208 10 11 12
  leafTestAt2208_block_10
  leafTestAt2208_block_11))
  (interval_append leafTestAt2208 12 14 16
  (interval_append leafTestAt2208 12 13 14
  leafTestAt2208_block_12
  leafTestAt2208_block_13)
  (interval_append leafTestAt2208 14 15 16
  leafTestAt2208_block_14
  leafTestAt2208_block_15))))
  (interval_append leafTestAt2208 16 24 32
  (interval_append leafTestAt2208 16 20 24
  (interval_append leafTestAt2208 16 18 20
  (interval_append leafTestAt2208 16 17 18
  leafTestAt2208_block_16
  leafTestAt2208_block_17)
  (interval_append leafTestAt2208 18 19 20
  leafTestAt2208_block_18
  leafTestAt2208_block_19))
  (interval_append leafTestAt2208 20 22 24
  (interval_append leafTestAt2208 20 21 22
  leafTestAt2208_block_20
  leafTestAt2208_block_21)
  (interval_append leafTestAt2208 22 23 24
  leafTestAt2208_block_22
  leafTestAt2208_block_23)))
  (interval_append leafTestAt2208 24 28 32
  (interval_append leafTestAt2208 24 26 28
  (interval_append leafTestAt2208 24 25 26
  leafTestAt2208_block_24
  leafTestAt2208_block_25)
  (interval_append leafTestAt2208 26 27 28
  leafTestAt2208_block_26
  leafTestAt2208_block_27))
  (interval_append leafTestAt2208 28 30 32
  (interval_append leafTestAt2208 28 29 30
  leafTestAt2208_block_28
  leafTestAt2208_block_29)
  (interval_append leafTestAt2208 30 31 32
  leafTestAt2208_block_30
  leafTestAt2208_block_31)))))
theorem leafInterval2208 : Interval leafTest 2208 2240 := by
  intro i hlo hhi
  have h := leafTestAt2208_complete (i-2208) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt2208, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
