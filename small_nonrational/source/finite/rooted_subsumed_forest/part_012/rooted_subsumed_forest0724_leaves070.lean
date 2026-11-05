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
def leafTestAt2240 (i : Nat) := leafTest (i+2240)
theorem leafTestAt2240_block_0 : Interval leafTestAt2240 0 1 :=
  interval_of_check leafTestAt2240 0 1 (by decide +kernel)

theorem leafTestAt2240_block_1 : Interval leafTestAt2240 1 2 :=
  interval_of_check leafTestAt2240 1 1 (by decide +kernel)

theorem leafTestAt2240_block_2 : Interval leafTestAt2240 2 3 :=
  interval_of_check leafTestAt2240 2 1 (by decide +kernel)

theorem leafTestAt2240_block_3 : Interval leafTestAt2240 3 4 :=
  interval_of_check leafTestAt2240 3 1 (by decide +kernel)

theorem leafTestAt2240_block_4 : Interval leafTestAt2240 4 5 :=
  interval_of_check leafTestAt2240 4 1 (by decide +kernel)

theorem leafTestAt2240_block_5 : Interval leafTestAt2240 5 6 :=
  interval_of_check leafTestAt2240 5 1 (by decide +kernel)

theorem leafTestAt2240_block_6 : Interval leafTestAt2240 6 7 :=
  interval_of_check leafTestAt2240 6 1 (by decide +kernel)

theorem leafTestAt2240_block_7 : Interval leafTestAt2240 7 8 :=
  interval_of_check leafTestAt2240 7 1 (by decide +kernel)

theorem leafTestAt2240_block_8 : Interval leafTestAt2240 8 9 :=
  interval_of_check leafTestAt2240 8 1 (by decide +kernel)

theorem leafTestAt2240_block_9 : Interval leafTestAt2240 9 10 :=
  interval_of_check leafTestAt2240 9 1 (by decide +kernel)

theorem leafTestAt2240_block_10 : Interval leafTestAt2240 10 11 :=
  interval_of_check leafTestAt2240 10 1 (by decide +kernel)

theorem leafTestAt2240_block_11 : Interval leafTestAt2240 11 12 :=
  interval_of_check leafTestAt2240 11 1 (by decide +kernel)

theorem leafTestAt2240_block_12 : Interval leafTestAt2240 12 13 :=
  interval_of_check leafTestAt2240 12 1 (by decide +kernel)

theorem leafTestAt2240_block_13 : Interval leafTestAt2240 13 14 :=
  interval_of_check leafTestAt2240 13 1 (by decide +kernel)

theorem leafTestAt2240_block_14 : Interval leafTestAt2240 14 15 :=
  interval_of_check leafTestAt2240 14 1 (by decide +kernel)

theorem leafTestAt2240_block_15 : Interval leafTestAt2240 15 16 :=
  interval_of_check leafTestAt2240 15 1 (by decide +kernel)

theorem leafTestAt2240_block_16 : Interval leafTestAt2240 16 17 :=
  interval_of_check leafTestAt2240 16 1 (by decide +kernel)

theorem leafTestAt2240_block_17 : Interval leafTestAt2240 17 18 :=
  interval_of_check leafTestAt2240 17 1 (by decide +kernel)

theorem leafTestAt2240_block_18 : Interval leafTestAt2240 18 19 :=
  interval_of_check leafTestAt2240 18 1 (by decide +kernel)

theorem leafTestAt2240_block_19 : Interval leafTestAt2240 19 20 :=
  interval_of_check leafTestAt2240 19 1 (by decide +kernel)

theorem leafTestAt2240_block_20 : Interval leafTestAt2240 20 21 :=
  interval_of_check leafTestAt2240 20 1 (by decide +kernel)

theorem leafTestAt2240_block_21 : Interval leafTestAt2240 21 22 :=
  interval_of_check leafTestAt2240 21 1 (by decide +kernel)

theorem leafTestAt2240_block_22 : Interval leafTestAt2240 22 23 :=
  interval_of_check leafTestAt2240 22 1 (by decide +kernel)

theorem leafTestAt2240_block_23 : Interval leafTestAt2240 23 24 :=
  interval_of_check leafTestAt2240 23 1 (by decide +kernel)

theorem leafTestAt2240_block_24 : Interval leafTestAt2240 24 25 :=
  interval_of_check leafTestAt2240 24 1 (by decide +kernel)

theorem leafTestAt2240_block_25 : Interval leafTestAt2240 25 26 :=
  interval_of_check leafTestAt2240 25 1 (by decide +kernel)

theorem leafTestAt2240_block_26 : Interval leafTestAt2240 26 27 :=
  interval_of_check leafTestAt2240 26 1 (by decide +kernel)

theorem leafTestAt2240_block_27 : Interval leafTestAt2240 27 28 :=
  interval_of_check leafTestAt2240 27 1 (by decide +kernel)

theorem leafTestAt2240_block_28 : Interval leafTestAt2240 28 29 :=
  interval_of_check leafTestAt2240 28 1 (by decide +kernel)

theorem leafTestAt2240_block_29 : Interval leafTestAt2240 29 30 :=
  interval_of_check leafTestAt2240 29 1 (by decide +kernel)

theorem leafTestAt2240_block_30 : Interval leafTestAt2240 30 31 :=
  interval_of_check leafTestAt2240 30 1 (by decide +kernel)

theorem leafTestAt2240_block_31 : Interval leafTestAt2240 31 32 :=
  interval_of_check leafTestAt2240 31 1 (by decide +kernel)

theorem leafTestAt2240_complete : Interval leafTestAt2240 0 32 :=
  (interval_append leafTestAt2240 0 16 32
  (interval_append leafTestAt2240 0 8 16
  (interval_append leafTestAt2240 0 4 8
  (interval_append leafTestAt2240 0 2 4
  (interval_append leafTestAt2240 0 1 2
  leafTestAt2240_block_0
  leafTestAt2240_block_1)
  (interval_append leafTestAt2240 2 3 4
  leafTestAt2240_block_2
  leafTestAt2240_block_3))
  (interval_append leafTestAt2240 4 6 8
  (interval_append leafTestAt2240 4 5 6
  leafTestAt2240_block_4
  leafTestAt2240_block_5)
  (interval_append leafTestAt2240 6 7 8
  leafTestAt2240_block_6
  leafTestAt2240_block_7)))
  (interval_append leafTestAt2240 8 12 16
  (interval_append leafTestAt2240 8 10 12
  (interval_append leafTestAt2240 8 9 10
  leafTestAt2240_block_8
  leafTestAt2240_block_9)
  (interval_append leafTestAt2240 10 11 12
  leafTestAt2240_block_10
  leafTestAt2240_block_11))
  (interval_append leafTestAt2240 12 14 16
  (interval_append leafTestAt2240 12 13 14
  leafTestAt2240_block_12
  leafTestAt2240_block_13)
  (interval_append leafTestAt2240 14 15 16
  leafTestAt2240_block_14
  leafTestAt2240_block_15))))
  (interval_append leafTestAt2240 16 24 32
  (interval_append leafTestAt2240 16 20 24
  (interval_append leafTestAt2240 16 18 20
  (interval_append leafTestAt2240 16 17 18
  leafTestAt2240_block_16
  leafTestAt2240_block_17)
  (interval_append leafTestAt2240 18 19 20
  leafTestAt2240_block_18
  leafTestAt2240_block_19))
  (interval_append leafTestAt2240 20 22 24
  (interval_append leafTestAt2240 20 21 22
  leafTestAt2240_block_20
  leafTestAt2240_block_21)
  (interval_append leafTestAt2240 22 23 24
  leafTestAt2240_block_22
  leafTestAt2240_block_23)))
  (interval_append leafTestAt2240 24 28 32
  (interval_append leafTestAt2240 24 26 28
  (interval_append leafTestAt2240 24 25 26
  leafTestAt2240_block_24
  leafTestAt2240_block_25)
  (interval_append leafTestAt2240 26 27 28
  leafTestAt2240_block_26
  leafTestAt2240_block_27))
  (interval_append leafTestAt2240 28 30 32
  (interval_append leafTestAt2240 28 29 30
  leafTestAt2240_block_28
  leafTestAt2240_block_29)
  (interval_append leafTestAt2240 30 31 32
  leafTestAt2240_block_30
  leafTestAt2240_block_31)))))
theorem leafInterval2240 : Interval leafTest 2240 2272 := by
  intro i hlo hhi
  have h := leafTestAt2240_complete (i-2240) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt2240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
