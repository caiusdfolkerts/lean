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
def leafTestAt960 (i : Nat) := leafTest (i+960)
theorem leafTestAt960_block_0 : Interval leafTestAt960 0 1 :=
  interval_of_check leafTestAt960 0 1 (by decide +kernel)

theorem leafTestAt960_block_1 : Interval leafTestAt960 1 2 :=
  interval_of_check leafTestAt960 1 1 (by decide +kernel)

theorem leafTestAt960_block_2 : Interval leafTestAt960 2 3 :=
  interval_of_check leafTestAt960 2 1 (by decide +kernel)

theorem leafTestAt960_block_3 : Interval leafTestAt960 3 4 :=
  interval_of_check leafTestAt960 3 1 (by decide +kernel)

theorem leafTestAt960_block_4 : Interval leafTestAt960 4 5 :=
  interval_of_check leafTestAt960 4 1 (by decide +kernel)

theorem leafTestAt960_block_5 : Interval leafTestAt960 5 6 :=
  interval_of_check leafTestAt960 5 1 (by decide +kernel)

theorem leafTestAt960_block_6 : Interval leafTestAt960 6 7 :=
  interval_of_check leafTestAt960 6 1 (by decide +kernel)

theorem leafTestAt960_block_7 : Interval leafTestAt960 7 8 :=
  interval_of_check leafTestAt960 7 1 (by decide +kernel)

theorem leafTestAt960_block_8 : Interval leafTestAt960 8 9 :=
  interval_of_check leafTestAt960 8 1 (by decide +kernel)

theorem leafTestAt960_block_9 : Interval leafTestAt960 9 10 :=
  interval_of_check leafTestAt960 9 1 (by decide +kernel)

theorem leafTestAt960_block_10 : Interval leafTestAt960 10 11 :=
  interval_of_check leafTestAt960 10 1 (by decide +kernel)

theorem leafTestAt960_block_11 : Interval leafTestAt960 11 12 :=
  interval_of_check leafTestAt960 11 1 (by decide +kernel)

theorem leafTestAt960_block_12 : Interval leafTestAt960 12 13 :=
  interval_of_check leafTestAt960 12 1 (by decide +kernel)

theorem leafTestAt960_block_13 : Interval leafTestAt960 13 14 :=
  interval_of_check leafTestAt960 13 1 (by decide +kernel)

theorem leafTestAt960_block_14 : Interval leafTestAt960 14 15 :=
  interval_of_check leafTestAt960 14 1 (by decide +kernel)

theorem leafTestAt960_block_15 : Interval leafTestAt960 15 16 :=
  interval_of_check leafTestAt960 15 1 (by decide +kernel)

theorem leafTestAt960_block_16 : Interval leafTestAt960 16 17 :=
  interval_of_check leafTestAt960 16 1 (by decide +kernel)

theorem leafTestAt960_block_17 : Interval leafTestAt960 17 18 :=
  interval_of_check leafTestAt960 17 1 (by decide +kernel)

theorem leafTestAt960_block_18 : Interval leafTestAt960 18 19 :=
  interval_of_check leafTestAt960 18 1 (by decide +kernel)

theorem leafTestAt960_block_19 : Interval leafTestAt960 19 20 :=
  interval_of_check leafTestAt960 19 1 (by decide +kernel)

theorem leafTestAt960_block_20 : Interval leafTestAt960 20 21 :=
  interval_of_check leafTestAt960 20 1 (by decide +kernel)

theorem leafTestAt960_block_21 : Interval leafTestAt960 21 22 :=
  interval_of_check leafTestAt960 21 1 (by decide +kernel)

theorem leafTestAt960_block_22 : Interval leafTestAt960 22 23 :=
  interval_of_check leafTestAt960 22 1 (by decide +kernel)

theorem leafTestAt960_block_23 : Interval leafTestAt960 23 24 :=
  interval_of_check leafTestAt960 23 1 (by decide +kernel)

theorem leafTestAt960_block_24 : Interval leafTestAt960 24 25 :=
  interval_of_check leafTestAt960 24 1 (by decide +kernel)

theorem leafTestAt960_block_25 : Interval leafTestAt960 25 26 :=
  interval_of_check leafTestAt960 25 1 (by decide +kernel)

theorem leafTestAt960_block_26 : Interval leafTestAt960 26 27 :=
  interval_of_check leafTestAt960 26 1 (by decide +kernel)

theorem leafTestAt960_block_27 : Interval leafTestAt960 27 28 :=
  interval_of_check leafTestAt960 27 1 (by decide +kernel)

theorem leafTestAt960_block_28 : Interval leafTestAt960 28 29 :=
  interval_of_check leafTestAt960 28 1 (by decide +kernel)

theorem leafTestAt960_block_29 : Interval leafTestAt960 29 30 :=
  interval_of_check leafTestAt960 29 1 (by decide +kernel)

theorem leafTestAt960_block_30 : Interval leafTestAt960 30 31 :=
  interval_of_check leafTestAt960 30 1 (by decide +kernel)

theorem leafTestAt960_block_31 : Interval leafTestAt960 31 32 :=
  interval_of_check leafTestAt960 31 1 (by decide +kernel)

theorem leafTestAt960_complete : Interval leafTestAt960 0 32 :=
  (interval_append leafTestAt960 0 16 32
  (interval_append leafTestAt960 0 8 16
  (interval_append leafTestAt960 0 4 8
  (interval_append leafTestAt960 0 2 4
  (interval_append leafTestAt960 0 1 2
  leafTestAt960_block_0
  leafTestAt960_block_1)
  (interval_append leafTestAt960 2 3 4
  leafTestAt960_block_2
  leafTestAt960_block_3))
  (interval_append leafTestAt960 4 6 8
  (interval_append leafTestAt960 4 5 6
  leafTestAt960_block_4
  leafTestAt960_block_5)
  (interval_append leafTestAt960 6 7 8
  leafTestAt960_block_6
  leafTestAt960_block_7)))
  (interval_append leafTestAt960 8 12 16
  (interval_append leafTestAt960 8 10 12
  (interval_append leafTestAt960 8 9 10
  leafTestAt960_block_8
  leafTestAt960_block_9)
  (interval_append leafTestAt960 10 11 12
  leafTestAt960_block_10
  leafTestAt960_block_11))
  (interval_append leafTestAt960 12 14 16
  (interval_append leafTestAt960 12 13 14
  leafTestAt960_block_12
  leafTestAt960_block_13)
  (interval_append leafTestAt960 14 15 16
  leafTestAt960_block_14
  leafTestAt960_block_15))))
  (interval_append leafTestAt960 16 24 32
  (interval_append leafTestAt960 16 20 24
  (interval_append leafTestAt960 16 18 20
  (interval_append leafTestAt960 16 17 18
  leafTestAt960_block_16
  leafTestAt960_block_17)
  (interval_append leafTestAt960 18 19 20
  leafTestAt960_block_18
  leafTestAt960_block_19))
  (interval_append leafTestAt960 20 22 24
  (interval_append leafTestAt960 20 21 22
  leafTestAt960_block_20
  leafTestAt960_block_21)
  (interval_append leafTestAt960 22 23 24
  leafTestAt960_block_22
  leafTestAt960_block_23)))
  (interval_append leafTestAt960 24 28 32
  (interval_append leafTestAt960 24 26 28
  (interval_append leafTestAt960 24 25 26
  leafTestAt960_block_24
  leafTestAt960_block_25)
  (interval_append leafTestAt960 26 27 28
  leafTestAt960_block_26
  leafTestAt960_block_27))
  (interval_append leafTestAt960 28 30 32
  (interval_append leafTestAt960 28 29 30
  leafTestAt960_block_28
  leafTestAt960_block_29)
  (interval_append leafTestAt960 30 31 32
  leafTestAt960_block_30
  leafTestAt960_block_31)))))
theorem leafInterval960 : Interval leafTest 960 992 := by
  intro i hlo hhi
  have h := leafTestAt960_complete (i-960) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt960, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
