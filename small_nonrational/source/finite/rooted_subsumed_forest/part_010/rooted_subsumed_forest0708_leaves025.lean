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
def leafTestAt800 (i : Nat) := leafTest (i+800)
theorem leafTestAt800_block_0 : Interval leafTestAt800 0 1 :=
  interval_of_check leafTestAt800 0 1 (by decide +kernel)

theorem leafTestAt800_block_1 : Interval leafTestAt800 1 2 :=
  interval_of_check leafTestAt800 1 1 (by decide +kernel)

theorem leafTestAt800_block_2 : Interval leafTestAt800 2 3 :=
  interval_of_check leafTestAt800 2 1 (by decide +kernel)

theorem leafTestAt800_block_3 : Interval leafTestAt800 3 4 :=
  interval_of_check leafTestAt800 3 1 (by decide +kernel)

theorem leafTestAt800_block_4 : Interval leafTestAt800 4 5 :=
  interval_of_check leafTestAt800 4 1 (by decide +kernel)

theorem leafTestAt800_block_5 : Interval leafTestAt800 5 6 :=
  interval_of_check leafTestAt800 5 1 (by decide +kernel)

theorem leafTestAt800_block_6 : Interval leafTestAt800 6 7 :=
  interval_of_check leafTestAt800 6 1 (by decide +kernel)

theorem leafTestAt800_block_7 : Interval leafTestAt800 7 8 :=
  interval_of_check leafTestAt800 7 1 (by decide +kernel)

theorem leafTestAt800_block_8 : Interval leafTestAt800 8 9 :=
  interval_of_check leafTestAt800 8 1 (by decide +kernel)

theorem leafTestAt800_block_9 : Interval leafTestAt800 9 10 :=
  interval_of_check leafTestAt800 9 1 (by decide +kernel)

theorem leafTestAt800_block_10 : Interval leafTestAt800 10 11 :=
  interval_of_check leafTestAt800 10 1 (by decide +kernel)

theorem leafTestAt800_block_11 : Interval leafTestAt800 11 12 :=
  interval_of_check leafTestAt800 11 1 (by decide +kernel)

theorem leafTestAt800_block_12 : Interval leafTestAt800 12 13 :=
  interval_of_check leafTestAt800 12 1 (by decide +kernel)

theorem leafTestAt800_block_13 : Interval leafTestAt800 13 14 :=
  interval_of_check leafTestAt800 13 1 (by decide +kernel)

theorem leafTestAt800_block_14 : Interval leafTestAt800 14 15 :=
  interval_of_check leafTestAt800 14 1 (by decide +kernel)

theorem leafTestAt800_block_15 : Interval leafTestAt800 15 16 :=
  interval_of_check leafTestAt800 15 1 (by decide +kernel)

theorem leafTestAt800_block_16 : Interval leafTestAt800 16 17 :=
  interval_of_check leafTestAt800 16 1 (by decide +kernel)

theorem leafTestAt800_block_17 : Interval leafTestAt800 17 18 :=
  interval_of_check leafTestAt800 17 1 (by decide +kernel)

theorem leafTestAt800_block_18 : Interval leafTestAt800 18 19 :=
  interval_of_check leafTestAt800 18 1 (by decide +kernel)

theorem leafTestAt800_block_19 : Interval leafTestAt800 19 20 :=
  interval_of_check leafTestAt800 19 1 (by decide +kernel)

theorem leafTestAt800_block_20 : Interval leafTestAt800 20 21 :=
  interval_of_check leafTestAt800 20 1 (by decide +kernel)

theorem leafTestAt800_block_21 : Interval leafTestAt800 21 22 :=
  interval_of_check leafTestAt800 21 1 (by decide +kernel)

theorem leafTestAt800_block_22 : Interval leafTestAt800 22 23 :=
  interval_of_check leafTestAt800 22 1 (by decide +kernel)

theorem leafTestAt800_block_23 : Interval leafTestAt800 23 24 :=
  interval_of_check leafTestAt800 23 1 (by decide +kernel)

theorem leafTestAt800_block_24 : Interval leafTestAt800 24 25 :=
  interval_of_check leafTestAt800 24 1 (by decide +kernel)

theorem leafTestAt800_block_25 : Interval leafTestAt800 25 26 :=
  interval_of_check leafTestAt800 25 1 (by decide +kernel)

theorem leafTestAt800_block_26 : Interval leafTestAt800 26 27 :=
  interval_of_check leafTestAt800 26 1 (by decide +kernel)

theorem leafTestAt800_block_27 : Interval leafTestAt800 27 28 :=
  interval_of_check leafTestAt800 27 1 (by decide +kernel)

theorem leafTestAt800_block_28 : Interval leafTestAt800 28 29 :=
  interval_of_check leafTestAt800 28 1 (by decide +kernel)

theorem leafTestAt800_block_29 : Interval leafTestAt800 29 30 :=
  interval_of_check leafTestAt800 29 1 (by decide +kernel)

theorem leafTestAt800_block_30 : Interval leafTestAt800 30 31 :=
  interval_of_check leafTestAt800 30 1 (by decide +kernel)

theorem leafTestAt800_block_31 : Interval leafTestAt800 31 32 :=
  interval_of_check leafTestAt800 31 1 (by decide +kernel)

theorem leafTestAt800_complete : Interval leafTestAt800 0 32 :=
  (interval_append leafTestAt800 0 16 32
  (interval_append leafTestAt800 0 8 16
  (interval_append leafTestAt800 0 4 8
  (interval_append leafTestAt800 0 2 4
  (interval_append leafTestAt800 0 1 2
  leafTestAt800_block_0
  leafTestAt800_block_1)
  (interval_append leafTestAt800 2 3 4
  leafTestAt800_block_2
  leafTestAt800_block_3))
  (interval_append leafTestAt800 4 6 8
  (interval_append leafTestAt800 4 5 6
  leafTestAt800_block_4
  leafTestAt800_block_5)
  (interval_append leafTestAt800 6 7 8
  leafTestAt800_block_6
  leafTestAt800_block_7)))
  (interval_append leafTestAt800 8 12 16
  (interval_append leafTestAt800 8 10 12
  (interval_append leafTestAt800 8 9 10
  leafTestAt800_block_8
  leafTestAt800_block_9)
  (interval_append leafTestAt800 10 11 12
  leafTestAt800_block_10
  leafTestAt800_block_11))
  (interval_append leafTestAt800 12 14 16
  (interval_append leafTestAt800 12 13 14
  leafTestAt800_block_12
  leafTestAt800_block_13)
  (interval_append leafTestAt800 14 15 16
  leafTestAt800_block_14
  leafTestAt800_block_15))))
  (interval_append leafTestAt800 16 24 32
  (interval_append leafTestAt800 16 20 24
  (interval_append leafTestAt800 16 18 20
  (interval_append leafTestAt800 16 17 18
  leafTestAt800_block_16
  leafTestAt800_block_17)
  (interval_append leafTestAt800 18 19 20
  leafTestAt800_block_18
  leafTestAt800_block_19))
  (interval_append leafTestAt800 20 22 24
  (interval_append leafTestAt800 20 21 22
  leafTestAt800_block_20
  leafTestAt800_block_21)
  (interval_append leafTestAt800 22 23 24
  leafTestAt800_block_22
  leafTestAt800_block_23)))
  (interval_append leafTestAt800 24 28 32
  (interval_append leafTestAt800 24 26 28
  (interval_append leafTestAt800 24 25 26
  leafTestAt800_block_24
  leafTestAt800_block_25)
  (interval_append leafTestAt800 26 27 28
  leafTestAt800_block_26
  leafTestAt800_block_27))
  (interval_append leafTestAt800 28 30 32
  (interval_append leafTestAt800 28 29 30
  leafTestAt800_block_28
  leafTestAt800_block_29)
  (interval_append leafTestAt800 30 31 32
  leafTestAt800_block_30
  leafTestAt800_block_31)))))
theorem leafInterval800 : Interval leafTest 800 832 := by
  intro i hlo hhi
  have h := leafTestAt800_complete (i-800) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt800, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
