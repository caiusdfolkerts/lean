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
def leafTestAt1792 (i : Nat) := leafTest (i+1792)
theorem leafTestAt1792_block_0 : Interval leafTestAt1792 0 1 :=
  interval_of_check leafTestAt1792 0 1 (by decide +kernel)

theorem leafTestAt1792_block_1 : Interval leafTestAt1792 1 2 :=
  interval_of_check leafTestAt1792 1 1 (by decide +kernel)

theorem leafTestAt1792_block_2 : Interval leafTestAt1792 2 3 :=
  interval_of_check leafTestAt1792 2 1 (by decide +kernel)

theorem leafTestAt1792_block_3 : Interval leafTestAt1792 3 4 :=
  interval_of_check leafTestAt1792 3 1 (by decide +kernel)

theorem leafTestAt1792_block_4 : Interval leafTestAt1792 4 5 :=
  interval_of_check leafTestAt1792 4 1 (by decide +kernel)

theorem leafTestAt1792_block_5 : Interval leafTestAt1792 5 6 :=
  interval_of_check leafTestAt1792 5 1 (by decide +kernel)

theorem leafTestAt1792_block_6 : Interval leafTestAt1792 6 7 :=
  interval_of_check leafTestAt1792 6 1 (by decide +kernel)

theorem leafTestAt1792_block_7 : Interval leafTestAt1792 7 8 :=
  interval_of_check leafTestAt1792 7 1 (by decide +kernel)

theorem leafTestAt1792_block_8 : Interval leafTestAt1792 8 9 :=
  interval_of_check leafTestAt1792 8 1 (by decide +kernel)

theorem leafTestAt1792_block_9 : Interval leafTestAt1792 9 10 :=
  interval_of_check leafTestAt1792 9 1 (by decide +kernel)

theorem leafTestAt1792_block_10 : Interval leafTestAt1792 10 11 :=
  interval_of_check leafTestAt1792 10 1 (by decide +kernel)

theorem leafTestAt1792_block_11 : Interval leafTestAt1792 11 12 :=
  interval_of_check leafTestAt1792 11 1 (by decide +kernel)

theorem leafTestAt1792_block_12 : Interval leafTestAt1792 12 13 :=
  interval_of_check leafTestAt1792 12 1 (by decide +kernel)

theorem leafTestAt1792_block_13 : Interval leafTestAt1792 13 14 :=
  interval_of_check leafTestAt1792 13 1 (by decide +kernel)

theorem leafTestAt1792_block_14 : Interval leafTestAt1792 14 15 :=
  interval_of_check leafTestAt1792 14 1 (by decide +kernel)

theorem leafTestAt1792_block_15 : Interval leafTestAt1792 15 16 :=
  interval_of_check leafTestAt1792 15 1 (by decide +kernel)

theorem leafTestAt1792_block_16 : Interval leafTestAt1792 16 17 :=
  interval_of_check leafTestAt1792 16 1 (by decide +kernel)

theorem leafTestAt1792_block_17 : Interval leafTestAt1792 17 18 :=
  interval_of_check leafTestAt1792 17 1 (by decide +kernel)

theorem leafTestAt1792_block_18 : Interval leafTestAt1792 18 19 :=
  interval_of_check leafTestAt1792 18 1 (by decide +kernel)

theorem leafTestAt1792_block_19 : Interval leafTestAt1792 19 20 :=
  interval_of_check leafTestAt1792 19 1 (by decide +kernel)

theorem leafTestAt1792_block_20 : Interval leafTestAt1792 20 21 :=
  interval_of_check leafTestAt1792 20 1 (by decide +kernel)

theorem leafTestAt1792_block_21 : Interval leafTestAt1792 21 22 :=
  interval_of_check leafTestAt1792 21 1 (by decide +kernel)

theorem leafTestAt1792_block_22 : Interval leafTestAt1792 22 23 :=
  interval_of_check leafTestAt1792 22 1 (by decide +kernel)

theorem leafTestAt1792_block_23 : Interval leafTestAt1792 23 24 :=
  interval_of_check leafTestAt1792 23 1 (by decide +kernel)

theorem leafTestAt1792_block_24 : Interval leafTestAt1792 24 25 :=
  interval_of_check leafTestAt1792 24 1 (by decide +kernel)

theorem leafTestAt1792_block_25 : Interval leafTestAt1792 25 26 :=
  interval_of_check leafTestAt1792 25 1 (by decide +kernel)

theorem leafTestAt1792_block_26 : Interval leafTestAt1792 26 27 :=
  interval_of_check leafTestAt1792 26 1 (by decide +kernel)

theorem leafTestAt1792_block_27 : Interval leafTestAt1792 27 28 :=
  interval_of_check leafTestAt1792 27 1 (by decide +kernel)

theorem leafTestAt1792_block_28 : Interval leafTestAt1792 28 29 :=
  interval_of_check leafTestAt1792 28 1 (by decide +kernel)

theorem leafTestAt1792_block_29 : Interval leafTestAt1792 29 30 :=
  interval_of_check leafTestAt1792 29 1 (by decide +kernel)

theorem leafTestAt1792_block_30 : Interval leafTestAt1792 30 31 :=
  interval_of_check leafTestAt1792 30 1 (by decide +kernel)

theorem leafTestAt1792_block_31 : Interval leafTestAt1792 31 32 :=
  interval_of_check leafTestAt1792 31 1 (by decide +kernel)

theorem leafTestAt1792_complete : Interval leafTestAt1792 0 32 :=
  (interval_append leafTestAt1792 0 16 32
  (interval_append leafTestAt1792 0 8 16
  (interval_append leafTestAt1792 0 4 8
  (interval_append leafTestAt1792 0 2 4
  (interval_append leafTestAt1792 0 1 2
  leafTestAt1792_block_0
  leafTestAt1792_block_1)
  (interval_append leafTestAt1792 2 3 4
  leafTestAt1792_block_2
  leafTestAt1792_block_3))
  (interval_append leafTestAt1792 4 6 8
  (interval_append leafTestAt1792 4 5 6
  leafTestAt1792_block_4
  leafTestAt1792_block_5)
  (interval_append leafTestAt1792 6 7 8
  leafTestAt1792_block_6
  leafTestAt1792_block_7)))
  (interval_append leafTestAt1792 8 12 16
  (interval_append leafTestAt1792 8 10 12
  (interval_append leafTestAt1792 8 9 10
  leafTestAt1792_block_8
  leafTestAt1792_block_9)
  (interval_append leafTestAt1792 10 11 12
  leafTestAt1792_block_10
  leafTestAt1792_block_11))
  (interval_append leafTestAt1792 12 14 16
  (interval_append leafTestAt1792 12 13 14
  leafTestAt1792_block_12
  leafTestAt1792_block_13)
  (interval_append leafTestAt1792 14 15 16
  leafTestAt1792_block_14
  leafTestAt1792_block_15))))
  (interval_append leafTestAt1792 16 24 32
  (interval_append leafTestAt1792 16 20 24
  (interval_append leafTestAt1792 16 18 20
  (interval_append leafTestAt1792 16 17 18
  leafTestAt1792_block_16
  leafTestAt1792_block_17)
  (interval_append leafTestAt1792 18 19 20
  leafTestAt1792_block_18
  leafTestAt1792_block_19))
  (interval_append leafTestAt1792 20 22 24
  (interval_append leafTestAt1792 20 21 22
  leafTestAt1792_block_20
  leafTestAt1792_block_21)
  (interval_append leafTestAt1792 22 23 24
  leafTestAt1792_block_22
  leafTestAt1792_block_23)))
  (interval_append leafTestAt1792 24 28 32
  (interval_append leafTestAt1792 24 26 28
  (interval_append leafTestAt1792 24 25 26
  leafTestAt1792_block_24
  leafTestAt1792_block_25)
  (interval_append leafTestAt1792 26 27 28
  leafTestAt1792_block_26
  leafTestAt1792_block_27))
  (interval_append leafTestAt1792 28 30 32
  (interval_append leafTestAt1792 28 29 30
  leafTestAt1792_block_28
  leafTestAt1792_block_29)
  (interval_append leafTestAt1792 30 31 32
  leafTestAt1792_block_30
  leafTestAt1792_block_31)))))
theorem leafInterval1792 : Interval leafTest 1792 1824 := by
  intro i hlo hhi
  have h := leafTestAt1792_complete (i-1792) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt1792, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
