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
def leafTestAt1856 (i : Nat) := leafTest (i+1856)
theorem leafTestAt1856_block_0 : Interval leafTestAt1856 0 1 :=
  interval_of_check leafTestAt1856 0 1 (by decide +kernel)

theorem leafTestAt1856_block_1 : Interval leafTestAt1856 1 2 :=
  interval_of_check leafTestAt1856 1 1 (by decide +kernel)

theorem leafTestAt1856_block_2 : Interval leafTestAt1856 2 3 :=
  interval_of_check leafTestAt1856 2 1 (by decide +kernel)

theorem leafTestAt1856_block_3 : Interval leafTestAt1856 3 4 :=
  interval_of_check leafTestAt1856 3 1 (by decide +kernel)

theorem leafTestAt1856_block_4 : Interval leafTestAt1856 4 5 :=
  interval_of_check leafTestAt1856 4 1 (by decide +kernel)

theorem leafTestAt1856_block_5 : Interval leafTestAt1856 5 6 :=
  interval_of_check leafTestAt1856 5 1 (by decide +kernel)

theorem leafTestAt1856_block_6 : Interval leafTestAt1856 6 7 :=
  interval_of_check leafTestAt1856 6 1 (by decide +kernel)

theorem leafTestAt1856_block_7 : Interval leafTestAt1856 7 8 :=
  interval_of_check leafTestAt1856 7 1 (by decide +kernel)

theorem leafTestAt1856_block_8 : Interval leafTestAt1856 8 9 :=
  interval_of_check leafTestAt1856 8 1 (by decide +kernel)

theorem leafTestAt1856_block_9 : Interval leafTestAt1856 9 10 :=
  interval_of_check leafTestAt1856 9 1 (by decide +kernel)

theorem leafTestAt1856_block_10 : Interval leafTestAt1856 10 11 :=
  interval_of_check leafTestAt1856 10 1 (by decide +kernel)

theorem leafTestAt1856_block_11 : Interval leafTestAt1856 11 12 :=
  interval_of_check leafTestAt1856 11 1 (by decide +kernel)

theorem leafTestAt1856_block_12 : Interval leafTestAt1856 12 13 :=
  interval_of_check leafTestAt1856 12 1 (by decide +kernel)

theorem leafTestAt1856_block_13 : Interval leafTestAt1856 13 14 :=
  interval_of_check leafTestAt1856 13 1 (by decide +kernel)

theorem leafTestAt1856_block_14 : Interval leafTestAt1856 14 15 :=
  interval_of_check leafTestAt1856 14 1 (by decide +kernel)

theorem leafTestAt1856_block_15 : Interval leafTestAt1856 15 16 :=
  interval_of_check leafTestAt1856 15 1 (by decide +kernel)

theorem leafTestAt1856_block_16 : Interval leafTestAt1856 16 17 :=
  interval_of_check leafTestAt1856 16 1 (by decide +kernel)

theorem leafTestAt1856_block_17 : Interval leafTestAt1856 17 18 :=
  interval_of_check leafTestAt1856 17 1 (by decide +kernel)

theorem leafTestAt1856_block_18 : Interval leafTestAt1856 18 19 :=
  interval_of_check leafTestAt1856 18 1 (by decide +kernel)

theorem leafTestAt1856_block_19 : Interval leafTestAt1856 19 20 :=
  interval_of_check leafTestAt1856 19 1 (by decide +kernel)

theorem leafTestAt1856_block_20 : Interval leafTestAt1856 20 21 :=
  interval_of_check leafTestAt1856 20 1 (by decide +kernel)

theorem leafTestAt1856_block_21 : Interval leafTestAt1856 21 22 :=
  interval_of_check leafTestAt1856 21 1 (by decide +kernel)

theorem leafTestAt1856_block_22 : Interval leafTestAt1856 22 23 :=
  interval_of_check leafTestAt1856 22 1 (by decide +kernel)

theorem leafTestAt1856_block_23 : Interval leafTestAt1856 23 24 :=
  interval_of_check leafTestAt1856 23 1 (by decide +kernel)

theorem leafTestAt1856_block_24 : Interval leafTestAt1856 24 25 :=
  interval_of_check leafTestAt1856 24 1 (by decide +kernel)

theorem leafTestAt1856_block_25 : Interval leafTestAt1856 25 26 :=
  interval_of_check leafTestAt1856 25 1 (by decide +kernel)

theorem leafTestAt1856_block_26 : Interval leafTestAt1856 26 27 :=
  interval_of_check leafTestAt1856 26 1 (by decide +kernel)

theorem leafTestAt1856_block_27 : Interval leafTestAt1856 27 28 :=
  interval_of_check leafTestAt1856 27 1 (by decide +kernel)

theorem leafTestAt1856_block_28 : Interval leafTestAt1856 28 29 :=
  interval_of_check leafTestAt1856 28 1 (by decide +kernel)

theorem leafTestAt1856_block_29 : Interval leafTestAt1856 29 30 :=
  interval_of_check leafTestAt1856 29 1 (by decide +kernel)

theorem leafTestAt1856_block_30 : Interval leafTestAt1856 30 31 :=
  interval_of_check leafTestAt1856 30 1 (by decide +kernel)

theorem leafTestAt1856_block_31 : Interval leafTestAt1856 31 32 :=
  interval_of_check leafTestAt1856 31 1 (by decide +kernel)

theorem leafTestAt1856_complete : Interval leafTestAt1856 0 32 :=
  (interval_append leafTestAt1856 0 16 32
  (interval_append leafTestAt1856 0 8 16
  (interval_append leafTestAt1856 0 4 8
  (interval_append leafTestAt1856 0 2 4
  (interval_append leafTestAt1856 0 1 2
  leafTestAt1856_block_0
  leafTestAt1856_block_1)
  (interval_append leafTestAt1856 2 3 4
  leafTestAt1856_block_2
  leafTestAt1856_block_3))
  (interval_append leafTestAt1856 4 6 8
  (interval_append leafTestAt1856 4 5 6
  leafTestAt1856_block_4
  leafTestAt1856_block_5)
  (interval_append leafTestAt1856 6 7 8
  leafTestAt1856_block_6
  leafTestAt1856_block_7)))
  (interval_append leafTestAt1856 8 12 16
  (interval_append leafTestAt1856 8 10 12
  (interval_append leafTestAt1856 8 9 10
  leafTestAt1856_block_8
  leafTestAt1856_block_9)
  (interval_append leafTestAt1856 10 11 12
  leafTestAt1856_block_10
  leafTestAt1856_block_11))
  (interval_append leafTestAt1856 12 14 16
  (interval_append leafTestAt1856 12 13 14
  leafTestAt1856_block_12
  leafTestAt1856_block_13)
  (interval_append leafTestAt1856 14 15 16
  leafTestAt1856_block_14
  leafTestAt1856_block_15))))
  (interval_append leafTestAt1856 16 24 32
  (interval_append leafTestAt1856 16 20 24
  (interval_append leafTestAt1856 16 18 20
  (interval_append leafTestAt1856 16 17 18
  leafTestAt1856_block_16
  leafTestAt1856_block_17)
  (interval_append leafTestAt1856 18 19 20
  leafTestAt1856_block_18
  leafTestAt1856_block_19))
  (interval_append leafTestAt1856 20 22 24
  (interval_append leafTestAt1856 20 21 22
  leafTestAt1856_block_20
  leafTestAt1856_block_21)
  (interval_append leafTestAt1856 22 23 24
  leafTestAt1856_block_22
  leafTestAt1856_block_23)))
  (interval_append leafTestAt1856 24 28 32
  (interval_append leafTestAt1856 24 26 28
  (interval_append leafTestAt1856 24 25 26
  leafTestAt1856_block_24
  leafTestAt1856_block_25)
  (interval_append leafTestAt1856 26 27 28
  leafTestAt1856_block_26
  leafTestAt1856_block_27))
  (interval_append leafTestAt1856 28 30 32
  (interval_append leafTestAt1856 28 29 30
  leafTestAt1856_block_28
  leafTestAt1856_block_29)
  (interval_append leafTestAt1856 30 31 32
  leafTestAt1856_block_30
  leafTestAt1856_block_31)))))
theorem leafInterval1856 : Interval leafTest 1856 1888 := by
  intro i hlo hhi
  have h := leafTestAt1856_complete (i-1856) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt1856, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
