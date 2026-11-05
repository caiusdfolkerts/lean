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
def leafTestAt640 (i : Nat) := leafTest (i+640)
theorem leafTestAt640_block_0 : Interval leafTestAt640 0 1 :=
  interval_of_check leafTestAt640 0 1 (by decide +kernel)

theorem leafTestAt640_block_1 : Interval leafTestAt640 1 2 :=
  interval_of_check leafTestAt640 1 1 (by decide +kernel)

theorem leafTestAt640_block_2 : Interval leafTestAt640 2 3 :=
  interval_of_check leafTestAt640 2 1 (by decide +kernel)

theorem leafTestAt640_block_3 : Interval leafTestAt640 3 4 :=
  interval_of_check leafTestAt640 3 1 (by decide +kernel)

theorem leafTestAt640_block_4 : Interval leafTestAt640 4 5 :=
  interval_of_check leafTestAt640 4 1 (by decide +kernel)

theorem leafTestAt640_block_5 : Interval leafTestAt640 5 6 :=
  interval_of_check leafTestAt640 5 1 (by decide +kernel)

theorem leafTestAt640_block_6 : Interval leafTestAt640 6 7 :=
  interval_of_check leafTestAt640 6 1 (by decide +kernel)

theorem leafTestAt640_block_7 : Interval leafTestAt640 7 8 :=
  interval_of_check leafTestAt640 7 1 (by decide +kernel)

theorem leafTestAt640_block_8 : Interval leafTestAt640 8 9 :=
  interval_of_check leafTestAt640 8 1 (by decide +kernel)

theorem leafTestAt640_block_9 : Interval leafTestAt640 9 10 :=
  interval_of_check leafTestAt640 9 1 (by decide +kernel)

theorem leafTestAt640_block_10 : Interval leafTestAt640 10 11 :=
  interval_of_check leafTestAt640 10 1 (by decide +kernel)

theorem leafTestAt640_block_11 : Interval leafTestAt640 11 12 :=
  interval_of_check leafTestAt640 11 1 (by decide +kernel)

theorem leafTestAt640_block_12 : Interval leafTestAt640 12 13 :=
  interval_of_check leafTestAt640 12 1 (by decide +kernel)

theorem leafTestAt640_block_13 : Interval leafTestAt640 13 14 :=
  interval_of_check leafTestAt640 13 1 (by decide +kernel)

theorem leafTestAt640_block_14 : Interval leafTestAt640 14 15 :=
  interval_of_check leafTestAt640 14 1 (by decide +kernel)

theorem leafTestAt640_block_15 : Interval leafTestAt640 15 16 :=
  interval_of_check leafTestAt640 15 1 (by decide +kernel)

theorem leafTestAt640_block_16 : Interval leafTestAt640 16 17 :=
  interval_of_check leafTestAt640 16 1 (by decide +kernel)

theorem leafTestAt640_block_17 : Interval leafTestAt640 17 18 :=
  interval_of_check leafTestAt640 17 1 (by decide +kernel)

theorem leafTestAt640_block_18 : Interval leafTestAt640 18 19 :=
  interval_of_check leafTestAt640 18 1 (by decide +kernel)

theorem leafTestAt640_block_19 : Interval leafTestAt640 19 20 :=
  interval_of_check leafTestAt640 19 1 (by decide +kernel)

theorem leafTestAt640_block_20 : Interval leafTestAt640 20 21 :=
  interval_of_check leafTestAt640 20 1 (by decide +kernel)

theorem leafTestAt640_block_21 : Interval leafTestAt640 21 22 :=
  interval_of_check leafTestAt640 21 1 (by decide +kernel)

theorem leafTestAt640_block_22 : Interval leafTestAt640 22 23 :=
  interval_of_check leafTestAt640 22 1 (by decide +kernel)

theorem leafTestAt640_block_23 : Interval leafTestAt640 23 24 :=
  interval_of_check leafTestAt640 23 1 (by decide +kernel)

theorem leafTestAt640_block_24 : Interval leafTestAt640 24 25 :=
  interval_of_check leafTestAt640 24 1 (by decide +kernel)

theorem leafTestAt640_block_25 : Interval leafTestAt640 25 26 :=
  interval_of_check leafTestAt640 25 1 (by decide +kernel)

theorem leafTestAt640_block_26 : Interval leafTestAt640 26 27 :=
  interval_of_check leafTestAt640 26 1 (by decide +kernel)

theorem leafTestAt640_block_27 : Interval leafTestAt640 27 28 :=
  interval_of_check leafTestAt640 27 1 (by decide +kernel)

theorem leafTestAt640_block_28 : Interval leafTestAt640 28 29 :=
  interval_of_check leafTestAt640 28 1 (by decide +kernel)

theorem leafTestAt640_block_29 : Interval leafTestAt640 29 30 :=
  interval_of_check leafTestAt640 29 1 (by decide +kernel)

theorem leafTestAt640_block_30 : Interval leafTestAt640 30 31 :=
  interval_of_check leafTestAt640 30 1 (by decide +kernel)

theorem leafTestAt640_block_31 : Interval leafTestAt640 31 32 :=
  interval_of_check leafTestAt640 31 1 (by decide +kernel)

theorem leafTestAt640_complete : Interval leafTestAt640 0 32 :=
  (interval_append leafTestAt640 0 16 32
  (interval_append leafTestAt640 0 8 16
  (interval_append leafTestAt640 0 4 8
  (interval_append leafTestAt640 0 2 4
  (interval_append leafTestAt640 0 1 2
  leafTestAt640_block_0
  leafTestAt640_block_1)
  (interval_append leafTestAt640 2 3 4
  leafTestAt640_block_2
  leafTestAt640_block_3))
  (interval_append leafTestAt640 4 6 8
  (interval_append leafTestAt640 4 5 6
  leafTestAt640_block_4
  leafTestAt640_block_5)
  (interval_append leafTestAt640 6 7 8
  leafTestAt640_block_6
  leafTestAt640_block_7)))
  (interval_append leafTestAt640 8 12 16
  (interval_append leafTestAt640 8 10 12
  (interval_append leafTestAt640 8 9 10
  leafTestAt640_block_8
  leafTestAt640_block_9)
  (interval_append leafTestAt640 10 11 12
  leafTestAt640_block_10
  leafTestAt640_block_11))
  (interval_append leafTestAt640 12 14 16
  (interval_append leafTestAt640 12 13 14
  leafTestAt640_block_12
  leafTestAt640_block_13)
  (interval_append leafTestAt640 14 15 16
  leafTestAt640_block_14
  leafTestAt640_block_15))))
  (interval_append leafTestAt640 16 24 32
  (interval_append leafTestAt640 16 20 24
  (interval_append leafTestAt640 16 18 20
  (interval_append leafTestAt640 16 17 18
  leafTestAt640_block_16
  leafTestAt640_block_17)
  (interval_append leafTestAt640 18 19 20
  leafTestAt640_block_18
  leafTestAt640_block_19))
  (interval_append leafTestAt640 20 22 24
  (interval_append leafTestAt640 20 21 22
  leafTestAt640_block_20
  leafTestAt640_block_21)
  (interval_append leafTestAt640 22 23 24
  leafTestAt640_block_22
  leafTestAt640_block_23)))
  (interval_append leafTestAt640 24 28 32
  (interval_append leafTestAt640 24 26 28
  (interval_append leafTestAt640 24 25 26
  leafTestAt640_block_24
  leafTestAt640_block_25)
  (interval_append leafTestAt640 26 27 28
  leafTestAt640_block_26
  leafTestAt640_block_27))
  (interval_append leafTestAt640 28 30 32
  (interval_append leafTestAt640 28 29 30
  leafTestAt640_block_28
  leafTestAt640_block_29)
  (interval_append leafTestAt640 30 31 32
  leafTestAt640_block_30
  leafTestAt640_block_31)))))
theorem leafInterval640 : Interval leafTest 640 672 := by
  intro i hlo hhi
  have h := leafTestAt640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
