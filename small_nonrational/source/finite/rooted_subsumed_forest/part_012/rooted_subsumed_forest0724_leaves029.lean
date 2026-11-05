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
def leafTestAt928 (i : Nat) := leafTest (i+928)
theorem leafTestAt928_block_0 : Interval leafTestAt928 0 1 :=
  interval_of_check leafTestAt928 0 1 (by decide +kernel)

theorem leafTestAt928_block_1 : Interval leafTestAt928 1 2 :=
  interval_of_check leafTestAt928 1 1 (by decide +kernel)

theorem leafTestAt928_block_2 : Interval leafTestAt928 2 3 :=
  interval_of_check leafTestAt928 2 1 (by decide +kernel)

theorem leafTestAt928_block_3 : Interval leafTestAt928 3 4 :=
  interval_of_check leafTestAt928 3 1 (by decide +kernel)

theorem leafTestAt928_block_4 : Interval leafTestAt928 4 5 :=
  interval_of_check leafTestAt928 4 1 (by decide +kernel)

theorem leafTestAt928_block_5 : Interval leafTestAt928 5 6 :=
  interval_of_check leafTestAt928 5 1 (by decide +kernel)

theorem leafTestAt928_block_6 : Interval leafTestAt928 6 7 :=
  interval_of_check leafTestAt928 6 1 (by decide +kernel)

theorem leafTestAt928_block_7 : Interval leafTestAt928 7 8 :=
  interval_of_check leafTestAt928 7 1 (by decide +kernel)

theorem leafTestAt928_block_8 : Interval leafTestAt928 8 9 :=
  interval_of_check leafTestAt928 8 1 (by decide +kernel)

theorem leafTestAt928_block_9 : Interval leafTestAt928 9 10 :=
  interval_of_check leafTestAt928 9 1 (by decide +kernel)

theorem leafTestAt928_block_10 : Interval leafTestAt928 10 11 :=
  interval_of_check leafTestAt928 10 1 (by decide +kernel)

theorem leafTestAt928_block_11 : Interval leafTestAt928 11 12 :=
  interval_of_check leafTestAt928 11 1 (by decide +kernel)

theorem leafTestAt928_block_12 : Interval leafTestAt928 12 13 :=
  interval_of_check leafTestAt928 12 1 (by decide +kernel)

theorem leafTestAt928_block_13 : Interval leafTestAt928 13 14 :=
  interval_of_check leafTestAt928 13 1 (by decide +kernel)

theorem leafTestAt928_block_14 : Interval leafTestAt928 14 15 :=
  interval_of_check leafTestAt928 14 1 (by decide +kernel)

theorem leafTestAt928_block_15 : Interval leafTestAt928 15 16 :=
  interval_of_check leafTestAt928 15 1 (by decide +kernel)

theorem leafTestAt928_block_16 : Interval leafTestAt928 16 17 :=
  interval_of_check leafTestAt928 16 1 (by decide +kernel)

theorem leafTestAt928_block_17 : Interval leafTestAt928 17 18 :=
  interval_of_check leafTestAt928 17 1 (by decide +kernel)

theorem leafTestAt928_block_18 : Interval leafTestAt928 18 19 :=
  interval_of_check leafTestAt928 18 1 (by decide +kernel)

theorem leafTestAt928_block_19 : Interval leafTestAt928 19 20 :=
  interval_of_check leafTestAt928 19 1 (by decide +kernel)

theorem leafTestAt928_block_20 : Interval leafTestAt928 20 21 :=
  interval_of_check leafTestAt928 20 1 (by decide +kernel)

theorem leafTestAt928_block_21 : Interval leafTestAt928 21 22 :=
  interval_of_check leafTestAt928 21 1 (by decide +kernel)

theorem leafTestAt928_block_22 : Interval leafTestAt928 22 23 :=
  interval_of_check leafTestAt928 22 1 (by decide +kernel)

theorem leafTestAt928_block_23 : Interval leafTestAt928 23 24 :=
  interval_of_check leafTestAt928 23 1 (by decide +kernel)

theorem leafTestAt928_block_24 : Interval leafTestAt928 24 25 :=
  interval_of_check leafTestAt928 24 1 (by decide +kernel)

theorem leafTestAt928_block_25 : Interval leafTestAt928 25 26 :=
  interval_of_check leafTestAt928 25 1 (by decide +kernel)

theorem leafTestAt928_block_26 : Interval leafTestAt928 26 27 :=
  interval_of_check leafTestAt928 26 1 (by decide +kernel)

theorem leafTestAt928_block_27 : Interval leafTestAt928 27 28 :=
  interval_of_check leafTestAt928 27 1 (by decide +kernel)

theorem leafTestAt928_block_28 : Interval leafTestAt928 28 29 :=
  interval_of_check leafTestAt928 28 1 (by decide +kernel)

theorem leafTestAt928_block_29 : Interval leafTestAt928 29 30 :=
  interval_of_check leafTestAt928 29 1 (by decide +kernel)

theorem leafTestAt928_block_30 : Interval leafTestAt928 30 31 :=
  interval_of_check leafTestAt928 30 1 (by decide +kernel)

theorem leafTestAt928_block_31 : Interval leafTestAt928 31 32 :=
  interval_of_check leafTestAt928 31 1 (by decide +kernel)

theorem leafTestAt928_complete : Interval leafTestAt928 0 32 :=
  (interval_append leafTestAt928 0 16 32
  (interval_append leafTestAt928 0 8 16
  (interval_append leafTestAt928 0 4 8
  (interval_append leafTestAt928 0 2 4
  (interval_append leafTestAt928 0 1 2
  leafTestAt928_block_0
  leafTestAt928_block_1)
  (interval_append leafTestAt928 2 3 4
  leafTestAt928_block_2
  leafTestAt928_block_3))
  (interval_append leafTestAt928 4 6 8
  (interval_append leafTestAt928 4 5 6
  leafTestAt928_block_4
  leafTestAt928_block_5)
  (interval_append leafTestAt928 6 7 8
  leafTestAt928_block_6
  leafTestAt928_block_7)))
  (interval_append leafTestAt928 8 12 16
  (interval_append leafTestAt928 8 10 12
  (interval_append leafTestAt928 8 9 10
  leafTestAt928_block_8
  leafTestAt928_block_9)
  (interval_append leafTestAt928 10 11 12
  leafTestAt928_block_10
  leafTestAt928_block_11))
  (interval_append leafTestAt928 12 14 16
  (interval_append leafTestAt928 12 13 14
  leafTestAt928_block_12
  leafTestAt928_block_13)
  (interval_append leafTestAt928 14 15 16
  leafTestAt928_block_14
  leafTestAt928_block_15))))
  (interval_append leafTestAt928 16 24 32
  (interval_append leafTestAt928 16 20 24
  (interval_append leafTestAt928 16 18 20
  (interval_append leafTestAt928 16 17 18
  leafTestAt928_block_16
  leafTestAt928_block_17)
  (interval_append leafTestAt928 18 19 20
  leafTestAt928_block_18
  leafTestAt928_block_19))
  (interval_append leafTestAt928 20 22 24
  (interval_append leafTestAt928 20 21 22
  leafTestAt928_block_20
  leafTestAt928_block_21)
  (interval_append leafTestAt928 22 23 24
  leafTestAt928_block_22
  leafTestAt928_block_23)))
  (interval_append leafTestAt928 24 28 32
  (interval_append leafTestAt928 24 26 28
  (interval_append leafTestAt928 24 25 26
  leafTestAt928_block_24
  leafTestAt928_block_25)
  (interval_append leafTestAt928 26 27 28
  leafTestAt928_block_26
  leafTestAt928_block_27))
  (interval_append leafTestAt928 28 30 32
  (interval_append leafTestAt928 28 29 30
  leafTestAt928_block_28
  leafTestAt928_block_29)
  (interval_append leafTestAt928 30 31 32
  leafTestAt928_block_30
  leafTestAt928_block_31)))))
theorem leafInterval928 : Interval leafTest 928 960 := by
  intro i hlo hhi
  have h := leafTestAt928_complete (i-928) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt928, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
