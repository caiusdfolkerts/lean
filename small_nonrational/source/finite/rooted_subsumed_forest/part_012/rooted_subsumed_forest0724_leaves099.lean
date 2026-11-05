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
def leafTestAt3168 (i : Nat) := leafTest (i+3168)
theorem leafTestAt3168_block_0 : Interval leafTestAt3168 0 1 :=
  interval_of_check leafTestAt3168 0 1 (by decide +kernel)

theorem leafTestAt3168_block_1 : Interval leafTestAt3168 1 2 :=
  interval_of_check leafTestAt3168 1 1 (by decide +kernel)

theorem leafTestAt3168_block_2 : Interval leafTestAt3168 2 3 :=
  interval_of_check leafTestAt3168 2 1 (by decide +kernel)

theorem leafTestAt3168_block_3 : Interval leafTestAt3168 3 4 :=
  interval_of_check leafTestAt3168 3 1 (by decide +kernel)

theorem leafTestAt3168_block_4 : Interval leafTestAt3168 4 5 :=
  interval_of_check leafTestAt3168 4 1 (by decide +kernel)

theorem leafTestAt3168_block_5 : Interval leafTestAt3168 5 6 :=
  interval_of_check leafTestAt3168 5 1 (by decide +kernel)

theorem leafTestAt3168_block_6 : Interval leafTestAt3168 6 7 :=
  interval_of_check leafTestAt3168 6 1 (by decide +kernel)

theorem leafTestAt3168_block_7 : Interval leafTestAt3168 7 8 :=
  interval_of_check leafTestAt3168 7 1 (by decide +kernel)

theorem leafTestAt3168_block_8 : Interval leafTestAt3168 8 9 :=
  interval_of_check leafTestAt3168 8 1 (by decide +kernel)

theorem leafTestAt3168_block_9 : Interval leafTestAt3168 9 10 :=
  interval_of_check leafTestAt3168 9 1 (by decide +kernel)

theorem leafTestAt3168_block_10 : Interval leafTestAt3168 10 11 :=
  interval_of_check leafTestAt3168 10 1 (by decide +kernel)

theorem leafTestAt3168_block_11 : Interval leafTestAt3168 11 12 :=
  interval_of_check leafTestAt3168 11 1 (by decide +kernel)

theorem leafTestAt3168_block_12 : Interval leafTestAt3168 12 13 :=
  interval_of_check leafTestAt3168 12 1 (by decide +kernel)

theorem leafTestAt3168_block_13 : Interval leafTestAt3168 13 14 :=
  interval_of_check leafTestAt3168 13 1 (by decide +kernel)

theorem leafTestAt3168_block_14 : Interval leafTestAt3168 14 15 :=
  interval_of_check leafTestAt3168 14 1 (by decide +kernel)

theorem leafTestAt3168_block_15 : Interval leafTestAt3168 15 16 :=
  interval_of_check leafTestAt3168 15 1 (by decide +kernel)

theorem leafTestAt3168_block_16 : Interval leafTestAt3168 16 17 :=
  interval_of_check leafTestAt3168 16 1 (by decide +kernel)

theorem leafTestAt3168_block_17 : Interval leafTestAt3168 17 18 :=
  interval_of_check leafTestAt3168 17 1 (by decide +kernel)

theorem leafTestAt3168_block_18 : Interval leafTestAt3168 18 19 :=
  interval_of_check leafTestAt3168 18 1 (by decide +kernel)

theorem leafTestAt3168_block_19 : Interval leafTestAt3168 19 20 :=
  interval_of_check leafTestAt3168 19 1 (by decide +kernel)

theorem leafTestAt3168_block_20 : Interval leafTestAt3168 20 21 :=
  interval_of_check leafTestAt3168 20 1 (by decide +kernel)

theorem leafTestAt3168_block_21 : Interval leafTestAt3168 21 22 :=
  interval_of_check leafTestAt3168 21 1 (by decide +kernel)

theorem leafTestAt3168_block_22 : Interval leafTestAt3168 22 23 :=
  interval_of_check leafTestAt3168 22 1 (by decide +kernel)

theorem leafTestAt3168_block_23 : Interval leafTestAt3168 23 24 :=
  interval_of_check leafTestAt3168 23 1 (by decide +kernel)

theorem leafTestAt3168_block_24 : Interval leafTestAt3168 24 25 :=
  interval_of_check leafTestAt3168 24 1 (by decide +kernel)

theorem leafTestAt3168_block_25 : Interval leafTestAt3168 25 26 :=
  interval_of_check leafTestAt3168 25 1 (by decide +kernel)

theorem leafTestAt3168_block_26 : Interval leafTestAt3168 26 27 :=
  interval_of_check leafTestAt3168 26 1 (by decide +kernel)

theorem leafTestAt3168_block_27 : Interval leafTestAt3168 27 28 :=
  interval_of_check leafTestAt3168 27 1 (by decide +kernel)

theorem leafTestAt3168_block_28 : Interval leafTestAt3168 28 29 :=
  interval_of_check leafTestAt3168 28 1 (by decide +kernel)

theorem leafTestAt3168_block_29 : Interval leafTestAt3168 29 30 :=
  interval_of_check leafTestAt3168 29 1 (by decide +kernel)

theorem leafTestAt3168_block_30 : Interval leafTestAt3168 30 31 :=
  interval_of_check leafTestAt3168 30 1 (by decide +kernel)

theorem leafTestAt3168_block_31 : Interval leafTestAt3168 31 32 :=
  interval_of_check leafTestAt3168 31 1 (by decide +kernel)

theorem leafTestAt3168_complete : Interval leafTestAt3168 0 32 :=
  (interval_append leafTestAt3168 0 16 32
  (interval_append leafTestAt3168 0 8 16
  (interval_append leafTestAt3168 0 4 8
  (interval_append leafTestAt3168 0 2 4
  (interval_append leafTestAt3168 0 1 2
  leafTestAt3168_block_0
  leafTestAt3168_block_1)
  (interval_append leafTestAt3168 2 3 4
  leafTestAt3168_block_2
  leafTestAt3168_block_3))
  (interval_append leafTestAt3168 4 6 8
  (interval_append leafTestAt3168 4 5 6
  leafTestAt3168_block_4
  leafTestAt3168_block_5)
  (interval_append leafTestAt3168 6 7 8
  leafTestAt3168_block_6
  leafTestAt3168_block_7)))
  (interval_append leafTestAt3168 8 12 16
  (interval_append leafTestAt3168 8 10 12
  (interval_append leafTestAt3168 8 9 10
  leafTestAt3168_block_8
  leafTestAt3168_block_9)
  (interval_append leafTestAt3168 10 11 12
  leafTestAt3168_block_10
  leafTestAt3168_block_11))
  (interval_append leafTestAt3168 12 14 16
  (interval_append leafTestAt3168 12 13 14
  leafTestAt3168_block_12
  leafTestAt3168_block_13)
  (interval_append leafTestAt3168 14 15 16
  leafTestAt3168_block_14
  leafTestAt3168_block_15))))
  (interval_append leafTestAt3168 16 24 32
  (interval_append leafTestAt3168 16 20 24
  (interval_append leafTestAt3168 16 18 20
  (interval_append leafTestAt3168 16 17 18
  leafTestAt3168_block_16
  leafTestAt3168_block_17)
  (interval_append leafTestAt3168 18 19 20
  leafTestAt3168_block_18
  leafTestAt3168_block_19))
  (interval_append leafTestAt3168 20 22 24
  (interval_append leafTestAt3168 20 21 22
  leafTestAt3168_block_20
  leafTestAt3168_block_21)
  (interval_append leafTestAt3168 22 23 24
  leafTestAt3168_block_22
  leafTestAt3168_block_23)))
  (interval_append leafTestAt3168 24 28 32
  (interval_append leafTestAt3168 24 26 28
  (interval_append leafTestAt3168 24 25 26
  leafTestAt3168_block_24
  leafTestAt3168_block_25)
  (interval_append leafTestAt3168 26 27 28
  leafTestAt3168_block_26
  leafTestAt3168_block_27))
  (interval_append leafTestAt3168 28 30 32
  (interval_append leafTestAt3168 28 29 30
  leafTestAt3168_block_28
  leafTestAt3168_block_29)
  (interval_append leafTestAt3168 30 31 32
  leafTestAt3168_block_30
  leafTestAt3168_block_31)))))
theorem leafInterval3168 : Interval leafTest 3168 3200 := by
  intro i hlo hhi
  have h := leafTestAt3168_complete (i-3168) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt3168, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
