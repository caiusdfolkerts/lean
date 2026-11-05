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
def leafTestAt1024 (i : Nat) := leafTest (i+1024)
theorem leafTestAt1024_block_0 : Interval leafTestAt1024 0 1 :=
  interval_of_check leafTestAt1024 0 1 (by decide +kernel)

theorem leafTestAt1024_block_1 : Interval leafTestAt1024 1 2 :=
  interval_of_check leafTestAt1024 1 1 (by decide +kernel)

theorem leafTestAt1024_block_2 : Interval leafTestAt1024 2 3 :=
  interval_of_check leafTestAt1024 2 1 (by decide +kernel)

theorem leafTestAt1024_block_3 : Interval leafTestAt1024 3 4 :=
  interval_of_check leafTestAt1024 3 1 (by decide +kernel)

theorem leafTestAt1024_block_4 : Interval leafTestAt1024 4 5 :=
  interval_of_check leafTestAt1024 4 1 (by decide +kernel)

theorem leafTestAt1024_block_5 : Interval leafTestAt1024 5 6 :=
  interval_of_check leafTestAt1024 5 1 (by decide +kernel)

theorem leafTestAt1024_block_6 : Interval leafTestAt1024 6 7 :=
  interval_of_check leafTestAt1024 6 1 (by decide +kernel)

theorem leafTestAt1024_block_7 : Interval leafTestAt1024 7 8 :=
  interval_of_check leafTestAt1024 7 1 (by decide +kernel)

theorem leafTestAt1024_block_8 : Interval leafTestAt1024 8 9 :=
  interval_of_check leafTestAt1024 8 1 (by decide +kernel)

theorem leafTestAt1024_block_9 : Interval leafTestAt1024 9 10 :=
  interval_of_check leafTestAt1024 9 1 (by decide +kernel)

theorem leafTestAt1024_block_10 : Interval leafTestAt1024 10 11 :=
  interval_of_check leafTestAt1024 10 1 (by decide +kernel)

theorem leafTestAt1024_block_11 : Interval leafTestAt1024 11 12 :=
  interval_of_check leafTestAt1024 11 1 (by decide +kernel)

theorem leafTestAt1024_block_12 : Interval leafTestAt1024 12 13 :=
  interval_of_check leafTestAt1024 12 1 (by decide +kernel)

theorem leafTestAt1024_block_13 : Interval leafTestAt1024 13 14 :=
  interval_of_check leafTestAt1024 13 1 (by decide +kernel)

theorem leafTestAt1024_block_14 : Interval leafTestAt1024 14 15 :=
  interval_of_check leafTestAt1024 14 1 (by decide +kernel)

theorem leafTestAt1024_block_15 : Interval leafTestAt1024 15 16 :=
  interval_of_check leafTestAt1024 15 1 (by decide +kernel)

theorem leafTestAt1024_block_16 : Interval leafTestAt1024 16 17 :=
  interval_of_check leafTestAt1024 16 1 (by decide +kernel)

theorem leafTestAt1024_block_17 : Interval leafTestAt1024 17 18 :=
  interval_of_check leafTestAt1024 17 1 (by decide +kernel)

theorem leafTestAt1024_block_18 : Interval leafTestAt1024 18 19 :=
  interval_of_check leafTestAt1024 18 1 (by decide +kernel)

theorem leafTestAt1024_block_19 : Interval leafTestAt1024 19 20 :=
  interval_of_check leafTestAt1024 19 1 (by decide +kernel)

theorem leafTestAt1024_block_20 : Interval leafTestAt1024 20 21 :=
  interval_of_check leafTestAt1024 20 1 (by decide +kernel)

theorem leafTestAt1024_block_21 : Interval leafTestAt1024 21 22 :=
  interval_of_check leafTestAt1024 21 1 (by decide +kernel)

theorem leafTestAt1024_block_22 : Interval leafTestAt1024 22 23 :=
  interval_of_check leafTestAt1024 22 1 (by decide +kernel)

theorem leafTestAt1024_block_23 : Interval leafTestAt1024 23 24 :=
  interval_of_check leafTestAt1024 23 1 (by decide +kernel)

theorem leafTestAt1024_block_24 : Interval leafTestAt1024 24 25 :=
  interval_of_check leafTestAt1024 24 1 (by decide +kernel)

theorem leafTestAt1024_block_25 : Interval leafTestAt1024 25 26 :=
  interval_of_check leafTestAt1024 25 1 (by decide +kernel)

theorem leafTestAt1024_block_26 : Interval leafTestAt1024 26 27 :=
  interval_of_check leafTestAt1024 26 1 (by decide +kernel)

theorem leafTestAt1024_block_27 : Interval leafTestAt1024 27 28 :=
  interval_of_check leafTestAt1024 27 1 (by decide +kernel)

theorem leafTestAt1024_block_28 : Interval leafTestAt1024 28 29 :=
  interval_of_check leafTestAt1024 28 1 (by decide +kernel)

theorem leafTestAt1024_block_29 : Interval leafTestAt1024 29 30 :=
  interval_of_check leafTestAt1024 29 1 (by decide +kernel)

theorem leafTestAt1024_block_30 : Interval leafTestAt1024 30 31 :=
  interval_of_check leafTestAt1024 30 1 (by decide +kernel)

theorem leafTestAt1024_block_31 : Interval leafTestAt1024 31 32 :=
  interval_of_check leafTestAt1024 31 1 (by decide +kernel)

theorem leafTestAt1024_complete : Interval leafTestAt1024 0 32 :=
  (interval_append leafTestAt1024 0 16 32
  (interval_append leafTestAt1024 0 8 16
  (interval_append leafTestAt1024 0 4 8
  (interval_append leafTestAt1024 0 2 4
  (interval_append leafTestAt1024 0 1 2
  leafTestAt1024_block_0
  leafTestAt1024_block_1)
  (interval_append leafTestAt1024 2 3 4
  leafTestAt1024_block_2
  leafTestAt1024_block_3))
  (interval_append leafTestAt1024 4 6 8
  (interval_append leafTestAt1024 4 5 6
  leafTestAt1024_block_4
  leafTestAt1024_block_5)
  (interval_append leafTestAt1024 6 7 8
  leafTestAt1024_block_6
  leafTestAt1024_block_7)))
  (interval_append leafTestAt1024 8 12 16
  (interval_append leafTestAt1024 8 10 12
  (interval_append leafTestAt1024 8 9 10
  leafTestAt1024_block_8
  leafTestAt1024_block_9)
  (interval_append leafTestAt1024 10 11 12
  leafTestAt1024_block_10
  leafTestAt1024_block_11))
  (interval_append leafTestAt1024 12 14 16
  (interval_append leafTestAt1024 12 13 14
  leafTestAt1024_block_12
  leafTestAt1024_block_13)
  (interval_append leafTestAt1024 14 15 16
  leafTestAt1024_block_14
  leafTestAt1024_block_15))))
  (interval_append leafTestAt1024 16 24 32
  (interval_append leafTestAt1024 16 20 24
  (interval_append leafTestAt1024 16 18 20
  (interval_append leafTestAt1024 16 17 18
  leafTestAt1024_block_16
  leafTestAt1024_block_17)
  (interval_append leafTestAt1024 18 19 20
  leafTestAt1024_block_18
  leafTestAt1024_block_19))
  (interval_append leafTestAt1024 20 22 24
  (interval_append leafTestAt1024 20 21 22
  leafTestAt1024_block_20
  leafTestAt1024_block_21)
  (interval_append leafTestAt1024 22 23 24
  leafTestAt1024_block_22
  leafTestAt1024_block_23)))
  (interval_append leafTestAt1024 24 28 32
  (interval_append leafTestAt1024 24 26 28
  (interval_append leafTestAt1024 24 25 26
  leafTestAt1024_block_24
  leafTestAt1024_block_25)
  (interval_append leafTestAt1024 26 27 28
  leafTestAt1024_block_26
  leafTestAt1024_block_27))
  (interval_append leafTestAt1024 28 30 32
  (interval_append leafTestAt1024 28 29 30
  leafTestAt1024_block_28
  leafTestAt1024_block_29)
  (interval_append leafTestAt1024 30 31 32
  leafTestAt1024_block_30
  leafTestAt1024_block_31)))))
theorem leafInterval1024 : Interval leafTest 1024 1056 := by
  intro i hlo hhi
  have h := leafTestAt1024_complete (i-1024) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt1024, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
