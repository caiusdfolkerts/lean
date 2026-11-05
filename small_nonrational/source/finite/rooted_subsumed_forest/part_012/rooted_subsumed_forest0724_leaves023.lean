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
def leafTestAt736 (i : Nat) := leafTest (i+736)
theorem leafTestAt736_block_0 : Interval leafTestAt736 0 1 :=
  interval_of_check leafTestAt736 0 1 (by decide +kernel)

theorem leafTestAt736_block_1 : Interval leafTestAt736 1 2 :=
  interval_of_check leafTestAt736 1 1 (by decide +kernel)

theorem leafTestAt736_block_2 : Interval leafTestAt736 2 3 :=
  interval_of_check leafTestAt736 2 1 (by decide +kernel)

theorem leafTestAt736_block_3 : Interval leafTestAt736 3 4 :=
  interval_of_check leafTestAt736 3 1 (by decide +kernel)

theorem leafTestAt736_block_4 : Interval leafTestAt736 4 5 :=
  interval_of_check leafTestAt736 4 1 (by decide +kernel)

theorem leafTestAt736_block_5 : Interval leafTestAt736 5 6 :=
  interval_of_check leafTestAt736 5 1 (by decide +kernel)

theorem leafTestAt736_block_6 : Interval leafTestAt736 6 7 :=
  interval_of_check leafTestAt736 6 1 (by decide +kernel)

theorem leafTestAt736_block_7 : Interval leafTestAt736 7 8 :=
  interval_of_check leafTestAt736 7 1 (by decide +kernel)

theorem leafTestAt736_block_8 : Interval leafTestAt736 8 9 :=
  interval_of_check leafTestAt736 8 1 (by decide +kernel)

theorem leafTestAt736_block_9 : Interval leafTestAt736 9 10 :=
  interval_of_check leafTestAt736 9 1 (by decide +kernel)

theorem leafTestAt736_block_10 : Interval leafTestAt736 10 11 :=
  interval_of_check leafTestAt736 10 1 (by decide +kernel)

theorem leafTestAt736_block_11 : Interval leafTestAt736 11 12 :=
  interval_of_check leafTestAt736 11 1 (by decide +kernel)

theorem leafTestAt736_block_12 : Interval leafTestAt736 12 13 :=
  interval_of_check leafTestAt736 12 1 (by decide +kernel)

theorem leafTestAt736_block_13 : Interval leafTestAt736 13 14 :=
  interval_of_check leafTestAt736 13 1 (by decide +kernel)

theorem leafTestAt736_block_14 : Interval leafTestAt736 14 15 :=
  interval_of_check leafTestAt736 14 1 (by decide +kernel)

theorem leafTestAt736_block_15 : Interval leafTestAt736 15 16 :=
  interval_of_check leafTestAt736 15 1 (by decide +kernel)

theorem leafTestAt736_block_16 : Interval leafTestAt736 16 17 :=
  interval_of_check leafTestAt736 16 1 (by decide +kernel)

theorem leafTestAt736_block_17 : Interval leafTestAt736 17 18 :=
  interval_of_check leafTestAt736 17 1 (by decide +kernel)

theorem leafTestAt736_block_18 : Interval leafTestAt736 18 19 :=
  interval_of_check leafTestAt736 18 1 (by decide +kernel)

theorem leafTestAt736_block_19 : Interval leafTestAt736 19 20 :=
  interval_of_check leafTestAt736 19 1 (by decide +kernel)

theorem leafTestAt736_block_20 : Interval leafTestAt736 20 21 :=
  interval_of_check leafTestAt736 20 1 (by decide +kernel)

theorem leafTestAt736_block_21 : Interval leafTestAt736 21 22 :=
  interval_of_check leafTestAt736 21 1 (by decide +kernel)

theorem leafTestAt736_block_22 : Interval leafTestAt736 22 23 :=
  interval_of_check leafTestAt736 22 1 (by decide +kernel)

theorem leafTestAt736_block_23 : Interval leafTestAt736 23 24 :=
  interval_of_check leafTestAt736 23 1 (by decide +kernel)

theorem leafTestAt736_block_24 : Interval leafTestAt736 24 25 :=
  interval_of_check leafTestAt736 24 1 (by decide +kernel)

theorem leafTestAt736_block_25 : Interval leafTestAt736 25 26 :=
  interval_of_check leafTestAt736 25 1 (by decide +kernel)

theorem leafTestAt736_block_26 : Interval leafTestAt736 26 27 :=
  interval_of_check leafTestAt736 26 1 (by decide +kernel)

theorem leafTestAt736_block_27 : Interval leafTestAt736 27 28 :=
  interval_of_check leafTestAt736 27 1 (by decide +kernel)

theorem leafTestAt736_block_28 : Interval leafTestAt736 28 29 :=
  interval_of_check leafTestAt736 28 1 (by decide +kernel)

theorem leafTestAt736_block_29 : Interval leafTestAt736 29 30 :=
  interval_of_check leafTestAt736 29 1 (by decide +kernel)

theorem leafTestAt736_block_30 : Interval leafTestAt736 30 31 :=
  interval_of_check leafTestAt736 30 1 (by decide +kernel)

theorem leafTestAt736_block_31 : Interval leafTestAt736 31 32 :=
  interval_of_check leafTestAt736 31 1 (by decide +kernel)

theorem leafTestAt736_complete : Interval leafTestAt736 0 32 :=
  (interval_append leafTestAt736 0 16 32
  (interval_append leafTestAt736 0 8 16
  (interval_append leafTestAt736 0 4 8
  (interval_append leafTestAt736 0 2 4
  (interval_append leafTestAt736 0 1 2
  leafTestAt736_block_0
  leafTestAt736_block_1)
  (interval_append leafTestAt736 2 3 4
  leafTestAt736_block_2
  leafTestAt736_block_3))
  (interval_append leafTestAt736 4 6 8
  (interval_append leafTestAt736 4 5 6
  leafTestAt736_block_4
  leafTestAt736_block_5)
  (interval_append leafTestAt736 6 7 8
  leafTestAt736_block_6
  leafTestAt736_block_7)))
  (interval_append leafTestAt736 8 12 16
  (interval_append leafTestAt736 8 10 12
  (interval_append leafTestAt736 8 9 10
  leafTestAt736_block_8
  leafTestAt736_block_9)
  (interval_append leafTestAt736 10 11 12
  leafTestAt736_block_10
  leafTestAt736_block_11))
  (interval_append leafTestAt736 12 14 16
  (interval_append leafTestAt736 12 13 14
  leafTestAt736_block_12
  leafTestAt736_block_13)
  (interval_append leafTestAt736 14 15 16
  leafTestAt736_block_14
  leafTestAt736_block_15))))
  (interval_append leafTestAt736 16 24 32
  (interval_append leafTestAt736 16 20 24
  (interval_append leafTestAt736 16 18 20
  (interval_append leafTestAt736 16 17 18
  leafTestAt736_block_16
  leafTestAt736_block_17)
  (interval_append leafTestAt736 18 19 20
  leafTestAt736_block_18
  leafTestAt736_block_19))
  (interval_append leafTestAt736 20 22 24
  (interval_append leafTestAt736 20 21 22
  leafTestAt736_block_20
  leafTestAt736_block_21)
  (interval_append leafTestAt736 22 23 24
  leafTestAt736_block_22
  leafTestAt736_block_23)))
  (interval_append leafTestAt736 24 28 32
  (interval_append leafTestAt736 24 26 28
  (interval_append leafTestAt736 24 25 26
  leafTestAt736_block_24
  leafTestAt736_block_25)
  (interval_append leafTestAt736 26 27 28
  leafTestAt736_block_26
  leafTestAt736_block_27))
  (interval_append leafTestAt736 28 30 32
  (interval_append leafTestAt736 28 29 30
  leafTestAt736_block_28
  leafTestAt736_block_29)
  (interval_append leafTestAt736 30 31 32
  leafTestAt736_block_30
  leafTestAt736_block_31)))))
theorem leafInterval736 : Interval leafTest 736 768 := by
  intro i hlo hhi
  have h := leafTestAt736_complete (i-736) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt736, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
