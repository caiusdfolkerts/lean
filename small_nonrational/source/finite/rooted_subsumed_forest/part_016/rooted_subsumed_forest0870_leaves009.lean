module
prelude
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt288 (i : Nat) := leafTest (i+288)
theorem leafTestAt288_block_0 : Interval leafTestAt288 0 1 :=
  interval_of_check leafTestAt288 0 1 (by decide +kernel)

theorem leafTestAt288_block_1 : Interval leafTestAt288 1 2 :=
  interval_of_check leafTestAt288 1 1 (by decide +kernel)

theorem leafTestAt288_block_2 : Interval leafTestAt288 2 3 :=
  interval_of_check leafTestAt288 2 1 (by decide +kernel)

theorem leafTestAt288_block_3 : Interval leafTestAt288 3 4 :=
  interval_of_check leafTestAt288 3 1 (by decide +kernel)

theorem leafTestAt288_block_4 : Interval leafTestAt288 4 5 :=
  interval_of_check leafTestAt288 4 1 (by decide +kernel)

theorem leafTestAt288_block_5 : Interval leafTestAt288 5 6 :=
  interval_of_check leafTestAt288 5 1 (by decide +kernel)

theorem leafTestAt288_block_6 : Interval leafTestAt288 6 7 :=
  interval_of_check leafTestAt288 6 1 (by decide +kernel)

theorem leafTestAt288_block_7 : Interval leafTestAt288 7 8 :=
  interval_of_check leafTestAt288 7 1 (by decide +kernel)

theorem leafTestAt288_block_8 : Interval leafTestAt288 8 9 :=
  interval_of_check leafTestAt288 8 1 (by decide +kernel)

theorem leafTestAt288_block_9 : Interval leafTestAt288 9 10 :=
  interval_of_check leafTestAt288 9 1 (by decide +kernel)

theorem leafTestAt288_block_10 : Interval leafTestAt288 10 11 :=
  interval_of_check leafTestAt288 10 1 (by decide +kernel)

theorem leafTestAt288_block_11 : Interval leafTestAt288 11 12 :=
  interval_of_check leafTestAt288 11 1 (by decide +kernel)

theorem leafTestAt288_block_12 : Interval leafTestAt288 12 13 :=
  interval_of_check leafTestAt288 12 1 (by decide +kernel)

theorem leafTestAt288_block_13 : Interval leafTestAt288 13 14 :=
  interval_of_check leafTestAt288 13 1 (by decide +kernel)

theorem leafTestAt288_block_14 : Interval leafTestAt288 14 15 :=
  interval_of_check leafTestAt288 14 1 (by decide +kernel)

theorem leafTestAt288_block_15 : Interval leafTestAt288 15 16 :=
  interval_of_check leafTestAt288 15 1 (by decide +kernel)

theorem leafTestAt288_block_16 : Interval leafTestAt288 16 17 :=
  interval_of_check leafTestAt288 16 1 (by decide +kernel)

theorem leafTestAt288_block_17 : Interval leafTestAt288 17 18 :=
  interval_of_check leafTestAt288 17 1 (by decide +kernel)

theorem leafTestAt288_block_18 : Interval leafTestAt288 18 19 :=
  interval_of_check leafTestAt288 18 1 (by decide +kernel)

theorem leafTestAt288_block_19 : Interval leafTestAt288 19 20 :=
  interval_of_check leafTestAt288 19 1 (by decide +kernel)

theorem leafTestAt288_block_20 : Interval leafTestAt288 20 21 :=
  interval_of_check leafTestAt288 20 1 (by decide +kernel)

theorem leafTestAt288_block_21 : Interval leafTestAt288 21 22 :=
  interval_of_check leafTestAt288 21 1 (by decide +kernel)

theorem leafTestAt288_block_22 : Interval leafTestAt288 22 23 :=
  interval_of_check leafTestAt288 22 1 (by decide +kernel)

theorem leafTestAt288_block_23 : Interval leafTestAt288 23 24 :=
  interval_of_check leafTestAt288 23 1 (by decide +kernel)

theorem leafTestAt288_block_24 : Interval leafTestAt288 24 25 :=
  interval_of_check leafTestAt288 24 1 (by decide +kernel)

theorem leafTestAt288_block_25 : Interval leafTestAt288 25 26 :=
  interval_of_check leafTestAt288 25 1 (by decide +kernel)

theorem leafTestAt288_block_26 : Interval leafTestAt288 26 27 :=
  interval_of_check leafTestAt288 26 1 (by decide +kernel)

theorem leafTestAt288_block_27 : Interval leafTestAt288 27 28 :=
  interval_of_check leafTestAt288 27 1 (by decide +kernel)

theorem leafTestAt288_block_28 : Interval leafTestAt288 28 29 :=
  interval_of_check leafTestAt288 28 1 (by decide +kernel)

theorem leafTestAt288_block_29 : Interval leafTestAt288 29 30 :=
  interval_of_check leafTestAt288 29 1 (by decide +kernel)

theorem leafTestAt288_block_30 : Interval leafTestAt288 30 31 :=
  interval_of_check leafTestAt288 30 1 (by decide +kernel)

theorem leafTestAt288_block_31 : Interval leafTestAt288 31 32 :=
  interval_of_check leafTestAt288 31 1 (by decide +kernel)

theorem leafTestAt288_complete : Interval leafTestAt288 0 32 :=
  (interval_append leafTestAt288 0 16 32
  (interval_append leafTestAt288 0 8 16
  (interval_append leafTestAt288 0 4 8
  (interval_append leafTestAt288 0 2 4
  (interval_append leafTestAt288 0 1 2
  leafTestAt288_block_0
  leafTestAt288_block_1)
  (interval_append leafTestAt288 2 3 4
  leafTestAt288_block_2
  leafTestAt288_block_3))
  (interval_append leafTestAt288 4 6 8
  (interval_append leafTestAt288 4 5 6
  leafTestAt288_block_4
  leafTestAt288_block_5)
  (interval_append leafTestAt288 6 7 8
  leafTestAt288_block_6
  leafTestAt288_block_7)))
  (interval_append leafTestAt288 8 12 16
  (interval_append leafTestAt288 8 10 12
  (interval_append leafTestAt288 8 9 10
  leafTestAt288_block_8
  leafTestAt288_block_9)
  (interval_append leafTestAt288 10 11 12
  leafTestAt288_block_10
  leafTestAt288_block_11))
  (interval_append leafTestAt288 12 14 16
  (interval_append leafTestAt288 12 13 14
  leafTestAt288_block_12
  leafTestAt288_block_13)
  (interval_append leafTestAt288 14 15 16
  leafTestAt288_block_14
  leafTestAt288_block_15))))
  (interval_append leafTestAt288 16 24 32
  (interval_append leafTestAt288 16 20 24
  (interval_append leafTestAt288 16 18 20
  (interval_append leafTestAt288 16 17 18
  leafTestAt288_block_16
  leafTestAt288_block_17)
  (interval_append leafTestAt288 18 19 20
  leafTestAt288_block_18
  leafTestAt288_block_19))
  (interval_append leafTestAt288 20 22 24
  (interval_append leafTestAt288 20 21 22
  leafTestAt288_block_20
  leafTestAt288_block_21)
  (interval_append leafTestAt288 22 23 24
  leafTestAt288_block_22
  leafTestAt288_block_23)))
  (interval_append leafTestAt288 24 28 32
  (interval_append leafTestAt288 24 26 28
  (interval_append leafTestAt288 24 25 26
  leafTestAt288_block_24
  leafTestAt288_block_25)
  (interval_append leafTestAt288 26 27 28
  leafTestAt288_block_26
  leafTestAt288_block_27))
  (interval_append leafTestAt288 28 30 32
  (interval_append leafTestAt288 28 29 30
  leafTestAt288_block_28
  leafTestAt288_block_29)
  (interval_append leafTestAt288 30 31 32
  leafTestAt288_block_30
  leafTestAt288_block_31)))))
theorem leafInterval288 : Interval leafTest 288 320 := by
  intro i hlo hhi
  have h := leafTestAt288_complete (i-288) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt288, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
