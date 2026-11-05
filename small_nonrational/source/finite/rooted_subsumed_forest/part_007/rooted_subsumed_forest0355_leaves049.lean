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
def leafTestAt1568 (i : Nat) := leafTest (i+1568)
theorem leafTestAt1568_block_0 : Interval leafTestAt1568 0 1 :=
  interval_of_check leafTestAt1568 0 1 (by decide +kernel)

theorem leafTestAt1568_block_1 : Interval leafTestAt1568 1 2 :=
  interval_of_check leafTestAt1568 1 1 (by decide +kernel)

theorem leafTestAt1568_block_2 : Interval leafTestAt1568 2 3 :=
  interval_of_check leafTestAt1568 2 1 (by decide +kernel)

theorem leafTestAt1568_block_3 : Interval leafTestAt1568 3 4 :=
  interval_of_check leafTestAt1568 3 1 (by decide +kernel)

theorem leafTestAt1568_block_4 : Interval leafTestAt1568 4 5 :=
  interval_of_check leafTestAt1568 4 1 (by decide +kernel)

theorem leafTestAt1568_block_5 : Interval leafTestAt1568 5 6 :=
  interval_of_check leafTestAt1568 5 1 (by decide +kernel)

theorem leafTestAt1568_block_6 : Interval leafTestAt1568 6 7 :=
  interval_of_check leafTestAt1568 6 1 (by decide +kernel)

theorem leafTestAt1568_block_7 : Interval leafTestAt1568 7 8 :=
  interval_of_check leafTestAt1568 7 1 (by decide +kernel)

theorem leafTestAt1568_block_8 : Interval leafTestAt1568 8 9 :=
  interval_of_check leafTestAt1568 8 1 (by decide +kernel)

theorem leafTestAt1568_block_9 : Interval leafTestAt1568 9 10 :=
  interval_of_check leafTestAt1568 9 1 (by decide +kernel)

theorem leafTestAt1568_block_10 : Interval leafTestAt1568 10 11 :=
  interval_of_check leafTestAt1568 10 1 (by decide +kernel)

theorem leafTestAt1568_block_11 : Interval leafTestAt1568 11 12 :=
  interval_of_check leafTestAt1568 11 1 (by decide +kernel)

theorem leafTestAt1568_block_12 : Interval leafTestAt1568 12 13 :=
  interval_of_check leafTestAt1568 12 1 (by decide +kernel)

theorem leafTestAt1568_block_13 : Interval leafTestAt1568 13 14 :=
  interval_of_check leafTestAt1568 13 1 (by decide +kernel)

theorem leafTestAt1568_block_14 : Interval leafTestAt1568 14 15 :=
  interval_of_check leafTestAt1568 14 1 (by decide +kernel)

theorem leafTestAt1568_block_15 : Interval leafTestAt1568 15 16 :=
  interval_of_check leafTestAt1568 15 1 (by decide +kernel)

theorem leafTestAt1568_block_16 : Interval leafTestAt1568 16 17 :=
  interval_of_check leafTestAt1568 16 1 (by decide +kernel)

theorem leafTestAt1568_block_17 : Interval leafTestAt1568 17 18 :=
  interval_of_check leafTestAt1568 17 1 (by decide +kernel)

theorem leafTestAt1568_block_18 : Interval leafTestAt1568 18 19 :=
  interval_of_check leafTestAt1568 18 1 (by decide +kernel)

theorem leafTestAt1568_block_19 : Interval leafTestAt1568 19 20 :=
  interval_of_check leafTestAt1568 19 1 (by decide +kernel)

theorem leafTestAt1568_block_20 : Interval leafTestAt1568 20 21 :=
  interval_of_check leafTestAt1568 20 1 (by decide +kernel)

theorem leafTestAt1568_block_21 : Interval leafTestAt1568 21 22 :=
  interval_of_check leafTestAt1568 21 1 (by decide +kernel)

theorem leafTestAt1568_block_22 : Interval leafTestAt1568 22 23 :=
  interval_of_check leafTestAt1568 22 1 (by decide +kernel)

theorem leafTestAt1568_block_23 : Interval leafTestAt1568 23 24 :=
  interval_of_check leafTestAt1568 23 1 (by decide +kernel)

theorem leafTestAt1568_block_24 : Interval leafTestAt1568 24 25 :=
  interval_of_check leafTestAt1568 24 1 (by decide +kernel)

theorem leafTestAt1568_block_25 : Interval leafTestAt1568 25 26 :=
  interval_of_check leafTestAt1568 25 1 (by decide +kernel)

theorem leafTestAt1568_block_26 : Interval leafTestAt1568 26 27 :=
  interval_of_check leafTestAt1568 26 1 (by decide +kernel)

theorem leafTestAt1568_block_27 : Interval leafTestAt1568 27 28 :=
  interval_of_check leafTestAt1568 27 1 (by decide +kernel)

theorem leafTestAt1568_block_28 : Interval leafTestAt1568 28 29 :=
  interval_of_check leafTestAt1568 28 1 (by decide +kernel)

theorem leafTestAt1568_block_29 : Interval leafTestAt1568 29 30 :=
  interval_of_check leafTestAt1568 29 1 (by decide +kernel)

theorem leafTestAt1568_block_30 : Interval leafTestAt1568 30 31 :=
  interval_of_check leafTestAt1568 30 1 (by decide +kernel)

theorem leafTestAt1568_block_31 : Interval leafTestAt1568 31 32 :=
  interval_of_check leafTestAt1568 31 1 (by decide +kernel)

theorem leafTestAt1568_complete : Interval leafTestAt1568 0 32 :=
  (interval_append leafTestAt1568 0 16 32
  (interval_append leafTestAt1568 0 8 16
  (interval_append leafTestAt1568 0 4 8
  (interval_append leafTestAt1568 0 2 4
  (interval_append leafTestAt1568 0 1 2
  leafTestAt1568_block_0
  leafTestAt1568_block_1)
  (interval_append leafTestAt1568 2 3 4
  leafTestAt1568_block_2
  leafTestAt1568_block_3))
  (interval_append leafTestAt1568 4 6 8
  (interval_append leafTestAt1568 4 5 6
  leafTestAt1568_block_4
  leafTestAt1568_block_5)
  (interval_append leafTestAt1568 6 7 8
  leafTestAt1568_block_6
  leafTestAt1568_block_7)))
  (interval_append leafTestAt1568 8 12 16
  (interval_append leafTestAt1568 8 10 12
  (interval_append leafTestAt1568 8 9 10
  leafTestAt1568_block_8
  leafTestAt1568_block_9)
  (interval_append leafTestAt1568 10 11 12
  leafTestAt1568_block_10
  leafTestAt1568_block_11))
  (interval_append leafTestAt1568 12 14 16
  (interval_append leafTestAt1568 12 13 14
  leafTestAt1568_block_12
  leafTestAt1568_block_13)
  (interval_append leafTestAt1568 14 15 16
  leafTestAt1568_block_14
  leafTestAt1568_block_15))))
  (interval_append leafTestAt1568 16 24 32
  (interval_append leafTestAt1568 16 20 24
  (interval_append leafTestAt1568 16 18 20
  (interval_append leafTestAt1568 16 17 18
  leafTestAt1568_block_16
  leafTestAt1568_block_17)
  (interval_append leafTestAt1568 18 19 20
  leafTestAt1568_block_18
  leafTestAt1568_block_19))
  (interval_append leafTestAt1568 20 22 24
  (interval_append leafTestAt1568 20 21 22
  leafTestAt1568_block_20
  leafTestAt1568_block_21)
  (interval_append leafTestAt1568 22 23 24
  leafTestAt1568_block_22
  leafTestAt1568_block_23)))
  (interval_append leafTestAt1568 24 28 32
  (interval_append leafTestAt1568 24 26 28
  (interval_append leafTestAt1568 24 25 26
  leafTestAt1568_block_24
  leafTestAt1568_block_25)
  (interval_append leafTestAt1568 26 27 28
  leafTestAt1568_block_26
  leafTestAt1568_block_27))
  (interval_append leafTestAt1568 28 30 32
  (interval_append leafTestAt1568 28 29 30
  leafTestAt1568_block_28
  leafTestAt1568_block_29)
  (interval_append leafTestAt1568 30 31 32
  leafTestAt1568_block_30
  leafTestAt1568_block_31)))))
theorem leafInterval1568 : Interval leafTest 1568 1600 := by
  intro i hlo hhi
  have h := leafTestAt1568_complete (i-1568) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt1568, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
