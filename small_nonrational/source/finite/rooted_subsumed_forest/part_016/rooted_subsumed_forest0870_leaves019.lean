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
def leafTestAt608 (i : Nat) := leafTest (i+608)
theorem leafTestAt608_block_0 : Interval leafTestAt608 0 1 :=
  interval_of_check leafTestAt608 0 1 (by decide +kernel)

theorem leafTestAt608_block_1 : Interval leafTestAt608 1 2 :=
  interval_of_check leafTestAt608 1 1 (by decide +kernel)

theorem leafTestAt608_block_2 : Interval leafTestAt608 2 3 :=
  interval_of_check leafTestAt608 2 1 (by decide +kernel)

theorem leafTestAt608_block_3 : Interval leafTestAt608 3 4 :=
  interval_of_check leafTestAt608 3 1 (by decide +kernel)

theorem leafTestAt608_block_4 : Interval leafTestAt608 4 5 :=
  interval_of_check leafTestAt608 4 1 (by decide +kernel)

theorem leafTestAt608_block_5 : Interval leafTestAt608 5 6 :=
  interval_of_check leafTestAt608 5 1 (by decide +kernel)

theorem leafTestAt608_block_6 : Interval leafTestAt608 6 7 :=
  interval_of_check leafTestAt608 6 1 (by decide +kernel)

theorem leafTestAt608_block_7 : Interval leafTestAt608 7 8 :=
  interval_of_check leafTestAt608 7 1 (by decide +kernel)

theorem leafTestAt608_block_8 : Interval leafTestAt608 8 9 :=
  interval_of_check leafTestAt608 8 1 (by decide +kernel)

theorem leafTestAt608_block_9 : Interval leafTestAt608 9 10 :=
  interval_of_check leafTestAt608 9 1 (by decide +kernel)

theorem leafTestAt608_block_10 : Interval leafTestAt608 10 11 :=
  interval_of_check leafTestAt608 10 1 (by decide +kernel)

theorem leafTestAt608_block_11 : Interval leafTestAt608 11 12 :=
  interval_of_check leafTestAt608 11 1 (by decide +kernel)

theorem leafTestAt608_block_12 : Interval leafTestAt608 12 13 :=
  interval_of_check leafTestAt608 12 1 (by decide +kernel)

theorem leafTestAt608_block_13 : Interval leafTestAt608 13 14 :=
  interval_of_check leafTestAt608 13 1 (by decide +kernel)

theorem leafTestAt608_block_14 : Interval leafTestAt608 14 15 :=
  interval_of_check leafTestAt608 14 1 (by decide +kernel)

theorem leafTestAt608_block_15 : Interval leafTestAt608 15 16 :=
  interval_of_check leafTestAt608 15 1 (by decide +kernel)

theorem leafTestAt608_block_16 : Interval leafTestAt608 16 17 :=
  interval_of_check leafTestAt608 16 1 (by decide +kernel)

theorem leafTestAt608_block_17 : Interval leafTestAt608 17 18 :=
  interval_of_check leafTestAt608 17 1 (by decide +kernel)

theorem leafTestAt608_block_18 : Interval leafTestAt608 18 19 :=
  interval_of_check leafTestAt608 18 1 (by decide +kernel)

theorem leafTestAt608_block_19 : Interval leafTestAt608 19 20 :=
  interval_of_check leafTestAt608 19 1 (by decide +kernel)

theorem leafTestAt608_block_20 : Interval leafTestAt608 20 21 :=
  interval_of_check leafTestAt608 20 1 (by decide +kernel)

theorem leafTestAt608_block_21 : Interval leafTestAt608 21 22 :=
  interval_of_check leafTestAt608 21 1 (by decide +kernel)

theorem leafTestAt608_block_22 : Interval leafTestAt608 22 23 :=
  interval_of_check leafTestAt608 22 1 (by decide +kernel)

theorem leafTestAt608_block_23 : Interval leafTestAt608 23 24 :=
  interval_of_check leafTestAt608 23 1 (by decide +kernel)

theorem leafTestAt608_block_24 : Interval leafTestAt608 24 25 :=
  interval_of_check leafTestAt608 24 1 (by decide +kernel)

theorem leafTestAt608_block_25 : Interval leafTestAt608 25 26 :=
  interval_of_check leafTestAt608 25 1 (by decide +kernel)

theorem leafTestAt608_block_26 : Interval leafTestAt608 26 27 :=
  interval_of_check leafTestAt608 26 1 (by decide +kernel)

theorem leafTestAt608_block_27 : Interval leafTestAt608 27 28 :=
  interval_of_check leafTestAt608 27 1 (by decide +kernel)

theorem leafTestAt608_block_28 : Interval leafTestAt608 28 29 :=
  interval_of_check leafTestAt608 28 1 (by decide +kernel)

theorem leafTestAt608_block_29 : Interval leafTestAt608 29 30 :=
  interval_of_check leafTestAt608 29 1 (by decide +kernel)

theorem leafTestAt608_block_30 : Interval leafTestAt608 30 31 :=
  interval_of_check leafTestAt608 30 1 (by decide +kernel)

theorem leafTestAt608_block_31 : Interval leafTestAt608 31 32 :=
  interval_of_check leafTestAt608 31 1 (by decide +kernel)

theorem leafTestAt608_complete : Interval leafTestAt608 0 32 :=
  (interval_append leafTestAt608 0 16 32
  (interval_append leafTestAt608 0 8 16
  (interval_append leafTestAt608 0 4 8
  (interval_append leafTestAt608 0 2 4
  (interval_append leafTestAt608 0 1 2
  leafTestAt608_block_0
  leafTestAt608_block_1)
  (interval_append leafTestAt608 2 3 4
  leafTestAt608_block_2
  leafTestAt608_block_3))
  (interval_append leafTestAt608 4 6 8
  (interval_append leafTestAt608 4 5 6
  leafTestAt608_block_4
  leafTestAt608_block_5)
  (interval_append leafTestAt608 6 7 8
  leafTestAt608_block_6
  leafTestAt608_block_7)))
  (interval_append leafTestAt608 8 12 16
  (interval_append leafTestAt608 8 10 12
  (interval_append leafTestAt608 8 9 10
  leafTestAt608_block_8
  leafTestAt608_block_9)
  (interval_append leafTestAt608 10 11 12
  leafTestAt608_block_10
  leafTestAt608_block_11))
  (interval_append leafTestAt608 12 14 16
  (interval_append leafTestAt608 12 13 14
  leafTestAt608_block_12
  leafTestAt608_block_13)
  (interval_append leafTestAt608 14 15 16
  leafTestAt608_block_14
  leafTestAt608_block_15))))
  (interval_append leafTestAt608 16 24 32
  (interval_append leafTestAt608 16 20 24
  (interval_append leafTestAt608 16 18 20
  (interval_append leafTestAt608 16 17 18
  leafTestAt608_block_16
  leafTestAt608_block_17)
  (interval_append leafTestAt608 18 19 20
  leafTestAt608_block_18
  leafTestAt608_block_19))
  (interval_append leafTestAt608 20 22 24
  (interval_append leafTestAt608 20 21 22
  leafTestAt608_block_20
  leafTestAt608_block_21)
  (interval_append leafTestAt608 22 23 24
  leafTestAt608_block_22
  leafTestAt608_block_23)))
  (interval_append leafTestAt608 24 28 32
  (interval_append leafTestAt608 24 26 28
  (interval_append leafTestAt608 24 25 26
  leafTestAt608_block_24
  leafTestAt608_block_25)
  (interval_append leafTestAt608 26 27 28
  leafTestAt608_block_26
  leafTestAt608_block_27))
  (interval_append leafTestAt608 28 30 32
  (interval_append leafTestAt608 28 29 30
  leafTestAt608_block_28
  leafTestAt608_block_29)
  (interval_append leafTestAt608 30 31 32
  leafTestAt608_block_30
  leafTestAt608_block_31)))))
theorem leafInterval608 : Interval leafTest 608 640 := by
  intro i hlo hhi
  have h := leafTestAt608_complete (i-608) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt608, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
