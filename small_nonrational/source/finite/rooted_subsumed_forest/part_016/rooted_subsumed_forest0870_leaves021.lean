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
def leafTestAt672 (i : Nat) := leafTest (i+672)
theorem leafTestAt672_block_0 : Interval leafTestAt672 0 1 :=
  interval_of_check leafTestAt672 0 1 (by decide +kernel)

theorem leafTestAt672_block_1 : Interval leafTestAt672 1 2 :=
  interval_of_check leafTestAt672 1 1 (by decide +kernel)

theorem leafTestAt672_block_2 : Interval leafTestAt672 2 3 :=
  interval_of_check leafTestAt672 2 1 (by decide +kernel)

theorem leafTestAt672_block_3 : Interval leafTestAt672 3 4 :=
  interval_of_check leafTestAt672 3 1 (by decide +kernel)

theorem leafTestAt672_block_4 : Interval leafTestAt672 4 5 :=
  interval_of_check leafTestAt672 4 1 (by decide +kernel)

theorem leafTestAt672_block_5 : Interval leafTestAt672 5 6 :=
  interval_of_check leafTestAt672 5 1 (by decide +kernel)

theorem leafTestAt672_block_6 : Interval leafTestAt672 6 7 :=
  interval_of_check leafTestAt672 6 1 (by decide +kernel)

theorem leafTestAt672_block_7 : Interval leafTestAt672 7 8 :=
  interval_of_check leafTestAt672 7 1 (by decide +kernel)

theorem leafTestAt672_block_8 : Interval leafTestAt672 8 9 :=
  interval_of_check leafTestAt672 8 1 (by decide +kernel)

theorem leafTestAt672_block_9 : Interval leafTestAt672 9 10 :=
  interval_of_check leafTestAt672 9 1 (by decide +kernel)

theorem leafTestAt672_block_10 : Interval leafTestAt672 10 11 :=
  interval_of_check leafTestAt672 10 1 (by decide +kernel)

theorem leafTestAt672_block_11 : Interval leafTestAt672 11 12 :=
  interval_of_check leafTestAt672 11 1 (by decide +kernel)

theorem leafTestAt672_block_12 : Interval leafTestAt672 12 13 :=
  interval_of_check leafTestAt672 12 1 (by decide +kernel)

theorem leafTestAt672_block_13 : Interval leafTestAt672 13 14 :=
  interval_of_check leafTestAt672 13 1 (by decide +kernel)

theorem leafTestAt672_block_14 : Interval leafTestAt672 14 15 :=
  interval_of_check leafTestAt672 14 1 (by decide +kernel)

theorem leafTestAt672_block_15 : Interval leafTestAt672 15 16 :=
  interval_of_check leafTestAt672 15 1 (by decide +kernel)

theorem leafTestAt672_block_16 : Interval leafTestAt672 16 17 :=
  interval_of_check leafTestAt672 16 1 (by decide +kernel)

theorem leafTestAt672_block_17 : Interval leafTestAt672 17 18 :=
  interval_of_check leafTestAt672 17 1 (by decide +kernel)

theorem leafTestAt672_block_18 : Interval leafTestAt672 18 19 :=
  interval_of_check leafTestAt672 18 1 (by decide +kernel)

theorem leafTestAt672_block_19 : Interval leafTestAt672 19 20 :=
  interval_of_check leafTestAt672 19 1 (by decide +kernel)

theorem leafTestAt672_block_20 : Interval leafTestAt672 20 21 :=
  interval_of_check leafTestAt672 20 1 (by decide +kernel)

theorem leafTestAt672_block_21 : Interval leafTestAt672 21 22 :=
  interval_of_check leafTestAt672 21 1 (by decide +kernel)

theorem leafTestAt672_block_22 : Interval leafTestAt672 22 23 :=
  interval_of_check leafTestAt672 22 1 (by decide +kernel)

theorem leafTestAt672_block_23 : Interval leafTestAt672 23 24 :=
  interval_of_check leafTestAt672 23 1 (by decide +kernel)

theorem leafTestAt672_block_24 : Interval leafTestAt672 24 25 :=
  interval_of_check leafTestAt672 24 1 (by decide +kernel)

theorem leafTestAt672_block_25 : Interval leafTestAt672 25 26 :=
  interval_of_check leafTestAt672 25 1 (by decide +kernel)

theorem leafTestAt672_block_26 : Interval leafTestAt672 26 27 :=
  interval_of_check leafTestAt672 26 1 (by decide +kernel)

theorem leafTestAt672_block_27 : Interval leafTestAt672 27 28 :=
  interval_of_check leafTestAt672 27 1 (by decide +kernel)

theorem leafTestAt672_block_28 : Interval leafTestAt672 28 29 :=
  interval_of_check leafTestAt672 28 1 (by decide +kernel)

theorem leafTestAt672_block_29 : Interval leafTestAt672 29 30 :=
  interval_of_check leafTestAt672 29 1 (by decide +kernel)

theorem leafTestAt672_block_30 : Interval leafTestAt672 30 31 :=
  interval_of_check leafTestAt672 30 1 (by decide +kernel)

theorem leafTestAt672_block_31 : Interval leafTestAt672 31 32 :=
  interval_of_check leafTestAt672 31 1 (by decide +kernel)

theorem leafTestAt672_complete : Interval leafTestAt672 0 32 :=
  (interval_append leafTestAt672 0 16 32
  (interval_append leafTestAt672 0 8 16
  (interval_append leafTestAt672 0 4 8
  (interval_append leafTestAt672 0 2 4
  (interval_append leafTestAt672 0 1 2
  leafTestAt672_block_0
  leafTestAt672_block_1)
  (interval_append leafTestAt672 2 3 4
  leafTestAt672_block_2
  leafTestAt672_block_3))
  (interval_append leafTestAt672 4 6 8
  (interval_append leafTestAt672 4 5 6
  leafTestAt672_block_4
  leafTestAt672_block_5)
  (interval_append leafTestAt672 6 7 8
  leafTestAt672_block_6
  leafTestAt672_block_7)))
  (interval_append leafTestAt672 8 12 16
  (interval_append leafTestAt672 8 10 12
  (interval_append leafTestAt672 8 9 10
  leafTestAt672_block_8
  leafTestAt672_block_9)
  (interval_append leafTestAt672 10 11 12
  leafTestAt672_block_10
  leafTestAt672_block_11))
  (interval_append leafTestAt672 12 14 16
  (interval_append leafTestAt672 12 13 14
  leafTestAt672_block_12
  leafTestAt672_block_13)
  (interval_append leafTestAt672 14 15 16
  leafTestAt672_block_14
  leafTestAt672_block_15))))
  (interval_append leafTestAt672 16 24 32
  (interval_append leafTestAt672 16 20 24
  (interval_append leafTestAt672 16 18 20
  (interval_append leafTestAt672 16 17 18
  leafTestAt672_block_16
  leafTestAt672_block_17)
  (interval_append leafTestAt672 18 19 20
  leafTestAt672_block_18
  leafTestAt672_block_19))
  (interval_append leafTestAt672 20 22 24
  (interval_append leafTestAt672 20 21 22
  leafTestAt672_block_20
  leafTestAt672_block_21)
  (interval_append leafTestAt672 22 23 24
  leafTestAt672_block_22
  leafTestAt672_block_23)))
  (interval_append leafTestAt672 24 28 32
  (interval_append leafTestAt672 24 26 28
  (interval_append leafTestAt672 24 25 26
  leafTestAt672_block_24
  leafTestAt672_block_25)
  (interval_append leafTestAt672 26 27 28
  leafTestAt672_block_26
  leafTestAt672_block_27))
  (interval_append leafTestAt672 28 30 32
  (interval_append leafTestAt672 28 29 30
  leafTestAt672_block_28
  leafTestAt672_block_29)
  (interval_append leafTestAt672 30 31 32
  leafTestAt672_block_30
  leafTestAt672_block_31)))))
theorem leafInterval672 : Interval leafTest 672 704 := by
  intro i hlo hhi
  have h := leafTestAt672_complete (i-672) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt672, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
