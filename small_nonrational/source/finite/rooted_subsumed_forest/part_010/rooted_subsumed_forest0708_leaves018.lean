module
prelude
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt576 (i : Nat) := leafTest (i+576)
theorem leafTestAt576_block_0 : Interval leafTestAt576 0 1 :=
  interval_of_check leafTestAt576 0 1 (by decide +kernel)

theorem leafTestAt576_block_1 : Interval leafTestAt576 1 2 :=
  interval_of_check leafTestAt576 1 1 (by decide +kernel)

theorem leafTestAt576_block_2 : Interval leafTestAt576 2 3 :=
  interval_of_check leafTestAt576 2 1 (by decide +kernel)

theorem leafTestAt576_block_3 : Interval leafTestAt576 3 4 :=
  interval_of_check leafTestAt576 3 1 (by decide +kernel)

theorem leafTestAt576_block_4 : Interval leafTestAt576 4 5 :=
  interval_of_check leafTestAt576 4 1 (by decide +kernel)

theorem leafTestAt576_block_5 : Interval leafTestAt576 5 6 :=
  interval_of_check leafTestAt576 5 1 (by decide +kernel)

theorem leafTestAt576_block_6 : Interval leafTestAt576 6 7 :=
  interval_of_check leafTestAt576 6 1 (by decide +kernel)

theorem leafTestAt576_block_7 : Interval leafTestAt576 7 8 :=
  interval_of_check leafTestAt576 7 1 (by decide +kernel)

theorem leafTestAt576_block_8 : Interval leafTestAt576 8 9 :=
  interval_of_check leafTestAt576 8 1 (by decide +kernel)

theorem leafTestAt576_block_9 : Interval leafTestAt576 9 10 :=
  interval_of_check leafTestAt576 9 1 (by decide +kernel)

theorem leafTestAt576_block_10 : Interval leafTestAt576 10 11 :=
  interval_of_check leafTestAt576 10 1 (by decide +kernel)

theorem leafTestAt576_block_11 : Interval leafTestAt576 11 12 :=
  interval_of_check leafTestAt576 11 1 (by decide +kernel)

theorem leafTestAt576_block_12 : Interval leafTestAt576 12 13 :=
  interval_of_check leafTestAt576 12 1 (by decide +kernel)

theorem leafTestAt576_block_13 : Interval leafTestAt576 13 14 :=
  interval_of_check leafTestAt576 13 1 (by decide +kernel)

theorem leafTestAt576_block_14 : Interval leafTestAt576 14 15 :=
  interval_of_check leafTestAt576 14 1 (by decide +kernel)

theorem leafTestAt576_block_15 : Interval leafTestAt576 15 16 :=
  interval_of_check leafTestAt576 15 1 (by decide +kernel)

theorem leafTestAt576_block_16 : Interval leafTestAt576 16 17 :=
  interval_of_check leafTestAt576 16 1 (by decide +kernel)

theorem leafTestAt576_block_17 : Interval leafTestAt576 17 18 :=
  interval_of_check leafTestAt576 17 1 (by decide +kernel)

theorem leafTestAt576_block_18 : Interval leafTestAt576 18 19 :=
  interval_of_check leafTestAt576 18 1 (by decide +kernel)

theorem leafTestAt576_block_19 : Interval leafTestAt576 19 20 :=
  interval_of_check leafTestAt576 19 1 (by decide +kernel)

theorem leafTestAt576_block_20 : Interval leafTestAt576 20 21 :=
  interval_of_check leafTestAt576 20 1 (by decide +kernel)

theorem leafTestAt576_block_21 : Interval leafTestAt576 21 22 :=
  interval_of_check leafTestAt576 21 1 (by decide +kernel)

theorem leafTestAt576_block_22 : Interval leafTestAt576 22 23 :=
  interval_of_check leafTestAt576 22 1 (by decide +kernel)

theorem leafTestAt576_block_23 : Interval leafTestAt576 23 24 :=
  interval_of_check leafTestAt576 23 1 (by decide +kernel)

theorem leafTestAt576_block_24 : Interval leafTestAt576 24 25 :=
  interval_of_check leafTestAt576 24 1 (by decide +kernel)

theorem leafTestAt576_block_25 : Interval leafTestAt576 25 26 :=
  interval_of_check leafTestAt576 25 1 (by decide +kernel)

theorem leafTestAt576_block_26 : Interval leafTestAt576 26 27 :=
  interval_of_check leafTestAt576 26 1 (by decide +kernel)

theorem leafTestAt576_block_27 : Interval leafTestAt576 27 28 :=
  interval_of_check leafTestAt576 27 1 (by decide +kernel)

theorem leafTestAt576_block_28 : Interval leafTestAt576 28 29 :=
  interval_of_check leafTestAt576 28 1 (by decide +kernel)

theorem leafTestAt576_block_29 : Interval leafTestAt576 29 30 :=
  interval_of_check leafTestAt576 29 1 (by decide +kernel)

theorem leafTestAt576_block_30 : Interval leafTestAt576 30 31 :=
  interval_of_check leafTestAt576 30 1 (by decide +kernel)

theorem leafTestAt576_block_31 : Interval leafTestAt576 31 32 :=
  interval_of_check leafTestAt576 31 1 (by decide +kernel)

theorem leafTestAt576_complete : Interval leafTestAt576 0 32 :=
  (interval_append leafTestAt576 0 16 32
  (interval_append leafTestAt576 0 8 16
  (interval_append leafTestAt576 0 4 8
  (interval_append leafTestAt576 0 2 4
  (interval_append leafTestAt576 0 1 2
  leafTestAt576_block_0
  leafTestAt576_block_1)
  (interval_append leafTestAt576 2 3 4
  leafTestAt576_block_2
  leafTestAt576_block_3))
  (interval_append leafTestAt576 4 6 8
  (interval_append leafTestAt576 4 5 6
  leafTestAt576_block_4
  leafTestAt576_block_5)
  (interval_append leafTestAt576 6 7 8
  leafTestAt576_block_6
  leafTestAt576_block_7)))
  (interval_append leafTestAt576 8 12 16
  (interval_append leafTestAt576 8 10 12
  (interval_append leafTestAt576 8 9 10
  leafTestAt576_block_8
  leafTestAt576_block_9)
  (interval_append leafTestAt576 10 11 12
  leafTestAt576_block_10
  leafTestAt576_block_11))
  (interval_append leafTestAt576 12 14 16
  (interval_append leafTestAt576 12 13 14
  leafTestAt576_block_12
  leafTestAt576_block_13)
  (interval_append leafTestAt576 14 15 16
  leafTestAt576_block_14
  leafTestAt576_block_15))))
  (interval_append leafTestAt576 16 24 32
  (interval_append leafTestAt576 16 20 24
  (interval_append leafTestAt576 16 18 20
  (interval_append leafTestAt576 16 17 18
  leafTestAt576_block_16
  leafTestAt576_block_17)
  (interval_append leafTestAt576 18 19 20
  leafTestAt576_block_18
  leafTestAt576_block_19))
  (interval_append leafTestAt576 20 22 24
  (interval_append leafTestAt576 20 21 22
  leafTestAt576_block_20
  leafTestAt576_block_21)
  (interval_append leafTestAt576 22 23 24
  leafTestAt576_block_22
  leafTestAt576_block_23)))
  (interval_append leafTestAt576 24 28 32
  (interval_append leafTestAt576 24 26 28
  (interval_append leafTestAt576 24 25 26
  leafTestAt576_block_24
  leafTestAt576_block_25)
  (interval_append leafTestAt576 26 27 28
  leafTestAt576_block_26
  leafTestAt576_block_27))
  (interval_append leafTestAt576 28 30 32
  (interval_append leafTestAt576 28 29 30
  leafTestAt576_block_28
  leafTestAt576_block_29)
  (interval_append leafTestAt576 30 31 32
  leafTestAt576_block_30
  leafTestAt576_block_31)))))
theorem leafInterval576 : Interval leafTest 576 608 := by
  intro i hlo hhi
  have h := leafTestAt576_complete (i-576) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt576, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
