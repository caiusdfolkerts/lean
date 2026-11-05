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
def leafTestAt480 (i : Nat) := leafTest (i+480)
theorem leafTestAt480_block_0 : Interval leafTestAt480 0 1 :=
  interval_of_check leafTestAt480 0 1 (by decide +kernel)

theorem leafTestAt480_block_1 : Interval leafTestAt480 1 2 :=
  interval_of_check leafTestAt480 1 1 (by decide +kernel)

theorem leafTestAt480_block_2 : Interval leafTestAt480 2 3 :=
  interval_of_check leafTestAt480 2 1 (by decide +kernel)

theorem leafTestAt480_block_3 : Interval leafTestAt480 3 4 :=
  interval_of_check leafTestAt480 3 1 (by decide +kernel)

theorem leafTestAt480_block_4 : Interval leafTestAt480 4 5 :=
  interval_of_check leafTestAt480 4 1 (by decide +kernel)

theorem leafTestAt480_block_5 : Interval leafTestAt480 5 6 :=
  interval_of_check leafTestAt480 5 1 (by decide +kernel)

theorem leafTestAt480_block_6 : Interval leafTestAt480 6 7 :=
  interval_of_check leafTestAt480 6 1 (by decide +kernel)

theorem leafTestAt480_block_7 : Interval leafTestAt480 7 8 :=
  interval_of_check leafTestAt480 7 1 (by decide +kernel)

theorem leafTestAt480_block_8 : Interval leafTestAt480 8 9 :=
  interval_of_check leafTestAt480 8 1 (by decide +kernel)

theorem leafTestAt480_block_9 : Interval leafTestAt480 9 10 :=
  interval_of_check leafTestAt480 9 1 (by decide +kernel)

theorem leafTestAt480_block_10 : Interval leafTestAt480 10 11 :=
  interval_of_check leafTestAt480 10 1 (by decide +kernel)

theorem leafTestAt480_block_11 : Interval leafTestAt480 11 12 :=
  interval_of_check leafTestAt480 11 1 (by decide +kernel)

theorem leafTestAt480_block_12 : Interval leafTestAt480 12 13 :=
  interval_of_check leafTestAt480 12 1 (by decide +kernel)

theorem leafTestAt480_block_13 : Interval leafTestAt480 13 14 :=
  interval_of_check leafTestAt480 13 1 (by decide +kernel)

theorem leafTestAt480_block_14 : Interval leafTestAt480 14 15 :=
  interval_of_check leafTestAt480 14 1 (by decide +kernel)

theorem leafTestAt480_block_15 : Interval leafTestAt480 15 16 :=
  interval_of_check leafTestAt480 15 1 (by decide +kernel)

theorem leafTestAt480_block_16 : Interval leafTestAt480 16 17 :=
  interval_of_check leafTestAt480 16 1 (by decide +kernel)

theorem leafTestAt480_block_17 : Interval leafTestAt480 17 18 :=
  interval_of_check leafTestAt480 17 1 (by decide +kernel)

theorem leafTestAt480_block_18 : Interval leafTestAt480 18 19 :=
  interval_of_check leafTestAt480 18 1 (by decide +kernel)

theorem leafTestAt480_block_19 : Interval leafTestAt480 19 20 :=
  interval_of_check leafTestAt480 19 1 (by decide +kernel)

theorem leafTestAt480_block_20 : Interval leafTestAt480 20 21 :=
  interval_of_check leafTestAt480 20 1 (by decide +kernel)

theorem leafTestAt480_block_21 : Interval leafTestAt480 21 22 :=
  interval_of_check leafTestAt480 21 1 (by decide +kernel)

theorem leafTestAt480_block_22 : Interval leafTestAt480 22 23 :=
  interval_of_check leafTestAt480 22 1 (by decide +kernel)

theorem leafTestAt480_block_23 : Interval leafTestAt480 23 24 :=
  interval_of_check leafTestAt480 23 1 (by decide +kernel)

theorem leafTestAt480_block_24 : Interval leafTestAt480 24 25 :=
  interval_of_check leafTestAt480 24 1 (by decide +kernel)

theorem leafTestAt480_block_25 : Interval leafTestAt480 25 26 :=
  interval_of_check leafTestAt480 25 1 (by decide +kernel)

theorem leafTestAt480_block_26 : Interval leafTestAt480 26 27 :=
  interval_of_check leafTestAt480 26 1 (by decide +kernel)

theorem leafTestAt480_block_27 : Interval leafTestAt480 27 28 :=
  interval_of_check leafTestAt480 27 1 (by decide +kernel)

theorem leafTestAt480_block_28 : Interval leafTestAt480 28 29 :=
  interval_of_check leafTestAt480 28 1 (by decide +kernel)

theorem leafTestAt480_block_29 : Interval leafTestAt480 29 30 :=
  interval_of_check leafTestAt480 29 1 (by decide +kernel)

theorem leafTestAt480_block_30 : Interval leafTestAt480 30 31 :=
  interval_of_check leafTestAt480 30 1 (by decide +kernel)

theorem leafTestAt480_block_31 : Interval leafTestAt480 31 32 :=
  interval_of_check leafTestAt480 31 1 (by decide +kernel)

theorem leafTestAt480_complete : Interval leafTestAt480 0 32 :=
  (interval_append leafTestAt480 0 16 32
  (interval_append leafTestAt480 0 8 16
  (interval_append leafTestAt480 0 4 8
  (interval_append leafTestAt480 0 2 4
  (interval_append leafTestAt480 0 1 2
  leafTestAt480_block_0
  leafTestAt480_block_1)
  (interval_append leafTestAt480 2 3 4
  leafTestAt480_block_2
  leafTestAt480_block_3))
  (interval_append leafTestAt480 4 6 8
  (interval_append leafTestAt480 4 5 6
  leafTestAt480_block_4
  leafTestAt480_block_5)
  (interval_append leafTestAt480 6 7 8
  leafTestAt480_block_6
  leafTestAt480_block_7)))
  (interval_append leafTestAt480 8 12 16
  (interval_append leafTestAt480 8 10 12
  (interval_append leafTestAt480 8 9 10
  leafTestAt480_block_8
  leafTestAt480_block_9)
  (interval_append leafTestAt480 10 11 12
  leafTestAt480_block_10
  leafTestAt480_block_11))
  (interval_append leafTestAt480 12 14 16
  (interval_append leafTestAt480 12 13 14
  leafTestAt480_block_12
  leafTestAt480_block_13)
  (interval_append leafTestAt480 14 15 16
  leafTestAt480_block_14
  leafTestAt480_block_15))))
  (interval_append leafTestAt480 16 24 32
  (interval_append leafTestAt480 16 20 24
  (interval_append leafTestAt480 16 18 20
  (interval_append leafTestAt480 16 17 18
  leafTestAt480_block_16
  leafTestAt480_block_17)
  (interval_append leafTestAt480 18 19 20
  leafTestAt480_block_18
  leafTestAt480_block_19))
  (interval_append leafTestAt480 20 22 24
  (interval_append leafTestAt480 20 21 22
  leafTestAt480_block_20
  leafTestAt480_block_21)
  (interval_append leafTestAt480 22 23 24
  leafTestAt480_block_22
  leafTestAt480_block_23)))
  (interval_append leafTestAt480 24 28 32
  (interval_append leafTestAt480 24 26 28
  (interval_append leafTestAt480 24 25 26
  leafTestAt480_block_24
  leafTestAt480_block_25)
  (interval_append leafTestAt480 26 27 28
  leafTestAt480_block_26
  leafTestAt480_block_27))
  (interval_append leafTestAt480 28 30 32
  (interval_append leafTestAt480 28 29 30
  leafTestAt480_block_28
  leafTestAt480_block_29)
  (interval_append leafTestAt480 30 31 32
  leafTestAt480_block_30
  leafTestAt480_block_31)))))
theorem leafInterval480 : Interval leafTest 480 512 := by
  intro i hlo hhi
  have h := leafTestAt480_complete (i-480) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
