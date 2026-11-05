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
def leafTestAt1760 (i : Nat) := leafTest (i+1760)
theorem leafTestAt1760_block_0 : Interval leafTestAt1760 0 1 :=
  interval_of_check leafTestAt1760 0 1 (by decide +kernel)

theorem leafTestAt1760_block_1 : Interval leafTestAt1760 1 2 :=
  interval_of_check leafTestAt1760 1 1 (by decide +kernel)

theorem leafTestAt1760_block_2 : Interval leafTestAt1760 2 3 :=
  interval_of_check leafTestAt1760 2 1 (by decide +kernel)

theorem leafTestAt1760_block_3 : Interval leafTestAt1760 3 4 :=
  interval_of_check leafTestAt1760 3 1 (by decide +kernel)

theorem leafTestAt1760_block_4 : Interval leafTestAt1760 4 5 :=
  interval_of_check leafTestAt1760 4 1 (by decide +kernel)

theorem leafTestAt1760_block_5 : Interval leafTestAt1760 5 6 :=
  interval_of_check leafTestAt1760 5 1 (by decide +kernel)

theorem leafTestAt1760_block_6 : Interval leafTestAt1760 6 7 :=
  interval_of_check leafTestAt1760 6 1 (by decide +kernel)

theorem leafTestAt1760_block_7 : Interval leafTestAt1760 7 8 :=
  interval_of_check leafTestAt1760 7 1 (by decide +kernel)

theorem leafTestAt1760_block_8 : Interval leafTestAt1760 8 9 :=
  interval_of_check leafTestAt1760 8 1 (by decide +kernel)

theorem leafTestAt1760_block_9 : Interval leafTestAt1760 9 10 :=
  interval_of_check leafTestAt1760 9 1 (by decide +kernel)

theorem leafTestAt1760_block_10 : Interval leafTestAt1760 10 11 :=
  interval_of_check leafTestAt1760 10 1 (by decide +kernel)

theorem leafTestAt1760_block_11 : Interval leafTestAt1760 11 12 :=
  interval_of_check leafTestAt1760 11 1 (by decide +kernel)

theorem leafTestAt1760_block_12 : Interval leafTestAt1760 12 13 :=
  interval_of_check leafTestAt1760 12 1 (by decide +kernel)

theorem leafTestAt1760_block_13 : Interval leafTestAt1760 13 14 :=
  interval_of_check leafTestAt1760 13 1 (by decide +kernel)

theorem leafTestAt1760_block_14 : Interval leafTestAt1760 14 15 :=
  interval_of_check leafTestAt1760 14 1 (by decide +kernel)

theorem leafTestAt1760_block_15 : Interval leafTestAt1760 15 16 :=
  interval_of_check leafTestAt1760 15 1 (by decide +kernel)

theorem leafTestAt1760_block_16 : Interval leafTestAt1760 16 17 :=
  interval_of_check leafTestAt1760 16 1 (by decide +kernel)

theorem leafTestAt1760_block_17 : Interval leafTestAt1760 17 18 :=
  interval_of_check leafTestAt1760 17 1 (by decide +kernel)

theorem leafTestAt1760_block_18 : Interval leafTestAt1760 18 19 :=
  interval_of_check leafTestAt1760 18 1 (by decide +kernel)

theorem leafTestAt1760_block_19 : Interval leafTestAt1760 19 20 :=
  interval_of_check leafTestAt1760 19 1 (by decide +kernel)

theorem leafTestAt1760_block_20 : Interval leafTestAt1760 20 21 :=
  interval_of_check leafTestAt1760 20 1 (by decide +kernel)

theorem leafTestAt1760_block_21 : Interval leafTestAt1760 21 22 :=
  interval_of_check leafTestAt1760 21 1 (by decide +kernel)

theorem leafTestAt1760_block_22 : Interval leafTestAt1760 22 23 :=
  interval_of_check leafTestAt1760 22 1 (by decide +kernel)

theorem leafTestAt1760_block_23 : Interval leafTestAt1760 23 24 :=
  interval_of_check leafTestAt1760 23 1 (by decide +kernel)

theorem leafTestAt1760_block_24 : Interval leafTestAt1760 24 25 :=
  interval_of_check leafTestAt1760 24 1 (by decide +kernel)

theorem leafTestAt1760_block_25 : Interval leafTestAt1760 25 26 :=
  interval_of_check leafTestAt1760 25 1 (by decide +kernel)

theorem leafTestAt1760_block_26 : Interval leafTestAt1760 26 27 :=
  interval_of_check leafTestAt1760 26 1 (by decide +kernel)

theorem leafTestAt1760_block_27 : Interval leafTestAt1760 27 28 :=
  interval_of_check leafTestAt1760 27 1 (by decide +kernel)

theorem leafTestAt1760_block_28 : Interval leafTestAt1760 28 29 :=
  interval_of_check leafTestAt1760 28 1 (by decide +kernel)

theorem leafTestAt1760_block_29 : Interval leafTestAt1760 29 30 :=
  interval_of_check leafTestAt1760 29 1 (by decide +kernel)

theorem leafTestAt1760_block_30 : Interval leafTestAt1760 30 31 :=
  interval_of_check leafTestAt1760 30 1 (by decide +kernel)

theorem leafTestAt1760_block_31 : Interval leafTestAt1760 31 32 :=
  interval_of_check leafTestAt1760 31 1 (by decide +kernel)

theorem leafTestAt1760_complete : Interval leafTestAt1760 0 32 :=
  (interval_append leafTestAt1760 0 16 32
  (interval_append leafTestAt1760 0 8 16
  (interval_append leafTestAt1760 0 4 8
  (interval_append leafTestAt1760 0 2 4
  (interval_append leafTestAt1760 0 1 2
  leafTestAt1760_block_0
  leafTestAt1760_block_1)
  (interval_append leafTestAt1760 2 3 4
  leafTestAt1760_block_2
  leafTestAt1760_block_3))
  (interval_append leafTestAt1760 4 6 8
  (interval_append leafTestAt1760 4 5 6
  leafTestAt1760_block_4
  leafTestAt1760_block_5)
  (interval_append leafTestAt1760 6 7 8
  leafTestAt1760_block_6
  leafTestAt1760_block_7)))
  (interval_append leafTestAt1760 8 12 16
  (interval_append leafTestAt1760 8 10 12
  (interval_append leafTestAt1760 8 9 10
  leafTestAt1760_block_8
  leafTestAt1760_block_9)
  (interval_append leafTestAt1760 10 11 12
  leafTestAt1760_block_10
  leafTestAt1760_block_11))
  (interval_append leafTestAt1760 12 14 16
  (interval_append leafTestAt1760 12 13 14
  leafTestAt1760_block_12
  leafTestAt1760_block_13)
  (interval_append leafTestAt1760 14 15 16
  leafTestAt1760_block_14
  leafTestAt1760_block_15))))
  (interval_append leafTestAt1760 16 24 32
  (interval_append leafTestAt1760 16 20 24
  (interval_append leafTestAt1760 16 18 20
  (interval_append leafTestAt1760 16 17 18
  leafTestAt1760_block_16
  leafTestAt1760_block_17)
  (interval_append leafTestAt1760 18 19 20
  leafTestAt1760_block_18
  leafTestAt1760_block_19))
  (interval_append leafTestAt1760 20 22 24
  (interval_append leafTestAt1760 20 21 22
  leafTestAt1760_block_20
  leafTestAt1760_block_21)
  (interval_append leafTestAt1760 22 23 24
  leafTestAt1760_block_22
  leafTestAt1760_block_23)))
  (interval_append leafTestAt1760 24 28 32
  (interval_append leafTestAt1760 24 26 28
  (interval_append leafTestAt1760 24 25 26
  leafTestAt1760_block_24
  leafTestAt1760_block_25)
  (interval_append leafTestAt1760 26 27 28
  leafTestAt1760_block_26
  leafTestAt1760_block_27))
  (interval_append leafTestAt1760 28 30 32
  (interval_append leafTestAt1760 28 29 30
  leafTestAt1760_block_28
  leafTestAt1760_block_29)
  (interval_append leafTestAt1760 30 31 32
  leafTestAt1760_block_30
  leafTestAt1760_block_31)))))
theorem leafInterval1760 : Interval leafTest 1760 1792 := by
  intro i hlo hhi
  have h := leafTestAt1760_complete (i-1760) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt1760, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
