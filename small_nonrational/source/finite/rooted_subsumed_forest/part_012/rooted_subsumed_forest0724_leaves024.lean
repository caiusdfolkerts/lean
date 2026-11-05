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
def leafTestAt768 (i : Nat) := leafTest (i+768)
theorem leafTestAt768_block_0 : Interval leafTestAt768 0 1 :=
  interval_of_check leafTestAt768 0 1 (by decide +kernel)

theorem leafTestAt768_block_1 : Interval leafTestAt768 1 2 :=
  interval_of_check leafTestAt768 1 1 (by decide +kernel)

theorem leafTestAt768_block_2 : Interval leafTestAt768 2 3 :=
  interval_of_check leafTestAt768 2 1 (by decide +kernel)

theorem leafTestAt768_block_3 : Interval leafTestAt768 3 4 :=
  interval_of_check leafTestAt768 3 1 (by decide +kernel)

theorem leafTestAt768_block_4 : Interval leafTestAt768 4 5 :=
  interval_of_check leafTestAt768 4 1 (by decide +kernel)

theorem leafTestAt768_block_5 : Interval leafTestAt768 5 6 :=
  interval_of_check leafTestAt768 5 1 (by decide +kernel)

theorem leafTestAt768_block_6 : Interval leafTestAt768 6 7 :=
  interval_of_check leafTestAt768 6 1 (by decide +kernel)

theorem leafTestAt768_block_7 : Interval leafTestAt768 7 8 :=
  interval_of_check leafTestAt768 7 1 (by decide +kernel)

theorem leafTestAt768_block_8 : Interval leafTestAt768 8 9 :=
  interval_of_check leafTestAt768 8 1 (by decide +kernel)

theorem leafTestAt768_block_9 : Interval leafTestAt768 9 10 :=
  interval_of_check leafTestAt768 9 1 (by decide +kernel)

theorem leafTestAt768_block_10 : Interval leafTestAt768 10 11 :=
  interval_of_check leafTestAt768 10 1 (by decide +kernel)

theorem leafTestAt768_block_11 : Interval leafTestAt768 11 12 :=
  interval_of_check leafTestAt768 11 1 (by decide +kernel)

theorem leafTestAt768_block_12 : Interval leafTestAt768 12 13 :=
  interval_of_check leafTestAt768 12 1 (by decide +kernel)

theorem leafTestAt768_block_13 : Interval leafTestAt768 13 14 :=
  interval_of_check leafTestAt768 13 1 (by decide +kernel)

theorem leafTestAt768_block_14 : Interval leafTestAt768 14 15 :=
  interval_of_check leafTestAt768 14 1 (by decide +kernel)

theorem leafTestAt768_block_15 : Interval leafTestAt768 15 16 :=
  interval_of_check leafTestAt768 15 1 (by decide +kernel)

theorem leafTestAt768_block_16 : Interval leafTestAt768 16 17 :=
  interval_of_check leafTestAt768 16 1 (by decide +kernel)

theorem leafTestAt768_block_17 : Interval leafTestAt768 17 18 :=
  interval_of_check leafTestAt768 17 1 (by decide +kernel)

theorem leafTestAt768_block_18 : Interval leafTestAt768 18 19 :=
  interval_of_check leafTestAt768 18 1 (by decide +kernel)

theorem leafTestAt768_block_19 : Interval leafTestAt768 19 20 :=
  interval_of_check leafTestAt768 19 1 (by decide +kernel)

theorem leafTestAt768_block_20 : Interval leafTestAt768 20 21 :=
  interval_of_check leafTestAt768 20 1 (by decide +kernel)

theorem leafTestAt768_block_21 : Interval leafTestAt768 21 22 :=
  interval_of_check leafTestAt768 21 1 (by decide +kernel)

theorem leafTestAt768_block_22 : Interval leafTestAt768 22 23 :=
  interval_of_check leafTestAt768 22 1 (by decide +kernel)

theorem leafTestAt768_block_23 : Interval leafTestAt768 23 24 :=
  interval_of_check leafTestAt768 23 1 (by decide +kernel)

theorem leafTestAt768_block_24 : Interval leafTestAt768 24 25 :=
  interval_of_check leafTestAt768 24 1 (by decide +kernel)

theorem leafTestAt768_block_25 : Interval leafTestAt768 25 26 :=
  interval_of_check leafTestAt768 25 1 (by decide +kernel)

theorem leafTestAt768_block_26 : Interval leafTestAt768 26 27 :=
  interval_of_check leafTestAt768 26 1 (by decide +kernel)

theorem leafTestAt768_block_27 : Interval leafTestAt768 27 28 :=
  interval_of_check leafTestAt768 27 1 (by decide +kernel)

theorem leafTestAt768_block_28 : Interval leafTestAt768 28 29 :=
  interval_of_check leafTestAt768 28 1 (by decide +kernel)

theorem leafTestAt768_block_29 : Interval leafTestAt768 29 30 :=
  interval_of_check leafTestAt768 29 1 (by decide +kernel)

theorem leafTestAt768_block_30 : Interval leafTestAt768 30 31 :=
  interval_of_check leafTestAt768 30 1 (by decide +kernel)

theorem leafTestAt768_block_31 : Interval leafTestAt768 31 32 :=
  interval_of_check leafTestAt768 31 1 (by decide +kernel)

theorem leafTestAt768_complete : Interval leafTestAt768 0 32 :=
  (interval_append leafTestAt768 0 16 32
  (interval_append leafTestAt768 0 8 16
  (interval_append leafTestAt768 0 4 8
  (interval_append leafTestAt768 0 2 4
  (interval_append leafTestAt768 0 1 2
  leafTestAt768_block_0
  leafTestAt768_block_1)
  (interval_append leafTestAt768 2 3 4
  leafTestAt768_block_2
  leafTestAt768_block_3))
  (interval_append leafTestAt768 4 6 8
  (interval_append leafTestAt768 4 5 6
  leafTestAt768_block_4
  leafTestAt768_block_5)
  (interval_append leafTestAt768 6 7 8
  leafTestAt768_block_6
  leafTestAt768_block_7)))
  (interval_append leafTestAt768 8 12 16
  (interval_append leafTestAt768 8 10 12
  (interval_append leafTestAt768 8 9 10
  leafTestAt768_block_8
  leafTestAt768_block_9)
  (interval_append leafTestAt768 10 11 12
  leafTestAt768_block_10
  leafTestAt768_block_11))
  (interval_append leafTestAt768 12 14 16
  (interval_append leafTestAt768 12 13 14
  leafTestAt768_block_12
  leafTestAt768_block_13)
  (interval_append leafTestAt768 14 15 16
  leafTestAt768_block_14
  leafTestAt768_block_15))))
  (interval_append leafTestAt768 16 24 32
  (interval_append leafTestAt768 16 20 24
  (interval_append leafTestAt768 16 18 20
  (interval_append leafTestAt768 16 17 18
  leafTestAt768_block_16
  leafTestAt768_block_17)
  (interval_append leafTestAt768 18 19 20
  leafTestAt768_block_18
  leafTestAt768_block_19))
  (interval_append leafTestAt768 20 22 24
  (interval_append leafTestAt768 20 21 22
  leafTestAt768_block_20
  leafTestAt768_block_21)
  (interval_append leafTestAt768 22 23 24
  leafTestAt768_block_22
  leafTestAt768_block_23)))
  (interval_append leafTestAt768 24 28 32
  (interval_append leafTestAt768 24 26 28
  (interval_append leafTestAt768 24 25 26
  leafTestAt768_block_24
  leafTestAt768_block_25)
  (interval_append leafTestAt768 26 27 28
  leafTestAt768_block_26
  leafTestAt768_block_27))
  (interval_append leafTestAt768 28 30 32
  (interval_append leafTestAt768 28 29 30
  leafTestAt768_block_28
  leafTestAt768_block_29)
  (interval_append leafTestAt768 30 31 32
  leafTestAt768_block_30
  leafTestAt768_block_31)))))
theorem leafInterval768 : Interval leafTest 768 800 := by
  intro i hlo hhi
  have h := leafTestAt768_complete (i-768) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt768, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
