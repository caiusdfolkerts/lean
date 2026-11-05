module
prelude
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt416 (i : Nat) := leafTest (i+416)
theorem leafTestAt416_block_0 : Interval leafTestAt416 0 1 :=
  interval_of_check leafTestAt416 0 1 (by decide +kernel)

theorem leafTestAt416_block_1 : Interval leafTestAt416 1 2 :=
  interval_of_check leafTestAt416 1 1 (by decide +kernel)

theorem leafTestAt416_block_2 : Interval leafTestAt416 2 3 :=
  interval_of_check leafTestAt416 2 1 (by decide +kernel)

theorem leafTestAt416_block_3 : Interval leafTestAt416 3 4 :=
  interval_of_check leafTestAt416 3 1 (by decide +kernel)

theorem leafTestAt416_block_4 : Interval leafTestAt416 4 5 :=
  interval_of_check leafTestAt416 4 1 (by decide +kernel)

theorem leafTestAt416_block_5 : Interval leafTestAt416 5 6 :=
  interval_of_check leafTestAt416 5 1 (by decide +kernel)

theorem leafTestAt416_block_6 : Interval leafTestAt416 6 7 :=
  interval_of_check leafTestAt416 6 1 (by decide +kernel)

theorem leafTestAt416_block_7 : Interval leafTestAt416 7 8 :=
  interval_of_check leafTestAt416 7 1 (by decide +kernel)

theorem leafTestAt416_block_8 : Interval leafTestAt416 8 9 :=
  interval_of_check leafTestAt416 8 1 (by decide +kernel)

theorem leafTestAt416_block_9 : Interval leafTestAt416 9 10 :=
  interval_of_check leafTestAt416 9 1 (by decide +kernel)

theorem leafTestAt416_block_10 : Interval leafTestAt416 10 11 :=
  interval_of_check leafTestAt416 10 1 (by decide +kernel)

theorem leafTestAt416_block_11 : Interval leafTestAt416 11 12 :=
  interval_of_check leafTestAt416 11 1 (by decide +kernel)

theorem leafTestAt416_block_12 : Interval leafTestAt416 12 13 :=
  interval_of_check leafTestAt416 12 1 (by decide +kernel)

theorem leafTestAt416_block_13 : Interval leafTestAt416 13 14 :=
  interval_of_check leafTestAt416 13 1 (by decide +kernel)

theorem leafTestAt416_block_14 : Interval leafTestAt416 14 15 :=
  interval_of_check leafTestAt416 14 1 (by decide +kernel)

theorem leafTestAt416_block_15 : Interval leafTestAt416 15 16 :=
  interval_of_check leafTestAt416 15 1 (by decide +kernel)

theorem leafTestAt416_block_16 : Interval leafTestAt416 16 17 :=
  interval_of_check leafTestAt416 16 1 (by decide +kernel)

theorem leafTestAt416_block_17 : Interval leafTestAt416 17 18 :=
  interval_of_check leafTestAt416 17 1 (by decide +kernel)

theorem leafTestAt416_block_18 : Interval leafTestAt416 18 19 :=
  interval_of_check leafTestAt416 18 1 (by decide +kernel)

theorem leafTestAt416_block_19 : Interval leafTestAt416 19 20 :=
  interval_of_check leafTestAt416 19 1 (by decide +kernel)

theorem leafTestAt416_block_20 : Interval leafTestAt416 20 21 :=
  interval_of_check leafTestAt416 20 1 (by decide +kernel)

theorem leafTestAt416_block_21 : Interval leafTestAt416 21 22 :=
  interval_of_check leafTestAt416 21 1 (by decide +kernel)

theorem leafTestAt416_block_22 : Interval leafTestAt416 22 23 :=
  interval_of_check leafTestAt416 22 1 (by decide +kernel)

theorem leafTestAt416_block_23 : Interval leafTestAt416 23 24 :=
  interval_of_check leafTestAt416 23 1 (by decide +kernel)

theorem leafTestAt416_block_24 : Interval leafTestAt416 24 25 :=
  interval_of_check leafTestAt416 24 1 (by decide +kernel)

theorem leafTestAt416_block_25 : Interval leafTestAt416 25 26 :=
  interval_of_check leafTestAt416 25 1 (by decide +kernel)

theorem leafTestAt416_block_26 : Interval leafTestAt416 26 27 :=
  interval_of_check leafTestAt416 26 1 (by decide +kernel)

theorem leafTestAt416_block_27 : Interval leafTestAt416 27 28 :=
  interval_of_check leafTestAt416 27 1 (by decide +kernel)

theorem leafTestAt416_block_28 : Interval leafTestAt416 28 29 :=
  interval_of_check leafTestAt416 28 1 (by decide +kernel)

theorem leafTestAt416_block_29 : Interval leafTestAt416 29 30 :=
  interval_of_check leafTestAt416 29 1 (by decide +kernel)

theorem leafTestAt416_block_30 : Interval leafTestAt416 30 31 :=
  interval_of_check leafTestAt416 30 1 (by decide +kernel)

theorem leafTestAt416_block_31 : Interval leafTestAt416 31 32 :=
  interval_of_check leafTestAt416 31 1 (by decide +kernel)

theorem leafTestAt416_complete : Interval leafTestAt416 0 32 :=
  (interval_append leafTestAt416 0 16 32
  (interval_append leafTestAt416 0 8 16
  (interval_append leafTestAt416 0 4 8
  (interval_append leafTestAt416 0 2 4
  (interval_append leafTestAt416 0 1 2
  leafTestAt416_block_0
  leafTestAt416_block_1)
  (interval_append leafTestAt416 2 3 4
  leafTestAt416_block_2
  leafTestAt416_block_3))
  (interval_append leafTestAt416 4 6 8
  (interval_append leafTestAt416 4 5 6
  leafTestAt416_block_4
  leafTestAt416_block_5)
  (interval_append leafTestAt416 6 7 8
  leafTestAt416_block_6
  leafTestAt416_block_7)))
  (interval_append leafTestAt416 8 12 16
  (interval_append leafTestAt416 8 10 12
  (interval_append leafTestAt416 8 9 10
  leafTestAt416_block_8
  leafTestAt416_block_9)
  (interval_append leafTestAt416 10 11 12
  leafTestAt416_block_10
  leafTestAt416_block_11))
  (interval_append leafTestAt416 12 14 16
  (interval_append leafTestAt416 12 13 14
  leafTestAt416_block_12
  leafTestAt416_block_13)
  (interval_append leafTestAt416 14 15 16
  leafTestAt416_block_14
  leafTestAt416_block_15))))
  (interval_append leafTestAt416 16 24 32
  (interval_append leafTestAt416 16 20 24
  (interval_append leafTestAt416 16 18 20
  (interval_append leafTestAt416 16 17 18
  leafTestAt416_block_16
  leafTestAt416_block_17)
  (interval_append leafTestAt416 18 19 20
  leafTestAt416_block_18
  leafTestAt416_block_19))
  (interval_append leafTestAt416 20 22 24
  (interval_append leafTestAt416 20 21 22
  leafTestAt416_block_20
  leafTestAt416_block_21)
  (interval_append leafTestAt416 22 23 24
  leafTestAt416_block_22
  leafTestAt416_block_23)))
  (interval_append leafTestAt416 24 28 32
  (interval_append leafTestAt416 24 26 28
  (interval_append leafTestAt416 24 25 26
  leafTestAt416_block_24
  leafTestAt416_block_25)
  (interval_append leafTestAt416 26 27 28
  leafTestAt416_block_26
  leafTestAt416_block_27))
  (interval_append leafTestAt416 28 30 32
  (interval_append leafTestAt416 28 29 30
  leafTestAt416_block_28
  leafTestAt416_block_29)
  (interval_append leafTestAt416 30 31 32
  leafTestAt416_block_30
  leafTestAt416_block_31)))))
theorem leafInterval416 : Interval leafTest 416 448 := by
  intro i hlo hhi
  have h := leafTestAt416_complete (i-416) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt416, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
