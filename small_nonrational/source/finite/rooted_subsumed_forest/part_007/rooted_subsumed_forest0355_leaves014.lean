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
def leafTestAt448 (i : Nat) := leafTest (i+448)
theorem leafTestAt448_block_0 : Interval leafTestAt448 0 1 :=
  interval_of_check leafTestAt448 0 1 (by decide +kernel)

theorem leafTestAt448_block_1 : Interval leafTestAt448 1 2 :=
  interval_of_check leafTestAt448 1 1 (by decide +kernel)

theorem leafTestAt448_block_2 : Interval leafTestAt448 2 3 :=
  interval_of_check leafTestAt448 2 1 (by decide +kernel)

theorem leafTestAt448_block_3 : Interval leafTestAt448 3 4 :=
  interval_of_check leafTestAt448 3 1 (by decide +kernel)

theorem leafTestAt448_block_4 : Interval leafTestAt448 4 5 :=
  interval_of_check leafTestAt448 4 1 (by decide +kernel)

theorem leafTestAt448_block_5 : Interval leafTestAt448 5 6 :=
  interval_of_check leafTestAt448 5 1 (by decide +kernel)

theorem leafTestAt448_block_6 : Interval leafTestAt448 6 7 :=
  interval_of_check leafTestAt448 6 1 (by decide +kernel)

theorem leafTestAt448_block_7 : Interval leafTestAt448 7 8 :=
  interval_of_check leafTestAt448 7 1 (by decide +kernel)

theorem leafTestAt448_block_8 : Interval leafTestAt448 8 9 :=
  interval_of_check leafTestAt448 8 1 (by decide +kernel)

theorem leafTestAt448_block_9 : Interval leafTestAt448 9 10 :=
  interval_of_check leafTestAt448 9 1 (by decide +kernel)

theorem leafTestAt448_block_10 : Interval leafTestAt448 10 11 :=
  interval_of_check leafTestAt448 10 1 (by decide +kernel)

theorem leafTestAt448_block_11 : Interval leafTestAt448 11 12 :=
  interval_of_check leafTestAt448 11 1 (by decide +kernel)

theorem leafTestAt448_block_12 : Interval leafTestAt448 12 13 :=
  interval_of_check leafTestAt448 12 1 (by decide +kernel)

theorem leafTestAt448_block_13 : Interval leafTestAt448 13 14 :=
  interval_of_check leafTestAt448 13 1 (by decide +kernel)

theorem leafTestAt448_block_14 : Interval leafTestAt448 14 15 :=
  interval_of_check leafTestAt448 14 1 (by decide +kernel)

theorem leafTestAt448_block_15 : Interval leafTestAt448 15 16 :=
  interval_of_check leafTestAt448 15 1 (by decide +kernel)

theorem leafTestAt448_block_16 : Interval leafTestAt448 16 17 :=
  interval_of_check leafTestAt448 16 1 (by decide +kernel)

theorem leafTestAt448_block_17 : Interval leafTestAt448 17 18 :=
  interval_of_check leafTestAt448 17 1 (by decide +kernel)

theorem leafTestAt448_block_18 : Interval leafTestAt448 18 19 :=
  interval_of_check leafTestAt448 18 1 (by decide +kernel)

theorem leafTestAt448_block_19 : Interval leafTestAt448 19 20 :=
  interval_of_check leafTestAt448 19 1 (by decide +kernel)

theorem leafTestAt448_block_20 : Interval leafTestAt448 20 21 :=
  interval_of_check leafTestAt448 20 1 (by decide +kernel)

theorem leafTestAt448_block_21 : Interval leafTestAt448 21 22 :=
  interval_of_check leafTestAt448 21 1 (by decide +kernel)

theorem leafTestAt448_block_22 : Interval leafTestAt448 22 23 :=
  interval_of_check leafTestAt448 22 1 (by decide +kernel)

theorem leafTestAt448_block_23 : Interval leafTestAt448 23 24 :=
  interval_of_check leafTestAt448 23 1 (by decide +kernel)

theorem leafTestAt448_block_24 : Interval leafTestAt448 24 25 :=
  interval_of_check leafTestAt448 24 1 (by decide +kernel)

theorem leafTestAt448_block_25 : Interval leafTestAt448 25 26 :=
  interval_of_check leafTestAt448 25 1 (by decide +kernel)

theorem leafTestAt448_block_26 : Interval leafTestAt448 26 27 :=
  interval_of_check leafTestAt448 26 1 (by decide +kernel)

theorem leafTestAt448_block_27 : Interval leafTestAt448 27 28 :=
  interval_of_check leafTestAt448 27 1 (by decide +kernel)

theorem leafTestAt448_block_28 : Interval leafTestAt448 28 29 :=
  interval_of_check leafTestAt448 28 1 (by decide +kernel)

theorem leafTestAt448_block_29 : Interval leafTestAt448 29 30 :=
  interval_of_check leafTestAt448 29 1 (by decide +kernel)

theorem leafTestAt448_block_30 : Interval leafTestAt448 30 31 :=
  interval_of_check leafTestAt448 30 1 (by decide +kernel)

theorem leafTestAt448_block_31 : Interval leafTestAt448 31 32 :=
  interval_of_check leafTestAt448 31 1 (by decide +kernel)

theorem leafTestAt448_complete : Interval leafTestAt448 0 32 :=
  (interval_append leafTestAt448 0 16 32
  (interval_append leafTestAt448 0 8 16
  (interval_append leafTestAt448 0 4 8
  (interval_append leafTestAt448 0 2 4
  (interval_append leafTestAt448 0 1 2
  leafTestAt448_block_0
  leafTestAt448_block_1)
  (interval_append leafTestAt448 2 3 4
  leafTestAt448_block_2
  leafTestAt448_block_3))
  (interval_append leafTestAt448 4 6 8
  (interval_append leafTestAt448 4 5 6
  leafTestAt448_block_4
  leafTestAt448_block_5)
  (interval_append leafTestAt448 6 7 8
  leafTestAt448_block_6
  leafTestAt448_block_7)))
  (interval_append leafTestAt448 8 12 16
  (interval_append leafTestAt448 8 10 12
  (interval_append leafTestAt448 8 9 10
  leafTestAt448_block_8
  leafTestAt448_block_9)
  (interval_append leafTestAt448 10 11 12
  leafTestAt448_block_10
  leafTestAt448_block_11))
  (interval_append leafTestAt448 12 14 16
  (interval_append leafTestAt448 12 13 14
  leafTestAt448_block_12
  leafTestAt448_block_13)
  (interval_append leafTestAt448 14 15 16
  leafTestAt448_block_14
  leafTestAt448_block_15))))
  (interval_append leafTestAt448 16 24 32
  (interval_append leafTestAt448 16 20 24
  (interval_append leafTestAt448 16 18 20
  (interval_append leafTestAt448 16 17 18
  leafTestAt448_block_16
  leafTestAt448_block_17)
  (interval_append leafTestAt448 18 19 20
  leafTestAt448_block_18
  leafTestAt448_block_19))
  (interval_append leafTestAt448 20 22 24
  (interval_append leafTestAt448 20 21 22
  leafTestAt448_block_20
  leafTestAt448_block_21)
  (interval_append leafTestAt448 22 23 24
  leafTestAt448_block_22
  leafTestAt448_block_23)))
  (interval_append leafTestAt448 24 28 32
  (interval_append leafTestAt448 24 26 28
  (interval_append leafTestAt448 24 25 26
  leafTestAt448_block_24
  leafTestAt448_block_25)
  (interval_append leafTestAt448 26 27 28
  leafTestAt448_block_26
  leafTestAt448_block_27))
  (interval_append leafTestAt448 28 30 32
  (interval_append leafTestAt448 28 29 30
  leafTestAt448_block_28
  leafTestAt448_block_29)
  (interval_append leafTestAt448 30 31 32
  leafTestAt448_block_30
  leafTestAt448_block_31)))))
theorem leafInterval448 : Interval leafTest 448 480 := by
  intro i hlo hhi
  have h := leafTestAt448_complete (i-448) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt448, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
