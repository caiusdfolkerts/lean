module
prelude
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt320 (i : Nat) := leafTest (i+320)
theorem leafTestAt320_block_0 : Interval leafTestAt320 0 1 :=
  interval_of_check leafTestAt320 0 1 (by decide +kernel)

theorem leafTestAt320_block_1 : Interval leafTestAt320 1 2 :=
  interval_of_check leafTestAt320 1 1 (by decide +kernel)

theorem leafTestAt320_block_2 : Interval leafTestAt320 2 3 :=
  interval_of_check leafTestAt320 2 1 (by decide +kernel)

theorem leafTestAt320_block_3 : Interval leafTestAt320 3 4 :=
  interval_of_check leafTestAt320 3 1 (by decide +kernel)

theorem leafTestAt320_block_4 : Interval leafTestAt320 4 5 :=
  interval_of_check leafTestAt320 4 1 (by decide +kernel)

theorem leafTestAt320_block_5 : Interval leafTestAt320 5 6 :=
  interval_of_check leafTestAt320 5 1 (by decide +kernel)

theorem leafTestAt320_block_6 : Interval leafTestAt320 6 7 :=
  interval_of_check leafTestAt320 6 1 (by decide +kernel)

theorem leafTestAt320_block_7 : Interval leafTestAt320 7 8 :=
  interval_of_check leafTestAt320 7 1 (by decide +kernel)

theorem leafTestAt320_block_8 : Interval leafTestAt320 8 9 :=
  interval_of_check leafTestAt320 8 1 (by decide +kernel)

theorem leafTestAt320_block_9 : Interval leafTestAt320 9 10 :=
  interval_of_check leafTestAt320 9 1 (by decide +kernel)

theorem leafTestAt320_block_10 : Interval leafTestAt320 10 11 :=
  interval_of_check leafTestAt320 10 1 (by decide +kernel)

theorem leafTestAt320_block_11 : Interval leafTestAt320 11 12 :=
  interval_of_check leafTestAt320 11 1 (by decide +kernel)

theorem leafTestAt320_block_12 : Interval leafTestAt320 12 13 :=
  interval_of_check leafTestAt320 12 1 (by decide +kernel)

theorem leafTestAt320_block_13 : Interval leafTestAt320 13 14 :=
  interval_of_check leafTestAt320 13 1 (by decide +kernel)

theorem leafTestAt320_block_14 : Interval leafTestAt320 14 15 :=
  interval_of_check leafTestAt320 14 1 (by decide +kernel)

theorem leafTestAt320_block_15 : Interval leafTestAt320 15 16 :=
  interval_of_check leafTestAt320 15 1 (by decide +kernel)

theorem leafTestAt320_block_16 : Interval leafTestAt320 16 17 :=
  interval_of_check leafTestAt320 16 1 (by decide +kernel)

theorem leafTestAt320_block_17 : Interval leafTestAt320 17 18 :=
  interval_of_check leafTestAt320 17 1 (by decide +kernel)

theorem leafTestAt320_block_18 : Interval leafTestAt320 18 19 :=
  interval_of_check leafTestAt320 18 1 (by decide +kernel)

theorem leafTestAt320_block_19 : Interval leafTestAt320 19 20 :=
  interval_of_check leafTestAt320 19 1 (by decide +kernel)

theorem leafTestAt320_block_20 : Interval leafTestAt320 20 21 :=
  interval_of_check leafTestAt320 20 1 (by decide +kernel)

theorem leafTestAt320_block_21 : Interval leafTestAt320 21 22 :=
  interval_of_check leafTestAt320 21 1 (by decide +kernel)

theorem leafTestAt320_block_22 : Interval leafTestAt320 22 23 :=
  interval_of_check leafTestAt320 22 1 (by decide +kernel)

theorem leafTestAt320_block_23 : Interval leafTestAt320 23 24 :=
  interval_of_check leafTestAt320 23 1 (by decide +kernel)

theorem leafTestAt320_block_24 : Interval leafTestAt320 24 25 :=
  interval_of_check leafTestAt320 24 1 (by decide +kernel)

theorem leafTestAt320_block_25 : Interval leafTestAt320 25 26 :=
  interval_of_check leafTestAt320 25 1 (by decide +kernel)

theorem leafTestAt320_block_26 : Interval leafTestAt320 26 27 :=
  interval_of_check leafTestAt320 26 1 (by decide +kernel)

theorem leafTestAt320_block_27 : Interval leafTestAt320 27 28 :=
  interval_of_check leafTestAt320 27 1 (by decide +kernel)

theorem leafTestAt320_block_28 : Interval leafTestAt320 28 29 :=
  interval_of_check leafTestAt320 28 1 (by decide +kernel)

theorem leafTestAt320_block_29 : Interval leafTestAt320 29 30 :=
  interval_of_check leafTestAt320 29 1 (by decide +kernel)

theorem leafTestAt320_block_30 : Interval leafTestAt320 30 31 :=
  interval_of_check leafTestAt320 30 1 (by decide +kernel)

theorem leafTestAt320_block_31 : Interval leafTestAt320 31 32 :=
  interval_of_check leafTestAt320 31 1 (by decide +kernel)

theorem leafTestAt320_complete : Interval leafTestAt320 0 32 :=
  (interval_append leafTestAt320 0 16 32
  (interval_append leafTestAt320 0 8 16
  (interval_append leafTestAt320 0 4 8
  (interval_append leafTestAt320 0 2 4
  (interval_append leafTestAt320 0 1 2
  leafTestAt320_block_0
  leafTestAt320_block_1)
  (interval_append leafTestAt320 2 3 4
  leafTestAt320_block_2
  leafTestAt320_block_3))
  (interval_append leafTestAt320 4 6 8
  (interval_append leafTestAt320 4 5 6
  leafTestAt320_block_4
  leafTestAt320_block_5)
  (interval_append leafTestAt320 6 7 8
  leafTestAt320_block_6
  leafTestAt320_block_7)))
  (interval_append leafTestAt320 8 12 16
  (interval_append leafTestAt320 8 10 12
  (interval_append leafTestAt320 8 9 10
  leafTestAt320_block_8
  leafTestAt320_block_9)
  (interval_append leafTestAt320 10 11 12
  leafTestAt320_block_10
  leafTestAt320_block_11))
  (interval_append leafTestAt320 12 14 16
  (interval_append leafTestAt320 12 13 14
  leafTestAt320_block_12
  leafTestAt320_block_13)
  (interval_append leafTestAt320 14 15 16
  leafTestAt320_block_14
  leafTestAt320_block_15))))
  (interval_append leafTestAt320 16 24 32
  (interval_append leafTestAt320 16 20 24
  (interval_append leafTestAt320 16 18 20
  (interval_append leafTestAt320 16 17 18
  leafTestAt320_block_16
  leafTestAt320_block_17)
  (interval_append leafTestAt320 18 19 20
  leafTestAt320_block_18
  leafTestAt320_block_19))
  (interval_append leafTestAt320 20 22 24
  (interval_append leafTestAt320 20 21 22
  leafTestAt320_block_20
  leafTestAt320_block_21)
  (interval_append leafTestAt320 22 23 24
  leafTestAt320_block_22
  leafTestAt320_block_23)))
  (interval_append leafTestAt320 24 28 32
  (interval_append leafTestAt320 24 26 28
  (interval_append leafTestAt320 24 25 26
  leafTestAt320_block_24
  leafTestAt320_block_25)
  (interval_append leafTestAt320 26 27 28
  leafTestAt320_block_26
  leafTestAt320_block_27))
  (interval_append leafTestAt320 28 30 32
  (interval_append leafTestAt320 28 29 30
  leafTestAt320_block_28
  leafTestAt320_block_29)
  (interval_append leafTestAt320 30 31 32
  leafTestAt320_block_30
  leafTestAt320_block_31)))))
theorem leafInterval320 : Interval leafTest 320 352 := by
  intro i hlo hhi
  have h := leafTestAt320_complete (i-320) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt320, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
