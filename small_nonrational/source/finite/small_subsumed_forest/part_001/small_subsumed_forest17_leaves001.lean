module
prelude
public import SmallSubsumedForest17Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt32 (i : Nat) := leafTest (i+32)
theorem leafTestAt32_block_0 : Interval leafTestAt32 0 1 :=
  interval_of_check leafTestAt32 0 1 (by decide +kernel)

theorem leafTestAt32_block_1 : Interval leafTestAt32 1 2 :=
  interval_of_check leafTestAt32 1 1 (by decide +kernel)

theorem leafTestAt32_block_2 : Interval leafTestAt32 2 3 :=
  interval_of_check leafTestAt32 2 1 (by decide +kernel)

theorem leafTestAt32_block_3 : Interval leafTestAt32 3 4 :=
  interval_of_check leafTestAt32 3 1 (by decide +kernel)

theorem leafTestAt32_block_4 : Interval leafTestAt32 4 5 :=
  interval_of_check leafTestAt32 4 1 (by decide +kernel)

theorem leafTestAt32_block_5 : Interval leafTestAt32 5 6 :=
  interval_of_check leafTestAt32 5 1 (by decide +kernel)

theorem leafTestAt32_block_6 : Interval leafTestAt32 6 7 :=
  interval_of_check leafTestAt32 6 1 (by decide +kernel)

theorem leafTestAt32_block_7 : Interval leafTestAt32 7 8 :=
  interval_of_check leafTestAt32 7 1 (by decide +kernel)

theorem leafTestAt32_block_8 : Interval leafTestAt32 8 9 :=
  interval_of_check leafTestAt32 8 1 (by decide +kernel)

theorem leafTestAt32_block_9 : Interval leafTestAt32 9 10 :=
  interval_of_check leafTestAt32 9 1 (by decide +kernel)

theorem leafTestAt32_block_10 : Interval leafTestAt32 10 11 :=
  interval_of_check leafTestAt32 10 1 (by decide +kernel)

theorem leafTestAt32_block_11 : Interval leafTestAt32 11 12 :=
  interval_of_check leafTestAt32 11 1 (by decide +kernel)

theorem leafTestAt32_block_12 : Interval leafTestAt32 12 13 :=
  interval_of_check leafTestAt32 12 1 (by decide +kernel)

theorem leafTestAt32_block_13 : Interval leafTestAt32 13 14 :=
  interval_of_check leafTestAt32 13 1 (by decide +kernel)

theorem leafTestAt32_block_14 : Interval leafTestAt32 14 15 :=
  interval_of_check leafTestAt32 14 1 (by decide +kernel)

theorem leafTestAt32_block_15 : Interval leafTestAt32 15 16 :=
  interval_of_check leafTestAt32 15 1 (by decide +kernel)

theorem leafTestAt32_block_16 : Interval leafTestAt32 16 17 :=
  interval_of_check leafTestAt32 16 1 (by decide +kernel)

theorem leafTestAt32_block_17 : Interval leafTestAt32 17 18 :=
  interval_of_check leafTestAt32 17 1 (by decide +kernel)

theorem leafTestAt32_block_18 : Interval leafTestAt32 18 19 :=
  interval_of_check leafTestAt32 18 1 (by decide +kernel)

theorem leafTestAt32_block_19 : Interval leafTestAt32 19 20 :=
  interval_of_check leafTestAt32 19 1 (by decide +kernel)

theorem leafTestAt32_block_20 : Interval leafTestAt32 20 21 :=
  interval_of_check leafTestAt32 20 1 (by decide +kernel)

theorem leafTestAt32_block_21 : Interval leafTestAt32 21 22 :=
  interval_of_check leafTestAt32 21 1 (by decide +kernel)

theorem leafTestAt32_block_22 : Interval leafTestAt32 22 23 :=
  interval_of_check leafTestAt32 22 1 (by decide +kernel)

theorem leafTestAt32_block_23 : Interval leafTestAt32 23 24 :=
  interval_of_check leafTestAt32 23 1 (by decide +kernel)

theorem leafTestAt32_block_24 : Interval leafTestAt32 24 25 :=
  interval_of_check leafTestAt32 24 1 (by decide +kernel)

theorem leafTestAt32_block_25 : Interval leafTestAt32 25 26 :=
  interval_of_check leafTestAt32 25 1 (by decide +kernel)

theorem leafTestAt32_block_26 : Interval leafTestAt32 26 27 :=
  interval_of_check leafTestAt32 26 1 (by decide +kernel)

theorem leafTestAt32_block_27 : Interval leafTestAt32 27 28 :=
  interval_of_check leafTestAt32 27 1 (by decide +kernel)

theorem leafTestAt32_block_28 : Interval leafTestAt32 28 29 :=
  interval_of_check leafTestAt32 28 1 (by decide +kernel)

theorem leafTestAt32_block_29 : Interval leafTestAt32 29 30 :=
  interval_of_check leafTestAt32 29 1 (by decide +kernel)

theorem leafTestAt32_block_30 : Interval leafTestAt32 30 31 :=
  interval_of_check leafTestAt32 30 1 (by decide +kernel)

theorem leafTestAt32_block_31 : Interval leafTestAt32 31 32 :=
  interval_of_check leafTestAt32 31 1 (by decide +kernel)

theorem leafTestAt32_complete : Interval leafTestAt32 0 32 :=
  (interval_append leafTestAt32 0 16 32
  (interval_append leafTestAt32 0 8 16
  (interval_append leafTestAt32 0 4 8
  (interval_append leafTestAt32 0 2 4
  (interval_append leafTestAt32 0 1 2
  leafTestAt32_block_0
  leafTestAt32_block_1)
  (interval_append leafTestAt32 2 3 4
  leafTestAt32_block_2
  leafTestAt32_block_3))
  (interval_append leafTestAt32 4 6 8
  (interval_append leafTestAt32 4 5 6
  leafTestAt32_block_4
  leafTestAt32_block_5)
  (interval_append leafTestAt32 6 7 8
  leafTestAt32_block_6
  leafTestAt32_block_7)))
  (interval_append leafTestAt32 8 12 16
  (interval_append leafTestAt32 8 10 12
  (interval_append leafTestAt32 8 9 10
  leafTestAt32_block_8
  leafTestAt32_block_9)
  (interval_append leafTestAt32 10 11 12
  leafTestAt32_block_10
  leafTestAt32_block_11))
  (interval_append leafTestAt32 12 14 16
  (interval_append leafTestAt32 12 13 14
  leafTestAt32_block_12
  leafTestAt32_block_13)
  (interval_append leafTestAt32 14 15 16
  leafTestAt32_block_14
  leafTestAt32_block_15))))
  (interval_append leafTestAt32 16 24 32
  (interval_append leafTestAt32 16 20 24
  (interval_append leafTestAt32 16 18 20
  (interval_append leafTestAt32 16 17 18
  leafTestAt32_block_16
  leafTestAt32_block_17)
  (interval_append leafTestAt32 18 19 20
  leafTestAt32_block_18
  leafTestAt32_block_19))
  (interval_append leafTestAt32 20 22 24
  (interval_append leafTestAt32 20 21 22
  leafTestAt32_block_20
  leafTestAt32_block_21)
  (interval_append leafTestAt32 22 23 24
  leafTestAt32_block_22
  leafTestAt32_block_23)))
  (interval_append leafTestAt32 24 28 32
  (interval_append leafTestAt32 24 26 28
  (interval_append leafTestAt32 24 25 26
  leafTestAt32_block_24
  leafTestAt32_block_25)
  (interval_append leafTestAt32 26 27 28
  leafTestAt32_block_26
  leafTestAt32_block_27))
  (interval_append leafTestAt32 28 30 32
  (interval_append leafTestAt32 28 29 30
  leafTestAt32_block_28
  leafTestAt32_block_29)
  (interval_append leafTestAt32 30 31 32
  leafTestAt32_block_30
  leafTestAt32_block_31)))))
theorem leafInterval32 : Interval leafTest 32 64 := by
  intro i hlo hhi
  have h := leafTestAt32_complete (i-32) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt32, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
