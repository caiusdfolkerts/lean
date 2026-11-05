module
prelude
public import SmallSubsumedForest20Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
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

theorem leafTestAt32_complete : Interval leafTestAt32 0 29 :=
  (interval_append leafTestAt32 0 14 29
  (interval_append leafTestAt32 0 7 14
  (interval_append leafTestAt32 0 3 7
  (interval_append leafTestAt32 0 1 3
  leafTestAt32_block_0
  (interval_append leafTestAt32 1 2 3
  leafTestAt32_block_1
  leafTestAt32_block_2))
  (interval_append leafTestAt32 3 5 7
  (interval_append leafTestAt32 3 4 5
  leafTestAt32_block_3
  leafTestAt32_block_4)
  (interval_append leafTestAt32 5 6 7
  leafTestAt32_block_5
  leafTestAt32_block_6)))
  (interval_append leafTestAt32 7 10 14
  (interval_append leafTestAt32 7 8 10
  leafTestAt32_block_7
  (interval_append leafTestAt32 8 9 10
  leafTestAt32_block_8
  leafTestAt32_block_9))
  (interval_append leafTestAt32 10 12 14
  (interval_append leafTestAt32 10 11 12
  leafTestAt32_block_10
  leafTestAt32_block_11)
  (interval_append leafTestAt32 12 13 14
  leafTestAt32_block_12
  leafTestAt32_block_13))))
  (interval_append leafTestAt32 14 21 29
  (interval_append leafTestAt32 14 17 21
  (interval_append leafTestAt32 14 15 17
  leafTestAt32_block_14
  (interval_append leafTestAt32 15 16 17
  leafTestAt32_block_15
  leafTestAt32_block_16))
  (interval_append leafTestAt32 17 19 21
  (interval_append leafTestAt32 17 18 19
  leafTestAt32_block_17
  leafTestAt32_block_18)
  (interval_append leafTestAt32 19 20 21
  leafTestAt32_block_19
  leafTestAt32_block_20)))
  (interval_append leafTestAt32 21 25 29
  (interval_append leafTestAt32 21 23 25
  (interval_append leafTestAt32 21 22 23
  leafTestAt32_block_21
  leafTestAt32_block_22)
  (interval_append leafTestAt32 23 24 25
  leafTestAt32_block_23
  leafTestAt32_block_24))
  (interval_append leafTestAt32 25 27 29
  (interval_append leafTestAt32 25 26 27
  leafTestAt32_block_25
  leafTestAt32_block_26)
  (interval_append leafTestAt32 27 28 29
  leafTestAt32_block_27
  leafTestAt32_block_28)))))
theorem leafInterval32 : Interval leafTest 32 61 := by
  intro i hlo hhi
  have h := leafTestAt32_complete (i-32) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt32, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
