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
def leafTestAt0 (i : Nat) := leafTest (i+0)
theorem leafTestAt0_block_0 : Interval leafTestAt0 0 1 :=
  interval_of_check leafTestAt0 0 1 (by decide +kernel)

theorem leafTestAt0_block_1 : Interval leafTestAt0 1 2 :=
  interval_of_check leafTestAt0 1 1 (by decide +kernel)

theorem leafTestAt0_block_2 : Interval leafTestAt0 2 3 :=
  interval_of_check leafTestAt0 2 1 (by decide +kernel)

theorem leafTestAt0_block_3 : Interval leafTestAt0 3 4 :=
  interval_of_check leafTestAt0 3 1 (by decide +kernel)

theorem leafTestAt0_block_4 : Interval leafTestAt0 4 5 :=
  interval_of_check leafTestAt0 4 1 (by decide +kernel)

theorem leafTestAt0_block_5 : Interval leafTestAt0 5 6 :=
  interval_of_check leafTestAt0 5 1 (by decide +kernel)

theorem leafTestAt0_block_6 : Interval leafTestAt0 6 7 :=
  interval_of_check leafTestAt0 6 1 (by decide +kernel)

theorem leafTestAt0_block_7 : Interval leafTestAt0 7 8 :=
  interval_of_check leafTestAt0 7 1 (by decide +kernel)

theorem leafTestAt0_block_8 : Interval leafTestAt0 8 9 :=
  interval_of_check leafTestAt0 8 1 (by decide +kernel)

theorem leafTestAt0_block_9 : Interval leafTestAt0 9 10 :=
  interval_of_check leafTestAt0 9 1 (by decide +kernel)

theorem leafTestAt0_block_10 : Interval leafTestAt0 10 11 :=
  interval_of_check leafTestAt0 10 1 (by decide +kernel)

theorem leafTestAt0_block_11 : Interval leafTestAt0 11 12 :=
  interval_of_check leafTestAt0 11 1 (by decide +kernel)

theorem leafTestAt0_block_12 : Interval leafTestAt0 12 13 :=
  interval_of_check leafTestAt0 12 1 (by decide +kernel)

theorem leafTestAt0_block_13 : Interval leafTestAt0 13 14 :=
  interval_of_check leafTestAt0 13 1 (by decide +kernel)

theorem leafTestAt0_block_14 : Interval leafTestAt0 14 15 :=
  interval_of_check leafTestAt0 14 1 (by decide +kernel)

theorem leafTestAt0_block_15 : Interval leafTestAt0 15 16 :=
  interval_of_check leafTestAt0 15 1 (by decide +kernel)

theorem leafTestAt0_block_16 : Interval leafTestAt0 16 17 :=
  interval_of_check leafTestAt0 16 1 (by decide +kernel)

theorem leafTestAt0_block_17 : Interval leafTestAt0 17 18 :=
  interval_of_check leafTestAt0 17 1 (by decide +kernel)

theorem leafTestAt0_block_18 : Interval leafTestAt0 18 19 :=
  interval_of_check leafTestAt0 18 1 (by decide +kernel)

theorem leafTestAt0_block_19 : Interval leafTestAt0 19 20 :=
  interval_of_check leafTestAt0 19 1 (by decide +kernel)

theorem leafTestAt0_block_20 : Interval leafTestAt0 20 21 :=
  interval_of_check leafTestAt0 20 1 (by decide +kernel)

theorem leafTestAt0_block_21 : Interval leafTestAt0 21 22 :=
  interval_of_check leafTestAt0 21 1 (by decide +kernel)

theorem leafTestAt0_block_22 : Interval leafTestAt0 22 23 :=
  interval_of_check leafTestAt0 22 1 (by decide +kernel)

theorem leafTestAt0_block_23 : Interval leafTestAt0 23 24 :=
  interval_of_check leafTestAt0 23 1 (by decide +kernel)

theorem leafTestAt0_block_24 : Interval leafTestAt0 24 25 :=
  interval_of_check leafTestAt0 24 1 (by decide +kernel)

theorem leafTestAt0_block_25 : Interval leafTestAt0 25 26 :=
  interval_of_check leafTestAt0 25 1 (by decide +kernel)

theorem leafTestAt0_block_26 : Interval leafTestAt0 26 27 :=
  interval_of_check leafTestAt0 26 1 (by decide +kernel)

theorem leafTestAt0_block_27 : Interval leafTestAt0 27 28 :=
  interval_of_check leafTestAt0 27 1 (by decide +kernel)

theorem leafTestAt0_block_28 : Interval leafTestAt0 28 29 :=
  interval_of_check leafTestAt0 28 1 (by decide +kernel)

theorem leafTestAt0_block_29 : Interval leafTestAt0 29 30 :=
  interval_of_check leafTestAt0 29 1 (by decide +kernel)

theorem leafTestAt0_block_30 : Interval leafTestAt0 30 31 :=
  interval_of_check leafTestAt0 30 1 (by decide +kernel)

theorem leafTestAt0_block_31 : Interval leafTestAt0 31 32 :=
  interval_of_check leafTestAt0 31 1 (by decide +kernel)

theorem leafTestAt0_complete : Interval leafTestAt0 0 32 :=
  (interval_append leafTestAt0 0 16 32
  (interval_append leafTestAt0 0 8 16
  (interval_append leafTestAt0 0 4 8
  (interval_append leafTestAt0 0 2 4
  (interval_append leafTestAt0 0 1 2
  leafTestAt0_block_0
  leafTestAt0_block_1)
  (interval_append leafTestAt0 2 3 4
  leafTestAt0_block_2
  leafTestAt0_block_3))
  (interval_append leafTestAt0 4 6 8
  (interval_append leafTestAt0 4 5 6
  leafTestAt0_block_4
  leafTestAt0_block_5)
  (interval_append leafTestAt0 6 7 8
  leafTestAt0_block_6
  leafTestAt0_block_7)))
  (interval_append leafTestAt0 8 12 16
  (interval_append leafTestAt0 8 10 12
  (interval_append leafTestAt0 8 9 10
  leafTestAt0_block_8
  leafTestAt0_block_9)
  (interval_append leafTestAt0 10 11 12
  leafTestAt0_block_10
  leafTestAt0_block_11))
  (interval_append leafTestAt0 12 14 16
  (interval_append leafTestAt0 12 13 14
  leafTestAt0_block_12
  leafTestAt0_block_13)
  (interval_append leafTestAt0 14 15 16
  leafTestAt0_block_14
  leafTestAt0_block_15))))
  (interval_append leafTestAt0 16 24 32
  (interval_append leafTestAt0 16 20 24
  (interval_append leafTestAt0 16 18 20
  (interval_append leafTestAt0 16 17 18
  leafTestAt0_block_16
  leafTestAt0_block_17)
  (interval_append leafTestAt0 18 19 20
  leafTestAt0_block_18
  leafTestAt0_block_19))
  (interval_append leafTestAt0 20 22 24
  (interval_append leafTestAt0 20 21 22
  leafTestAt0_block_20
  leafTestAt0_block_21)
  (interval_append leafTestAt0 22 23 24
  leafTestAt0_block_22
  leafTestAt0_block_23)))
  (interval_append leafTestAt0 24 28 32
  (interval_append leafTestAt0 24 26 28
  (interval_append leafTestAt0 24 25 26
  leafTestAt0_block_24
  leafTestAt0_block_25)
  (interval_append leafTestAt0 26 27 28
  leafTestAt0_block_26
  leafTestAt0_block_27))
  (interval_append leafTestAt0 28 30 32
  (interval_append leafTestAt0 28 29 30
  leafTestAt0_block_28
  leafTestAt0_block_29)
  (interval_append leafTestAt0 30 31 32
  leafTestAt0_block_30
  leafTestAt0_block_31)))))
theorem leafInterval0 : Interval leafTest 0 32 := by
  intro i hlo hhi
  have h := leafTestAt0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
