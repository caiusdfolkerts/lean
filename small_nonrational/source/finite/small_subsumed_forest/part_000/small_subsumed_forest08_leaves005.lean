module
prelude
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt160 (i : Nat) := leafTest (i+160)
theorem leafTestAt160_block_0 : Interval leafTestAt160 0 1 :=
  interval_of_check leafTestAt160 0 1 (by decide +kernel)

theorem leafTestAt160_block_1 : Interval leafTestAt160 1 2 :=
  interval_of_check leafTestAt160 1 1 (by decide +kernel)

theorem leafTestAt160_block_2 : Interval leafTestAt160 2 3 :=
  interval_of_check leafTestAt160 2 1 (by decide +kernel)

theorem leafTestAt160_block_3 : Interval leafTestAt160 3 4 :=
  interval_of_check leafTestAt160 3 1 (by decide +kernel)

theorem leafTestAt160_block_4 : Interval leafTestAt160 4 5 :=
  interval_of_check leafTestAt160 4 1 (by decide +kernel)

theorem leafTestAt160_block_5 : Interval leafTestAt160 5 6 :=
  interval_of_check leafTestAt160 5 1 (by decide +kernel)

theorem leafTestAt160_block_6 : Interval leafTestAt160 6 7 :=
  interval_of_check leafTestAt160 6 1 (by decide +kernel)

theorem leafTestAt160_block_7 : Interval leafTestAt160 7 8 :=
  interval_of_check leafTestAt160 7 1 (by decide +kernel)

theorem leafTestAt160_block_8 : Interval leafTestAt160 8 9 :=
  interval_of_check leafTestAt160 8 1 (by decide +kernel)

theorem leafTestAt160_block_9 : Interval leafTestAt160 9 10 :=
  interval_of_check leafTestAt160 9 1 (by decide +kernel)

theorem leafTestAt160_block_10 : Interval leafTestAt160 10 11 :=
  interval_of_check leafTestAt160 10 1 (by decide +kernel)

theorem leafTestAt160_block_11 : Interval leafTestAt160 11 12 :=
  interval_of_check leafTestAt160 11 1 (by decide +kernel)

theorem leafTestAt160_block_12 : Interval leafTestAt160 12 13 :=
  interval_of_check leafTestAt160 12 1 (by decide +kernel)

theorem leafTestAt160_block_13 : Interval leafTestAt160 13 14 :=
  interval_of_check leafTestAt160 13 1 (by decide +kernel)

theorem leafTestAt160_block_14 : Interval leafTestAt160 14 15 :=
  interval_of_check leafTestAt160 14 1 (by decide +kernel)

theorem leafTestAt160_block_15 : Interval leafTestAt160 15 16 :=
  interval_of_check leafTestAt160 15 1 (by decide +kernel)

theorem leafTestAt160_block_16 : Interval leafTestAt160 16 17 :=
  interval_of_check leafTestAt160 16 1 (by decide +kernel)

theorem leafTestAt160_block_17 : Interval leafTestAt160 17 18 :=
  interval_of_check leafTestAt160 17 1 (by decide +kernel)

theorem leafTestAt160_block_18 : Interval leafTestAt160 18 19 :=
  interval_of_check leafTestAt160 18 1 (by decide +kernel)

theorem leafTestAt160_block_19 : Interval leafTestAt160 19 20 :=
  interval_of_check leafTestAt160 19 1 (by decide +kernel)

theorem leafTestAt160_block_20 : Interval leafTestAt160 20 21 :=
  interval_of_check leafTestAt160 20 1 (by decide +kernel)

theorem leafTestAt160_block_21 : Interval leafTestAt160 21 22 :=
  interval_of_check leafTestAt160 21 1 (by decide +kernel)

theorem leafTestAt160_block_22 : Interval leafTestAt160 22 23 :=
  interval_of_check leafTestAt160 22 1 (by decide +kernel)

theorem leafTestAt160_block_23 : Interval leafTestAt160 23 24 :=
  interval_of_check leafTestAt160 23 1 (by decide +kernel)

theorem leafTestAt160_block_24 : Interval leafTestAt160 24 25 :=
  interval_of_check leafTestAt160 24 1 (by decide +kernel)

theorem leafTestAt160_block_25 : Interval leafTestAt160 25 26 :=
  interval_of_check leafTestAt160 25 1 (by decide +kernel)

theorem leafTestAt160_block_26 : Interval leafTestAt160 26 27 :=
  interval_of_check leafTestAt160 26 1 (by decide +kernel)

theorem leafTestAt160_block_27 : Interval leafTestAt160 27 28 :=
  interval_of_check leafTestAt160 27 1 (by decide +kernel)

theorem leafTestAt160_block_28 : Interval leafTestAt160 28 29 :=
  interval_of_check leafTestAt160 28 1 (by decide +kernel)

theorem leafTestAt160_block_29 : Interval leafTestAt160 29 30 :=
  interval_of_check leafTestAt160 29 1 (by decide +kernel)

theorem leafTestAt160_block_30 : Interval leafTestAt160 30 31 :=
  interval_of_check leafTestAt160 30 1 (by decide +kernel)

theorem leafTestAt160_block_31 : Interval leafTestAt160 31 32 :=
  interval_of_check leafTestAt160 31 1 (by decide +kernel)

theorem leafTestAt160_complete : Interval leafTestAt160 0 32 :=
  (interval_append leafTestAt160 0 16 32
  (interval_append leafTestAt160 0 8 16
  (interval_append leafTestAt160 0 4 8
  (interval_append leafTestAt160 0 2 4
  (interval_append leafTestAt160 0 1 2
  leafTestAt160_block_0
  leafTestAt160_block_1)
  (interval_append leafTestAt160 2 3 4
  leafTestAt160_block_2
  leafTestAt160_block_3))
  (interval_append leafTestAt160 4 6 8
  (interval_append leafTestAt160 4 5 6
  leafTestAt160_block_4
  leafTestAt160_block_5)
  (interval_append leafTestAt160 6 7 8
  leafTestAt160_block_6
  leafTestAt160_block_7)))
  (interval_append leafTestAt160 8 12 16
  (interval_append leafTestAt160 8 10 12
  (interval_append leafTestAt160 8 9 10
  leafTestAt160_block_8
  leafTestAt160_block_9)
  (interval_append leafTestAt160 10 11 12
  leafTestAt160_block_10
  leafTestAt160_block_11))
  (interval_append leafTestAt160 12 14 16
  (interval_append leafTestAt160 12 13 14
  leafTestAt160_block_12
  leafTestAt160_block_13)
  (interval_append leafTestAt160 14 15 16
  leafTestAt160_block_14
  leafTestAt160_block_15))))
  (interval_append leafTestAt160 16 24 32
  (interval_append leafTestAt160 16 20 24
  (interval_append leafTestAt160 16 18 20
  (interval_append leafTestAt160 16 17 18
  leafTestAt160_block_16
  leafTestAt160_block_17)
  (interval_append leafTestAt160 18 19 20
  leafTestAt160_block_18
  leafTestAt160_block_19))
  (interval_append leafTestAt160 20 22 24
  (interval_append leafTestAt160 20 21 22
  leafTestAt160_block_20
  leafTestAt160_block_21)
  (interval_append leafTestAt160 22 23 24
  leafTestAt160_block_22
  leafTestAt160_block_23)))
  (interval_append leafTestAt160 24 28 32
  (interval_append leafTestAt160 24 26 28
  (interval_append leafTestAt160 24 25 26
  leafTestAt160_block_24
  leafTestAt160_block_25)
  (interval_append leafTestAt160 26 27 28
  leafTestAt160_block_26
  leafTestAt160_block_27))
  (interval_append leafTestAt160 28 30 32
  (interval_append leafTestAt160 28 29 30
  leafTestAt160_block_28
  leafTestAt160_block_29)
  (interval_append leafTestAt160 30 31 32
  leafTestAt160_block_30
  leafTestAt160_block_31)))))
theorem leafInterval160 : Interval leafTest 160 192 := by
  intro i hlo hhi
  have h := leafTestAt160_complete (i-160) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt160, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
