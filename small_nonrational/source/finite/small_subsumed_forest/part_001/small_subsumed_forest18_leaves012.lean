module
prelude
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt384 (i : Nat) := leafTest (i+384)
theorem leafTestAt384_block_0 : Interval leafTestAt384 0 1 :=
  interval_of_check leafTestAt384 0 1 (by decide +kernel)

theorem leafTestAt384_block_1 : Interval leafTestAt384 1 2 :=
  interval_of_check leafTestAt384 1 1 (by decide +kernel)

theorem leafTestAt384_block_2 : Interval leafTestAt384 2 3 :=
  interval_of_check leafTestAt384 2 1 (by decide +kernel)

theorem leafTestAt384_block_3 : Interval leafTestAt384 3 4 :=
  interval_of_check leafTestAt384 3 1 (by decide +kernel)

theorem leafTestAt384_block_4 : Interval leafTestAt384 4 5 :=
  interval_of_check leafTestAt384 4 1 (by decide +kernel)

theorem leafTestAt384_block_5 : Interval leafTestAt384 5 6 :=
  interval_of_check leafTestAt384 5 1 (by decide +kernel)

theorem leafTestAt384_block_6 : Interval leafTestAt384 6 7 :=
  interval_of_check leafTestAt384 6 1 (by decide +kernel)

theorem leafTestAt384_block_7 : Interval leafTestAt384 7 8 :=
  interval_of_check leafTestAt384 7 1 (by decide +kernel)

theorem leafTestAt384_block_8 : Interval leafTestAt384 8 9 :=
  interval_of_check leafTestAt384 8 1 (by decide +kernel)

theorem leafTestAt384_block_9 : Interval leafTestAt384 9 10 :=
  interval_of_check leafTestAt384 9 1 (by decide +kernel)

theorem leafTestAt384_block_10 : Interval leafTestAt384 10 11 :=
  interval_of_check leafTestAt384 10 1 (by decide +kernel)

theorem leafTestAt384_block_11 : Interval leafTestAt384 11 12 :=
  interval_of_check leafTestAt384 11 1 (by decide +kernel)

theorem leafTestAt384_block_12 : Interval leafTestAt384 12 13 :=
  interval_of_check leafTestAt384 12 1 (by decide +kernel)

theorem leafTestAt384_block_13 : Interval leafTestAt384 13 14 :=
  interval_of_check leafTestAt384 13 1 (by decide +kernel)

theorem leafTestAt384_block_14 : Interval leafTestAt384 14 15 :=
  interval_of_check leafTestAt384 14 1 (by decide +kernel)

theorem leafTestAt384_block_15 : Interval leafTestAt384 15 16 :=
  interval_of_check leafTestAt384 15 1 (by decide +kernel)

theorem leafTestAt384_block_16 : Interval leafTestAt384 16 17 :=
  interval_of_check leafTestAt384 16 1 (by decide +kernel)

theorem leafTestAt384_block_17 : Interval leafTestAt384 17 18 :=
  interval_of_check leafTestAt384 17 1 (by decide +kernel)

theorem leafTestAt384_block_18 : Interval leafTestAt384 18 19 :=
  interval_of_check leafTestAt384 18 1 (by decide +kernel)

theorem leafTestAt384_block_19 : Interval leafTestAt384 19 20 :=
  interval_of_check leafTestAt384 19 1 (by decide +kernel)

theorem leafTestAt384_block_20 : Interval leafTestAt384 20 21 :=
  interval_of_check leafTestAt384 20 1 (by decide +kernel)

theorem leafTestAt384_block_21 : Interval leafTestAt384 21 22 :=
  interval_of_check leafTestAt384 21 1 (by decide +kernel)

theorem leafTestAt384_block_22 : Interval leafTestAt384 22 23 :=
  interval_of_check leafTestAt384 22 1 (by decide +kernel)

theorem leafTestAt384_block_23 : Interval leafTestAt384 23 24 :=
  interval_of_check leafTestAt384 23 1 (by decide +kernel)

theorem leafTestAt384_block_24 : Interval leafTestAt384 24 25 :=
  interval_of_check leafTestAt384 24 1 (by decide +kernel)

theorem leafTestAt384_block_25 : Interval leafTestAt384 25 26 :=
  interval_of_check leafTestAt384 25 1 (by decide +kernel)

theorem leafTestAt384_block_26 : Interval leafTestAt384 26 27 :=
  interval_of_check leafTestAt384 26 1 (by decide +kernel)

theorem leafTestAt384_block_27 : Interval leafTestAt384 27 28 :=
  interval_of_check leafTestAt384 27 1 (by decide +kernel)

theorem leafTestAt384_block_28 : Interval leafTestAt384 28 29 :=
  interval_of_check leafTestAt384 28 1 (by decide +kernel)

theorem leafTestAt384_block_29 : Interval leafTestAt384 29 30 :=
  interval_of_check leafTestAt384 29 1 (by decide +kernel)

theorem leafTestAt384_block_30 : Interval leafTestAt384 30 31 :=
  interval_of_check leafTestAt384 30 1 (by decide +kernel)

theorem leafTestAt384_block_31 : Interval leafTestAt384 31 32 :=
  interval_of_check leafTestAt384 31 1 (by decide +kernel)

theorem leafTestAt384_complete : Interval leafTestAt384 0 32 :=
  (interval_append leafTestAt384 0 16 32
  (interval_append leafTestAt384 0 8 16
  (interval_append leafTestAt384 0 4 8
  (interval_append leafTestAt384 0 2 4
  (interval_append leafTestAt384 0 1 2
  leafTestAt384_block_0
  leafTestAt384_block_1)
  (interval_append leafTestAt384 2 3 4
  leafTestAt384_block_2
  leafTestAt384_block_3))
  (interval_append leafTestAt384 4 6 8
  (interval_append leafTestAt384 4 5 6
  leafTestAt384_block_4
  leafTestAt384_block_5)
  (interval_append leafTestAt384 6 7 8
  leafTestAt384_block_6
  leafTestAt384_block_7)))
  (interval_append leafTestAt384 8 12 16
  (interval_append leafTestAt384 8 10 12
  (interval_append leafTestAt384 8 9 10
  leafTestAt384_block_8
  leafTestAt384_block_9)
  (interval_append leafTestAt384 10 11 12
  leafTestAt384_block_10
  leafTestAt384_block_11))
  (interval_append leafTestAt384 12 14 16
  (interval_append leafTestAt384 12 13 14
  leafTestAt384_block_12
  leafTestAt384_block_13)
  (interval_append leafTestAt384 14 15 16
  leafTestAt384_block_14
  leafTestAt384_block_15))))
  (interval_append leafTestAt384 16 24 32
  (interval_append leafTestAt384 16 20 24
  (interval_append leafTestAt384 16 18 20
  (interval_append leafTestAt384 16 17 18
  leafTestAt384_block_16
  leafTestAt384_block_17)
  (interval_append leafTestAt384 18 19 20
  leafTestAt384_block_18
  leafTestAt384_block_19))
  (interval_append leafTestAt384 20 22 24
  (interval_append leafTestAt384 20 21 22
  leafTestAt384_block_20
  leafTestAt384_block_21)
  (interval_append leafTestAt384 22 23 24
  leafTestAt384_block_22
  leafTestAt384_block_23)))
  (interval_append leafTestAt384 24 28 32
  (interval_append leafTestAt384 24 26 28
  (interval_append leafTestAt384 24 25 26
  leafTestAt384_block_24
  leafTestAt384_block_25)
  (interval_append leafTestAt384 26 27 28
  leafTestAt384_block_26
  leafTestAt384_block_27))
  (interval_append leafTestAt384 28 30 32
  (interval_append leafTestAt384 28 29 30
  leafTestAt384_block_28
  leafTestAt384_block_29)
  (interval_append leafTestAt384 30 31 32
  leafTestAt384_block_30
  leafTestAt384_block_31)))))
theorem leafInterval384 : Interval leafTest 384 416 := by
  intro i hlo hhi
  have h := leafTestAt384_complete (i-384) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt384, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
