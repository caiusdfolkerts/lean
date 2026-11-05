module
prelude
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt192 (i : Nat) := leafTest (i+192)
theorem leafTestAt192_block_0 : Interval leafTestAt192 0 1 :=
  interval_of_check leafTestAt192 0 1 (by decide +kernel)

theorem leafTestAt192_block_1 : Interval leafTestAt192 1 2 :=
  interval_of_check leafTestAt192 1 1 (by decide +kernel)

theorem leafTestAt192_block_2 : Interval leafTestAt192 2 3 :=
  interval_of_check leafTestAt192 2 1 (by decide +kernel)

theorem leafTestAt192_block_3 : Interval leafTestAt192 3 4 :=
  interval_of_check leafTestAt192 3 1 (by decide +kernel)

theorem leafTestAt192_block_4 : Interval leafTestAt192 4 5 :=
  interval_of_check leafTestAt192 4 1 (by decide +kernel)

theorem leafTestAt192_block_5 : Interval leafTestAt192 5 6 :=
  interval_of_check leafTestAt192 5 1 (by decide +kernel)

theorem leafTestAt192_block_6 : Interval leafTestAt192 6 7 :=
  interval_of_check leafTestAt192 6 1 (by decide +kernel)

theorem leafTestAt192_block_7 : Interval leafTestAt192 7 8 :=
  interval_of_check leafTestAt192 7 1 (by decide +kernel)

theorem leafTestAt192_block_8 : Interval leafTestAt192 8 9 :=
  interval_of_check leafTestAt192 8 1 (by decide +kernel)

theorem leafTestAt192_block_9 : Interval leafTestAt192 9 10 :=
  interval_of_check leafTestAt192 9 1 (by decide +kernel)

theorem leafTestAt192_block_10 : Interval leafTestAt192 10 11 :=
  interval_of_check leafTestAt192 10 1 (by decide +kernel)

theorem leafTestAt192_block_11 : Interval leafTestAt192 11 12 :=
  interval_of_check leafTestAt192 11 1 (by decide +kernel)

theorem leafTestAt192_block_12 : Interval leafTestAt192 12 13 :=
  interval_of_check leafTestAt192 12 1 (by decide +kernel)

theorem leafTestAt192_block_13 : Interval leafTestAt192 13 14 :=
  interval_of_check leafTestAt192 13 1 (by decide +kernel)

theorem leafTestAt192_block_14 : Interval leafTestAt192 14 15 :=
  interval_of_check leafTestAt192 14 1 (by decide +kernel)

theorem leafTestAt192_block_15 : Interval leafTestAt192 15 16 :=
  interval_of_check leafTestAt192 15 1 (by decide +kernel)

theorem leafTestAt192_block_16 : Interval leafTestAt192 16 17 :=
  interval_of_check leafTestAt192 16 1 (by decide +kernel)

theorem leafTestAt192_block_17 : Interval leafTestAt192 17 18 :=
  interval_of_check leafTestAt192 17 1 (by decide +kernel)

theorem leafTestAt192_block_18 : Interval leafTestAt192 18 19 :=
  interval_of_check leafTestAt192 18 1 (by decide +kernel)

theorem leafTestAt192_block_19 : Interval leafTestAt192 19 20 :=
  interval_of_check leafTestAt192 19 1 (by decide +kernel)

theorem leafTestAt192_block_20 : Interval leafTestAt192 20 21 :=
  interval_of_check leafTestAt192 20 1 (by decide +kernel)

theorem leafTestAt192_block_21 : Interval leafTestAt192 21 22 :=
  interval_of_check leafTestAt192 21 1 (by decide +kernel)

theorem leafTestAt192_block_22 : Interval leafTestAt192 22 23 :=
  interval_of_check leafTestAt192 22 1 (by decide +kernel)

theorem leafTestAt192_block_23 : Interval leafTestAt192 23 24 :=
  interval_of_check leafTestAt192 23 1 (by decide +kernel)

theorem leafTestAt192_block_24 : Interval leafTestAt192 24 25 :=
  interval_of_check leafTestAt192 24 1 (by decide +kernel)

theorem leafTestAt192_block_25 : Interval leafTestAt192 25 26 :=
  interval_of_check leafTestAt192 25 1 (by decide +kernel)

theorem leafTestAt192_block_26 : Interval leafTestAt192 26 27 :=
  interval_of_check leafTestAt192 26 1 (by decide +kernel)

theorem leafTestAt192_block_27 : Interval leafTestAt192 27 28 :=
  interval_of_check leafTestAt192 27 1 (by decide +kernel)

theorem leafTestAt192_block_28 : Interval leafTestAt192 28 29 :=
  interval_of_check leafTestAt192 28 1 (by decide +kernel)

theorem leafTestAt192_block_29 : Interval leafTestAt192 29 30 :=
  interval_of_check leafTestAt192 29 1 (by decide +kernel)

theorem leafTestAt192_block_30 : Interval leafTestAt192 30 31 :=
  interval_of_check leafTestAt192 30 1 (by decide +kernel)

theorem leafTestAt192_block_31 : Interval leafTestAt192 31 32 :=
  interval_of_check leafTestAt192 31 1 (by decide +kernel)

theorem leafTestAt192_complete : Interval leafTestAt192 0 32 :=
  (interval_append leafTestAt192 0 16 32
  (interval_append leafTestAt192 0 8 16
  (interval_append leafTestAt192 0 4 8
  (interval_append leafTestAt192 0 2 4
  (interval_append leafTestAt192 0 1 2
  leafTestAt192_block_0
  leafTestAt192_block_1)
  (interval_append leafTestAt192 2 3 4
  leafTestAt192_block_2
  leafTestAt192_block_3))
  (interval_append leafTestAt192 4 6 8
  (interval_append leafTestAt192 4 5 6
  leafTestAt192_block_4
  leafTestAt192_block_5)
  (interval_append leafTestAt192 6 7 8
  leafTestAt192_block_6
  leafTestAt192_block_7)))
  (interval_append leafTestAt192 8 12 16
  (interval_append leafTestAt192 8 10 12
  (interval_append leafTestAt192 8 9 10
  leafTestAt192_block_8
  leafTestAt192_block_9)
  (interval_append leafTestAt192 10 11 12
  leafTestAt192_block_10
  leafTestAt192_block_11))
  (interval_append leafTestAt192 12 14 16
  (interval_append leafTestAt192 12 13 14
  leafTestAt192_block_12
  leafTestAt192_block_13)
  (interval_append leafTestAt192 14 15 16
  leafTestAt192_block_14
  leafTestAt192_block_15))))
  (interval_append leafTestAt192 16 24 32
  (interval_append leafTestAt192 16 20 24
  (interval_append leafTestAt192 16 18 20
  (interval_append leafTestAt192 16 17 18
  leafTestAt192_block_16
  leafTestAt192_block_17)
  (interval_append leafTestAt192 18 19 20
  leafTestAt192_block_18
  leafTestAt192_block_19))
  (interval_append leafTestAt192 20 22 24
  (interval_append leafTestAt192 20 21 22
  leafTestAt192_block_20
  leafTestAt192_block_21)
  (interval_append leafTestAt192 22 23 24
  leafTestAt192_block_22
  leafTestAt192_block_23)))
  (interval_append leafTestAt192 24 28 32
  (interval_append leafTestAt192 24 26 28
  (interval_append leafTestAt192 24 25 26
  leafTestAt192_block_24
  leafTestAt192_block_25)
  (interval_append leafTestAt192 26 27 28
  leafTestAt192_block_26
  leafTestAt192_block_27))
  (interval_append leafTestAt192 28 30 32
  (interval_append leafTestAt192 28 29 30
  leafTestAt192_block_28
  leafTestAt192_block_29)
  (interval_append leafTestAt192 30 31 32
  leafTestAt192_block_30
  leafTestAt192_block_31)))))
theorem leafInterval192 : Interval leafTest 192 224 := by
  intro i hlo hhi
  have h := leafTestAt192_complete (i-192) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt192, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
