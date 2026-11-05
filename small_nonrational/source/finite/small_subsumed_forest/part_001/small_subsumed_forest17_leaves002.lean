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
def leafTestAt64 (i : Nat) := leafTest (i+64)
theorem leafTestAt64_block_0 : Interval leafTestAt64 0 1 :=
  interval_of_check leafTestAt64 0 1 (by decide +kernel)

theorem leafTestAt64_block_1 : Interval leafTestAt64 1 2 :=
  interval_of_check leafTestAt64 1 1 (by decide +kernel)

theorem leafTestAt64_block_2 : Interval leafTestAt64 2 3 :=
  interval_of_check leafTestAt64 2 1 (by decide +kernel)

theorem leafTestAt64_block_3 : Interval leafTestAt64 3 4 :=
  interval_of_check leafTestAt64 3 1 (by decide +kernel)

theorem leafTestAt64_block_4 : Interval leafTestAt64 4 5 :=
  interval_of_check leafTestAt64 4 1 (by decide +kernel)

theorem leafTestAt64_block_5 : Interval leafTestAt64 5 6 :=
  interval_of_check leafTestAt64 5 1 (by decide +kernel)

theorem leafTestAt64_block_6 : Interval leafTestAt64 6 7 :=
  interval_of_check leafTestAt64 6 1 (by decide +kernel)

theorem leafTestAt64_block_7 : Interval leafTestAt64 7 8 :=
  interval_of_check leafTestAt64 7 1 (by decide +kernel)

theorem leafTestAt64_block_8 : Interval leafTestAt64 8 9 :=
  interval_of_check leafTestAt64 8 1 (by decide +kernel)

theorem leafTestAt64_block_9 : Interval leafTestAt64 9 10 :=
  interval_of_check leafTestAt64 9 1 (by decide +kernel)

theorem leafTestAt64_block_10 : Interval leafTestAt64 10 11 :=
  interval_of_check leafTestAt64 10 1 (by decide +kernel)

theorem leafTestAt64_block_11 : Interval leafTestAt64 11 12 :=
  interval_of_check leafTestAt64 11 1 (by decide +kernel)

theorem leafTestAt64_block_12 : Interval leafTestAt64 12 13 :=
  interval_of_check leafTestAt64 12 1 (by decide +kernel)

theorem leafTestAt64_block_13 : Interval leafTestAt64 13 14 :=
  interval_of_check leafTestAt64 13 1 (by decide +kernel)

theorem leafTestAt64_block_14 : Interval leafTestAt64 14 15 :=
  interval_of_check leafTestAt64 14 1 (by decide +kernel)

theorem leafTestAt64_block_15 : Interval leafTestAt64 15 16 :=
  interval_of_check leafTestAt64 15 1 (by decide +kernel)

theorem leafTestAt64_block_16 : Interval leafTestAt64 16 17 :=
  interval_of_check leafTestAt64 16 1 (by decide +kernel)

theorem leafTestAt64_block_17 : Interval leafTestAt64 17 18 :=
  interval_of_check leafTestAt64 17 1 (by decide +kernel)

theorem leafTestAt64_block_18 : Interval leafTestAt64 18 19 :=
  interval_of_check leafTestAt64 18 1 (by decide +kernel)

theorem leafTestAt64_block_19 : Interval leafTestAt64 19 20 :=
  interval_of_check leafTestAt64 19 1 (by decide +kernel)

theorem leafTestAt64_block_20 : Interval leafTestAt64 20 21 :=
  interval_of_check leafTestAt64 20 1 (by decide +kernel)

theorem leafTestAt64_block_21 : Interval leafTestAt64 21 22 :=
  interval_of_check leafTestAt64 21 1 (by decide +kernel)

theorem leafTestAt64_block_22 : Interval leafTestAt64 22 23 :=
  interval_of_check leafTestAt64 22 1 (by decide +kernel)

theorem leafTestAt64_complete : Interval leafTestAt64 0 23 :=
  (interval_append leafTestAt64 0 11 23
  (interval_append leafTestAt64 0 5 11
  (interval_append leafTestAt64 0 2 5
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 5
  leafTestAt64_block_2
  (interval_append leafTestAt64 3 4 5
  leafTestAt64_block_3
  leafTestAt64_block_4)))
  (interval_append leafTestAt64 5 8 11
  (interval_append leafTestAt64 5 6 8
  leafTestAt64_block_5
  (interval_append leafTestAt64 6 7 8
  leafTestAt64_block_6
  leafTestAt64_block_7))
  (interval_append leafTestAt64 8 9 11
  leafTestAt64_block_8
  (interval_append leafTestAt64 9 10 11
  leafTestAt64_block_9
  leafTestAt64_block_10))))
  (interval_append leafTestAt64 11 17 23
  (interval_append leafTestAt64 11 14 17
  (interval_append leafTestAt64 11 12 14
  leafTestAt64_block_11
  (interval_append leafTestAt64 12 13 14
  leafTestAt64_block_12
  leafTestAt64_block_13))
  (interval_append leafTestAt64 14 15 17
  leafTestAt64_block_14
  (interval_append leafTestAt64 15 16 17
  leafTestAt64_block_15
  leafTestAt64_block_16)))
  (interval_append leafTestAt64 17 20 23
  (interval_append leafTestAt64 17 18 20
  leafTestAt64_block_17
  (interval_append leafTestAt64 18 19 20
  leafTestAt64_block_18
  leafTestAt64_block_19))
  (interval_append leafTestAt64 20 21 23
  leafTestAt64_block_20
  (interval_append leafTestAt64 21 22 23
  leafTestAt64_block_21
  leafTestAt64_block_22)))))
theorem leafInterval64 : Interval leafTest 64 87 := by
  intro i hlo hhi
  have h := leafTestAt64_complete (i-64) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt64, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest17
