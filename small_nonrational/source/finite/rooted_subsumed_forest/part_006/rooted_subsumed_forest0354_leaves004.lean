module
prelude
public import RootedSubsumedForest0354Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt128 (i : Nat) := leafTest (i+128)
theorem leafTestAt128_block_0 : Interval leafTestAt128 0 1 :=
  interval_of_check leafTestAt128 0 1 (by decide +kernel)

theorem leafTestAt128_block_1 : Interval leafTestAt128 1 2 :=
  interval_of_check leafTestAt128 1 1 (by decide +kernel)

theorem leafTestAt128_block_2 : Interval leafTestAt128 2 3 :=
  interval_of_check leafTestAt128 2 1 (by decide +kernel)

theorem leafTestAt128_block_3 : Interval leafTestAt128 3 4 :=
  interval_of_check leafTestAt128 3 1 (by decide +kernel)

theorem leafTestAt128_block_4 : Interval leafTestAt128 4 5 :=
  interval_of_check leafTestAt128 4 1 (by decide +kernel)

theorem leafTestAt128_block_5 : Interval leafTestAt128 5 6 :=
  interval_of_check leafTestAt128 5 1 (by decide +kernel)

theorem leafTestAt128_block_6 : Interval leafTestAt128 6 7 :=
  interval_of_check leafTestAt128 6 1 (by decide +kernel)

theorem leafTestAt128_block_7 : Interval leafTestAt128 7 8 :=
  interval_of_check leafTestAt128 7 1 (by decide +kernel)

theorem leafTestAt128_block_8 : Interval leafTestAt128 8 9 :=
  interval_of_check leafTestAt128 8 1 (by decide +kernel)

theorem leafTestAt128_block_9 : Interval leafTestAt128 9 10 :=
  interval_of_check leafTestAt128 9 1 (by decide +kernel)

theorem leafTestAt128_block_10 : Interval leafTestAt128 10 11 :=
  interval_of_check leafTestAt128 10 1 (by decide +kernel)

theorem leafTestAt128_block_11 : Interval leafTestAt128 11 12 :=
  interval_of_check leafTestAt128 11 1 (by decide +kernel)

theorem leafTestAt128_block_12 : Interval leafTestAt128 12 13 :=
  interval_of_check leafTestAt128 12 1 (by decide +kernel)

theorem leafTestAt128_block_13 : Interval leafTestAt128 13 14 :=
  interval_of_check leafTestAt128 13 1 (by decide +kernel)

theorem leafTestAt128_block_14 : Interval leafTestAt128 14 15 :=
  interval_of_check leafTestAt128 14 1 (by decide +kernel)

theorem leafTestAt128_block_15 : Interval leafTestAt128 15 16 :=
  interval_of_check leafTestAt128 15 1 (by decide +kernel)

theorem leafTestAt128_block_16 : Interval leafTestAt128 16 17 :=
  interval_of_check leafTestAt128 16 1 (by decide +kernel)

theorem leafTestAt128_block_17 : Interval leafTestAt128 17 18 :=
  interval_of_check leafTestAt128 17 1 (by decide +kernel)

theorem leafTestAt128_block_18 : Interval leafTestAt128 18 19 :=
  interval_of_check leafTestAt128 18 1 (by decide +kernel)

theorem leafTestAt128_block_19 : Interval leafTestAt128 19 20 :=
  interval_of_check leafTestAt128 19 1 (by decide +kernel)

theorem leafTestAt128_block_20 : Interval leafTestAt128 20 21 :=
  interval_of_check leafTestAt128 20 1 (by decide +kernel)

theorem leafTestAt128_block_21 : Interval leafTestAt128 21 22 :=
  interval_of_check leafTestAt128 21 1 (by decide +kernel)

theorem leafTestAt128_block_22 : Interval leafTestAt128 22 23 :=
  interval_of_check leafTestAt128 22 1 (by decide +kernel)

theorem leafTestAt128_block_23 : Interval leafTestAt128 23 24 :=
  interval_of_check leafTestAt128 23 1 (by decide +kernel)

theorem leafTestAt128_block_24 : Interval leafTestAt128 24 25 :=
  interval_of_check leafTestAt128 24 1 (by decide +kernel)

theorem leafTestAt128_block_25 : Interval leafTestAt128 25 26 :=
  interval_of_check leafTestAt128 25 1 (by decide +kernel)

theorem leafTestAt128_block_26 : Interval leafTestAt128 26 27 :=
  interval_of_check leafTestAt128 26 1 (by decide +kernel)

theorem leafTestAt128_block_27 : Interval leafTestAt128 27 28 :=
  interval_of_check leafTestAt128 27 1 (by decide +kernel)

theorem leafTestAt128_complete : Interval leafTestAt128 0 28 :=
  (interval_append leafTestAt128 0 14 28
  (interval_append leafTestAt128 0 7 14
  (interval_append leafTestAt128 0 3 7
  (interval_append leafTestAt128 0 1 3
  leafTestAt128_block_0
  (interval_append leafTestAt128 1 2 3
  leafTestAt128_block_1
  leafTestAt128_block_2))
  (interval_append leafTestAt128 3 5 7
  (interval_append leafTestAt128 3 4 5
  leafTestAt128_block_3
  leafTestAt128_block_4)
  (interval_append leafTestAt128 5 6 7
  leafTestAt128_block_5
  leafTestAt128_block_6)))
  (interval_append leafTestAt128 7 10 14
  (interval_append leafTestAt128 7 8 10
  leafTestAt128_block_7
  (interval_append leafTestAt128 8 9 10
  leafTestAt128_block_8
  leafTestAt128_block_9))
  (interval_append leafTestAt128 10 12 14
  (interval_append leafTestAt128 10 11 12
  leafTestAt128_block_10
  leafTestAt128_block_11)
  (interval_append leafTestAt128 12 13 14
  leafTestAt128_block_12
  leafTestAt128_block_13))))
  (interval_append leafTestAt128 14 21 28
  (interval_append leafTestAt128 14 17 21
  (interval_append leafTestAt128 14 15 17
  leafTestAt128_block_14
  (interval_append leafTestAt128 15 16 17
  leafTestAt128_block_15
  leafTestAt128_block_16))
  (interval_append leafTestAt128 17 19 21
  (interval_append leafTestAt128 17 18 19
  leafTestAt128_block_17
  leafTestAt128_block_18)
  (interval_append leafTestAt128 19 20 21
  leafTestAt128_block_19
  leafTestAt128_block_20)))
  (interval_append leafTestAt128 21 24 28
  (interval_append leafTestAt128 21 22 24
  leafTestAt128_block_21
  (interval_append leafTestAt128 22 23 24
  leafTestAt128_block_22
  leafTestAt128_block_23))
  (interval_append leafTestAt128 24 26 28
  (interval_append leafTestAt128 24 25 26
  leafTestAt128_block_24
  leafTestAt128_block_25)
  (interval_append leafTestAt128 26 27 28
  leafTestAt128_block_26
  leafTestAt128_block_27)))))
theorem leafInterval128 : Interval leafTest 128 156 := by
  intro i hlo hhi
  have h := leafTestAt128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
