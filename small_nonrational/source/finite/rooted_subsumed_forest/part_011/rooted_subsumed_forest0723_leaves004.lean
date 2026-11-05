module
prelude
public import RootedSubsumedForest0723Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
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

theorem leafTestAt128_complete : Interval leafTestAt128 0 18 :=
  (interval_append leafTestAt128 0 9 18
  (interval_append leafTestAt128 0 4 9
  (interval_append leafTestAt128 0 2 4
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 4
  leafTestAt128_block_2
  leafTestAt128_block_3))
  (interval_append leafTestAt128 4 6 9
  (interval_append leafTestAt128 4 5 6
  leafTestAt128_block_4
  leafTestAt128_block_5)
  (interval_append leafTestAt128 6 7 9
  leafTestAt128_block_6
  (interval_append leafTestAt128 7 8 9
  leafTestAt128_block_7
  leafTestAt128_block_8))))
  (interval_append leafTestAt128 9 13 18
  (interval_append leafTestAt128 9 11 13
  (interval_append leafTestAt128 9 10 11
  leafTestAt128_block_9
  leafTestAt128_block_10)
  (interval_append leafTestAt128 11 12 13
  leafTestAt128_block_11
  leafTestAt128_block_12))
  (interval_append leafTestAt128 13 15 18
  (interval_append leafTestAt128 13 14 15
  leafTestAt128_block_13
  leafTestAt128_block_14)
  (interval_append leafTestAt128 15 16 18
  leafTestAt128_block_15
  (interval_append leafTestAt128 16 17 18
  leafTestAt128_block_16
  leafTestAt128_block_17)))))
theorem leafInterval128 : Interval leafTest 128 146 := by
  intro i hlo hhi
  have h := leafTestAt128_complete (i-128) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt128, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
