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
def leafTestAt352 (i : Nat) := leafTest (i+352)
theorem leafTestAt352_block_0 : Interval leafTestAt352 0 1 :=
  interval_of_check leafTestAt352 0 1 (by decide +kernel)

theorem leafTestAt352_block_1 : Interval leafTestAt352 1 2 :=
  interval_of_check leafTestAt352 1 1 (by decide +kernel)

theorem leafTestAt352_block_2 : Interval leafTestAt352 2 3 :=
  interval_of_check leafTestAt352 2 1 (by decide +kernel)

theorem leafTestAt352_block_3 : Interval leafTestAt352 3 4 :=
  interval_of_check leafTestAt352 3 1 (by decide +kernel)

theorem leafTestAt352_block_4 : Interval leafTestAt352 4 5 :=
  interval_of_check leafTestAt352 4 1 (by decide +kernel)

theorem leafTestAt352_block_5 : Interval leafTestAt352 5 6 :=
  interval_of_check leafTestAt352 5 1 (by decide +kernel)

theorem leafTestAt352_block_6 : Interval leafTestAt352 6 7 :=
  interval_of_check leafTestAt352 6 1 (by decide +kernel)

theorem leafTestAt352_block_7 : Interval leafTestAt352 7 8 :=
  interval_of_check leafTestAt352 7 1 (by decide +kernel)

theorem leafTestAt352_block_8 : Interval leafTestAt352 8 9 :=
  interval_of_check leafTestAt352 8 1 (by decide +kernel)

theorem leafTestAt352_block_9 : Interval leafTestAt352 9 10 :=
  interval_of_check leafTestAt352 9 1 (by decide +kernel)

theorem leafTestAt352_block_10 : Interval leafTestAt352 10 11 :=
  interval_of_check leafTestAt352 10 1 (by decide +kernel)

theorem leafTestAt352_block_11 : Interval leafTestAt352 11 12 :=
  interval_of_check leafTestAt352 11 1 (by decide +kernel)

theorem leafTestAt352_block_12 : Interval leafTestAt352 12 13 :=
  interval_of_check leafTestAt352 12 1 (by decide +kernel)

theorem leafTestAt352_block_13 : Interval leafTestAt352 13 14 :=
  interval_of_check leafTestAt352 13 1 (by decide +kernel)

theorem leafTestAt352_block_14 : Interval leafTestAt352 14 15 :=
  interval_of_check leafTestAt352 14 1 (by decide +kernel)

theorem leafTestAt352_block_15 : Interval leafTestAt352 15 16 :=
  interval_of_check leafTestAt352 15 1 (by decide +kernel)

theorem leafTestAt352_block_16 : Interval leafTestAt352 16 17 :=
  interval_of_check leafTestAt352 16 1 (by decide +kernel)

theorem leafTestAt352_block_17 : Interval leafTestAt352 17 18 :=
  interval_of_check leafTestAt352 17 1 (by decide +kernel)

theorem leafTestAt352_block_18 : Interval leafTestAt352 18 19 :=
  interval_of_check leafTestAt352 18 1 (by decide +kernel)

theorem leafTestAt352_block_19 : Interval leafTestAt352 19 20 :=
  interval_of_check leafTestAt352 19 1 (by decide +kernel)

theorem leafTestAt352_block_20 : Interval leafTestAt352 20 21 :=
  interval_of_check leafTestAt352 20 1 (by decide +kernel)

theorem leafTestAt352_block_21 : Interval leafTestAt352 21 22 :=
  interval_of_check leafTestAt352 21 1 (by decide +kernel)

theorem leafTestAt352_block_22 : Interval leafTestAt352 22 23 :=
  interval_of_check leafTestAt352 22 1 (by decide +kernel)

theorem leafTestAt352_block_23 : Interval leafTestAt352 23 24 :=
  interval_of_check leafTestAt352 23 1 (by decide +kernel)

theorem leafTestAt352_block_24 : Interval leafTestAt352 24 25 :=
  interval_of_check leafTestAt352 24 1 (by decide +kernel)

theorem leafTestAt352_block_25 : Interval leafTestAt352 25 26 :=
  interval_of_check leafTestAt352 25 1 (by decide +kernel)

theorem leafTestAt352_block_26 : Interval leafTestAt352 26 27 :=
  interval_of_check leafTestAt352 26 1 (by decide +kernel)

theorem leafTestAt352_block_27 : Interval leafTestAt352 27 28 :=
  interval_of_check leafTestAt352 27 1 (by decide +kernel)

theorem leafTestAt352_block_28 : Interval leafTestAt352 28 29 :=
  interval_of_check leafTestAt352 28 1 (by decide +kernel)

theorem leafTestAt352_block_29 : Interval leafTestAt352 29 30 :=
  interval_of_check leafTestAt352 29 1 (by decide +kernel)

theorem leafTestAt352_block_30 : Interval leafTestAt352 30 31 :=
  interval_of_check leafTestAt352 30 1 (by decide +kernel)

theorem leafTestAt352_complete : Interval leafTestAt352 0 31 :=
  (interval_append leafTestAt352 0 15 31
  (interval_append leafTestAt352 0 7 15
  (interval_append leafTestAt352 0 3 7
  (interval_append leafTestAt352 0 1 3
  leafTestAt352_block_0
  (interval_append leafTestAt352 1 2 3
  leafTestAt352_block_1
  leafTestAt352_block_2))
  (interval_append leafTestAt352 3 5 7
  (interval_append leafTestAt352 3 4 5
  leafTestAt352_block_3
  leafTestAt352_block_4)
  (interval_append leafTestAt352 5 6 7
  leafTestAt352_block_5
  leafTestAt352_block_6)))
  (interval_append leafTestAt352 7 11 15
  (interval_append leafTestAt352 7 9 11
  (interval_append leafTestAt352 7 8 9
  leafTestAt352_block_7
  leafTestAt352_block_8)
  (interval_append leafTestAt352 9 10 11
  leafTestAt352_block_9
  leafTestAt352_block_10))
  (interval_append leafTestAt352 11 13 15
  (interval_append leafTestAt352 11 12 13
  leafTestAt352_block_11
  leafTestAt352_block_12)
  (interval_append leafTestAt352 13 14 15
  leafTestAt352_block_13
  leafTestAt352_block_14))))
  (interval_append leafTestAt352 15 23 31
  (interval_append leafTestAt352 15 19 23
  (interval_append leafTestAt352 15 17 19
  (interval_append leafTestAt352 15 16 17
  leafTestAt352_block_15
  leafTestAt352_block_16)
  (interval_append leafTestAt352 17 18 19
  leafTestAt352_block_17
  leafTestAt352_block_18))
  (interval_append leafTestAt352 19 21 23
  (interval_append leafTestAt352 19 20 21
  leafTestAt352_block_19
  leafTestAt352_block_20)
  (interval_append leafTestAt352 21 22 23
  leafTestAt352_block_21
  leafTestAt352_block_22)))
  (interval_append leafTestAt352 23 27 31
  (interval_append leafTestAt352 23 25 27
  (interval_append leafTestAt352 23 24 25
  leafTestAt352_block_23
  leafTestAt352_block_24)
  (interval_append leafTestAt352 25 26 27
  leafTestAt352_block_25
  leafTestAt352_block_26))
  (interval_append leafTestAt352 27 29 31
  (interval_append leafTestAt352 27 28 29
  leafTestAt352_block_27
  leafTestAt352_block_28)
  (interval_append leafTestAt352 29 30 31
  leafTestAt352_block_29
  leafTestAt352_block_30)))))
theorem leafInterval352 : Interval leafTest 352 383 := by
  intro i hlo hhi
  have h := leafTestAt352_complete (i-352) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt352, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
