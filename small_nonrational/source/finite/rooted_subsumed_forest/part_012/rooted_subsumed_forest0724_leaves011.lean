module
prelude
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
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

theorem leafTestAt352_block_31 : Interval leafTestAt352 31 32 :=
  interval_of_check leafTestAt352 31 1 (by decide +kernel)

theorem leafTestAt352_complete : Interval leafTestAt352 0 32 :=
  (interval_append leafTestAt352 0 16 32
  (interval_append leafTestAt352 0 8 16
  (interval_append leafTestAt352 0 4 8
  (interval_append leafTestAt352 0 2 4
  (interval_append leafTestAt352 0 1 2
  leafTestAt352_block_0
  leafTestAt352_block_1)
  (interval_append leafTestAt352 2 3 4
  leafTestAt352_block_2
  leafTestAt352_block_3))
  (interval_append leafTestAt352 4 6 8
  (interval_append leafTestAt352 4 5 6
  leafTestAt352_block_4
  leafTestAt352_block_5)
  (interval_append leafTestAt352 6 7 8
  leafTestAt352_block_6
  leafTestAt352_block_7)))
  (interval_append leafTestAt352 8 12 16
  (interval_append leafTestAt352 8 10 12
  (interval_append leafTestAt352 8 9 10
  leafTestAt352_block_8
  leafTestAt352_block_9)
  (interval_append leafTestAt352 10 11 12
  leafTestAt352_block_10
  leafTestAt352_block_11))
  (interval_append leafTestAt352 12 14 16
  (interval_append leafTestAt352 12 13 14
  leafTestAt352_block_12
  leafTestAt352_block_13)
  (interval_append leafTestAt352 14 15 16
  leafTestAt352_block_14
  leafTestAt352_block_15))))
  (interval_append leafTestAt352 16 24 32
  (interval_append leafTestAt352 16 20 24
  (interval_append leafTestAt352 16 18 20
  (interval_append leafTestAt352 16 17 18
  leafTestAt352_block_16
  leafTestAt352_block_17)
  (interval_append leafTestAt352 18 19 20
  leafTestAt352_block_18
  leafTestAt352_block_19))
  (interval_append leafTestAt352 20 22 24
  (interval_append leafTestAt352 20 21 22
  leafTestAt352_block_20
  leafTestAt352_block_21)
  (interval_append leafTestAt352 22 23 24
  leafTestAt352_block_22
  leafTestAt352_block_23)))
  (interval_append leafTestAt352 24 28 32
  (interval_append leafTestAt352 24 26 28
  (interval_append leafTestAt352 24 25 26
  leafTestAt352_block_24
  leafTestAt352_block_25)
  (interval_append leafTestAt352 26 27 28
  leafTestAt352_block_26
  leafTestAt352_block_27))
  (interval_append leafTestAt352 28 30 32
  (interval_append leafTestAt352 28 29 30
  leafTestAt352_block_28
  leafTestAt352_block_29)
  (interval_append leafTestAt352 30 31 32
  leafTestAt352_block_30
  leafTestAt352_block_31)))))
theorem leafInterval352 : Interval leafTest 352 384 := by
  intro i hlo hhi
  have h := leafTestAt352_complete (i-352) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt352, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
