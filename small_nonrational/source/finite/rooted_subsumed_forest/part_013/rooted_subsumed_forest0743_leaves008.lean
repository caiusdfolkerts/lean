module
prelude
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt256 (i : Nat) := leafTest (i+256)
theorem leafTestAt256_block_0 : Interval leafTestAt256 0 1 :=
  interval_of_check leafTestAt256 0 1 (by decide +kernel)

theorem leafTestAt256_block_1 : Interval leafTestAt256 1 2 :=
  interval_of_check leafTestAt256 1 1 (by decide +kernel)

theorem leafTestAt256_block_2 : Interval leafTestAt256 2 3 :=
  interval_of_check leafTestAt256 2 1 (by decide +kernel)

theorem leafTestAt256_block_3 : Interval leafTestAt256 3 4 :=
  interval_of_check leafTestAt256 3 1 (by decide +kernel)

theorem leafTestAt256_block_4 : Interval leafTestAt256 4 5 :=
  interval_of_check leafTestAt256 4 1 (by decide +kernel)

theorem leafTestAt256_block_5 : Interval leafTestAt256 5 6 :=
  interval_of_check leafTestAt256 5 1 (by decide +kernel)

theorem leafTestAt256_block_6 : Interval leafTestAt256 6 7 :=
  interval_of_check leafTestAt256 6 1 (by decide +kernel)

theorem leafTestAt256_block_7 : Interval leafTestAt256 7 8 :=
  interval_of_check leafTestAt256 7 1 (by decide +kernel)

theorem leafTestAt256_block_8 : Interval leafTestAt256 8 9 :=
  interval_of_check leafTestAt256 8 1 (by decide +kernel)

theorem leafTestAt256_block_9 : Interval leafTestAt256 9 10 :=
  interval_of_check leafTestAt256 9 1 (by decide +kernel)

theorem leafTestAt256_block_10 : Interval leafTestAt256 10 11 :=
  interval_of_check leafTestAt256 10 1 (by decide +kernel)

theorem leafTestAt256_block_11 : Interval leafTestAt256 11 12 :=
  interval_of_check leafTestAt256 11 1 (by decide +kernel)

theorem leafTestAt256_block_12 : Interval leafTestAt256 12 13 :=
  interval_of_check leafTestAt256 12 1 (by decide +kernel)

theorem leafTestAt256_block_13 : Interval leafTestAt256 13 14 :=
  interval_of_check leafTestAt256 13 1 (by decide +kernel)

theorem leafTestAt256_block_14 : Interval leafTestAt256 14 15 :=
  interval_of_check leafTestAt256 14 1 (by decide +kernel)

theorem leafTestAt256_block_15 : Interval leafTestAt256 15 16 :=
  interval_of_check leafTestAt256 15 1 (by decide +kernel)

theorem leafTestAt256_block_16 : Interval leafTestAt256 16 17 :=
  interval_of_check leafTestAt256 16 1 (by decide +kernel)

theorem leafTestAt256_block_17 : Interval leafTestAt256 17 18 :=
  interval_of_check leafTestAt256 17 1 (by decide +kernel)

theorem leafTestAt256_block_18 : Interval leafTestAt256 18 19 :=
  interval_of_check leafTestAt256 18 1 (by decide +kernel)

theorem leafTestAt256_block_19 : Interval leafTestAt256 19 20 :=
  interval_of_check leafTestAt256 19 1 (by decide +kernel)

theorem leafTestAt256_block_20 : Interval leafTestAt256 20 21 :=
  interval_of_check leafTestAt256 20 1 (by decide +kernel)

theorem leafTestAt256_block_21 : Interval leafTestAt256 21 22 :=
  interval_of_check leafTestAt256 21 1 (by decide +kernel)

theorem leafTestAt256_block_22 : Interval leafTestAt256 22 23 :=
  interval_of_check leafTestAt256 22 1 (by decide +kernel)

theorem leafTestAt256_block_23 : Interval leafTestAt256 23 24 :=
  interval_of_check leafTestAt256 23 1 (by decide +kernel)

theorem leafTestAt256_block_24 : Interval leafTestAt256 24 25 :=
  interval_of_check leafTestAt256 24 1 (by decide +kernel)

theorem leafTestAt256_block_25 : Interval leafTestAt256 25 26 :=
  interval_of_check leafTestAt256 25 1 (by decide +kernel)

theorem leafTestAt256_block_26 : Interval leafTestAt256 26 27 :=
  interval_of_check leafTestAt256 26 1 (by decide +kernel)

theorem leafTestAt256_block_27 : Interval leafTestAt256 27 28 :=
  interval_of_check leafTestAt256 27 1 (by decide +kernel)

theorem leafTestAt256_block_28 : Interval leafTestAt256 28 29 :=
  interval_of_check leafTestAt256 28 1 (by decide +kernel)

theorem leafTestAt256_block_29 : Interval leafTestAt256 29 30 :=
  interval_of_check leafTestAt256 29 1 (by decide +kernel)

theorem leafTestAt256_block_30 : Interval leafTestAt256 30 31 :=
  interval_of_check leafTestAt256 30 1 (by decide +kernel)

theorem leafTestAt256_block_31 : Interval leafTestAt256 31 32 :=
  interval_of_check leafTestAt256 31 1 (by decide +kernel)

theorem leafTestAt256_complete : Interval leafTestAt256 0 32 :=
  (interval_append leafTestAt256 0 16 32
  (interval_append leafTestAt256 0 8 16
  (interval_append leafTestAt256 0 4 8
  (interval_append leafTestAt256 0 2 4
  (interval_append leafTestAt256 0 1 2
  leafTestAt256_block_0
  leafTestAt256_block_1)
  (interval_append leafTestAt256 2 3 4
  leafTestAt256_block_2
  leafTestAt256_block_3))
  (interval_append leafTestAt256 4 6 8
  (interval_append leafTestAt256 4 5 6
  leafTestAt256_block_4
  leafTestAt256_block_5)
  (interval_append leafTestAt256 6 7 8
  leafTestAt256_block_6
  leafTestAt256_block_7)))
  (interval_append leafTestAt256 8 12 16
  (interval_append leafTestAt256 8 10 12
  (interval_append leafTestAt256 8 9 10
  leafTestAt256_block_8
  leafTestAt256_block_9)
  (interval_append leafTestAt256 10 11 12
  leafTestAt256_block_10
  leafTestAt256_block_11))
  (interval_append leafTestAt256 12 14 16
  (interval_append leafTestAt256 12 13 14
  leafTestAt256_block_12
  leafTestAt256_block_13)
  (interval_append leafTestAt256 14 15 16
  leafTestAt256_block_14
  leafTestAt256_block_15))))
  (interval_append leafTestAt256 16 24 32
  (interval_append leafTestAt256 16 20 24
  (interval_append leafTestAt256 16 18 20
  (interval_append leafTestAt256 16 17 18
  leafTestAt256_block_16
  leafTestAt256_block_17)
  (interval_append leafTestAt256 18 19 20
  leafTestAt256_block_18
  leafTestAt256_block_19))
  (interval_append leafTestAt256 20 22 24
  (interval_append leafTestAt256 20 21 22
  leafTestAt256_block_20
  leafTestAt256_block_21)
  (interval_append leafTestAt256 22 23 24
  leafTestAt256_block_22
  leafTestAt256_block_23)))
  (interval_append leafTestAt256 24 28 32
  (interval_append leafTestAt256 24 26 28
  (interval_append leafTestAt256 24 25 26
  leafTestAt256_block_24
  leafTestAt256_block_25)
  (interval_append leafTestAt256 26 27 28
  leafTestAt256_block_26
  leafTestAt256_block_27))
  (interval_append leafTestAt256 28 30 32
  (interval_append leafTestAt256 28 29 30
  leafTestAt256_block_28
  leafTestAt256_block_29)
  (interval_append leafTestAt256 30 31 32
  leafTestAt256_block_30
  leafTestAt256_block_31)))))
theorem leafInterval256 : Interval leafTest 256 288 := by
  intro i hlo hhi
  have h := leafTestAt256_complete (i-256) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt256, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
