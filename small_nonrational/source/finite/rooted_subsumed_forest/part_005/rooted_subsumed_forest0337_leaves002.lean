module
prelude
public import RootedSubsumedForest0337Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
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

theorem leafTestAt64_block_23 : Interval leafTestAt64 23 24 :=
  interval_of_check leafTestAt64 23 1 (by decide +kernel)

theorem leafTestAt64_block_24 : Interval leafTestAt64 24 25 :=
  interval_of_check leafTestAt64 24 1 (by decide +kernel)

theorem leafTestAt64_block_25 : Interval leafTestAt64 25 26 :=
  interval_of_check leafTestAt64 25 1 (by decide +kernel)

theorem leafTestAt64_block_26 : Interval leafTestAt64 26 27 :=
  interval_of_check leafTestAt64 26 1 (by decide +kernel)

theorem leafTestAt64_block_27 : Interval leafTestAt64 27 28 :=
  interval_of_check leafTestAt64 27 1 (by decide +kernel)

theorem leafTestAt64_block_28 : Interval leafTestAt64 28 29 :=
  interval_of_check leafTestAt64 28 1 (by decide +kernel)

theorem leafTestAt64_block_29 : Interval leafTestAt64 29 30 :=
  interval_of_check leafTestAt64 29 1 (by decide +kernel)

theorem leafTestAt64_block_30 : Interval leafTestAt64 30 31 :=
  interval_of_check leafTestAt64 30 1 (by decide +kernel)

theorem leafTestAt64_block_31 : Interval leafTestAt64 31 32 :=
  interval_of_check leafTestAt64 31 1 (by decide +kernel)

theorem leafTestAt64_complete : Interval leafTestAt64 0 32 :=
  (interval_append leafTestAt64 0 16 32
  (interval_append leafTestAt64 0 8 16
  (interval_append leafTestAt64 0 4 8
  (interval_append leafTestAt64 0 2 4
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 4
  leafTestAt64_block_2
  leafTestAt64_block_3))
  (interval_append leafTestAt64 4 6 8
  (interval_append leafTestAt64 4 5 6
  leafTestAt64_block_4
  leafTestAt64_block_5)
  (interval_append leafTestAt64 6 7 8
  leafTestAt64_block_6
  leafTestAt64_block_7)))
  (interval_append leafTestAt64 8 12 16
  (interval_append leafTestAt64 8 10 12
  (interval_append leafTestAt64 8 9 10
  leafTestAt64_block_8
  leafTestAt64_block_9)
  (interval_append leafTestAt64 10 11 12
  leafTestAt64_block_10
  leafTestAt64_block_11))
  (interval_append leafTestAt64 12 14 16
  (interval_append leafTestAt64 12 13 14
  leafTestAt64_block_12
  leafTestAt64_block_13)
  (interval_append leafTestAt64 14 15 16
  leafTestAt64_block_14
  leafTestAt64_block_15))))
  (interval_append leafTestAt64 16 24 32
  (interval_append leafTestAt64 16 20 24
  (interval_append leafTestAt64 16 18 20
  (interval_append leafTestAt64 16 17 18
  leafTestAt64_block_16
  leafTestAt64_block_17)
  (interval_append leafTestAt64 18 19 20
  leafTestAt64_block_18
  leafTestAt64_block_19))
  (interval_append leafTestAt64 20 22 24
  (interval_append leafTestAt64 20 21 22
  leafTestAt64_block_20
  leafTestAt64_block_21)
  (interval_append leafTestAt64 22 23 24
  leafTestAt64_block_22
  leafTestAt64_block_23)))
  (interval_append leafTestAt64 24 28 32
  (interval_append leafTestAt64 24 26 28
  (interval_append leafTestAt64 24 25 26
  leafTestAt64_block_24
  leafTestAt64_block_25)
  (interval_append leafTestAt64 26 27 28
  leafTestAt64_block_26
  leafTestAt64_block_27))
  (interval_append leafTestAt64 28 30 32
  (interval_append leafTestAt64 28 29 30
  leafTestAt64_block_28
  leafTestAt64_block_29)
  (interval_append leafTestAt64 30 31 32
  leafTestAt64_block_30
  leafTestAt64_block_31)))))
theorem leafInterval64 : Interval leafTest 64 96 := by
  intro i hlo hhi
  have h := leafTestAt64_complete (i-64) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt64, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
