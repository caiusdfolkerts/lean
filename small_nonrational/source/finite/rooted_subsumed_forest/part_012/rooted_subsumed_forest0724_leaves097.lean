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
def leafTestAt3104 (i : Nat) := leafTest (i+3104)
theorem leafTestAt3104_block_0 : Interval leafTestAt3104 0 1 :=
  interval_of_check leafTestAt3104 0 1 (by decide +kernel)

theorem leafTestAt3104_block_1 : Interval leafTestAt3104 1 2 :=
  interval_of_check leafTestAt3104 1 1 (by decide +kernel)

theorem leafTestAt3104_block_2 : Interval leafTestAt3104 2 3 :=
  interval_of_check leafTestAt3104 2 1 (by decide +kernel)

theorem leafTestAt3104_block_3 : Interval leafTestAt3104 3 4 :=
  interval_of_check leafTestAt3104 3 1 (by decide +kernel)

theorem leafTestAt3104_block_4 : Interval leafTestAt3104 4 5 :=
  interval_of_check leafTestAt3104 4 1 (by decide +kernel)

theorem leafTestAt3104_block_5 : Interval leafTestAt3104 5 6 :=
  interval_of_check leafTestAt3104 5 1 (by decide +kernel)

theorem leafTestAt3104_block_6 : Interval leafTestAt3104 6 7 :=
  interval_of_check leafTestAt3104 6 1 (by decide +kernel)

theorem leafTestAt3104_block_7 : Interval leafTestAt3104 7 8 :=
  interval_of_check leafTestAt3104 7 1 (by decide +kernel)

theorem leafTestAt3104_block_8 : Interval leafTestAt3104 8 9 :=
  interval_of_check leafTestAt3104 8 1 (by decide +kernel)

theorem leafTestAt3104_block_9 : Interval leafTestAt3104 9 10 :=
  interval_of_check leafTestAt3104 9 1 (by decide +kernel)

theorem leafTestAt3104_block_10 : Interval leafTestAt3104 10 11 :=
  interval_of_check leafTestAt3104 10 1 (by decide +kernel)

theorem leafTestAt3104_block_11 : Interval leafTestAt3104 11 12 :=
  interval_of_check leafTestAt3104 11 1 (by decide +kernel)

theorem leafTestAt3104_block_12 : Interval leafTestAt3104 12 13 :=
  interval_of_check leafTestAt3104 12 1 (by decide +kernel)

theorem leafTestAt3104_block_13 : Interval leafTestAt3104 13 14 :=
  interval_of_check leafTestAt3104 13 1 (by decide +kernel)

theorem leafTestAt3104_block_14 : Interval leafTestAt3104 14 15 :=
  interval_of_check leafTestAt3104 14 1 (by decide +kernel)

theorem leafTestAt3104_block_15 : Interval leafTestAt3104 15 16 :=
  interval_of_check leafTestAt3104 15 1 (by decide +kernel)

theorem leafTestAt3104_block_16 : Interval leafTestAt3104 16 17 :=
  interval_of_check leafTestAt3104 16 1 (by decide +kernel)

theorem leafTestAt3104_block_17 : Interval leafTestAt3104 17 18 :=
  interval_of_check leafTestAt3104 17 1 (by decide +kernel)

theorem leafTestAt3104_block_18 : Interval leafTestAt3104 18 19 :=
  interval_of_check leafTestAt3104 18 1 (by decide +kernel)

theorem leafTestAt3104_block_19 : Interval leafTestAt3104 19 20 :=
  interval_of_check leafTestAt3104 19 1 (by decide +kernel)

theorem leafTestAt3104_block_20 : Interval leafTestAt3104 20 21 :=
  interval_of_check leafTestAt3104 20 1 (by decide +kernel)

theorem leafTestAt3104_block_21 : Interval leafTestAt3104 21 22 :=
  interval_of_check leafTestAt3104 21 1 (by decide +kernel)

theorem leafTestAt3104_block_22 : Interval leafTestAt3104 22 23 :=
  interval_of_check leafTestAt3104 22 1 (by decide +kernel)

theorem leafTestAt3104_block_23 : Interval leafTestAt3104 23 24 :=
  interval_of_check leafTestAt3104 23 1 (by decide +kernel)

theorem leafTestAt3104_block_24 : Interval leafTestAt3104 24 25 :=
  interval_of_check leafTestAt3104 24 1 (by decide +kernel)

theorem leafTestAt3104_block_25 : Interval leafTestAt3104 25 26 :=
  interval_of_check leafTestAt3104 25 1 (by decide +kernel)

theorem leafTestAt3104_block_26 : Interval leafTestAt3104 26 27 :=
  interval_of_check leafTestAt3104 26 1 (by decide +kernel)

theorem leafTestAt3104_block_27 : Interval leafTestAt3104 27 28 :=
  interval_of_check leafTestAt3104 27 1 (by decide +kernel)

theorem leafTestAt3104_block_28 : Interval leafTestAt3104 28 29 :=
  interval_of_check leafTestAt3104 28 1 (by decide +kernel)

theorem leafTestAt3104_block_29 : Interval leafTestAt3104 29 30 :=
  interval_of_check leafTestAt3104 29 1 (by decide +kernel)

theorem leafTestAt3104_block_30 : Interval leafTestAt3104 30 31 :=
  interval_of_check leafTestAt3104 30 1 (by decide +kernel)

theorem leafTestAt3104_block_31 : Interval leafTestAt3104 31 32 :=
  interval_of_check leafTestAt3104 31 1 (by decide +kernel)

theorem leafTestAt3104_complete : Interval leafTestAt3104 0 32 :=
  (interval_append leafTestAt3104 0 16 32
  (interval_append leafTestAt3104 0 8 16
  (interval_append leafTestAt3104 0 4 8
  (interval_append leafTestAt3104 0 2 4
  (interval_append leafTestAt3104 0 1 2
  leafTestAt3104_block_0
  leafTestAt3104_block_1)
  (interval_append leafTestAt3104 2 3 4
  leafTestAt3104_block_2
  leafTestAt3104_block_3))
  (interval_append leafTestAt3104 4 6 8
  (interval_append leafTestAt3104 4 5 6
  leafTestAt3104_block_4
  leafTestAt3104_block_5)
  (interval_append leafTestAt3104 6 7 8
  leafTestAt3104_block_6
  leafTestAt3104_block_7)))
  (interval_append leafTestAt3104 8 12 16
  (interval_append leafTestAt3104 8 10 12
  (interval_append leafTestAt3104 8 9 10
  leafTestAt3104_block_8
  leafTestAt3104_block_9)
  (interval_append leafTestAt3104 10 11 12
  leafTestAt3104_block_10
  leafTestAt3104_block_11))
  (interval_append leafTestAt3104 12 14 16
  (interval_append leafTestAt3104 12 13 14
  leafTestAt3104_block_12
  leafTestAt3104_block_13)
  (interval_append leafTestAt3104 14 15 16
  leafTestAt3104_block_14
  leafTestAt3104_block_15))))
  (interval_append leafTestAt3104 16 24 32
  (interval_append leafTestAt3104 16 20 24
  (interval_append leafTestAt3104 16 18 20
  (interval_append leafTestAt3104 16 17 18
  leafTestAt3104_block_16
  leafTestAt3104_block_17)
  (interval_append leafTestAt3104 18 19 20
  leafTestAt3104_block_18
  leafTestAt3104_block_19))
  (interval_append leafTestAt3104 20 22 24
  (interval_append leafTestAt3104 20 21 22
  leafTestAt3104_block_20
  leafTestAt3104_block_21)
  (interval_append leafTestAt3104 22 23 24
  leafTestAt3104_block_22
  leafTestAt3104_block_23)))
  (interval_append leafTestAt3104 24 28 32
  (interval_append leafTestAt3104 24 26 28
  (interval_append leafTestAt3104 24 25 26
  leafTestAt3104_block_24
  leafTestAt3104_block_25)
  (interval_append leafTestAt3104 26 27 28
  leafTestAt3104_block_26
  leafTestAt3104_block_27))
  (interval_append leafTestAt3104 28 30 32
  (interval_append leafTestAt3104 28 29 30
  leafTestAt3104_block_28
  leafTestAt3104_block_29)
  (interval_append leafTestAt3104 30 31 32
  leafTestAt3104_block_30
  leafTestAt3104_block_31)))))
theorem leafInterval3104 : Interval leafTest 3104 3136 := by
  intro i hlo hhi
  have h := leafTestAt3104_complete (i-3104) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt3104, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
