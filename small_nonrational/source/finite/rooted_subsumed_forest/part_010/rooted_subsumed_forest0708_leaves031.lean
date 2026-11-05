module
prelude
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt992 (i : Nat) := leafTest (i+992)
theorem leafTestAt992_block_0 : Interval leafTestAt992 0 1 :=
  interval_of_check leafTestAt992 0 1 (by decide +kernel)

theorem leafTestAt992_block_1 : Interval leafTestAt992 1 2 :=
  interval_of_check leafTestAt992 1 1 (by decide +kernel)

theorem leafTestAt992_block_2 : Interval leafTestAt992 2 3 :=
  interval_of_check leafTestAt992 2 1 (by decide +kernel)

theorem leafTestAt992_block_3 : Interval leafTestAt992 3 4 :=
  interval_of_check leafTestAt992 3 1 (by decide +kernel)

theorem leafTestAt992_block_4 : Interval leafTestAt992 4 5 :=
  interval_of_check leafTestAt992 4 1 (by decide +kernel)

theorem leafTestAt992_block_5 : Interval leafTestAt992 5 6 :=
  interval_of_check leafTestAt992 5 1 (by decide +kernel)

theorem leafTestAt992_block_6 : Interval leafTestAt992 6 7 :=
  interval_of_check leafTestAt992 6 1 (by decide +kernel)

theorem leafTestAt992_block_7 : Interval leafTestAt992 7 8 :=
  interval_of_check leafTestAt992 7 1 (by decide +kernel)

theorem leafTestAt992_block_8 : Interval leafTestAt992 8 9 :=
  interval_of_check leafTestAt992 8 1 (by decide +kernel)

theorem leafTestAt992_block_9 : Interval leafTestAt992 9 10 :=
  interval_of_check leafTestAt992 9 1 (by decide +kernel)

theorem leafTestAt992_block_10 : Interval leafTestAt992 10 11 :=
  interval_of_check leafTestAt992 10 1 (by decide +kernel)

theorem leafTestAt992_block_11 : Interval leafTestAt992 11 12 :=
  interval_of_check leafTestAt992 11 1 (by decide +kernel)

theorem leafTestAt992_block_12 : Interval leafTestAt992 12 13 :=
  interval_of_check leafTestAt992 12 1 (by decide +kernel)

theorem leafTestAt992_block_13 : Interval leafTestAt992 13 14 :=
  interval_of_check leafTestAt992 13 1 (by decide +kernel)

theorem leafTestAt992_block_14 : Interval leafTestAt992 14 15 :=
  interval_of_check leafTestAt992 14 1 (by decide +kernel)

theorem leafTestAt992_block_15 : Interval leafTestAt992 15 16 :=
  interval_of_check leafTestAt992 15 1 (by decide +kernel)

theorem leafTestAt992_block_16 : Interval leafTestAt992 16 17 :=
  interval_of_check leafTestAt992 16 1 (by decide +kernel)

theorem leafTestAt992_block_17 : Interval leafTestAt992 17 18 :=
  interval_of_check leafTestAt992 17 1 (by decide +kernel)

theorem leafTestAt992_block_18 : Interval leafTestAt992 18 19 :=
  interval_of_check leafTestAt992 18 1 (by decide +kernel)

theorem leafTestAt992_block_19 : Interval leafTestAt992 19 20 :=
  interval_of_check leafTestAt992 19 1 (by decide +kernel)

theorem leafTestAt992_block_20 : Interval leafTestAt992 20 21 :=
  interval_of_check leafTestAt992 20 1 (by decide +kernel)

theorem leafTestAt992_block_21 : Interval leafTestAt992 21 22 :=
  interval_of_check leafTestAt992 21 1 (by decide +kernel)

theorem leafTestAt992_block_22 : Interval leafTestAt992 22 23 :=
  interval_of_check leafTestAt992 22 1 (by decide +kernel)

theorem leafTestAt992_block_23 : Interval leafTestAt992 23 24 :=
  interval_of_check leafTestAt992 23 1 (by decide +kernel)

theorem leafTestAt992_block_24 : Interval leafTestAt992 24 25 :=
  interval_of_check leafTestAt992 24 1 (by decide +kernel)

theorem leafTestAt992_block_25 : Interval leafTestAt992 25 26 :=
  interval_of_check leafTestAt992 25 1 (by decide +kernel)

theorem leafTestAt992_block_26 : Interval leafTestAt992 26 27 :=
  interval_of_check leafTestAt992 26 1 (by decide +kernel)

theorem leafTestAt992_block_27 : Interval leafTestAt992 27 28 :=
  interval_of_check leafTestAt992 27 1 (by decide +kernel)

theorem leafTestAt992_block_28 : Interval leafTestAt992 28 29 :=
  interval_of_check leafTestAt992 28 1 (by decide +kernel)

theorem leafTestAt992_block_29 : Interval leafTestAt992 29 30 :=
  interval_of_check leafTestAt992 29 1 (by decide +kernel)

theorem leafTestAt992_block_30 : Interval leafTestAt992 30 31 :=
  interval_of_check leafTestAt992 30 1 (by decide +kernel)

theorem leafTestAt992_block_31 : Interval leafTestAt992 31 32 :=
  interval_of_check leafTestAt992 31 1 (by decide +kernel)

theorem leafTestAt992_complete : Interval leafTestAt992 0 32 :=
  (interval_append leafTestAt992 0 16 32
  (interval_append leafTestAt992 0 8 16
  (interval_append leafTestAt992 0 4 8
  (interval_append leafTestAt992 0 2 4
  (interval_append leafTestAt992 0 1 2
  leafTestAt992_block_0
  leafTestAt992_block_1)
  (interval_append leafTestAt992 2 3 4
  leafTestAt992_block_2
  leafTestAt992_block_3))
  (interval_append leafTestAt992 4 6 8
  (interval_append leafTestAt992 4 5 6
  leafTestAt992_block_4
  leafTestAt992_block_5)
  (interval_append leafTestAt992 6 7 8
  leafTestAt992_block_6
  leafTestAt992_block_7)))
  (interval_append leafTestAt992 8 12 16
  (interval_append leafTestAt992 8 10 12
  (interval_append leafTestAt992 8 9 10
  leafTestAt992_block_8
  leafTestAt992_block_9)
  (interval_append leafTestAt992 10 11 12
  leafTestAt992_block_10
  leafTestAt992_block_11))
  (interval_append leafTestAt992 12 14 16
  (interval_append leafTestAt992 12 13 14
  leafTestAt992_block_12
  leafTestAt992_block_13)
  (interval_append leafTestAt992 14 15 16
  leafTestAt992_block_14
  leafTestAt992_block_15))))
  (interval_append leafTestAt992 16 24 32
  (interval_append leafTestAt992 16 20 24
  (interval_append leafTestAt992 16 18 20
  (interval_append leafTestAt992 16 17 18
  leafTestAt992_block_16
  leafTestAt992_block_17)
  (interval_append leafTestAt992 18 19 20
  leafTestAt992_block_18
  leafTestAt992_block_19))
  (interval_append leafTestAt992 20 22 24
  (interval_append leafTestAt992 20 21 22
  leafTestAt992_block_20
  leafTestAt992_block_21)
  (interval_append leafTestAt992 22 23 24
  leafTestAt992_block_22
  leafTestAt992_block_23)))
  (interval_append leafTestAt992 24 28 32
  (interval_append leafTestAt992 24 26 28
  (interval_append leafTestAt992 24 25 26
  leafTestAt992_block_24
  leafTestAt992_block_25)
  (interval_append leafTestAt992 26 27 28
  leafTestAt992_block_26
  leafTestAt992_block_27))
  (interval_append leafTestAt992 28 30 32
  (interval_append leafTestAt992 28 29 30
  leafTestAt992_block_28
  leafTestAt992_block_29)
  (interval_append leafTestAt992 30 31 32
  leafTestAt992_block_30
  leafTestAt992_block_31)))))
theorem leafInterval992 : Interval leafTest 992 1024 := by
  intro i hlo hhi
  have h := leafTestAt992_complete (i-992) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt992, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
