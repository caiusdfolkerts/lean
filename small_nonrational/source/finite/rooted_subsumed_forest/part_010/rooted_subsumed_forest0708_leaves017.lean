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
def leafTestAt544 (i : Nat) := leafTest (i+544)
theorem leafTestAt544_block_0 : Interval leafTestAt544 0 1 :=
  interval_of_check leafTestAt544 0 1 (by decide +kernel)

theorem leafTestAt544_block_1 : Interval leafTestAt544 1 2 :=
  interval_of_check leafTestAt544 1 1 (by decide +kernel)

theorem leafTestAt544_block_2 : Interval leafTestAt544 2 3 :=
  interval_of_check leafTestAt544 2 1 (by decide +kernel)

theorem leafTestAt544_block_3 : Interval leafTestAt544 3 4 :=
  interval_of_check leafTestAt544 3 1 (by decide +kernel)

theorem leafTestAt544_block_4 : Interval leafTestAt544 4 5 :=
  interval_of_check leafTestAt544 4 1 (by decide +kernel)

theorem leafTestAt544_block_5 : Interval leafTestAt544 5 6 :=
  interval_of_check leafTestAt544 5 1 (by decide +kernel)

theorem leafTestAt544_block_6 : Interval leafTestAt544 6 7 :=
  interval_of_check leafTestAt544 6 1 (by decide +kernel)

theorem leafTestAt544_block_7 : Interval leafTestAt544 7 8 :=
  interval_of_check leafTestAt544 7 1 (by decide +kernel)

theorem leafTestAt544_block_8 : Interval leafTestAt544 8 9 :=
  interval_of_check leafTestAt544 8 1 (by decide +kernel)

theorem leafTestAt544_block_9 : Interval leafTestAt544 9 10 :=
  interval_of_check leafTestAt544 9 1 (by decide +kernel)

theorem leafTestAt544_block_10 : Interval leafTestAt544 10 11 :=
  interval_of_check leafTestAt544 10 1 (by decide +kernel)

theorem leafTestAt544_block_11 : Interval leafTestAt544 11 12 :=
  interval_of_check leafTestAt544 11 1 (by decide +kernel)

theorem leafTestAt544_block_12 : Interval leafTestAt544 12 13 :=
  interval_of_check leafTestAt544 12 1 (by decide +kernel)

theorem leafTestAt544_block_13 : Interval leafTestAt544 13 14 :=
  interval_of_check leafTestAt544 13 1 (by decide +kernel)

theorem leafTestAt544_block_14 : Interval leafTestAt544 14 15 :=
  interval_of_check leafTestAt544 14 1 (by decide +kernel)

theorem leafTestAt544_block_15 : Interval leafTestAt544 15 16 :=
  interval_of_check leafTestAt544 15 1 (by decide +kernel)

theorem leafTestAt544_block_16 : Interval leafTestAt544 16 17 :=
  interval_of_check leafTestAt544 16 1 (by decide +kernel)

theorem leafTestAt544_block_17 : Interval leafTestAt544 17 18 :=
  interval_of_check leafTestAt544 17 1 (by decide +kernel)

theorem leafTestAt544_block_18 : Interval leafTestAt544 18 19 :=
  interval_of_check leafTestAt544 18 1 (by decide +kernel)

theorem leafTestAt544_block_19 : Interval leafTestAt544 19 20 :=
  interval_of_check leafTestAt544 19 1 (by decide +kernel)

theorem leafTestAt544_block_20 : Interval leafTestAt544 20 21 :=
  interval_of_check leafTestAt544 20 1 (by decide +kernel)

theorem leafTestAt544_block_21 : Interval leafTestAt544 21 22 :=
  interval_of_check leafTestAt544 21 1 (by decide +kernel)

theorem leafTestAt544_block_22 : Interval leafTestAt544 22 23 :=
  interval_of_check leafTestAt544 22 1 (by decide +kernel)

theorem leafTestAt544_block_23 : Interval leafTestAt544 23 24 :=
  interval_of_check leafTestAt544 23 1 (by decide +kernel)

theorem leafTestAt544_block_24 : Interval leafTestAt544 24 25 :=
  interval_of_check leafTestAt544 24 1 (by decide +kernel)

theorem leafTestAt544_block_25 : Interval leafTestAt544 25 26 :=
  interval_of_check leafTestAt544 25 1 (by decide +kernel)

theorem leafTestAt544_block_26 : Interval leafTestAt544 26 27 :=
  interval_of_check leafTestAt544 26 1 (by decide +kernel)

theorem leafTestAt544_block_27 : Interval leafTestAt544 27 28 :=
  interval_of_check leafTestAt544 27 1 (by decide +kernel)

theorem leafTestAt544_block_28 : Interval leafTestAt544 28 29 :=
  interval_of_check leafTestAt544 28 1 (by decide +kernel)

theorem leafTestAt544_block_29 : Interval leafTestAt544 29 30 :=
  interval_of_check leafTestAt544 29 1 (by decide +kernel)

theorem leafTestAt544_block_30 : Interval leafTestAt544 30 31 :=
  interval_of_check leafTestAt544 30 1 (by decide +kernel)

theorem leafTestAt544_block_31 : Interval leafTestAt544 31 32 :=
  interval_of_check leafTestAt544 31 1 (by decide +kernel)

theorem leafTestAt544_complete : Interval leafTestAt544 0 32 :=
  (interval_append leafTestAt544 0 16 32
  (interval_append leafTestAt544 0 8 16
  (interval_append leafTestAt544 0 4 8
  (interval_append leafTestAt544 0 2 4
  (interval_append leafTestAt544 0 1 2
  leafTestAt544_block_0
  leafTestAt544_block_1)
  (interval_append leafTestAt544 2 3 4
  leafTestAt544_block_2
  leafTestAt544_block_3))
  (interval_append leafTestAt544 4 6 8
  (interval_append leafTestAt544 4 5 6
  leafTestAt544_block_4
  leafTestAt544_block_5)
  (interval_append leafTestAt544 6 7 8
  leafTestAt544_block_6
  leafTestAt544_block_7)))
  (interval_append leafTestAt544 8 12 16
  (interval_append leafTestAt544 8 10 12
  (interval_append leafTestAt544 8 9 10
  leafTestAt544_block_8
  leafTestAt544_block_9)
  (interval_append leafTestAt544 10 11 12
  leafTestAt544_block_10
  leafTestAt544_block_11))
  (interval_append leafTestAt544 12 14 16
  (interval_append leafTestAt544 12 13 14
  leafTestAt544_block_12
  leafTestAt544_block_13)
  (interval_append leafTestAt544 14 15 16
  leafTestAt544_block_14
  leafTestAt544_block_15))))
  (interval_append leafTestAt544 16 24 32
  (interval_append leafTestAt544 16 20 24
  (interval_append leafTestAt544 16 18 20
  (interval_append leafTestAt544 16 17 18
  leafTestAt544_block_16
  leafTestAt544_block_17)
  (interval_append leafTestAt544 18 19 20
  leafTestAt544_block_18
  leafTestAt544_block_19))
  (interval_append leafTestAt544 20 22 24
  (interval_append leafTestAt544 20 21 22
  leafTestAt544_block_20
  leafTestAt544_block_21)
  (interval_append leafTestAt544 22 23 24
  leafTestAt544_block_22
  leafTestAt544_block_23)))
  (interval_append leafTestAt544 24 28 32
  (interval_append leafTestAt544 24 26 28
  (interval_append leafTestAt544 24 25 26
  leafTestAt544_block_24
  leafTestAt544_block_25)
  (interval_append leafTestAt544 26 27 28
  leafTestAt544_block_26
  leafTestAt544_block_27))
  (interval_append leafTestAt544 28 30 32
  (interval_append leafTestAt544 28 29 30
  leafTestAt544_block_28
  leafTestAt544_block_29)
  (interval_append leafTestAt544 30 31 32
  leafTestAt544_block_30
  leafTestAt544_block_31)))))
theorem leafInterval544 : Interval leafTest 544 576 := by
  intro i hlo hhi
  have h := leafTestAt544_complete (i-544) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt544, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
