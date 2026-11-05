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
def leafTestAt864 (i : Nat) := leafTest (i+864)
theorem leafTestAt864_block_0 : Interval leafTestAt864 0 1 :=
  interval_of_check leafTestAt864 0 1 (by decide +kernel)

theorem leafTestAt864_block_1 : Interval leafTestAt864 1 2 :=
  interval_of_check leafTestAt864 1 1 (by decide +kernel)

theorem leafTestAt864_block_2 : Interval leafTestAt864 2 3 :=
  interval_of_check leafTestAt864 2 1 (by decide +kernel)

theorem leafTestAt864_block_3 : Interval leafTestAt864 3 4 :=
  interval_of_check leafTestAt864 3 1 (by decide +kernel)

theorem leafTestAt864_block_4 : Interval leafTestAt864 4 5 :=
  interval_of_check leafTestAt864 4 1 (by decide +kernel)

theorem leafTestAt864_block_5 : Interval leafTestAt864 5 6 :=
  interval_of_check leafTestAt864 5 1 (by decide +kernel)

theorem leafTestAt864_block_6 : Interval leafTestAt864 6 7 :=
  interval_of_check leafTestAt864 6 1 (by decide +kernel)

theorem leafTestAt864_block_7 : Interval leafTestAt864 7 8 :=
  interval_of_check leafTestAt864 7 1 (by decide +kernel)

theorem leafTestAt864_block_8 : Interval leafTestAt864 8 9 :=
  interval_of_check leafTestAt864 8 1 (by decide +kernel)

theorem leafTestAt864_block_9 : Interval leafTestAt864 9 10 :=
  interval_of_check leafTestAt864 9 1 (by decide +kernel)

theorem leafTestAt864_block_10 : Interval leafTestAt864 10 11 :=
  interval_of_check leafTestAt864 10 1 (by decide +kernel)

theorem leafTestAt864_block_11 : Interval leafTestAt864 11 12 :=
  interval_of_check leafTestAt864 11 1 (by decide +kernel)

theorem leafTestAt864_block_12 : Interval leafTestAt864 12 13 :=
  interval_of_check leafTestAt864 12 1 (by decide +kernel)

theorem leafTestAt864_block_13 : Interval leafTestAt864 13 14 :=
  interval_of_check leafTestAt864 13 1 (by decide +kernel)

theorem leafTestAt864_block_14 : Interval leafTestAt864 14 15 :=
  interval_of_check leafTestAt864 14 1 (by decide +kernel)

theorem leafTestAt864_block_15 : Interval leafTestAt864 15 16 :=
  interval_of_check leafTestAt864 15 1 (by decide +kernel)

theorem leafTestAt864_block_16 : Interval leafTestAt864 16 17 :=
  interval_of_check leafTestAt864 16 1 (by decide +kernel)

theorem leafTestAt864_block_17 : Interval leafTestAt864 17 18 :=
  interval_of_check leafTestAt864 17 1 (by decide +kernel)

theorem leafTestAt864_block_18 : Interval leafTestAt864 18 19 :=
  interval_of_check leafTestAt864 18 1 (by decide +kernel)

theorem leafTestAt864_block_19 : Interval leafTestAt864 19 20 :=
  interval_of_check leafTestAt864 19 1 (by decide +kernel)

theorem leafTestAt864_block_20 : Interval leafTestAt864 20 21 :=
  interval_of_check leafTestAt864 20 1 (by decide +kernel)

theorem leafTestAt864_block_21 : Interval leafTestAt864 21 22 :=
  interval_of_check leafTestAt864 21 1 (by decide +kernel)

theorem leafTestAt864_block_22 : Interval leafTestAt864 22 23 :=
  interval_of_check leafTestAt864 22 1 (by decide +kernel)

theorem leafTestAt864_block_23 : Interval leafTestAt864 23 24 :=
  interval_of_check leafTestAt864 23 1 (by decide +kernel)

theorem leafTestAt864_block_24 : Interval leafTestAt864 24 25 :=
  interval_of_check leafTestAt864 24 1 (by decide +kernel)

theorem leafTestAt864_block_25 : Interval leafTestAt864 25 26 :=
  interval_of_check leafTestAt864 25 1 (by decide +kernel)

theorem leafTestAt864_block_26 : Interval leafTestAt864 26 27 :=
  interval_of_check leafTestAt864 26 1 (by decide +kernel)

theorem leafTestAt864_block_27 : Interval leafTestAt864 27 28 :=
  interval_of_check leafTestAt864 27 1 (by decide +kernel)

theorem leafTestAt864_block_28 : Interval leafTestAt864 28 29 :=
  interval_of_check leafTestAt864 28 1 (by decide +kernel)

theorem leafTestAt864_block_29 : Interval leafTestAt864 29 30 :=
  interval_of_check leafTestAt864 29 1 (by decide +kernel)

theorem leafTestAt864_block_30 : Interval leafTestAt864 30 31 :=
  interval_of_check leafTestAt864 30 1 (by decide +kernel)

theorem leafTestAt864_block_31 : Interval leafTestAt864 31 32 :=
  interval_of_check leafTestAt864 31 1 (by decide +kernel)

theorem leafTestAt864_complete : Interval leafTestAt864 0 32 :=
  (interval_append leafTestAt864 0 16 32
  (interval_append leafTestAt864 0 8 16
  (interval_append leafTestAt864 0 4 8
  (interval_append leafTestAt864 0 2 4
  (interval_append leafTestAt864 0 1 2
  leafTestAt864_block_0
  leafTestAt864_block_1)
  (interval_append leafTestAt864 2 3 4
  leafTestAt864_block_2
  leafTestAt864_block_3))
  (interval_append leafTestAt864 4 6 8
  (interval_append leafTestAt864 4 5 6
  leafTestAt864_block_4
  leafTestAt864_block_5)
  (interval_append leafTestAt864 6 7 8
  leafTestAt864_block_6
  leafTestAt864_block_7)))
  (interval_append leafTestAt864 8 12 16
  (interval_append leafTestAt864 8 10 12
  (interval_append leafTestAt864 8 9 10
  leafTestAt864_block_8
  leafTestAt864_block_9)
  (interval_append leafTestAt864 10 11 12
  leafTestAt864_block_10
  leafTestAt864_block_11))
  (interval_append leafTestAt864 12 14 16
  (interval_append leafTestAt864 12 13 14
  leafTestAt864_block_12
  leafTestAt864_block_13)
  (interval_append leafTestAt864 14 15 16
  leafTestAt864_block_14
  leafTestAt864_block_15))))
  (interval_append leafTestAt864 16 24 32
  (interval_append leafTestAt864 16 20 24
  (interval_append leafTestAt864 16 18 20
  (interval_append leafTestAt864 16 17 18
  leafTestAt864_block_16
  leafTestAt864_block_17)
  (interval_append leafTestAt864 18 19 20
  leafTestAt864_block_18
  leafTestAt864_block_19))
  (interval_append leafTestAt864 20 22 24
  (interval_append leafTestAt864 20 21 22
  leafTestAt864_block_20
  leafTestAt864_block_21)
  (interval_append leafTestAt864 22 23 24
  leafTestAt864_block_22
  leafTestAt864_block_23)))
  (interval_append leafTestAt864 24 28 32
  (interval_append leafTestAt864 24 26 28
  (interval_append leafTestAt864 24 25 26
  leafTestAt864_block_24
  leafTestAt864_block_25)
  (interval_append leafTestAt864 26 27 28
  leafTestAt864_block_26
  leafTestAt864_block_27))
  (interval_append leafTestAt864 28 30 32
  (interval_append leafTestAt864 28 29 30
  leafTestAt864_block_28
  leafTestAt864_block_29)
  (interval_append leafTestAt864 30 31 32
  leafTestAt864_block_30
  leafTestAt864_block_31)))))
theorem leafInterval864 : Interval leafTest 864 896 := by
  intro i hlo hhi
  have h := leafTestAt864_complete (i-864) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt864, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
