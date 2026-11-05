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
def leafTestAt512 (i : Nat) := leafTest (i+512)
theorem leafTestAt512_block_0 : Interval leafTestAt512 0 1 :=
  interval_of_check leafTestAt512 0 1 (by decide +kernel)

theorem leafTestAt512_block_1 : Interval leafTestAt512 1 2 :=
  interval_of_check leafTestAt512 1 1 (by decide +kernel)

theorem leafTestAt512_block_2 : Interval leafTestAt512 2 3 :=
  interval_of_check leafTestAt512 2 1 (by decide +kernel)

theorem leafTestAt512_block_3 : Interval leafTestAt512 3 4 :=
  interval_of_check leafTestAt512 3 1 (by decide +kernel)

theorem leafTestAt512_block_4 : Interval leafTestAt512 4 5 :=
  interval_of_check leafTestAt512 4 1 (by decide +kernel)

theorem leafTestAt512_block_5 : Interval leafTestAt512 5 6 :=
  interval_of_check leafTestAt512 5 1 (by decide +kernel)

theorem leafTestAt512_block_6 : Interval leafTestAt512 6 7 :=
  interval_of_check leafTestAt512 6 1 (by decide +kernel)

theorem leafTestAt512_block_7 : Interval leafTestAt512 7 8 :=
  interval_of_check leafTestAt512 7 1 (by decide +kernel)

theorem leafTestAt512_block_8 : Interval leafTestAt512 8 9 :=
  interval_of_check leafTestAt512 8 1 (by decide +kernel)

theorem leafTestAt512_block_9 : Interval leafTestAt512 9 10 :=
  interval_of_check leafTestAt512 9 1 (by decide +kernel)

theorem leafTestAt512_block_10 : Interval leafTestAt512 10 11 :=
  interval_of_check leafTestAt512 10 1 (by decide +kernel)

theorem leafTestAt512_block_11 : Interval leafTestAt512 11 12 :=
  interval_of_check leafTestAt512 11 1 (by decide +kernel)

theorem leafTestAt512_block_12 : Interval leafTestAt512 12 13 :=
  interval_of_check leafTestAt512 12 1 (by decide +kernel)

theorem leafTestAt512_block_13 : Interval leafTestAt512 13 14 :=
  interval_of_check leafTestAt512 13 1 (by decide +kernel)

theorem leafTestAt512_block_14 : Interval leafTestAt512 14 15 :=
  interval_of_check leafTestAt512 14 1 (by decide +kernel)

theorem leafTestAt512_block_15 : Interval leafTestAt512 15 16 :=
  interval_of_check leafTestAt512 15 1 (by decide +kernel)

theorem leafTestAt512_block_16 : Interval leafTestAt512 16 17 :=
  interval_of_check leafTestAt512 16 1 (by decide +kernel)

theorem leafTestAt512_block_17 : Interval leafTestAt512 17 18 :=
  interval_of_check leafTestAt512 17 1 (by decide +kernel)

theorem leafTestAt512_block_18 : Interval leafTestAt512 18 19 :=
  interval_of_check leafTestAt512 18 1 (by decide +kernel)

theorem leafTestAt512_block_19 : Interval leafTestAt512 19 20 :=
  interval_of_check leafTestAt512 19 1 (by decide +kernel)

theorem leafTestAt512_block_20 : Interval leafTestAt512 20 21 :=
  interval_of_check leafTestAt512 20 1 (by decide +kernel)

theorem leafTestAt512_block_21 : Interval leafTestAt512 21 22 :=
  interval_of_check leafTestAt512 21 1 (by decide +kernel)

theorem leafTestAt512_block_22 : Interval leafTestAt512 22 23 :=
  interval_of_check leafTestAt512 22 1 (by decide +kernel)

theorem leafTestAt512_block_23 : Interval leafTestAt512 23 24 :=
  interval_of_check leafTestAt512 23 1 (by decide +kernel)

theorem leafTestAt512_block_24 : Interval leafTestAt512 24 25 :=
  interval_of_check leafTestAt512 24 1 (by decide +kernel)

theorem leafTestAt512_block_25 : Interval leafTestAt512 25 26 :=
  interval_of_check leafTestAt512 25 1 (by decide +kernel)

theorem leafTestAt512_block_26 : Interval leafTestAt512 26 27 :=
  interval_of_check leafTestAt512 26 1 (by decide +kernel)

theorem leafTestAt512_block_27 : Interval leafTestAt512 27 28 :=
  interval_of_check leafTestAt512 27 1 (by decide +kernel)

theorem leafTestAt512_block_28 : Interval leafTestAt512 28 29 :=
  interval_of_check leafTestAt512 28 1 (by decide +kernel)

theorem leafTestAt512_block_29 : Interval leafTestAt512 29 30 :=
  interval_of_check leafTestAt512 29 1 (by decide +kernel)

theorem leafTestAt512_block_30 : Interval leafTestAt512 30 31 :=
  interval_of_check leafTestAt512 30 1 (by decide +kernel)

theorem leafTestAt512_block_31 : Interval leafTestAt512 31 32 :=
  interval_of_check leafTestAt512 31 1 (by decide +kernel)

theorem leafTestAt512_complete : Interval leafTestAt512 0 32 :=
  (interval_append leafTestAt512 0 16 32
  (interval_append leafTestAt512 0 8 16
  (interval_append leafTestAt512 0 4 8
  (interval_append leafTestAt512 0 2 4
  (interval_append leafTestAt512 0 1 2
  leafTestAt512_block_0
  leafTestAt512_block_1)
  (interval_append leafTestAt512 2 3 4
  leafTestAt512_block_2
  leafTestAt512_block_3))
  (interval_append leafTestAt512 4 6 8
  (interval_append leafTestAt512 4 5 6
  leafTestAt512_block_4
  leafTestAt512_block_5)
  (interval_append leafTestAt512 6 7 8
  leafTestAt512_block_6
  leafTestAt512_block_7)))
  (interval_append leafTestAt512 8 12 16
  (interval_append leafTestAt512 8 10 12
  (interval_append leafTestAt512 8 9 10
  leafTestAt512_block_8
  leafTestAt512_block_9)
  (interval_append leafTestAt512 10 11 12
  leafTestAt512_block_10
  leafTestAt512_block_11))
  (interval_append leafTestAt512 12 14 16
  (interval_append leafTestAt512 12 13 14
  leafTestAt512_block_12
  leafTestAt512_block_13)
  (interval_append leafTestAt512 14 15 16
  leafTestAt512_block_14
  leafTestAt512_block_15))))
  (interval_append leafTestAt512 16 24 32
  (interval_append leafTestAt512 16 20 24
  (interval_append leafTestAt512 16 18 20
  (interval_append leafTestAt512 16 17 18
  leafTestAt512_block_16
  leafTestAt512_block_17)
  (interval_append leafTestAt512 18 19 20
  leafTestAt512_block_18
  leafTestAt512_block_19))
  (interval_append leafTestAt512 20 22 24
  (interval_append leafTestAt512 20 21 22
  leafTestAt512_block_20
  leafTestAt512_block_21)
  (interval_append leafTestAt512 22 23 24
  leafTestAt512_block_22
  leafTestAt512_block_23)))
  (interval_append leafTestAt512 24 28 32
  (interval_append leafTestAt512 24 26 28
  (interval_append leafTestAt512 24 25 26
  leafTestAt512_block_24
  leafTestAt512_block_25)
  (interval_append leafTestAt512 26 27 28
  leafTestAt512_block_26
  leafTestAt512_block_27))
  (interval_append leafTestAt512 28 30 32
  (interval_append leafTestAt512 28 29 30
  leafTestAt512_block_28
  leafTestAt512_block_29)
  (interval_append leafTestAt512 30 31 32
  leafTestAt512_block_30
  leafTestAt512_block_31)))))
theorem leafInterval512 : Interval leafTest 512 544 := by
  intro i hlo hhi
  have h := leafTestAt512_complete (i-512) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt512, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
