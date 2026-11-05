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
def leafTestAt224 (i : Nat) := leafTest (i+224)
theorem leafTestAt224_block_0 : Interval leafTestAt224 0 1 :=
  interval_of_check leafTestAt224 0 1 (by decide +kernel)

theorem leafTestAt224_block_1 : Interval leafTestAt224 1 2 :=
  interval_of_check leafTestAt224 1 1 (by decide +kernel)

theorem leafTestAt224_block_2 : Interval leafTestAt224 2 3 :=
  interval_of_check leafTestAt224 2 1 (by decide +kernel)

theorem leafTestAt224_block_3 : Interval leafTestAt224 3 4 :=
  interval_of_check leafTestAt224 3 1 (by decide +kernel)

theorem leafTestAt224_block_4 : Interval leafTestAt224 4 5 :=
  interval_of_check leafTestAt224 4 1 (by decide +kernel)

theorem leafTestAt224_block_5 : Interval leafTestAt224 5 6 :=
  interval_of_check leafTestAt224 5 1 (by decide +kernel)

theorem leafTestAt224_block_6 : Interval leafTestAt224 6 7 :=
  interval_of_check leafTestAt224 6 1 (by decide +kernel)

theorem leafTestAt224_block_7 : Interval leafTestAt224 7 8 :=
  interval_of_check leafTestAt224 7 1 (by decide +kernel)

theorem leafTestAt224_block_8 : Interval leafTestAt224 8 9 :=
  interval_of_check leafTestAt224 8 1 (by decide +kernel)

theorem leafTestAt224_block_9 : Interval leafTestAt224 9 10 :=
  interval_of_check leafTestAt224 9 1 (by decide +kernel)

theorem leafTestAt224_block_10 : Interval leafTestAt224 10 11 :=
  interval_of_check leafTestAt224 10 1 (by decide +kernel)

theorem leafTestAt224_block_11 : Interval leafTestAt224 11 12 :=
  interval_of_check leafTestAt224 11 1 (by decide +kernel)

theorem leafTestAt224_block_12 : Interval leafTestAt224 12 13 :=
  interval_of_check leafTestAt224 12 1 (by decide +kernel)

theorem leafTestAt224_block_13 : Interval leafTestAt224 13 14 :=
  interval_of_check leafTestAt224 13 1 (by decide +kernel)

theorem leafTestAt224_block_14 : Interval leafTestAt224 14 15 :=
  interval_of_check leafTestAt224 14 1 (by decide +kernel)

theorem leafTestAt224_block_15 : Interval leafTestAt224 15 16 :=
  interval_of_check leafTestAt224 15 1 (by decide +kernel)

theorem leafTestAt224_block_16 : Interval leafTestAt224 16 17 :=
  interval_of_check leafTestAt224 16 1 (by decide +kernel)

theorem leafTestAt224_block_17 : Interval leafTestAt224 17 18 :=
  interval_of_check leafTestAt224 17 1 (by decide +kernel)

theorem leafTestAt224_block_18 : Interval leafTestAt224 18 19 :=
  interval_of_check leafTestAt224 18 1 (by decide +kernel)

theorem leafTestAt224_block_19 : Interval leafTestAt224 19 20 :=
  interval_of_check leafTestAt224 19 1 (by decide +kernel)

theorem leafTestAt224_block_20 : Interval leafTestAt224 20 21 :=
  interval_of_check leafTestAt224 20 1 (by decide +kernel)

theorem leafTestAt224_block_21 : Interval leafTestAt224 21 22 :=
  interval_of_check leafTestAt224 21 1 (by decide +kernel)

theorem leafTestAt224_block_22 : Interval leafTestAt224 22 23 :=
  interval_of_check leafTestAt224 22 1 (by decide +kernel)

theorem leafTestAt224_block_23 : Interval leafTestAt224 23 24 :=
  interval_of_check leafTestAt224 23 1 (by decide +kernel)

theorem leafTestAt224_block_24 : Interval leafTestAt224 24 25 :=
  interval_of_check leafTestAt224 24 1 (by decide +kernel)

theorem leafTestAt224_block_25 : Interval leafTestAt224 25 26 :=
  interval_of_check leafTestAt224 25 1 (by decide +kernel)

theorem leafTestAt224_block_26 : Interval leafTestAt224 26 27 :=
  interval_of_check leafTestAt224 26 1 (by decide +kernel)

theorem leafTestAt224_block_27 : Interval leafTestAt224 27 28 :=
  interval_of_check leafTestAt224 27 1 (by decide +kernel)

theorem leafTestAt224_block_28 : Interval leafTestAt224 28 29 :=
  interval_of_check leafTestAt224 28 1 (by decide +kernel)

theorem leafTestAt224_block_29 : Interval leafTestAt224 29 30 :=
  interval_of_check leafTestAt224 29 1 (by decide +kernel)

theorem leafTestAt224_block_30 : Interval leafTestAt224 30 31 :=
  interval_of_check leafTestAt224 30 1 (by decide +kernel)

theorem leafTestAt224_block_31 : Interval leafTestAt224 31 32 :=
  interval_of_check leafTestAt224 31 1 (by decide +kernel)

theorem leafTestAt224_complete : Interval leafTestAt224 0 32 :=
  (interval_append leafTestAt224 0 16 32
  (interval_append leafTestAt224 0 8 16
  (interval_append leafTestAt224 0 4 8
  (interval_append leafTestAt224 0 2 4
  (interval_append leafTestAt224 0 1 2
  leafTestAt224_block_0
  leafTestAt224_block_1)
  (interval_append leafTestAt224 2 3 4
  leafTestAt224_block_2
  leafTestAt224_block_3))
  (interval_append leafTestAt224 4 6 8
  (interval_append leafTestAt224 4 5 6
  leafTestAt224_block_4
  leafTestAt224_block_5)
  (interval_append leafTestAt224 6 7 8
  leafTestAt224_block_6
  leafTestAt224_block_7)))
  (interval_append leafTestAt224 8 12 16
  (interval_append leafTestAt224 8 10 12
  (interval_append leafTestAt224 8 9 10
  leafTestAt224_block_8
  leafTestAt224_block_9)
  (interval_append leafTestAt224 10 11 12
  leafTestAt224_block_10
  leafTestAt224_block_11))
  (interval_append leafTestAt224 12 14 16
  (interval_append leafTestAt224 12 13 14
  leafTestAt224_block_12
  leafTestAt224_block_13)
  (interval_append leafTestAt224 14 15 16
  leafTestAt224_block_14
  leafTestAt224_block_15))))
  (interval_append leafTestAt224 16 24 32
  (interval_append leafTestAt224 16 20 24
  (interval_append leafTestAt224 16 18 20
  (interval_append leafTestAt224 16 17 18
  leafTestAt224_block_16
  leafTestAt224_block_17)
  (interval_append leafTestAt224 18 19 20
  leafTestAt224_block_18
  leafTestAt224_block_19))
  (interval_append leafTestAt224 20 22 24
  (interval_append leafTestAt224 20 21 22
  leafTestAt224_block_20
  leafTestAt224_block_21)
  (interval_append leafTestAt224 22 23 24
  leafTestAt224_block_22
  leafTestAt224_block_23)))
  (interval_append leafTestAt224 24 28 32
  (interval_append leafTestAt224 24 26 28
  (interval_append leafTestAt224 24 25 26
  leafTestAt224_block_24
  leafTestAt224_block_25)
  (interval_append leafTestAt224 26 27 28
  leafTestAt224_block_26
  leafTestAt224_block_27))
  (interval_append leafTestAt224 28 30 32
  (interval_append leafTestAt224 28 29 30
  leafTestAt224_block_28
  leafTestAt224_block_29)
  (interval_append leafTestAt224 30 31 32
  leafTestAt224_block_30
  leafTestAt224_block_31)))))
theorem leafInterval224 : Interval leafTest 224 256 := by
  intro i hlo hhi
  have h := leafTestAt224_complete (i-224) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt224, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
