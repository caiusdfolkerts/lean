module
prelude
public import RootedSubsumedForest0301Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt96 (i : Nat) := leafTest (i+96)
theorem leafTestAt96_block_0 : Interval leafTestAt96 0 1 :=
  interval_of_check leafTestAt96 0 1 (by decide +kernel)

theorem leafTestAt96_block_1 : Interval leafTestAt96 1 2 :=
  interval_of_check leafTestAt96 1 1 (by decide +kernel)

theorem leafTestAt96_block_2 : Interval leafTestAt96 2 3 :=
  interval_of_check leafTestAt96 2 1 (by decide +kernel)

theorem leafTestAt96_block_3 : Interval leafTestAt96 3 4 :=
  interval_of_check leafTestAt96 3 1 (by decide +kernel)

theorem leafTestAt96_block_4 : Interval leafTestAt96 4 5 :=
  interval_of_check leafTestAt96 4 1 (by decide +kernel)

theorem leafTestAt96_block_5 : Interval leafTestAt96 5 6 :=
  interval_of_check leafTestAt96 5 1 (by decide +kernel)

theorem leafTestAt96_block_6 : Interval leafTestAt96 6 7 :=
  interval_of_check leafTestAt96 6 1 (by decide +kernel)

theorem leafTestAt96_block_7 : Interval leafTestAt96 7 8 :=
  interval_of_check leafTestAt96 7 1 (by decide +kernel)

theorem leafTestAt96_block_8 : Interval leafTestAt96 8 9 :=
  interval_of_check leafTestAt96 8 1 (by decide +kernel)

theorem leafTestAt96_block_9 : Interval leafTestAt96 9 10 :=
  interval_of_check leafTestAt96 9 1 (by decide +kernel)

theorem leafTestAt96_block_10 : Interval leafTestAt96 10 11 :=
  interval_of_check leafTestAt96 10 1 (by decide +kernel)

theorem leafTestAt96_block_11 : Interval leafTestAt96 11 12 :=
  interval_of_check leafTestAt96 11 1 (by decide +kernel)

theorem leafTestAt96_block_12 : Interval leafTestAt96 12 13 :=
  interval_of_check leafTestAt96 12 1 (by decide +kernel)

theorem leafTestAt96_block_13 : Interval leafTestAt96 13 14 :=
  interval_of_check leafTestAt96 13 1 (by decide +kernel)

theorem leafTestAt96_block_14 : Interval leafTestAt96 14 15 :=
  interval_of_check leafTestAt96 14 1 (by decide +kernel)

theorem leafTestAt96_block_15 : Interval leafTestAt96 15 16 :=
  interval_of_check leafTestAt96 15 1 (by decide +kernel)

theorem leafTestAt96_block_16 : Interval leafTestAt96 16 17 :=
  interval_of_check leafTestAt96 16 1 (by decide +kernel)

theorem leafTestAt96_block_17 : Interval leafTestAt96 17 18 :=
  interval_of_check leafTestAt96 17 1 (by decide +kernel)

theorem leafTestAt96_block_18 : Interval leafTestAt96 18 19 :=
  interval_of_check leafTestAt96 18 1 (by decide +kernel)

theorem leafTestAt96_block_19 : Interval leafTestAt96 19 20 :=
  interval_of_check leafTestAt96 19 1 (by decide +kernel)

theorem leafTestAt96_block_20 : Interval leafTestAt96 20 21 :=
  interval_of_check leafTestAt96 20 1 (by decide +kernel)

theorem leafTestAt96_block_21 : Interval leafTestAt96 21 22 :=
  interval_of_check leafTestAt96 21 1 (by decide +kernel)

theorem leafTestAt96_block_22 : Interval leafTestAt96 22 23 :=
  interval_of_check leafTestAt96 22 1 (by decide +kernel)

theorem leafTestAt96_block_23 : Interval leafTestAt96 23 24 :=
  interval_of_check leafTestAt96 23 1 (by decide +kernel)

theorem leafTestAt96_complete : Interval leafTestAt96 0 24 :=
  (interval_append leafTestAt96 0 12 24
  (interval_append leafTestAt96 0 6 12
  (interval_append leafTestAt96 0 3 6
  (interval_append leafTestAt96 0 1 3
  leafTestAt96_block_0
  (interval_append leafTestAt96 1 2 3
  leafTestAt96_block_1
  leafTestAt96_block_2))
  (interval_append leafTestAt96 3 4 6
  leafTestAt96_block_3
  (interval_append leafTestAt96 4 5 6
  leafTestAt96_block_4
  leafTestAt96_block_5)))
  (interval_append leafTestAt96 6 9 12
  (interval_append leafTestAt96 6 7 9
  leafTestAt96_block_6
  (interval_append leafTestAt96 7 8 9
  leafTestAt96_block_7
  leafTestAt96_block_8))
  (interval_append leafTestAt96 9 10 12
  leafTestAt96_block_9
  (interval_append leafTestAt96 10 11 12
  leafTestAt96_block_10
  leafTestAt96_block_11))))
  (interval_append leafTestAt96 12 18 24
  (interval_append leafTestAt96 12 15 18
  (interval_append leafTestAt96 12 13 15
  leafTestAt96_block_12
  (interval_append leafTestAt96 13 14 15
  leafTestAt96_block_13
  leafTestAt96_block_14))
  (interval_append leafTestAt96 15 16 18
  leafTestAt96_block_15
  (interval_append leafTestAt96 16 17 18
  leafTestAt96_block_16
  leafTestAt96_block_17)))
  (interval_append leafTestAt96 18 21 24
  (interval_append leafTestAt96 18 19 21
  leafTestAt96_block_18
  (interval_append leafTestAt96 19 20 21
  leafTestAt96_block_19
  leafTestAt96_block_20))
  (interval_append leafTestAt96 21 22 24
  leafTestAt96_block_21
  (interval_append leafTestAt96 22 23 24
  leafTestAt96_block_22
  leafTestAt96_block_23)))))
theorem leafInterval96 : Interval leafTest 96 120 := by
  intro i hlo hhi
  have h := leafTestAt96_complete (i-96) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt96, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
