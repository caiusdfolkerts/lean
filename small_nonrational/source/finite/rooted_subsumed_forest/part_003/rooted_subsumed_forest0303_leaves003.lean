module
prelude
public import RootedSubsumedForest0303Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
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

theorem leafTestAt96_complete : Interval leafTestAt96 0 9 :=
  (interval_append leafTestAt96 0 4 9
  (interval_append leafTestAt96 0 2 4
  (interval_append leafTestAt96 0 1 2
  leafTestAt96_block_0
  leafTestAt96_block_1)
  (interval_append leafTestAt96 2 3 4
  leafTestAt96_block_2
  leafTestAt96_block_3))
  (interval_append leafTestAt96 4 6 9
  (interval_append leafTestAt96 4 5 6
  leafTestAt96_block_4
  leafTestAt96_block_5)
  (interval_append leafTestAt96 6 7 9
  leafTestAt96_block_6
  (interval_append leafTestAt96 7 8 9
  leafTestAt96_block_7
  leafTestAt96_block_8))))
theorem leafInterval96 : Interval leafTest 96 105 := by
  intro i hlo hhi
  have h := leafTestAt96_complete (i-96) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt96, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
