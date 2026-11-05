module
prelude
public import RootedSubsumedForest0864Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt32 (i : Nat) := leafTest (i+32)
theorem leafTestAt32_block_0 : Interval leafTestAt32 0 1 :=
  interval_of_check leafTestAt32 0 1 (by decide +kernel)

theorem leafTestAt32_block_1 : Interval leafTestAt32 1 2 :=
  interval_of_check leafTestAt32 1 1 (by decide +kernel)

theorem leafTestAt32_block_2 : Interval leafTestAt32 2 3 :=
  interval_of_check leafTestAt32 2 1 (by decide +kernel)

theorem leafTestAt32_block_3 : Interval leafTestAt32 3 4 :=
  interval_of_check leafTestAt32 3 1 (by decide +kernel)

theorem leafTestAt32_block_4 : Interval leafTestAt32 4 5 :=
  interval_of_check leafTestAt32 4 1 (by decide +kernel)

theorem leafTestAt32_block_5 : Interval leafTestAt32 5 6 :=
  interval_of_check leafTestAt32 5 1 (by decide +kernel)

theorem leafTestAt32_block_6 : Interval leafTestAt32 6 7 :=
  interval_of_check leafTestAt32 6 1 (by decide +kernel)

theorem leafTestAt32_block_7 : Interval leafTestAt32 7 8 :=
  interval_of_check leafTestAt32 7 1 (by decide +kernel)

theorem leafTestAt32_block_8 : Interval leafTestAt32 8 9 :=
  interval_of_check leafTestAt32 8 1 (by decide +kernel)

theorem leafTestAt32_complete : Interval leafTestAt32 0 9 :=
  (interval_append leafTestAt32 0 4 9
  (interval_append leafTestAt32 0 2 4
  (interval_append leafTestAt32 0 1 2
  leafTestAt32_block_0
  leafTestAt32_block_1)
  (interval_append leafTestAt32 2 3 4
  leafTestAt32_block_2
  leafTestAt32_block_3))
  (interval_append leafTestAt32 4 6 9
  (interval_append leafTestAt32 4 5 6
  leafTestAt32_block_4
  leafTestAt32_block_5)
  (interval_append leafTestAt32 6 7 9
  leafTestAt32_block_6
  (interval_append leafTestAt32 7 8 9
  leafTestAt32_block_7
  leafTestAt32_block_8))))
theorem leafInterval32 : Interval leafTest 32 41 := by
  intro i hlo hhi
  have h := leafTestAt32_complete (i-32) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt32, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0864
