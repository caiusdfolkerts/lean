module
prelude
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt416 (i : Nat) := leafTest (i+416)
theorem leafTestAt416_block_0 : Interval leafTestAt416 0 1 :=
  interval_of_check leafTestAt416 0 1 (by decide +kernel)

theorem leafTestAt416_block_1 : Interval leafTestAt416 1 2 :=
  interval_of_check leafTestAt416 1 1 (by decide +kernel)

theorem leafTestAt416_block_2 : Interval leafTestAt416 2 3 :=
  interval_of_check leafTestAt416 2 1 (by decide +kernel)

theorem leafTestAt416_block_3 : Interval leafTestAt416 3 4 :=
  interval_of_check leafTestAt416 3 1 (by decide +kernel)

theorem leafTestAt416_block_4 : Interval leafTestAt416 4 5 :=
  interval_of_check leafTestAt416 4 1 (by decide +kernel)

theorem leafTestAt416_block_5 : Interval leafTestAt416 5 6 :=
  interval_of_check leafTestAt416 5 1 (by decide +kernel)

theorem leafTestAt416_block_6 : Interval leafTestAt416 6 7 :=
  interval_of_check leafTestAt416 6 1 (by decide +kernel)

theorem leafTestAt416_block_7 : Interval leafTestAt416 7 8 :=
  interval_of_check leafTestAt416 7 1 (by decide +kernel)

theorem leafTestAt416_block_8 : Interval leafTestAt416 8 9 :=
  interval_of_check leafTestAt416 8 1 (by decide +kernel)

theorem leafTestAt416_block_9 : Interval leafTestAt416 9 10 :=
  interval_of_check leafTestAt416 9 1 (by decide +kernel)

theorem leafTestAt416_block_10 : Interval leafTestAt416 10 11 :=
  interval_of_check leafTestAt416 10 1 (by decide +kernel)

theorem leafTestAt416_block_11 : Interval leafTestAt416 11 12 :=
  interval_of_check leafTestAt416 11 1 (by decide +kernel)

theorem leafTestAt416_block_12 : Interval leafTestAt416 12 13 :=
  interval_of_check leafTestAt416 12 1 (by decide +kernel)

theorem leafTestAt416_block_13 : Interval leafTestAt416 13 14 :=
  interval_of_check leafTestAt416 13 1 (by decide +kernel)

theorem leafTestAt416_block_14 : Interval leafTestAt416 14 15 :=
  interval_of_check leafTestAt416 14 1 (by decide +kernel)

theorem leafTestAt416_block_15 : Interval leafTestAt416 15 16 :=
  interval_of_check leafTestAt416 15 1 (by decide +kernel)

theorem leafTestAt416_complete : Interval leafTestAt416 0 16 :=
  (interval_append leafTestAt416 0 8 16
  (interval_append leafTestAt416 0 4 8
  (interval_append leafTestAt416 0 2 4
  (interval_append leafTestAt416 0 1 2
  leafTestAt416_block_0
  leafTestAt416_block_1)
  (interval_append leafTestAt416 2 3 4
  leafTestAt416_block_2
  leafTestAt416_block_3))
  (interval_append leafTestAt416 4 6 8
  (interval_append leafTestAt416 4 5 6
  leafTestAt416_block_4
  leafTestAt416_block_5)
  (interval_append leafTestAt416 6 7 8
  leafTestAt416_block_6
  leafTestAt416_block_7)))
  (interval_append leafTestAt416 8 12 16
  (interval_append leafTestAt416 8 10 12
  (interval_append leafTestAt416 8 9 10
  leafTestAt416_block_8
  leafTestAt416_block_9)
  (interval_append leafTestAt416 10 11 12
  leafTestAt416_block_10
  leafTestAt416_block_11))
  (interval_append leafTestAt416 12 14 16
  (interval_append leafTestAt416 12 13 14
  leafTestAt416_block_12
  leafTestAt416_block_13)
  (interval_append leafTestAt416 14 15 16
  leafTestAt416_block_14
  leafTestAt416_block_15))))
theorem leafInterval416 : Interval leafTest 416 432 := by
  intro i hlo hhi
  have h := leafTestAt416_complete (i-416) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt416, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
