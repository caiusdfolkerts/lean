module
prelude
public import RootedSubsumedForest0283Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3840 (i : Nat) := nodeTest (i+3840)
theorem test3840_block_0 : Interval test3840 0 16 :=
  interval_of_check test3840 0 16 (by decide +kernel)

theorem test3840_block_1 : Interval test3840 16 32 :=
  interval_of_check test3840 16 16 (by decide +kernel)

theorem test3840_block_2 : Interval test3840 32 48 :=
  interval_of_check test3840 32 16 (by decide +kernel)

theorem test3840_block_3 : Interval test3840 48 64 :=
  interval_of_check test3840 48 16 (by decide +kernel)

theorem test3840_block_4 : Interval test3840 64 80 :=
  interval_of_check test3840 64 16 (by decide +kernel)

theorem test3840_block_5 : Interval test3840 80 96 :=
  interval_of_check test3840 80 16 (by decide +kernel)

theorem test3840_block_6 : Interval test3840 96 112 :=
  interval_of_check test3840 96 16 (by decide +kernel)

theorem test3840_block_7 : Interval test3840 112 128 :=
  interval_of_check test3840 112 16 (by decide +kernel)

theorem test3840_block_8 : Interval test3840 128 144 :=
  interval_of_check test3840 128 16 (by decide +kernel)

theorem test3840_block_9 : Interval test3840 144 160 :=
  interval_of_check test3840 144 16 (by decide +kernel)

theorem test3840_block_10 : Interval test3840 160 176 :=
  interval_of_check test3840 160 16 (by decide +kernel)

theorem test3840_block_11 : Interval test3840 176 185 :=
  interval_of_check test3840 176 9 (by decide +kernel)

theorem test3840_complete : Interval test3840 0 185 :=
  (interval_append test3840 0 96 185
  (interval_append test3840 0 48 96
  (interval_append test3840 0 16 48
  test3840_block_0
  (interval_append test3840 16 32 48
  test3840_block_1
  test3840_block_2))
  (interval_append test3840 48 64 96
  test3840_block_3
  (interval_append test3840 64 80 96
  test3840_block_4
  test3840_block_5)))
  (interval_append test3840 96 144 185
  (interval_append test3840 96 112 144
  test3840_block_6
  (interval_append test3840 112 128 144
  test3840_block_7
  test3840_block_8))
  (interval_append test3840 144 160 185
  test3840_block_9
  (interval_append test3840 160 176 185
  test3840_block_10
  test3840_block_11))))
theorem nodeInterval3840 : Interval nodeTest 3840 4025 := by
  intro i hlo hhi
  have h := test3840_complete (i-3840) (Nat.zero_le _) (by omega)
  simpa only [test3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0283
