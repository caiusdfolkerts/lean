module
prelude
public import RootedSubsumedForest0284Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0284
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 16 :=
  interval_of_check test1920 0 16 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 16 32 :=
  interval_of_check test1920 16 16 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 32 48 :=
  interval_of_check test1920 32 16 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 48 64 :=
  interval_of_check test1920 48 16 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 64 80 :=
  interval_of_check test1920 64 16 (by decide +kernel)

theorem test1920_block_5 : Interval test1920 80 96 :=
  interval_of_check test1920 80 16 (by decide +kernel)

theorem test1920_block_6 : Interval test1920 96 112 :=
  interval_of_check test1920 96 16 (by decide +kernel)

theorem test1920_block_7 : Interval test1920 112 128 :=
  interval_of_check test1920 112 16 (by decide +kernel)

theorem test1920_block_8 : Interval test1920 128 144 :=
  interval_of_check test1920 128 16 (by decide +kernel)

theorem test1920_block_9 : Interval test1920 144 150 :=
  interval_of_check test1920 144 6 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 150 :=
  (interval_append test1920 0 80 150
  (interval_append test1920 0 32 80
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 80
  test1920_block_2
  (interval_append test1920 48 64 80
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 80 112 150
  (interval_append test1920 80 96 112
  test1920_block_5
  test1920_block_6)
  (interval_append test1920 112 128 150
  test1920_block_7
  (interval_append test1920 128 144 150
  test1920_block_8
  test1920_block_9))))
theorem nodeInterval1920 : Interval nodeTest 1920 2070 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0284
