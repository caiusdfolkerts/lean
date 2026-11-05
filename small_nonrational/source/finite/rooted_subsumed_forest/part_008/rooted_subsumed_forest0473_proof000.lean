module
prelude
public import RootedSubsumedForest0473Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0473
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_block_8 : Interval test0 128 144 :=
  interval_of_check test0 128 16 (by decide +kernel)

theorem test0_block_9 : Interval test0 144 153 :=
  interval_of_check test0 144 9 (by decide +kernel)

theorem test0_complete : Interval test0 0 153 :=
  (interval_append test0 0 80 153
  (interval_append test0 0 32 80
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 80
  test0_block_2
  (interval_append test0 48 64 80
  test0_block_3
  test0_block_4)))
  (interval_append test0 80 112 153
  (interval_append test0 80 96 112
  test0_block_5
  test0_block_6)
  (interval_append test0 112 128 153
  test0_block_7
  (interval_append test0 128 144 153
  test0_block_8
  test0_block_9))))
theorem nodeInterval0 : Interval nodeTest 0 153 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0473
