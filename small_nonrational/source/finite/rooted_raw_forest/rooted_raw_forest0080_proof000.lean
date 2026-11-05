module
prelude
public import RootedRawForest0080Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0080
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 32 :=
  interval_of_check test0 0 32 (by decide +kernel)

theorem test0_block_1 : Interval test0 32 64 :=
  interval_of_check test0 32 32 (by decide +kernel)

theorem test0_block_2 : Interval test0 64 96 :=
  interval_of_check test0 64 32 (by decide +kernel)

theorem test0_block_3 : Interval test0 96 128 :=
  interval_of_check test0 96 32 (by decide +kernel)

theorem test0_block_4 : Interval test0 128 160 :=
  interval_of_check test0 128 32 (by decide +kernel)

theorem test0_block_5 : Interval test0 160 192 :=
  interval_of_check test0 160 32 (by decide +kernel)

theorem test0_block_6 : Interval test0 192 199 :=
  interval_of_check test0 192 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 199 :=
  (interval_append test0 0 96 199
  (interval_append test0 0 32 96
  test0_block_0
  (interval_append test0 32 64 96
  test0_block_1
  test0_block_2))
  (interval_append test0 96 160 199
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)
  (interval_append test0 160 192 199
  test0_block_5
  test0_block_6)))
theorem nodeInterval0 : Interval nodeTest 0 199 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0080
