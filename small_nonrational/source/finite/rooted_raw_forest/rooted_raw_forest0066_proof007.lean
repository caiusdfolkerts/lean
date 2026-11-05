module
prelude
public import RootedRawForest0066Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test4480 (i : Nat) := nodeTest (i+4480)
theorem test4480_block_0 : Interval test4480 0 32 :=
  interval_of_check test4480 0 32 (by decide +kernel)

theorem test4480_block_1 : Interval test4480 32 64 :=
  interval_of_check test4480 32 32 (by decide +kernel)

theorem test4480_block_2 : Interval test4480 64 96 :=
  interval_of_check test4480 64 32 (by decide +kernel)

theorem test4480_block_3 : Interval test4480 96 128 :=
  interval_of_check test4480 96 32 (by decide +kernel)

theorem test4480_block_4 : Interval test4480 128 160 :=
  interval_of_check test4480 128 32 (by decide +kernel)

theorem test4480_block_5 : Interval test4480 160 192 :=
  interval_of_check test4480 160 32 (by decide +kernel)

theorem test4480_block_6 : Interval test4480 192 220 :=
  interval_of_check test4480 192 28 (by decide +kernel)

theorem test4480_complete : Interval test4480 0 220 :=
  (interval_append test4480 0 96 220
  (interval_append test4480 0 32 96
  test4480_block_0
  (interval_append test4480 32 64 96
  test4480_block_1
  test4480_block_2))
  (interval_append test4480 96 160 220
  (interval_append test4480 96 128 160
  test4480_block_3
  test4480_block_4)
  (interval_append test4480 160 192 220
  test4480_block_5
  test4480_block_6)))
theorem nodeInterval4480 : Interval nodeTest 4480 4700 := by
  intro i hlo hhi
  have h := test4480_complete (i-4480) (Nat.zero_le _) (by omega)
  simpa only [test4480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0066
