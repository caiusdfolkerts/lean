module
prelude
public import RootedSubsumedForest0698Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0698
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test5120 (i : Nat) := nodeTest (i+5120)
theorem test5120_block_0 : Interval test5120 0 16 :=
  interval_of_check test5120 0 16 (by decide +kernel)

theorem test5120_block_1 : Interval test5120 16 32 :=
  interval_of_check test5120 16 16 (by decide +kernel)

theorem test5120_block_2 : Interval test5120 32 48 :=
  interval_of_check test5120 32 16 (by decide +kernel)

theorem test5120_block_3 : Interval test5120 48 64 :=
  interval_of_check test5120 48 16 (by decide +kernel)

theorem test5120_block_4 : Interval test5120 64 80 :=
  interval_of_check test5120 64 16 (by decide +kernel)

theorem test5120_block_5 : Interval test5120 80 96 :=
  interval_of_check test5120 80 16 (by decide +kernel)

theorem test5120_block_6 : Interval test5120 96 112 :=
  interval_of_check test5120 96 16 (by decide +kernel)

theorem test5120_block_7 : Interval test5120 112 128 :=
  interval_of_check test5120 112 16 (by decide +kernel)

theorem test5120_block_8 : Interval test5120 128 136 :=
  interval_of_check test5120 128 8 (by decide +kernel)

theorem test5120_complete : Interval test5120 0 136 :=
  (interval_append test5120 0 64 136
  (interval_append test5120 0 32 64
  (interval_append test5120 0 16 32
  test5120_block_0
  test5120_block_1)
  (interval_append test5120 32 48 64
  test5120_block_2
  test5120_block_3))
  (interval_append test5120 64 96 136
  (interval_append test5120 64 80 96
  test5120_block_4
  test5120_block_5)
  (interval_append test5120 96 112 136
  test5120_block_6
  (interval_append test5120 112 128 136
  test5120_block_7
  test5120_block_8))))
theorem nodeInterval5120 : Interval nodeTest 5120 5256 := by
  intro i hlo hhi
  have h := test5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [test5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0698
