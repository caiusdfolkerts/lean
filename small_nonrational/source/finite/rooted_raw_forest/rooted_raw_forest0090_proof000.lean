module
prelude
public import RootedRawForest0090Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0090
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

theorem test0_block_6 : Interval test0 192 224 :=
  interval_of_check test0 192 32 (by decide +kernel)

theorem test0_block_7 : Interval test0 224 256 :=
  interval_of_check test0 224 32 (by decide +kernel)

theorem test0_block_8 : Interval test0 256 288 :=
  interval_of_check test0 256 32 (by decide +kernel)

theorem test0_block_9 : Interval test0 288 313 :=
  interval_of_check test0 288 25 (by decide +kernel)

theorem test0_complete : Interval test0 0 313 :=
  (interval_append test0 0 160 313
  (interval_append test0 0 64 160
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 160
  test0_block_2
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)))
  (interval_append test0 160 224 313
  (interval_append test0 160 192 224
  test0_block_5
  test0_block_6)
  (interval_append test0 224 256 313
  test0_block_7
  (interval_append test0 256 288 313
  test0_block_8
  test0_block_9))))
theorem nodeInterval0 : Interval nodeTest 0 313 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0090
