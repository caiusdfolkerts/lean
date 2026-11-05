module
prelude
public import SmallSubsumedForest03Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test10240 (i : Nat) := nodeTest (i+10240)
theorem test10240_block_0 : Interval test10240 0 16 :=
  interval_of_check test10240 0 16 (by decide +kernel)

theorem test10240_block_1 : Interval test10240 16 32 :=
  interval_of_check test10240 16 16 (by decide +kernel)

theorem test10240_block_2 : Interval test10240 32 48 :=
  interval_of_check test10240 32 16 (by decide +kernel)

theorem test10240_block_3 : Interval test10240 48 64 :=
  interval_of_check test10240 48 16 (by decide +kernel)

theorem test10240_block_4 : Interval test10240 64 80 :=
  interval_of_check test10240 64 16 (by decide +kernel)

theorem test10240_block_5 : Interval test10240 80 96 :=
  interval_of_check test10240 80 16 (by decide +kernel)

theorem test10240_block_6 : Interval test10240 96 112 :=
  interval_of_check test10240 96 16 (by decide +kernel)

theorem test10240_block_7 : Interval test10240 112 128 :=
  interval_of_check test10240 112 16 (by decide +kernel)

theorem test10240_block_8 : Interval test10240 128 144 :=
  interval_of_check test10240 128 16 (by decide +kernel)

theorem test10240_block_9 : Interval test10240 144 160 :=
  interval_of_check test10240 144 16 (by decide +kernel)

theorem test10240_block_10 : Interval test10240 160 162 :=
  interval_of_check test10240 160 2 (by decide +kernel)

theorem test10240_complete : Interval test10240 0 162 :=
  (interval_append test10240 0 80 162
  (interval_append test10240 0 32 80
  (interval_append test10240 0 16 32
  test10240_block_0
  test10240_block_1)
  (interval_append test10240 32 48 80
  test10240_block_2
  (interval_append test10240 48 64 80
  test10240_block_3
  test10240_block_4)))
  (interval_append test10240 80 128 162
  (interval_append test10240 80 96 128
  test10240_block_5
  (interval_append test10240 96 112 128
  test10240_block_6
  test10240_block_7))
  (interval_append test10240 128 144 162
  test10240_block_8
  (interval_append test10240 144 160 162
  test10240_block_9
  test10240_block_10))))
theorem nodeInterval10240 : Interval nodeTest 10240 10402 := by
  intro i hlo hhi
  have h := test10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [test10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
