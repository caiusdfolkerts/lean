module
prelude
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test60160 (i : Nat) := nodeTest (i+60160)
theorem test60160_block_0 : Interval test60160 0 16 :=
  interval_of_check test60160 0 16 (by decide +kernel)

theorem test60160_block_1 : Interval test60160 16 32 :=
  interval_of_check test60160 16 16 (by decide +kernel)

theorem test60160_block_2 : Interval test60160 32 48 :=
  interval_of_check test60160 32 16 (by decide +kernel)

theorem test60160_block_3 : Interval test60160 48 64 :=
  interval_of_check test60160 48 16 (by decide +kernel)

theorem test60160_block_4 : Interval test60160 64 80 :=
  interval_of_check test60160 64 16 (by decide +kernel)

theorem test60160_block_5 : Interval test60160 80 96 :=
  interval_of_check test60160 80 16 (by decide +kernel)

theorem test60160_block_6 : Interval test60160 96 112 :=
  interval_of_check test60160 96 16 (by decide +kernel)

theorem test60160_block_7 : Interval test60160 112 128 :=
  interval_of_check test60160 112 16 (by decide +kernel)

theorem test60160_block_8 : Interval test60160 128 144 :=
  interval_of_check test60160 128 16 (by decide +kernel)

theorem test60160_block_9 : Interval test60160 144 160 :=
  interval_of_check test60160 144 16 (by decide +kernel)

theorem test60160_block_10 : Interval test60160 160 176 :=
  interval_of_check test60160 160 16 (by decide +kernel)

theorem test60160_block_11 : Interval test60160 176 192 :=
  interval_of_check test60160 176 16 (by decide +kernel)

theorem test60160_block_12 : Interval test60160 192 206 :=
  interval_of_check test60160 192 14 (by decide +kernel)

theorem test60160_complete : Interval test60160 0 206 :=
  (interval_append test60160 0 96 206
  (interval_append test60160 0 48 96
  (interval_append test60160 0 16 48
  test60160_block_0
  (interval_append test60160 16 32 48
  test60160_block_1
  test60160_block_2))
  (interval_append test60160 48 64 96
  test60160_block_3
  (interval_append test60160 64 80 96
  test60160_block_4
  test60160_block_5)))
  (interval_append test60160 96 144 206
  (interval_append test60160 96 112 144
  test60160_block_6
  (interval_append test60160 112 128 144
  test60160_block_7
  test60160_block_8))
  (interval_append test60160 144 176 206
  (interval_append test60160 144 160 176
  test60160_block_9
  test60160_block_10)
  (interval_append test60160 176 192 206
  test60160_block_11
  test60160_block_12))))
theorem nodeInterval60160 : Interval nodeTest 60160 60366 := by
  intro i hlo hhi
  have h := test60160_complete (i-60160) (Nat.zero_le _) (by omega)
  simpa only [test60160, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
