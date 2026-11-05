module
prelude
public import RootedSubsumedForest0276Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0276
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1280 (i : Nat) := nodeTest (i+1280)
theorem test1280_block_0 : Interval test1280 0 16 :=
  interval_of_check test1280 0 16 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 16 32 :=
  interval_of_check test1280 16 16 (by decide +kernel)

theorem test1280_block_2 : Interval test1280 32 48 :=
  interval_of_check test1280 32 16 (by decide +kernel)

theorem test1280_block_3 : Interval test1280 48 64 :=
  interval_of_check test1280 48 16 (by decide +kernel)

theorem test1280_block_4 : Interval test1280 64 80 :=
  interval_of_check test1280 64 16 (by decide +kernel)

theorem test1280_block_5 : Interval test1280 80 96 :=
  interval_of_check test1280 80 16 (by decide +kernel)

theorem test1280_block_6 : Interval test1280 96 112 :=
  interval_of_check test1280 96 16 (by decide +kernel)

theorem test1280_block_7 : Interval test1280 112 128 :=
  interval_of_check test1280 112 16 (by decide +kernel)

theorem test1280_block_8 : Interval test1280 128 144 :=
  interval_of_check test1280 128 16 (by decide +kernel)

theorem test1280_block_9 : Interval test1280 144 160 :=
  interval_of_check test1280 144 16 (by decide +kernel)

theorem test1280_block_10 : Interval test1280 160 176 :=
  interval_of_check test1280 160 16 (by decide +kernel)

theorem test1280_block_11 : Interval test1280 176 192 :=
  interval_of_check test1280 176 16 (by decide +kernel)

theorem test1280_block_12 : Interval test1280 192 204 :=
  interval_of_check test1280 192 12 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 204 :=
  (interval_append test1280 0 96 204
  (interval_append test1280 0 48 96
  (interval_append test1280 0 16 48
  test1280_block_0
  (interval_append test1280 16 32 48
  test1280_block_1
  test1280_block_2))
  (interval_append test1280 48 64 96
  test1280_block_3
  (interval_append test1280 64 80 96
  test1280_block_4
  test1280_block_5)))
  (interval_append test1280 96 144 204
  (interval_append test1280 96 112 144
  test1280_block_6
  (interval_append test1280 112 128 144
  test1280_block_7
  test1280_block_8))
  (interval_append test1280 144 176 204
  (interval_append test1280 144 160 176
  test1280_block_9
  test1280_block_10)
  (interval_append test1280 176 192 204
  test1280_block_11
  test1280_block_12))))
theorem nodeInterval1280 : Interval nodeTest 1280 1484 := by
  intro i hlo hhi
  have h := test1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0276
