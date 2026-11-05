module
prelude
public import RootedRawForest0085Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0085
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1280 (i : Nat) := nodeTest (i+1280)
theorem test1280_block_0 : Interval test1280 0 32 :=
  interval_of_check test1280 0 32 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 32 64 :=
  interval_of_check test1280 32 32 (by decide +kernel)

theorem test1280_block_2 : Interval test1280 64 96 :=
  interval_of_check test1280 64 32 (by decide +kernel)

theorem test1280_block_3 : Interval test1280 96 128 :=
  interval_of_check test1280 96 32 (by decide +kernel)

theorem test1280_block_4 : Interval test1280 128 160 :=
  interval_of_check test1280 128 32 (by decide +kernel)

theorem test1280_block_5 : Interval test1280 160 192 :=
  interval_of_check test1280 160 32 (by decide +kernel)

theorem test1280_block_6 : Interval test1280 192 224 :=
  interval_of_check test1280 192 32 (by decide +kernel)

theorem test1280_block_7 : Interval test1280 224 256 :=
  interval_of_check test1280 224 32 (by decide +kernel)

theorem test1280_block_8 : Interval test1280 256 288 :=
  interval_of_check test1280 256 32 (by decide +kernel)

theorem test1280_block_9 : Interval test1280 288 302 :=
  interval_of_check test1280 288 14 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 302 :=
  (interval_append test1280 0 160 302
  (interval_append test1280 0 64 160
  (interval_append test1280 0 32 64
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 64 96 160
  test1280_block_2
  (interval_append test1280 96 128 160
  test1280_block_3
  test1280_block_4)))
  (interval_append test1280 160 224 302
  (interval_append test1280 160 192 224
  test1280_block_5
  test1280_block_6)
  (interval_append test1280 224 256 302
  test1280_block_7
  (interval_append test1280 256 288 302
  test1280_block_8
  test1280_block_9))))
theorem nodeInterval1280 : Interval nodeTest 1280 1582 := by
  intro i hlo hhi
  have h := test1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0085
