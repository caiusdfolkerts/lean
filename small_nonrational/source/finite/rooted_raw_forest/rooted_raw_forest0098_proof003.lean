module
prelude
public import RootedRawForest0098Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0098
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 32 :=
  interval_of_check test1920 0 32 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 32 64 :=
  interval_of_check test1920 32 32 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 64 96 :=
  interval_of_check test1920 64 32 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 96 128 :=
  interval_of_check test1920 96 32 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 128 160 :=
  interval_of_check test1920 128 32 (by decide +kernel)

theorem test1920_block_5 : Interval test1920 160 192 :=
  interval_of_check test1920 160 32 (by decide +kernel)

theorem test1920_block_6 : Interval test1920 192 224 :=
  interval_of_check test1920 192 32 (by decide +kernel)

theorem test1920_block_7 : Interval test1920 224 256 :=
  interval_of_check test1920 224 32 (by decide +kernel)

theorem test1920_block_8 : Interval test1920 256 288 :=
  interval_of_check test1920 256 32 (by decide +kernel)

theorem test1920_block_9 : Interval test1920 288 289 :=
  interval_of_check test1920 288 1 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 289 :=
  (interval_append test1920 0 160 289
  (interval_append test1920 0 64 160
  (interval_append test1920 0 32 64
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 64 96 160
  test1920_block_2
  (interval_append test1920 96 128 160
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 160 224 289
  (interval_append test1920 160 192 224
  test1920_block_5
  test1920_block_6)
  (interval_append test1920 224 256 289
  test1920_block_7
  (interval_append test1920 256 288 289
  test1920_block_8
  test1920_block_9))))
theorem nodeInterval1920 : Interval nodeTest 1920 2209 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0098
