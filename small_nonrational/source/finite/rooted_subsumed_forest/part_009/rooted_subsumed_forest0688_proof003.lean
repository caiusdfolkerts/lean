module
prelude
public import RootedSubsumedForest0688Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 16 :=
  interval_of_check test1920 0 16 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 16 32 :=
  interval_of_check test1920 16 16 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 32 48 :=
  interval_of_check test1920 32 16 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 48 64 :=
  interval_of_check test1920 48 16 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 64 80 :=
  interval_of_check test1920 64 16 (by decide +kernel)

theorem test1920_block_5 : Interval test1920 80 96 :=
  interval_of_check test1920 80 16 (by decide +kernel)

theorem test1920_block_6 : Interval test1920 96 112 :=
  interval_of_check test1920 96 16 (by decide +kernel)

theorem test1920_block_7 : Interval test1920 112 128 :=
  interval_of_check test1920 112 16 (by decide +kernel)

theorem test1920_block_8 : Interval test1920 128 144 :=
  interval_of_check test1920 128 16 (by decide +kernel)

theorem test1920_block_9 : Interval test1920 144 160 :=
  interval_of_check test1920 144 16 (by decide +kernel)

theorem test1920_block_10 : Interval test1920 160 176 :=
  interval_of_check test1920 160 16 (by decide +kernel)

theorem test1920_block_11 : Interval test1920 176 192 :=
  interval_of_check test1920 176 16 (by decide +kernel)

theorem test1920_block_12 : Interval test1920 192 208 :=
  interval_of_check test1920 192 16 (by decide +kernel)

theorem test1920_block_13 : Interval test1920 208 224 :=
  interval_of_check test1920 208 16 (by decide +kernel)

theorem test1920_block_14 : Interval test1920 224 240 :=
  interval_of_check test1920 224 16 (by decide +kernel)

theorem test1920_block_15 : Interval test1920 240 256 :=
  interval_of_check test1920 240 16 (by decide +kernel)

theorem test1920_block_16 : Interval test1920 256 269 :=
  interval_of_check test1920 256 13 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 269 :=
  (interval_append test1920 0 128 269
  (interval_append test1920 0 64 128
  (interval_append test1920 0 32 64
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 64
  test1920_block_2
  test1920_block_3))
  (interval_append test1920 64 96 128
  (interval_append test1920 64 80 96
  test1920_block_4
  test1920_block_5)
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7)))
  (interval_append test1920 128 192 269
  (interval_append test1920 128 160 192
  (interval_append test1920 128 144 160
  test1920_block_8
  test1920_block_9)
  (interval_append test1920 160 176 192
  test1920_block_10
  test1920_block_11))
  (interval_append test1920 192 224 269
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13)
  (interval_append test1920 224 240 269
  test1920_block_14
  (interval_append test1920 240 256 269
  test1920_block_15
  test1920_block_16)))))
theorem nodeInterval1920 : Interval nodeTest 1920 2189 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
