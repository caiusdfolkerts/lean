module
prelude
public import RootedSubsumedForest0278Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0278
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test4480 (i : Nat) := nodeTest (i+4480)
theorem test4480_block_0 : Interval test4480 0 16 :=
  interval_of_check test4480 0 16 (by decide +kernel)

theorem test4480_block_1 : Interval test4480 16 32 :=
  interval_of_check test4480 16 16 (by decide +kernel)

theorem test4480_block_2 : Interval test4480 32 48 :=
  interval_of_check test4480 32 16 (by decide +kernel)

theorem test4480_block_3 : Interval test4480 48 64 :=
  interval_of_check test4480 48 16 (by decide +kernel)

theorem test4480_block_4 : Interval test4480 64 80 :=
  interval_of_check test4480 64 16 (by decide +kernel)

theorem test4480_block_5 : Interval test4480 80 96 :=
  interval_of_check test4480 80 16 (by decide +kernel)

theorem test4480_block_6 : Interval test4480 96 112 :=
  interval_of_check test4480 96 16 (by decide +kernel)

theorem test4480_block_7 : Interval test4480 112 128 :=
  interval_of_check test4480 112 16 (by decide +kernel)

theorem test4480_block_8 : Interval test4480 128 144 :=
  interval_of_check test4480 128 16 (by decide +kernel)

theorem test4480_block_9 : Interval test4480 144 160 :=
  interval_of_check test4480 144 16 (by decide +kernel)

theorem test4480_block_10 : Interval test4480 160 176 :=
  interval_of_check test4480 160 16 (by decide +kernel)

theorem test4480_block_11 : Interval test4480 176 192 :=
  interval_of_check test4480 176 16 (by decide +kernel)

theorem test4480_block_12 : Interval test4480 192 208 :=
  interval_of_check test4480 192 16 (by decide +kernel)

theorem test4480_block_13 : Interval test4480 208 224 :=
  interval_of_check test4480 208 16 (by decide +kernel)

theorem test4480_block_14 : Interval test4480 224 240 :=
  interval_of_check test4480 224 16 (by decide +kernel)

theorem test4480_block_15 : Interval test4480 240 248 :=
  interval_of_check test4480 240 8 (by decide +kernel)

theorem test4480_complete : Interval test4480 0 248 :=
  (interval_append test4480 0 128 248
  (interval_append test4480 0 64 128
  (interval_append test4480 0 32 64
  (interval_append test4480 0 16 32
  test4480_block_0
  test4480_block_1)
  (interval_append test4480 32 48 64
  test4480_block_2
  test4480_block_3))
  (interval_append test4480 64 96 128
  (interval_append test4480 64 80 96
  test4480_block_4
  test4480_block_5)
  (interval_append test4480 96 112 128
  test4480_block_6
  test4480_block_7)))
  (interval_append test4480 128 192 248
  (interval_append test4480 128 160 192
  (interval_append test4480 128 144 160
  test4480_block_8
  test4480_block_9)
  (interval_append test4480 160 176 192
  test4480_block_10
  test4480_block_11))
  (interval_append test4480 192 224 248
  (interval_append test4480 192 208 224
  test4480_block_12
  test4480_block_13)
  (interval_append test4480 224 240 248
  test4480_block_14
  test4480_block_15))))
theorem nodeInterval4480 : Interval nodeTest 4480 4728 := by
  intro i hlo hhi
  have h := test4480_complete (i-4480) (Nat.zero_le _) (by omega)
  simpa only [test4480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0278
