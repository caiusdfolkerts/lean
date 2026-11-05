module
prelude
public import RootedSubsumedForest0296Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0296
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test10880 (i : Nat) := nodeTest (i+10880)
theorem test10880_block_0 : Interval test10880 0 16 :=
  interval_of_check test10880 0 16 (by decide +kernel)

theorem test10880_block_1 : Interval test10880 16 32 :=
  interval_of_check test10880 16 16 (by decide +kernel)

theorem test10880_block_2 : Interval test10880 32 48 :=
  interval_of_check test10880 32 16 (by decide +kernel)

theorem test10880_block_3 : Interval test10880 48 64 :=
  interval_of_check test10880 48 16 (by decide +kernel)

theorem test10880_block_4 : Interval test10880 64 80 :=
  interval_of_check test10880 64 16 (by decide +kernel)

theorem test10880_block_5 : Interval test10880 80 96 :=
  interval_of_check test10880 80 16 (by decide +kernel)

theorem test10880_block_6 : Interval test10880 96 112 :=
  interval_of_check test10880 96 16 (by decide +kernel)

theorem test10880_block_7 : Interval test10880 112 128 :=
  interval_of_check test10880 112 16 (by decide +kernel)

theorem test10880_block_8 : Interval test10880 128 144 :=
  interval_of_check test10880 128 16 (by decide +kernel)

theorem test10880_block_9 : Interval test10880 144 160 :=
  interval_of_check test10880 144 16 (by decide +kernel)

theorem test10880_block_10 : Interval test10880 160 176 :=
  interval_of_check test10880 160 16 (by decide +kernel)

theorem test10880_block_11 : Interval test10880 176 192 :=
  interval_of_check test10880 176 16 (by decide +kernel)

theorem test10880_block_12 : Interval test10880 192 208 :=
  interval_of_check test10880 192 16 (by decide +kernel)

theorem test10880_block_13 : Interval test10880 208 224 :=
  interval_of_check test10880 208 16 (by decide +kernel)

theorem test10880_complete : Interval test10880 0 224 :=
  (interval_append test10880 0 112 224
  (interval_append test10880 0 48 112
  (interval_append test10880 0 16 48
  test10880_block_0
  (interval_append test10880 16 32 48
  test10880_block_1
  test10880_block_2))
  (interval_append test10880 48 80 112
  (interval_append test10880 48 64 80
  test10880_block_3
  test10880_block_4)
  (interval_append test10880 80 96 112
  test10880_block_5
  test10880_block_6)))
  (interval_append test10880 112 160 224
  (interval_append test10880 112 128 160
  test10880_block_7
  (interval_append test10880 128 144 160
  test10880_block_8
  test10880_block_9))
  (interval_append test10880 160 192 224
  (interval_append test10880 160 176 192
  test10880_block_10
  test10880_block_11)
  (interval_append test10880 192 208 224
  test10880_block_12
  test10880_block_13))))
theorem nodeInterval10880 : Interval nodeTest 10880 11104 := by
  intro i hlo hhi
  have h := test10880_complete (i-10880) (Nat.zero_le _) (by omega)
  simpa only [test10880, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0296
