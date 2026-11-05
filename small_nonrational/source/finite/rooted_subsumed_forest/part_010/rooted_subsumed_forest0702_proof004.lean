module
prelude
public import RootedSubsumedForest0702Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0702
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test2560 (i : Nat) := nodeTest (i+2560)
theorem test2560_block_0 : Interval test2560 0 16 :=
  interval_of_check test2560 0 16 (by decide +kernel)

theorem test2560_block_1 : Interval test2560 16 32 :=
  interval_of_check test2560 16 16 (by decide +kernel)

theorem test2560_block_2 : Interval test2560 32 48 :=
  interval_of_check test2560 32 16 (by decide +kernel)

theorem test2560_block_3 : Interval test2560 48 64 :=
  interval_of_check test2560 48 16 (by decide +kernel)

theorem test2560_block_4 : Interval test2560 64 80 :=
  interval_of_check test2560 64 16 (by decide +kernel)

theorem test2560_block_5 : Interval test2560 80 96 :=
  interval_of_check test2560 80 16 (by decide +kernel)

theorem test2560_block_6 : Interval test2560 96 112 :=
  interval_of_check test2560 96 16 (by decide +kernel)

theorem test2560_block_7 : Interval test2560 112 128 :=
  interval_of_check test2560 112 16 (by decide +kernel)

theorem test2560_block_8 : Interval test2560 128 144 :=
  interval_of_check test2560 128 16 (by decide +kernel)

theorem test2560_block_9 : Interval test2560 144 160 :=
  interval_of_check test2560 144 16 (by decide +kernel)

theorem test2560_block_10 : Interval test2560 160 176 :=
  interval_of_check test2560 160 16 (by decide +kernel)

theorem test2560_block_11 : Interval test2560 176 192 :=
  interval_of_check test2560 176 16 (by decide +kernel)

theorem test2560_block_12 : Interval test2560 192 208 :=
  interval_of_check test2560 192 16 (by decide +kernel)

theorem test2560_block_13 : Interval test2560 208 221 :=
  interval_of_check test2560 208 13 (by decide +kernel)

theorem test2560_complete : Interval test2560 0 221 :=
  (interval_append test2560 0 112 221
  (interval_append test2560 0 48 112
  (interval_append test2560 0 16 48
  test2560_block_0
  (interval_append test2560 16 32 48
  test2560_block_1
  test2560_block_2))
  (interval_append test2560 48 80 112
  (interval_append test2560 48 64 80
  test2560_block_3
  test2560_block_4)
  (interval_append test2560 80 96 112
  test2560_block_5
  test2560_block_6)))
  (interval_append test2560 112 160 221
  (interval_append test2560 112 128 160
  test2560_block_7
  (interval_append test2560 128 144 160
  test2560_block_8
  test2560_block_9))
  (interval_append test2560 160 192 221
  (interval_append test2560 160 176 192
  test2560_block_10
  test2560_block_11)
  (interval_append test2560 192 208 221
  test2560_block_12
  test2560_block_13))))
theorem nodeInterval2560 : Interval nodeTest 2560 2781 := by
  intro i hlo hhi
  have h := test2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [test2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0702
