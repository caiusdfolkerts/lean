module
prelude
public import RootedSubsumedForest0306Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test11520 (i : Nat) := nodeTest (i+11520)
theorem test11520_block_0 : Interval test11520 0 16 :=
  interval_of_check test11520 0 16 (by decide +kernel)

theorem test11520_block_1 : Interval test11520 16 32 :=
  interval_of_check test11520 16 16 (by decide +kernel)

theorem test11520_block_2 : Interval test11520 32 48 :=
  interval_of_check test11520 32 16 (by decide +kernel)

theorem test11520_block_3 : Interval test11520 48 64 :=
  interval_of_check test11520 48 16 (by decide +kernel)

theorem test11520_block_4 : Interval test11520 64 80 :=
  interval_of_check test11520 64 16 (by decide +kernel)

theorem test11520_block_5 : Interval test11520 80 96 :=
  interval_of_check test11520 80 16 (by decide +kernel)

theorem test11520_block_6 : Interval test11520 96 112 :=
  interval_of_check test11520 96 16 (by decide +kernel)

theorem test11520_block_7 : Interval test11520 112 128 :=
  interval_of_check test11520 112 16 (by decide +kernel)

theorem test11520_block_8 : Interval test11520 128 144 :=
  interval_of_check test11520 128 16 (by decide +kernel)

theorem test11520_block_9 : Interval test11520 144 160 :=
  interval_of_check test11520 144 16 (by decide +kernel)

theorem test11520_block_10 : Interval test11520 160 176 :=
  interval_of_check test11520 160 16 (by decide +kernel)

theorem test11520_block_11 : Interval test11520 176 192 :=
  interval_of_check test11520 176 16 (by decide +kernel)

theorem test11520_block_12 : Interval test11520 192 199 :=
  interval_of_check test11520 192 7 (by decide +kernel)

theorem test11520_complete : Interval test11520 0 199 :=
  (interval_append test11520 0 96 199
  (interval_append test11520 0 48 96
  (interval_append test11520 0 16 48
  test11520_block_0
  (interval_append test11520 16 32 48
  test11520_block_1
  test11520_block_2))
  (interval_append test11520 48 64 96
  test11520_block_3
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)))
  (interval_append test11520 96 144 199
  (interval_append test11520 96 112 144
  test11520_block_6
  (interval_append test11520 112 128 144
  test11520_block_7
  test11520_block_8))
  (interval_append test11520 144 176 199
  (interval_append test11520 144 160 176
  test11520_block_9
  test11520_block_10)
  (interval_append test11520 176 192 199
  test11520_block_11
  test11520_block_12))))
theorem nodeInterval11520 : Interval nodeTest 11520 11719 := by
  intro i hlo hhi
  have h := test11520_complete (i-11520) (Nat.zero_le _) (by omega)
  simpa only [test11520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
