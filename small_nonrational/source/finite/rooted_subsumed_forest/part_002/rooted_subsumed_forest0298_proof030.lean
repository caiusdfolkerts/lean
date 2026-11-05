module
prelude
public import RootedSubsumedForest0298Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test19200 (i : Nat) := nodeTest (i+19200)
theorem test19200_block_0 : Interval test19200 0 16 :=
  interval_of_check test19200 0 16 (by decide +kernel)

theorem test19200_block_1 : Interval test19200 16 32 :=
  interval_of_check test19200 16 16 (by decide +kernel)

theorem test19200_block_2 : Interval test19200 32 48 :=
  interval_of_check test19200 32 16 (by decide +kernel)

theorem test19200_block_3 : Interval test19200 48 64 :=
  interval_of_check test19200 48 16 (by decide +kernel)

theorem test19200_block_4 : Interval test19200 64 80 :=
  interval_of_check test19200 64 16 (by decide +kernel)

theorem test19200_block_5 : Interval test19200 80 96 :=
  interval_of_check test19200 80 16 (by decide +kernel)

theorem test19200_block_6 : Interval test19200 96 112 :=
  interval_of_check test19200 96 16 (by decide +kernel)

theorem test19200_block_7 : Interval test19200 112 128 :=
  interval_of_check test19200 112 16 (by decide +kernel)

theorem test19200_block_8 : Interval test19200 128 144 :=
  interval_of_check test19200 128 16 (by decide +kernel)

theorem test19200_block_9 : Interval test19200 144 160 :=
  interval_of_check test19200 144 16 (by decide +kernel)

theorem test19200_block_10 : Interval test19200 160 176 :=
  interval_of_check test19200 160 16 (by decide +kernel)

theorem test19200_block_11 : Interval test19200 176 192 :=
  interval_of_check test19200 176 16 (by decide +kernel)

theorem test19200_block_12 : Interval test19200 192 208 :=
  interval_of_check test19200 192 16 (by decide +kernel)

theorem test19200_block_13 : Interval test19200 208 223 :=
  interval_of_check test19200 208 15 (by decide +kernel)

theorem test19200_complete : Interval test19200 0 223 :=
  (interval_append test19200 0 112 223
  (interval_append test19200 0 48 112
  (interval_append test19200 0 16 48
  test19200_block_0
  (interval_append test19200 16 32 48
  test19200_block_1
  test19200_block_2))
  (interval_append test19200 48 80 112
  (interval_append test19200 48 64 80
  test19200_block_3
  test19200_block_4)
  (interval_append test19200 80 96 112
  test19200_block_5
  test19200_block_6)))
  (interval_append test19200 112 160 223
  (interval_append test19200 112 128 160
  test19200_block_7
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9))
  (interval_append test19200 160 192 223
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11)
  (interval_append test19200 192 208 223
  test19200_block_12
  test19200_block_13))))
theorem nodeInterval19200 : Interval nodeTest 19200 19423 := by
  intro i hlo hhi
  have h := test19200_complete (i-19200) (Nat.zero_le _) (by omega)
  simpa only [test19200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0298
