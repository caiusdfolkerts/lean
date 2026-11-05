module
prelude
public import RootedSubsumedForest0354Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test16000 (i : Nat) := nodeTest (i+16000)
theorem test16000_block_0 : Interval test16000 0 16 :=
  interval_of_check test16000 0 16 (by decide +kernel)

theorem test16000_block_1 : Interval test16000 16 32 :=
  interval_of_check test16000 16 16 (by decide +kernel)

theorem test16000_block_2 : Interval test16000 32 48 :=
  interval_of_check test16000 32 16 (by decide +kernel)

theorem test16000_block_3 : Interval test16000 48 64 :=
  interval_of_check test16000 48 16 (by decide +kernel)

theorem test16000_block_4 : Interval test16000 64 80 :=
  interval_of_check test16000 64 16 (by decide +kernel)

theorem test16000_block_5 : Interval test16000 80 96 :=
  interval_of_check test16000 80 16 (by decide +kernel)

theorem test16000_block_6 : Interval test16000 96 112 :=
  interval_of_check test16000 96 16 (by decide +kernel)

theorem test16000_block_7 : Interval test16000 112 128 :=
  interval_of_check test16000 112 16 (by decide +kernel)

theorem test16000_block_8 : Interval test16000 128 144 :=
  interval_of_check test16000 128 16 (by decide +kernel)

theorem test16000_block_9 : Interval test16000 144 160 :=
  interval_of_check test16000 144 16 (by decide +kernel)

theorem test16000_block_10 : Interval test16000 160 176 :=
  interval_of_check test16000 160 16 (by decide +kernel)

theorem test16000_block_11 : Interval test16000 176 186 :=
  interval_of_check test16000 176 10 (by decide +kernel)

theorem test16000_complete : Interval test16000 0 186 :=
  (interval_append test16000 0 96 186
  (interval_append test16000 0 48 96
  (interval_append test16000 0 16 48
  test16000_block_0
  (interval_append test16000 16 32 48
  test16000_block_1
  test16000_block_2))
  (interval_append test16000 48 64 96
  test16000_block_3
  (interval_append test16000 64 80 96
  test16000_block_4
  test16000_block_5)))
  (interval_append test16000 96 144 186
  (interval_append test16000 96 112 144
  test16000_block_6
  (interval_append test16000 112 128 144
  test16000_block_7
  test16000_block_8))
  (interval_append test16000 144 160 186
  test16000_block_9
  (interval_append test16000 160 176 186
  test16000_block_10
  test16000_block_11))))
theorem nodeInterval16000 : Interval nodeTest 16000 16186 := by
  intro i hlo hhi
  have h := test16000_complete (i-16000) (Nat.zero_le _) (by omega)
  simpa only [test16000, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
