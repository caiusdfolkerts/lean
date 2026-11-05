module
prelude
public import RootedSubsumedForest0305Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test9600 (i : Nat) := nodeTest (i+9600)
theorem test9600_block_0 : Interval test9600 0 16 :=
  interval_of_check test9600 0 16 (by decide +kernel)

theorem test9600_block_1 : Interval test9600 16 32 :=
  interval_of_check test9600 16 16 (by decide +kernel)

theorem test9600_block_2 : Interval test9600 32 48 :=
  interval_of_check test9600 32 16 (by decide +kernel)

theorem test9600_block_3 : Interval test9600 48 64 :=
  interval_of_check test9600 48 16 (by decide +kernel)

theorem test9600_block_4 : Interval test9600 64 80 :=
  interval_of_check test9600 64 16 (by decide +kernel)

theorem test9600_block_5 : Interval test9600 80 96 :=
  interval_of_check test9600 80 16 (by decide +kernel)

theorem test9600_block_6 : Interval test9600 96 112 :=
  interval_of_check test9600 96 16 (by decide +kernel)

theorem test9600_block_7 : Interval test9600 112 128 :=
  interval_of_check test9600 112 16 (by decide +kernel)

theorem test9600_block_8 : Interval test9600 128 144 :=
  interval_of_check test9600 128 16 (by decide +kernel)

theorem test9600_block_9 : Interval test9600 144 150 :=
  interval_of_check test9600 144 6 (by decide +kernel)

theorem test9600_complete : Interval test9600 0 150 :=
  (interval_append test9600 0 80 150
  (interval_append test9600 0 32 80
  (interval_append test9600 0 16 32
  test9600_block_0
  test9600_block_1)
  (interval_append test9600 32 48 80
  test9600_block_2
  (interval_append test9600 48 64 80
  test9600_block_3
  test9600_block_4)))
  (interval_append test9600 80 112 150
  (interval_append test9600 80 96 112
  test9600_block_5
  test9600_block_6)
  (interval_append test9600 112 128 150
  test9600_block_7
  (interval_append test9600 128 144 150
  test9600_block_8
  test9600_block_9))))
theorem nodeInterval9600 : Interval nodeTest 9600 9750 := by
  intro i hlo hhi
  have h := test9600_complete (i-9600) (Nat.zero_le _) (by omega)
  simpa only [test9600, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
