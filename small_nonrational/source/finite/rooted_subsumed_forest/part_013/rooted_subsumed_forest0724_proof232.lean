module
prelude
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test148480 (i : Nat) := nodeTest (i+148480)
theorem test148480_block_0 : Interval test148480 0 16 :=
  interval_of_check test148480 0 16 (by decide +kernel)

theorem test148480_block_1 : Interval test148480 16 32 :=
  interval_of_check test148480 16 16 (by decide +kernel)

theorem test148480_block_2 : Interval test148480 32 48 :=
  interval_of_check test148480 32 16 (by decide +kernel)

theorem test148480_block_3 : Interval test148480 48 64 :=
  interval_of_check test148480 48 16 (by decide +kernel)

theorem test148480_block_4 : Interval test148480 64 80 :=
  interval_of_check test148480 64 16 (by decide +kernel)

theorem test148480_block_5 : Interval test148480 80 96 :=
  interval_of_check test148480 80 16 (by decide +kernel)

theorem test148480_block_6 : Interval test148480 96 112 :=
  interval_of_check test148480 96 16 (by decide +kernel)

theorem test148480_block_7 : Interval test148480 112 128 :=
  interval_of_check test148480 112 16 (by decide +kernel)

theorem test148480_block_8 : Interval test148480 128 144 :=
  interval_of_check test148480 128 16 (by decide +kernel)

theorem test148480_block_9 : Interval test148480 144 160 :=
  interval_of_check test148480 144 16 (by decide +kernel)

theorem test148480_block_10 : Interval test148480 160 176 :=
  interval_of_check test148480 160 16 (by decide +kernel)

theorem test148480_block_11 : Interval test148480 176 192 :=
  interval_of_check test148480 176 16 (by decide +kernel)

theorem test148480_block_12 : Interval test148480 192 208 :=
  interval_of_check test148480 192 16 (by decide +kernel)

theorem test148480_block_13 : Interval test148480 208 224 :=
  interval_of_check test148480 208 16 (by decide +kernel)

theorem test148480_block_14 : Interval test148480 224 240 :=
  interval_of_check test148480 224 16 (by decide +kernel)

theorem test148480_block_15 : Interval test148480 240 256 :=
  interval_of_check test148480 240 16 (by decide +kernel)

theorem test148480_block_16 : Interval test148480 256 266 :=
  interval_of_check test148480 256 10 (by decide +kernel)

theorem test148480_complete : Interval test148480 0 266 :=
  (interval_append test148480 0 128 266
  (interval_append test148480 0 64 128
  (interval_append test148480 0 32 64
  (interval_append test148480 0 16 32
  test148480_block_0
  test148480_block_1)
  (interval_append test148480 32 48 64
  test148480_block_2
  test148480_block_3))
  (interval_append test148480 64 96 128
  (interval_append test148480 64 80 96
  test148480_block_4
  test148480_block_5)
  (interval_append test148480 96 112 128
  test148480_block_6
  test148480_block_7)))
  (interval_append test148480 128 192 266
  (interval_append test148480 128 160 192
  (interval_append test148480 128 144 160
  test148480_block_8
  test148480_block_9)
  (interval_append test148480 160 176 192
  test148480_block_10
  test148480_block_11))
  (interval_append test148480 192 224 266
  (interval_append test148480 192 208 224
  test148480_block_12
  test148480_block_13)
  (interval_append test148480 224 240 266
  test148480_block_14
  (interval_append test148480 240 256 266
  test148480_block_15
  test148480_block_16)))))
theorem nodeInterval148480 : Interval nodeTest 148480 148746 := by
  intro i hlo hhi
  have h := test148480_complete (i-148480) (Nat.zero_le _) (by omega)
  simpa only [test148480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
