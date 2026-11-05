module
prelude
public import RootedSubsumedForest0266Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0266
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_block_8 : Interval test0 128 144 :=
  interval_of_check test0 128 16 (by decide +kernel)

theorem test0_block_9 : Interval test0 144 160 :=
  interval_of_check test0 144 16 (by decide +kernel)

theorem test0_block_10 : Interval test0 160 176 :=
  interval_of_check test0 160 16 (by decide +kernel)

theorem test0_block_11 : Interval test0 176 192 :=
  interval_of_check test0 176 16 (by decide +kernel)

theorem test0_block_12 : Interval test0 192 208 :=
  interval_of_check test0 192 16 (by decide +kernel)

theorem test0_block_13 : Interval test0 208 224 :=
  interval_of_check test0 208 16 (by decide +kernel)

theorem test0_block_14 : Interval test0 224 240 :=
  interval_of_check test0 224 16 (by decide +kernel)

theorem test0_block_15 : Interval test0 240 256 :=
  interval_of_check test0 240 16 (by decide +kernel)

theorem test0_block_16 : Interval test0 256 272 :=
  interval_of_check test0 256 16 (by decide +kernel)

theorem test0_block_17 : Interval test0 272 288 :=
  interval_of_check test0 272 16 (by decide +kernel)

theorem test0_block_18 : Interval test0 288 302 :=
  interval_of_check test0 288 14 (by decide +kernel)

theorem test0_complete : Interval test0 0 302 :=
  (interval_append test0 0 144 302
  (interval_append test0 0 64 144
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 144
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 144
  test0_block_6
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8))))
  (interval_append test0 144 224 302
  (interval_append test0 144 176 224
  (interval_append test0 144 160 176
  test0_block_9
  test0_block_10)
  (interval_append test0 176 192 224
  test0_block_11
  (interval_append test0 192 208 224
  test0_block_12
  test0_block_13)))
  (interval_append test0 224 256 302
  (interval_append test0 224 240 256
  test0_block_14
  test0_block_15)
  (interval_append test0 256 272 302
  test0_block_16
  (interval_append test0 272 288 302
  test0_block_17
  test0_block_18)))))
theorem nodeInterval0 : Interval nodeTest 0 302 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0266
