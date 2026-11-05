module
prelude
public import RootedSubsumedForest0337Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test41600 (i : Nat) := nodeTest (i+41600)
theorem test41600_block_0 : Interval test41600 0 16 :=
  interval_of_check test41600 0 16 (by decide +kernel)

theorem test41600_block_1 : Interval test41600 16 32 :=
  interval_of_check test41600 16 16 (by decide +kernel)

theorem test41600_block_2 : Interval test41600 32 48 :=
  interval_of_check test41600 32 16 (by decide +kernel)

theorem test41600_block_3 : Interval test41600 48 64 :=
  interval_of_check test41600 48 16 (by decide +kernel)

theorem test41600_block_4 : Interval test41600 64 80 :=
  interval_of_check test41600 64 16 (by decide +kernel)

theorem test41600_block_5 : Interval test41600 80 96 :=
  interval_of_check test41600 80 16 (by decide +kernel)

theorem test41600_block_6 : Interval test41600 96 112 :=
  interval_of_check test41600 96 16 (by decide +kernel)

theorem test41600_block_7 : Interval test41600 112 128 :=
  interval_of_check test41600 112 16 (by decide +kernel)

theorem test41600_block_8 : Interval test41600 128 144 :=
  interval_of_check test41600 128 16 (by decide +kernel)

theorem test41600_block_9 : Interval test41600 144 160 :=
  interval_of_check test41600 144 16 (by decide +kernel)

theorem test41600_block_10 : Interval test41600 160 176 :=
  interval_of_check test41600 160 16 (by decide +kernel)

theorem test41600_block_11 : Interval test41600 176 192 :=
  interval_of_check test41600 176 16 (by decide +kernel)

theorem test41600_block_12 : Interval test41600 192 208 :=
  interval_of_check test41600 192 16 (by decide +kernel)

theorem test41600_block_13 : Interval test41600 208 224 :=
  interval_of_check test41600 208 16 (by decide +kernel)

theorem test41600_block_14 : Interval test41600 224 240 :=
  interval_of_check test41600 224 16 (by decide +kernel)

theorem test41600_block_15 : Interval test41600 240 256 :=
  interval_of_check test41600 240 16 (by decide +kernel)

theorem test41600_block_16 : Interval test41600 256 272 :=
  interval_of_check test41600 256 16 (by decide +kernel)

theorem test41600_block_17 : Interval test41600 272 288 :=
  interval_of_check test41600 272 16 (by decide +kernel)

theorem test41600_block_18 : Interval test41600 288 295 :=
  interval_of_check test41600 288 7 (by decide +kernel)

theorem test41600_complete : Interval test41600 0 295 :=
  (interval_append test41600 0 144 295
  (interval_append test41600 0 64 144
  (interval_append test41600 0 32 64
  (interval_append test41600 0 16 32
  test41600_block_0
  test41600_block_1)
  (interval_append test41600 32 48 64
  test41600_block_2
  test41600_block_3))
  (interval_append test41600 64 96 144
  (interval_append test41600 64 80 96
  test41600_block_4
  test41600_block_5)
  (interval_append test41600 96 112 144
  test41600_block_6
  (interval_append test41600 112 128 144
  test41600_block_7
  test41600_block_8))))
  (interval_append test41600 144 224 295
  (interval_append test41600 144 176 224
  (interval_append test41600 144 160 176
  test41600_block_9
  test41600_block_10)
  (interval_append test41600 176 192 224
  test41600_block_11
  (interval_append test41600 192 208 224
  test41600_block_12
  test41600_block_13)))
  (interval_append test41600 224 256 295
  (interval_append test41600 224 240 256
  test41600_block_14
  test41600_block_15)
  (interval_append test41600 256 272 295
  test41600_block_16
  (interval_append test41600 272 288 295
  test41600_block_17
  test41600_block_18)))))
theorem nodeInterval41600 : Interval nodeTest 41600 41895 := by
  intro i hlo hhi
  have h := test41600_complete (i-41600) (Nat.zero_le _) (by omega)
  simpa only [test41600, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
