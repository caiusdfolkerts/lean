module
prelude
public import SmallSubsumedForest10Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test10240 (i : Nat) := nodeTest (i+10240)
theorem test10240_block_0 : Interval test10240 0 16 :=
  interval_of_check test10240 0 16 (by decide +kernel)

theorem test10240_block_1 : Interval test10240 16 32 :=
  interval_of_check test10240 16 16 (by decide +kernel)

theorem test10240_block_2 : Interval test10240 32 48 :=
  interval_of_check test10240 32 16 (by decide +kernel)

theorem test10240_block_3 : Interval test10240 48 64 :=
  interval_of_check test10240 48 16 (by decide +kernel)

theorem test10240_block_4 : Interval test10240 64 80 :=
  interval_of_check test10240 64 16 (by decide +kernel)

theorem test10240_block_5 : Interval test10240 80 96 :=
  interval_of_check test10240 80 16 (by decide +kernel)

theorem test10240_block_6 : Interval test10240 96 112 :=
  interval_of_check test10240 96 16 (by decide +kernel)

theorem test10240_block_7 : Interval test10240 112 128 :=
  interval_of_check test10240 112 16 (by decide +kernel)

theorem test10240_block_8 : Interval test10240 128 144 :=
  interval_of_check test10240 128 16 (by decide +kernel)

theorem test10240_block_9 : Interval test10240 144 160 :=
  interval_of_check test10240 144 16 (by decide +kernel)

theorem test10240_block_10 : Interval test10240 160 176 :=
  interval_of_check test10240 160 16 (by decide +kernel)

theorem test10240_block_11 : Interval test10240 176 192 :=
  interval_of_check test10240 176 16 (by decide +kernel)

theorem test10240_block_12 : Interval test10240 192 208 :=
  interval_of_check test10240 192 16 (by decide +kernel)

theorem test10240_block_13 : Interval test10240 208 224 :=
  interval_of_check test10240 208 16 (by decide +kernel)

theorem test10240_block_14 : Interval test10240 224 240 :=
  interval_of_check test10240 224 16 (by decide +kernel)

theorem test10240_block_15 : Interval test10240 240 256 :=
  interval_of_check test10240 240 16 (by decide +kernel)

theorem test10240_block_16 : Interval test10240 256 272 :=
  interval_of_check test10240 256 16 (by decide +kernel)

theorem test10240_block_17 : Interval test10240 272 288 :=
  interval_of_check test10240 272 16 (by decide +kernel)

theorem test10240_block_18 : Interval test10240 288 289 :=
  interval_of_check test10240 288 1 (by decide +kernel)

theorem test10240_complete : Interval test10240 0 289 :=
  (interval_append test10240 0 144 289
  (interval_append test10240 0 64 144
  (interval_append test10240 0 32 64
  (interval_append test10240 0 16 32
  test10240_block_0
  test10240_block_1)
  (interval_append test10240 32 48 64
  test10240_block_2
  test10240_block_3))
  (interval_append test10240 64 96 144
  (interval_append test10240 64 80 96
  test10240_block_4
  test10240_block_5)
  (interval_append test10240 96 112 144
  test10240_block_6
  (interval_append test10240 112 128 144
  test10240_block_7
  test10240_block_8))))
  (interval_append test10240 144 224 289
  (interval_append test10240 144 176 224
  (interval_append test10240 144 160 176
  test10240_block_9
  test10240_block_10)
  (interval_append test10240 176 192 224
  test10240_block_11
  (interval_append test10240 192 208 224
  test10240_block_12
  test10240_block_13)))
  (interval_append test10240 224 256 289
  (interval_append test10240 224 240 256
  test10240_block_14
  test10240_block_15)
  (interval_append test10240 256 272 289
  test10240_block_16
  (interval_append test10240 272 288 289
  test10240_block_17
  test10240_block_18)))))
theorem nodeInterval10240 : Interval nodeTest 10240 10529 := by
  intro i hlo hhi
  have h := test10240_complete (i-10240) (Nat.zero_le _) (by omega)
  simpa only [test10240, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest10
