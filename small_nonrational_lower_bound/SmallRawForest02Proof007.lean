module
prelude
public import SmallRawForest02Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallRawForest02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test4480 (i : Nat) := nodeTest (i+4480)
theorem test4480_block_0 : Interval test4480 0 32 :=
  interval_of_check test4480 0 32 (by decide +kernel)

theorem test4480_block_1 : Interval test4480 32 64 :=
  interval_of_check test4480 32 32 (by decide +kernel)

theorem test4480_block_2 : Interval test4480 64 96 :=
  interval_of_check test4480 64 32 (by decide +kernel)

theorem test4480_block_3 : Interval test4480 96 128 :=
  interval_of_check test4480 96 32 (by decide +kernel)

theorem test4480_block_4 : Interval test4480 128 160 :=
  interval_of_check test4480 128 32 (by decide +kernel)

theorem test4480_block_5 : Interval test4480 160 192 :=
  interval_of_check test4480 160 32 (by decide +kernel)

theorem test4480_block_6 : Interval test4480 192 224 :=
  interval_of_check test4480 192 32 (by decide +kernel)

theorem test4480_block_7 : Interval test4480 224 256 :=
  interval_of_check test4480 224 32 (by decide +kernel)

theorem test4480_block_8 : Interval test4480 256 288 :=
  interval_of_check test4480 256 32 (by decide +kernel)

theorem test4480_block_9 : Interval test4480 288 320 :=
  interval_of_check test4480 288 32 (by decide +kernel)

theorem test4480_block_10 : Interval test4480 320 352 :=
  interval_of_check test4480 320 32 (by decide +kernel)

theorem test4480_block_11 : Interval test4480 352 384 :=
  interval_of_check test4480 352 32 (by decide +kernel)

theorem test4480_block_12 : Interval test4480 384 416 :=
  interval_of_check test4480 384 32 (by decide +kernel)

theorem test4480_block_13 : Interval test4480 416 445 :=
  interval_of_check test4480 416 29 (by decide +kernel)

theorem test4480_complete : Interval test4480 0 445 :=
  (interval_append test4480 0 224 445
  (interval_append test4480 0 96 224
  (interval_append test4480 0 32 96
  test4480_block_0
  (interval_append test4480 32 64 96
  test4480_block_1
  test4480_block_2))
  (interval_append test4480 96 160 224
  (interval_append test4480 96 128 160
  test4480_block_3
  test4480_block_4)
  (interval_append test4480 160 192 224
  test4480_block_5
  test4480_block_6)))
  (interval_append test4480 224 320 445
  (interval_append test4480 224 256 320
  test4480_block_7
  (interval_append test4480 256 288 320
  test4480_block_8
  test4480_block_9))
  (interval_append test4480 320 384 445
  (interval_append test4480 320 352 384
  test4480_block_10
  test4480_block_11)
  (interval_append test4480 384 416 445
  test4480_block_12
  test4480_block_13))))
theorem nodeInterval4480 : Interval nodeTest 4480 4925 := by
  intro i hlo hhi
  have h := test4480_complete (i-4480) (Nat.zero_le _) (by omega)
  simpa only [test4480, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallRawForest02
