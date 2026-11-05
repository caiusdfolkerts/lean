module
prelude
public import RootedRawForest0064Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0064
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test640 (i : Nat) := nodeTest (i+640)
theorem test640_block_0 : Interval test640 0 32 :=
  interval_of_check test640 0 32 (by decide +kernel)

theorem test640_block_1 : Interval test640 32 64 :=
  interval_of_check test640 32 32 (by decide +kernel)

theorem test640_block_2 : Interval test640 64 96 :=
  interval_of_check test640 64 32 (by decide +kernel)

theorem test640_block_3 : Interval test640 96 128 :=
  interval_of_check test640 96 32 (by decide +kernel)

theorem test640_block_4 : Interval test640 128 160 :=
  interval_of_check test640 128 32 (by decide +kernel)

theorem test640_block_5 : Interval test640 160 192 :=
  interval_of_check test640 160 32 (by decide +kernel)

theorem test640_block_6 : Interval test640 192 224 :=
  interval_of_check test640 192 32 (by decide +kernel)

theorem test640_block_7 : Interval test640 224 256 :=
  interval_of_check test640 224 32 (by decide +kernel)

theorem test640_block_8 : Interval test640 256 288 :=
  interval_of_check test640 256 32 (by decide +kernel)

theorem test640_block_9 : Interval test640 288 320 :=
  interval_of_check test640 288 32 (by decide +kernel)

theorem test640_block_10 : Interval test640 320 352 :=
  interval_of_check test640 320 32 (by decide +kernel)

theorem test640_block_11 : Interval test640 352 384 :=
  interval_of_check test640 352 32 (by decide +kernel)

theorem test640_block_12 : Interval test640 384 416 :=
  interval_of_check test640 384 32 (by decide +kernel)

theorem test640_block_13 : Interval test640 416 448 :=
  interval_of_check test640 416 32 (by decide +kernel)

theorem test640_block_14 : Interval test640 448 465 :=
  interval_of_check test640 448 17 (by decide +kernel)

theorem test640_complete : Interval test640 0 465 :=
  (interval_append test640 0 224 465
  (interval_append test640 0 96 224
  (interval_append test640 0 32 96
  test640_block_0
  (interval_append test640 32 64 96
  test640_block_1
  test640_block_2))
  (interval_append test640 96 160 224
  (interval_append test640 96 128 160
  test640_block_3
  test640_block_4)
  (interval_append test640 160 192 224
  test640_block_5
  test640_block_6)))
  (interval_append test640 224 352 465
  (interval_append test640 224 288 352
  (interval_append test640 224 256 288
  test640_block_7
  test640_block_8)
  (interval_append test640 288 320 352
  test640_block_9
  test640_block_10))
  (interval_append test640 352 416 465
  (interval_append test640 352 384 416
  test640_block_11
  test640_block_12)
  (interval_append test640 416 448 465
  test640_block_13
  test640_block_14))))
theorem nodeInterval640 : Interval nodeTest 640 1105 := by
  intro i hlo hhi
  have h := test640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0064
