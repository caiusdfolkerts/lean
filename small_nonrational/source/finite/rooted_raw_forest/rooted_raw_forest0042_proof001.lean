module
prelude
public import RootedRawForest0042Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0042
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

theorem test640_block_14 : Interval test640 448 480 :=
  interval_of_check test640 448 32 (by decide +kernel)

theorem test640_block_15 : Interval test640 480 512 :=
  interval_of_check test640 480 32 (by decide +kernel)

theorem test640_block_16 : Interval test640 512 528 :=
  interval_of_check test640 512 16 (by decide +kernel)

theorem test640_complete : Interval test640 0 528 :=
  (interval_append test640 0 256 528
  (interval_append test640 0 128 256
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  test640_block_0
  test640_block_1)
  (interval_append test640 64 96 128
  test640_block_2
  test640_block_3))
  (interval_append test640 128 192 256
  (interval_append test640 128 160 192
  test640_block_4
  test640_block_5)
  (interval_append test640 192 224 256
  test640_block_6
  test640_block_7)))
  (interval_append test640 256 384 528
  (interval_append test640 256 320 384
  (interval_append test640 256 288 320
  test640_block_8
  test640_block_9)
  (interval_append test640 320 352 384
  test640_block_10
  test640_block_11))
  (interval_append test640 384 448 528
  (interval_append test640 384 416 448
  test640_block_12
  test640_block_13)
  (interval_append test640 448 480 528
  test640_block_14
  (interval_append test640 480 512 528
  test640_block_15
  test640_block_16)))))
theorem nodeInterval640 : Interval nodeTest 640 1168 := by
  intro i hlo hhi
  have h := test640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0042
