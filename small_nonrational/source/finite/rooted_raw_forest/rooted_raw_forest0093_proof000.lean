module
prelude
public import RootedRawForest0093Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0093
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 32 :=
  interval_of_check test0 0 32 (by decide +kernel)

theorem test0_block_1 : Interval test0 32 64 :=
  interval_of_check test0 32 32 (by decide +kernel)

theorem test0_block_2 : Interval test0 64 96 :=
  interval_of_check test0 64 32 (by decide +kernel)

theorem test0_block_3 : Interval test0 96 128 :=
  interval_of_check test0 96 32 (by decide +kernel)

theorem test0_block_4 : Interval test0 128 160 :=
  interval_of_check test0 128 32 (by decide +kernel)

theorem test0_block_5 : Interval test0 160 192 :=
  interval_of_check test0 160 32 (by decide +kernel)

theorem test0_block_6 : Interval test0 192 224 :=
  interval_of_check test0 192 32 (by decide +kernel)

theorem test0_block_7 : Interval test0 224 256 :=
  interval_of_check test0 224 32 (by decide +kernel)

theorem test0_block_8 : Interval test0 256 288 :=
  interval_of_check test0 256 32 (by decide +kernel)

theorem test0_block_9 : Interval test0 288 320 :=
  interval_of_check test0 288 32 (by decide +kernel)

theorem test0_block_10 : Interval test0 320 352 :=
  interval_of_check test0 320 32 (by decide +kernel)

theorem test0_block_11 : Interval test0 352 384 :=
  interval_of_check test0 352 32 (by decide +kernel)

theorem test0_block_12 : Interval test0 384 416 :=
  interval_of_check test0 384 32 (by decide +kernel)

theorem test0_block_13 : Interval test0 416 448 :=
  interval_of_check test0 416 32 (by decide +kernel)

theorem test0_block_14 : Interval test0 448 480 :=
  interval_of_check test0 448 32 (by decide +kernel)

theorem test0_block_15 : Interval test0 480 487 :=
  interval_of_check test0 480 7 (by decide +kernel)

theorem test0_complete : Interval test0 0 487 :=
  (interval_append test0 0 256 487
  (interval_append test0 0 128 256
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 128
  test0_block_2
  test0_block_3))
  (interval_append test0 128 192 256
  (interval_append test0 128 160 192
  test0_block_4
  test0_block_5)
  (interval_append test0 192 224 256
  test0_block_6
  test0_block_7)))
  (interval_append test0 256 384 487
  (interval_append test0 256 320 384
  (interval_append test0 256 288 320
  test0_block_8
  test0_block_9)
  (interval_append test0 320 352 384
  test0_block_10
  test0_block_11))
  (interval_append test0 384 448 487
  (interval_append test0 384 416 448
  test0_block_12
  test0_block_13)
  (interval_append test0 448 480 487
  test0_block_14
  test0_block_15))))
theorem nodeInterval0 : Interval nodeTest 0 487 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0093
