module
prelude
public import RootedRawForest0066Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3840 (i : Nat) := nodeTest (i+3840)
theorem test3840_block_0 : Interval test3840 0 32 :=
  interval_of_check test3840 0 32 (by decide +kernel)

theorem test3840_block_1 : Interval test3840 32 64 :=
  interval_of_check test3840 32 32 (by decide +kernel)

theorem test3840_block_2 : Interval test3840 64 96 :=
  interval_of_check test3840 64 32 (by decide +kernel)

theorem test3840_block_3 : Interval test3840 96 128 :=
  interval_of_check test3840 96 32 (by decide +kernel)

theorem test3840_block_4 : Interval test3840 128 160 :=
  interval_of_check test3840 128 32 (by decide +kernel)

theorem test3840_block_5 : Interval test3840 160 192 :=
  interval_of_check test3840 160 32 (by decide +kernel)

theorem test3840_block_6 : Interval test3840 192 224 :=
  interval_of_check test3840 192 32 (by decide +kernel)

theorem test3840_block_7 : Interval test3840 224 256 :=
  interval_of_check test3840 224 32 (by decide +kernel)

theorem test3840_block_8 : Interval test3840 256 288 :=
  interval_of_check test3840 256 32 (by decide +kernel)

theorem test3840_block_9 : Interval test3840 288 320 :=
  interval_of_check test3840 288 32 (by decide +kernel)

theorem test3840_block_10 : Interval test3840 320 352 :=
  interval_of_check test3840 320 32 (by decide +kernel)

theorem test3840_block_11 : Interval test3840 352 384 :=
  interval_of_check test3840 352 32 (by decide +kernel)

theorem test3840_block_12 : Interval test3840 384 416 :=
  interval_of_check test3840 384 32 (by decide +kernel)

theorem test3840_block_13 : Interval test3840 416 448 :=
  interval_of_check test3840 416 32 (by decide +kernel)

theorem test3840_block_14 : Interval test3840 448 480 :=
  interval_of_check test3840 448 32 (by decide +kernel)

theorem test3840_block_15 : Interval test3840 480 512 :=
  interval_of_check test3840 480 32 (by decide +kernel)

theorem test3840_block_16 : Interval test3840 512 544 :=
  interval_of_check test3840 512 32 (by decide +kernel)

theorem test3840_block_17 : Interval test3840 544 576 :=
  interval_of_check test3840 544 32 (by decide +kernel)

theorem test3840_block_18 : Interval test3840 576 608 :=
  interval_of_check test3840 576 32 (by decide +kernel)

theorem test3840_block_19 : Interval test3840 608 640 :=
  interval_of_check test3840 608 32 (by decide +kernel)

theorem test3840_complete : Interval test3840 0 640 :=
  (interval_append test3840 0 320 640
  (interval_append test3840 0 160 320
  (interval_append test3840 0 64 160
  (interval_append test3840 0 32 64
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 64 96 160
  test3840_block_2
  (interval_append test3840 96 128 160
  test3840_block_3
  test3840_block_4)))
  (interval_append test3840 160 224 320
  (interval_append test3840 160 192 224
  test3840_block_5
  test3840_block_6)
  (interval_append test3840 224 256 320
  test3840_block_7
  (interval_append test3840 256 288 320
  test3840_block_8
  test3840_block_9))))
  (interval_append test3840 320 480 640
  (interval_append test3840 320 384 480
  (interval_append test3840 320 352 384
  test3840_block_10
  test3840_block_11)
  (interval_append test3840 384 416 480
  test3840_block_12
  (interval_append test3840 416 448 480
  test3840_block_13
  test3840_block_14)))
  (interval_append test3840 480 544 640
  (interval_append test3840 480 512 544
  test3840_block_15
  test3840_block_16)
  (interval_append test3840 544 576 640
  test3840_block_17
  (interval_append test3840 576 608 640
  test3840_block_18
  test3840_block_19)))))
theorem nodeInterval3840 : Interval nodeTest 3840 4480 := by
  intro i hlo hhi
  have h := test3840_complete (i-3840) (Nat.zero_le _) (by omega)
  simpa only [test3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0066
