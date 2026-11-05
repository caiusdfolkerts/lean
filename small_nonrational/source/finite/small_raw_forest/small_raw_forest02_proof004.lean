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
def test2560 (i : Nat) := nodeTest (i+2560)
theorem test2560_block_0 : Interval test2560 0 32 :=
  interval_of_check test2560 0 32 (by decide +kernel)

theorem test2560_block_1 : Interval test2560 32 64 :=
  interval_of_check test2560 32 32 (by decide +kernel)

theorem test2560_block_2 : Interval test2560 64 96 :=
  interval_of_check test2560 64 32 (by decide +kernel)

theorem test2560_block_3 : Interval test2560 96 128 :=
  interval_of_check test2560 96 32 (by decide +kernel)

theorem test2560_block_4 : Interval test2560 128 160 :=
  interval_of_check test2560 128 32 (by decide +kernel)

theorem test2560_block_5 : Interval test2560 160 192 :=
  interval_of_check test2560 160 32 (by decide +kernel)

theorem test2560_block_6 : Interval test2560 192 224 :=
  interval_of_check test2560 192 32 (by decide +kernel)

theorem test2560_block_7 : Interval test2560 224 256 :=
  interval_of_check test2560 224 32 (by decide +kernel)

theorem test2560_block_8 : Interval test2560 256 288 :=
  interval_of_check test2560 256 32 (by decide +kernel)

theorem test2560_block_9 : Interval test2560 288 320 :=
  interval_of_check test2560 288 32 (by decide +kernel)

theorem test2560_block_10 : Interval test2560 320 352 :=
  interval_of_check test2560 320 32 (by decide +kernel)

theorem test2560_block_11 : Interval test2560 352 384 :=
  interval_of_check test2560 352 32 (by decide +kernel)

theorem test2560_block_12 : Interval test2560 384 416 :=
  interval_of_check test2560 384 32 (by decide +kernel)

theorem test2560_block_13 : Interval test2560 416 448 :=
  interval_of_check test2560 416 32 (by decide +kernel)

theorem test2560_block_14 : Interval test2560 448 480 :=
  interval_of_check test2560 448 32 (by decide +kernel)

theorem test2560_block_15 : Interval test2560 480 512 :=
  interval_of_check test2560 480 32 (by decide +kernel)

theorem test2560_block_16 : Interval test2560 512 544 :=
  interval_of_check test2560 512 32 (by decide +kernel)

theorem test2560_block_17 : Interval test2560 544 576 :=
  interval_of_check test2560 544 32 (by decide +kernel)

theorem test2560_block_18 : Interval test2560 576 608 :=
  interval_of_check test2560 576 32 (by decide +kernel)

theorem test2560_block_19 : Interval test2560 608 640 :=
  interval_of_check test2560 608 32 (by decide +kernel)

theorem test2560_complete : Interval test2560 0 640 :=
  (interval_append test2560 0 320 640
  (interval_append test2560 0 160 320
  (interval_append test2560 0 64 160
  (interval_append test2560 0 32 64
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 64 96 160
  test2560_block_2
  (interval_append test2560 96 128 160
  test2560_block_3
  test2560_block_4)))
  (interval_append test2560 160 224 320
  (interval_append test2560 160 192 224
  test2560_block_5
  test2560_block_6)
  (interval_append test2560 224 256 320
  test2560_block_7
  (interval_append test2560 256 288 320
  test2560_block_8
  test2560_block_9))))
  (interval_append test2560 320 480 640
  (interval_append test2560 320 384 480
  (interval_append test2560 320 352 384
  test2560_block_10
  test2560_block_11)
  (interval_append test2560 384 416 480
  test2560_block_12
  (interval_append test2560 416 448 480
  test2560_block_13
  test2560_block_14)))
  (interval_append test2560 480 544 640
  (interval_append test2560 480 512 544
  test2560_block_15
  test2560_block_16)
  (interval_append test2560 544 576 640
  test2560_block_17
  (interval_append test2560 576 608 640
  test2560_block_18
  test2560_block_19)))))
theorem nodeInterval2560 : Interval nodeTest 2560 3200 := by
  intro i hlo hhi
  have h := test2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [test2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallRawForest02
