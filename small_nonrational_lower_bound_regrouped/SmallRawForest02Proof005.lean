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
def test3200 (i : Nat) := nodeTest (i+3200)
theorem test3200_block_0 : Interval test3200 0 32 :=
  interval_of_check test3200 0 32 (by decide +kernel)

theorem test3200_block_1 : Interval test3200 32 64 :=
  interval_of_check test3200 32 32 (by decide +kernel)

theorem test3200_block_2 : Interval test3200 64 96 :=
  interval_of_check test3200 64 32 (by decide +kernel)

theorem test3200_block_3 : Interval test3200 96 128 :=
  interval_of_check test3200 96 32 (by decide +kernel)

theorem test3200_block_4 : Interval test3200 128 160 :=
  interval_of_check test3200 128 32 (by decide +kernel)

theorem test3200_block_5 : Interval test3200 160 192 :=
  interval_of_check test3200 160 32 (by decide +kernel)

theorem test3200_block_6 : Interval test3200 192 224 :=
  interval_of_check test3200 192 32 (by decide +kernel)

theorem test3200_block_7 : Interval test3200 224 256 :=
  interval_of_check test3200 224 32 (by decide +kernel)

theorem test3200_block_8 : Interval test3200 256 288 :=
  interval_of_check test3200 256 32 (by decide +kernel)

theorem test3200_block_9 : Interval test3200 288 320 :=
  interval_of_check test3200 288 32 (by decide +kernel)

theorem test3200_block_10 : Interval test3200 320 352 :=
  interval_of_check test3200 320 32 (by decide +kernel)

theorem test3200_block_11 : Interval test3200 352 384 :=
  interval_of_check test3200 352 32 (by decide +kernel)

theorem test3200_block_12 : Interval test3200 384 416 :=
  interval_of_check test3200 384 32 (by decide +kernel)

theorem test3200_block_13 : Interval test3200 416 448 :=
  interval_of_check test3200 416 32 (by decide +kernel)

theorem test3200_block_14 : Interval test3200 448 480 :=
  interval_of_check test3200 448 32 (by decide +kernel)

theorem test3200_block_15 : Interval test3200 480 512 :=
  interval_of_check test3200 480 32 (by decide +kernel)

theorem test3200_block_16 : Interval test3200 512 544 :=
  interval_of_check test3200 512 32 (by decide +kernel)

theorem test3200_block_17 : Interval test3200 544 576 :=
  interval_of_check test3200 544 32 (by decide +kernel)

theorem test3200_block_18 : Interval test3200 576 608 :=
  interval_of_check test3200 576 32 (by decide +kernel)

theorem test3200_block_19 : Interval test3200 608 640 :=
  interval_of_check test3200 608 32 (by decide +kernel)

theorem test3200_complete : Interval test3200 0 640 :=
  (interval_append test3200 0 320 640
  (interval_append test3200 0 160 320
  (interval_append test3200 0 64 160
  (interval_append test3200 0 32 64
  test3200_block_0
  test3200_block_1)
  (interval_append test3200 64 96 160
  test3200_block_2
  (interval_append test3200 96 128 160
  test3200_block_3
  test3200_block_4)))
  (interval_append test3200 160 224 320
  (interval_append test3200 160 192 224
  test3200_block_5
  test3200_block_6)
  (interval_append test3200 224 256 320
  test3200_block_7
  (interval_append test3200 256 288 320
  test3200_block_8
  test3200_block_9))))
  (interval_append test3200 320 480 640
  (interval_append test3200 320 384 480
  (interval_append test3200 320 352 384
  test3200_block_10
  test3200_block_11)
  (interval_append test3200 384 416 480
  test3200_block_12
  (interval_append test3200 416 448 480
  test3200_block_13
  test3200_block_14)))
  (interval_append test3200 480 544 640
  (interval_append test3200 480 512 544
  test3200_block_15
  test3200_block_16)
  (interval_append test3200 544 576 640
  test3200_block_17
  (interval_append test3200 576 608 640
  test3200_block_18
  test3200_block_19)))))
theorem nodeInterval3200 : Interval nodeTest 3200 3840 := by
  intro i hlo hhi
  have h := test3200_complete (i-3200) (Nat.zero_le _) (by omega)
  simpa only [test3200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallRawForest02
