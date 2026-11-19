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
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 32 :=
  interval_of_check test1920 0 32 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 32 64 :=
  interval_of_check test1920 32 32 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 64 96 :=
  interval_of_check test1920 64 32 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 96 128 :=
  interval_of_check test1920 96 32 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 128 160 :=
  interval_of_check test1920 128 32 (by decide +kernel)

theorem test1920_block_5 : Interval test1920 160 192 :=
  interval_of_check test1920 160 32 (by decide +kernel)

theorem test1920_block_6 : Interval test1920 192 224 :=
  interval_of_check test1920 192 32 (by decide +kernel)

theorem test1920_block_7 : Interval test1920 224 256 :=
  interval_of_check test1920 224 32 (by decide +kernel)

theorem test1920_block_8 : Interval test1920 256 288 :=
  interval_of_check test1920 256 32 (by decide +kernel)

theorem test1920_block_9 : Interval test1920 288 320 :=
  interval_of_check test1920 288 32 (by decide +kernel)

theorem test1920_block_10 : Interval test1920 320 352 :=
  interval_of_check test1920 320 32 (by decide +kernel)

theorem test1920_block_11 : Interval test1920 352 384 :=
  interval_of_check test1920 352 32 (by decide +kernel)

theorem test1920_block_12 : Interval test1920 384 416 :=
  interval_of_check test1920 384 32 (by decide +kernel)

theorem test1920_block_13 : Interval test1920 416 448 :=
  interval_of_check test1920 416 32 (by decide +kernel)

theorem test1920_block_14 : Interval test1920 448 480 :=
  interval_of_check test1920 448 32 (by decide +kernel)

theorem test1920_block_15 : Interval test1920 480 512 :=
  interval_of_check test1920 480 32 (by decide +kernel)

theorem test1920_block_16 : Interval test1920 512 544 :=
  interval_of_check test1920 512 32 (by decide +kernel)

theorem test1920_block_17 : Interval test1920 544 576 :=
  interval_of_check test1920 544 32 (by decide +kernel)

theorem test1920_block_18 : Interval test1920 576 608 :=
  interval_of_check test1920 576 32 (by decide +kernel)

theorem test1920_block_19 : Interval test1920 608 640 :=
  interval_of_check test1920 608 32 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 640 :=
  (interval_append test1920 0 320 640
  (interval_append test1920 0 160 320
  (interval_append test1920 0 64 160
  (interval_append test1920 0 32 64
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 64 96 160
  test1920_block_2
  (interval_append test1920 96 128 160
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 160 224 320
  (interval_append test1920 160 192 224
  test1920_block_5
  test1920_block_6)
  (interval_append test1920 224 256 320
  test1920_block_7
  (interval_append test1920 256 288 320
  test1920_block_8
  test1920_block_9))))
  (interval_append test1920 320 480 640
  (interval_append test1920 320 384 480
  (interval_append test1920 320 352 384
  test1920_block_10
  test1920_block_11)
  (interval_append test1920 384 416 480
  test1920_block_12
  (interval_append test1920 416 448 480
  test1920_block_13
  test1920_block_14)))
  (interval_append test1920 480 544 640
  (interval_append test1920 480 512 544
  test1920_block_15
  test1920_block_16)
  (interval_append test1920 544 576 640
  test1920_block_17
  (interval_append test1920 576 608 640
  test1920_block_18
  test1920_block_19)))))
theorem nodeInterval1920 : Interval nodeTest 1920 2560 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallRawForest02
