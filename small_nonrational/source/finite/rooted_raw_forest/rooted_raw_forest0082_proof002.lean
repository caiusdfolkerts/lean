module
prelude
public import RootedRawForest0082Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0082
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1280 (i : Nat) := nodeTest (i+1280)
theorem test1280_block_0 : Interval test1280 0 32 :=
  interval_of_check test1280 0 32 (by decide +kernel)

theorem test1280_block_1 : Interval test1280 32 64 :=
  interval_of_check test1280 32 32 (by decide +kernel)

theorem test1280_block_2 : Interval test1280 64 96 :=
  interval_of_check test1280 64 32 (by decide +kernel)

theorem test1280_block_3 : Interval test1280 96 128 :=
  interval_of_check test1280 96 32 (by decide +kernel)

theorem test1280_block_4 : Interval test1280 128 160 :=
  interval_of_check test1280 128 32 (by decide +kernel)

theorem test1280_block_5 : Interval test1280 160 192 :=
  interval_of_check test1280 160 32 (by decide +kernel)

theorem test1280_block_6 : Interval test1280 192 224 :=
  interval_of_check test1280 192 32 (by decide +kernel)

theorem test1280_block_7 : Interval test1280 224 256 :=
  interval_of_check test1280 224 32 (by decide +kernel)

theorem test1280_block_8 : Interval test1280 256 288 :=
  interval_of_check test1280 256 32 (by decide +kernel)

theorem test1280_block_9 : Interval test1280 288 320 :=
  interval_of_check test1280 288 32 (by decide +kernel)

theorem test1280_block_10 : Interval test1280 320 352 :=
  interval_of_check test1280 320 32 (by decide +kernel)

theorem test1280_block_11 : Interval test1280 352 384 :=
  interval_of_check test1280 352 32 (by decide +kernel)

theorem test1280_block_12 : Interval test1280 384 416 :=
  interval_of_check test1280 384 32 (by decide +kernel)

theorem test1280_block_13 : Interval test1280 416 448 :=
  interval_of_check test1280 416 32 (by decide +kernel)

theorem test1280_block_14 : Interval test1280 448 480 :=
  interval_of_check test1280 448 32 (by decide +kernel)

theorem test1280_block_15 : Interval test1280 480 512 :=
  interval_of_check test1280 480 32 (by decide +kernel)

theorem test1280_block_16 : Interval test1280 512 544 :=
  interval_of_check test1280 512 32 (by decide +kernel)

theorem test1280_block_17 : Interval test1280 544 576 :=
  interval_of_check test1280 544 32 (by decide +kernel)

theorem test1280_block_18 : Interval test1280 576 608 :=
  interval_of_check test1280 576 32 (by decide +kernel)

theorem test1280_block_19 : Interval test1280 608 640 :=
  interval_of_check test1280 608 32 (by decide +kernel)

theorem test1280_complete : Interval test1280 0 640 :=
  (interval_append test1280 0 320 640
  (interval_append test1280 0 160 320
  (interval_append test1280 0 64 160
  (interval_append test1280 0 32 64
  test1280_block_0
  test1280_block_1)
  (interval_append test1280 64 96 160
  test1280_block_2
  (interval_append test1280 96 128 160
  test1280_block_3
  test1280_block_4)))
  (interval_append test1280 160 224 320
  (interval_append test1280 160 192 224
  test1280_block_5
  test1280_block_6)
  (interval_append test1280 224 256 320
  test1280_block_7
  (interval_append test1280 256 288 320
  test1280_block_8
  test1280_block_9))))
  (interval_append test1280 320 480 640
  (interval_append test1280 320 384 480
  (interval_append test1280 320 352 384
  test1280_block_10
  test1280_block_11)
  (interval_append test1280 384 416 480
  test1280_block_12
  (interval_append test1280 416 448 480
  test1280_block_13
  test1280_block_14)))
  (interval_append test1280 480 544 640
  (interval_append test1280 480 512 544
  test1280_block_15
  test1280_block_16)
  (interval_append test1280 544 576 640
  test1280_block_17
  (interval_append test1280 576 608 640
  test1280_block_18
  test1280_block_19)))))
theorem nodeInterval1280 : Interval nodeTest 1280 1920 := by
  intro i hlo hhi
  have h := test1280_complete (i-1280) (Nat.zero_le _) (by omega)
  simpa only [test1280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0082
