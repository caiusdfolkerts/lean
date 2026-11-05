module
prelude
public import RootedSubsumedForest0295Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0295
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test640 (i : Nat) := nodeTest (i+640)
theorem test640_block_0 : Interval test640 0 16 :=
  interval_of_check test640 0 16 (by decide +kernel)

theorem test640_block_1 : Interval test640 16 32 :=
  interval_of_check test640 16 16 (by decide +kernel)

theorem test640_block_2 : Interval test640 32 48 :=
  interval_of_check test640 32 16 (by decide +kernel)

theorem test640_block_3 : Interval test640 48 64 :=
  interval_of_check test640 48 16 (by decide +kernel)

theorem test640_block_4 : Interval test640 64 80 :=
  interval_of_check test640 64 16 (by decide +kernel)

theorem test640_block_5 : Interval test640 80 96 :=
  interval_of_check test640 80 16 (by decide +kernel)

theorem test640_block_6 : Interval test640 96 112 :=
  interval_of_check test640 96 16 (by decide +kernel)

theorem test640_block_7 : Interval test640 112 128 :=
  interval_of_check test640 112 16 (by decide +kernel)

theorem test640_block_8 : Interval test640 128 144 :=
  interval_of_check test640 128 16 (by decide +kernel)

theorem test640_block_9 : Interval test640 144 160 :=
  interval_of_check test640 144 16 (by decide +kernel)

theorem test640_block_10 : Interval test640 160 176 :=
  interval_of_check test640 160 16 (by decide +kernel)

theorem test640_block_11 : Interval test640 176 192 :=
  interval_of_check test640 176 16 (by decide +kernel)

theorem test640_block_12 : Interval test640 192 208 :=
  interval_of_check test640 192 16 (by decide +kernel)

theorem test640_block_13 : Interval test640 208 224 :=
  interval_of_check test640 208 16 (by decide +kernel)

theorem test640_block_14 : Interval test640 224 240 :=
  interval_of_check test640 224 16 (by decide +kernel)

theorem test640_block_15 : Interval test640 240 256 :=
  interval_of_check test640 240 16 (by decide +kernel)

theorem test640_block_16 : Interval test640 256 272 :=
  interval_of_check test640 256 16 (by decide +kernel)

theorem test640_block_17 : Interval test640 272 288 :=
  interval_of_check test640 272 16 (by decide +kernel)

theorem test640_block_18 : Interval test640 288 304 :=
  interval_of_check test640 288 16 (by decide +kernel)

theorem test640_block_19 : Interval test640 304 320 :=
  interval_of_check test640 304 16 (by decide +kernel)

theorem test640_block_20 : Interval test640 320 336 :=
  interval_of_check test640 320 16 (by decide +kernel)

theorem test640_block_21 : Interval test640 336 352 :=
  interval_of_check test640 336 16 (by decide +kernel)

theorem test640_block_22 : Interval test640 352 368 :=
  interval_of_check test640 352 16 (by decide +kernel)

theorem test640_block_23 : Interval test640 368 384 :=
  interval_of_check test640 368 16 (by decide +kernel)

theorem test640_block_24 : Interval test640 384 400 :=
  interval_of_check test640 384 16 (by decide +kernel)

theorem test640_block_25 : Interval test640 400 416 :=
  interval_of_check test640 400 16 (by decide +kernel)

theorem test640_block_26 : Interval test640 416 417 :=
  interval_of_check test640 416 1 (by decide +kernel)

theorem test640_complete : Interval test640 0 417 :=
  (interval_append test640 0 208 417
  (interval_append test640 0 96 208
  (interval_append test640 0 48 96
  (interval_append test640 0 16 48
  test640_block_0
  (interval_append test640 16 32 48
  test640_block_1
  test640_block_2))
  (interval_append test640 48 64 96
  test640_block_3
  (interval_append test640 64 80 96
  test640_block_4
  test640_block_5)))
  (interval_append test640 96 144 208
  (interval_append test640 96 112 144
  test640_block_6
  (interval_append test640 112 128 144
  test640_block_7
  test640_block_8))
  (interval_append test640 144 176 208
  (interval_append test640 144 160 176
  test640_block_9
  test640_block_10)
  (interval_append test640 176 192 208
  test640_block_11
  test640_block_12))))
  (interval_append test640 208 320 417
  (interval_append test640 208 256 320
  (interval_append test640 208 224 256
  test640_block_13
  (interval_append test640 224 240 256
  test640_block_14
  test640_block_15))
  (interval_append test640 256 288 320
  (interval_append test640 256 272 288
  test640_block_16
  test640_block_17)
  (interval_append test640 288 304 320
  test640_block_18
  test640_block_19)))
  (interval_append test640 320 368 417
  (interval_append test640 320 336 368
  test640_block_20
  (interval_append test640 336 352 368
  test640_block_21
  test640_block_22))
  (interval_append test640 368 400 417
  (interval_append test640 368 384 400
  test640_block_23
  test640_block_24)
  (interval_append test640 400 416 417
  test640_block_25
  test640_block_26)))))
theorem nodeInterval640 : Interval nodeTest 640 1057 := by
  intro i hlo hhi
  have h := test640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0295
