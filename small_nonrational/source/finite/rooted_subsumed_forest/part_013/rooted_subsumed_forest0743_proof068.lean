module
prelude
public import RootedSubsumedForest0743Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test43520 (i : Nat) := nodeTest (i+43520)
theorem test43520_block_0 : Interval test43520 0 16 :=
  interval_of_check test43520 0 16 (by decide +kernel)

theorem test43520_block_1 : Interval test43520 16 32 :=
  interval_of_check test43520 16 16 (by decide +kernel)

theorem test43520_block_2 : Interval test43520 32 48 :=
  interval_of_check test43520 32 16 (by decide +kernel)

theorem test43520_block_3 : Interval test43520 48 64 :=
  interval_of_check test43520 48 16 (by decide +kernel)

theorem test43520_block_4 : Interval test43520 64 80 :=
  interval_of_check test43520 64 16 (by decide +kernel)

theorem test43520_block_5 : Interval test43520 80 96 :=
  interval_of_check test43520 80 16 (by decide +kernel)

theorem test43520_block_6 : Interval test43520 96 112 :=
  interval_of_check test43520 96 16 (by decide +kernel)

theorem test43520_block_7 : Interval test43520 112 128 :=
  interval_of_check test43520 112 16 (by decide +kernel)

theorem test43520_block_8 : Interval test43520 128 144 :=
  interval_of_check test43520 128 16 (by decide +kernel)

theorem test43520_block_9 : Interval test43520 144 160 :=
  interval_of_check test43520 144 16 (by decide +kernel)

theorem test43520_block_10 : Interval test43520 160 176 :=
  interval_of_check test43520 160 16 (by decide +kernel)

theorem test43520_block_11 : Interval test43520 176 192 :=
  interval_of_check test43520 176 16 (by decide +kernel)

theorem test43520_block_12 : Interval test43520 192 208 :=
  interval_of_check test43520 192 16 (by decide +kernel)

theorem test43520_block_13 : Interval test43520 208 224 :=
  interval_of_check test43520 208 16 (by decide +kernel)

theorem test43520_block_14 : Interval test43520 224 240 :=
  interval_of_check test43520 224 16 (by decide +kernel)

theorem test43520_block_15 : Interval test43520 240 256 :=
  interval_of_check test43520 240 16 (by decide +kernel)

theorem test43520_block_16 : Interval test43520 256 272 :=
  interval_of_check test43520 256 16 (by decide +kernel)

theorem test43520_block_17 : Interval test43520 272 288 :=
  interval_of_check test43520 272 16 (by decide +kernel)

theorem test43520_block_18 : Interval test43520 288 304 :=
  interval_of_check test43520 288 16 (by decide +kernel)

theorem test43520_block_19 : Interval test43520 304 320 :=
  interval_of_check test43520 304 16 (by decide +kernel)

theorem test43520_block_20 : Interval test43520 320 336 :=
  interval_of_check test43520 320 16 (by decide +kernel)

theorem test43520_block_21 : Interval test43520 336 352 :=
  interval_of_check test43520 336 16 (by decide +kernel)

theorem test43520_block_22 : Interval test43520 352 368 :=
  interval_of_check test43520 352 16 (by decide +kernel)

theorem test43520_block_23 : Interval test43520 368 384 :=
  interval_of_check test43520 368 16 (by decide +kernel)

theorem test43520_block_24 : Interval test43520 384 400 :=
  interval_of_check test43520 384 16 (by decide +kernel)

theorem test43520_block_25 : Interval test43520 400 416 :=
  interval_of_check test43520 400 16 (by decide +kernel)

theorem test43520_block_26 : Interval test43520 416 429 :=
  interval_of_check test43520 416 13 (by decide +kernel)

theorem test43520_complete : Interval test43520 0 429 :=
  (interval_append test43520 0 208 429
  (interval_append test43520 0 96 208
  (interval_append test43520 0 48 96
  (interval_append test43520 0 16 48
  test43520_block_0
  (interval_append test43520 16 32 48
  test43520_block_1
  test43520_block_2))
  (interval_append test43520 48 64 96
  test43520_block_3
  (interval_append test43520 64 80 96
  test43520_block_4
  test43520_block_5)))
  (interval_append test43520 96 144 208
  (interval_append test43520 96 112 144
  test43520_block_6
  (interval_append test43520 112 128 144
  test43520_block_7
  test43520_block_8))
  (interval_append test43520 144 176 208
  (interval_append test43520 144 160 176
  test43520_block_9
  test43520_block_10)
  (interval_append test43520 176 192 208
  test43520_block_11
  test43520_block_12))))
  (interval_append test43520 208 320 429
  (interval_append test43520 208 256 320
  (interval_append test43520 208 224 256
  test43520_block_13
  (interval_append test43520 224 240 256
  test43520_block_14
  test43520_block_15))
  (interval_append test43520 256 288 320
  (interval_append test43520 256 272 288
  test43520_block_16
  test43520_block_17)
  (interval_append test43520 288 304 320
  test43520_block_18
  test43520_block_19)))
  (interval_append test43520 320 368 429
  (interval_append test43520 320 336 368
  test43520_block_20
  (interval_append test43520 336 352 368
  test43520_block_21
  test43520_block_22))
  (interval_append test43520 368 400 429
  (interval_append test43520 368 384 400
  test43520_block_23
  test43520_block_24)
  (interval_append test43520 400 416 429
  test43520_block_25
  test43520_block_26)))))
theorem nodeInterval43520 : Interval nodeTest 43520 43949 := by
  intro i hlo hhi
  have h := test43520_complete (i-43520) (Nat.zero_le _) (by omega)
  simpa only [test43520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0743
