module
prelude
public import RootedSubsumedForest0309Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test5120 (i : Nat) := nodeTest (i+5120)
theorem test5120_block_0 : Interval test5120 0 16 :=
  interval_of_check test5120 0 16 (by decide +kernel)

theorem test5120_block_1 : Interval test5120 16 32 :=
  interval_of_check test5120 16 16 (by decide +kernel)

theorem test5120_block_2 : Interval test5120 32 48 :=
  interval_of_check test5120 32 16 (by decide +kernel)

theorem test5120_block_3 : Interval test5120 48 64 :=
  interval_of_check test5120 48 16 (by decide +kernel)

theorem test5120_block_4 : Interval test5120 64 80 :=
  interval_of_check test5120 64 16 (by decide +kernel)

theorem test5120_block_5 : Interval test5120 80 96 :=
  interval_of_check test5120 80 16 (by decide +kernel)

theorem test5120_block_6 : Interval test5120 96 112 :=
  interval_of_check test5120 96 16 (by decide +kernel)

theorem test5120_block_7 : Interval test5120 112 128 :=
  interval_of_check test5120 112 16 (by decide +kernel)

theorem test5120_block_8 : Interval test5120 128 144 :=
  interval_of_check test5120 128 16 (by decide +kernel)

theorem test5120_block_9 : Interval test5120 144 160 :=
  interval_of_check test5120 144 16 (by decide +kernel)

theorem test5120_block_10 : Interval test5120 160 176 :=
  interval_of_check test5120 160 16 (by decide +kernel)

theorem test5120_block_11 : Interval test5120 176 192 :=
  interval_of_check test5120 176 16 (by decide +kernel)

theorem test5120_block_12 : Interval test5120 192 208 :=
  interval_of_check test5120 192 16 (by decide +kernel)

theorem test5120_block_13 : Interval test5120 208 224 :=
  interval_of_check test5120 208 16 (by decide +kernel)

theorem test5120_block_14 : Interval test5120 224 240 :=
  interval_of_check test5120 224 16 (by decide +kernel)

theorem test5120_block_15 : Interval test5120 240 256 :=
  interval_of_check test5120 240 16 (by decide +kernel)

theorem test5120_block_16 : Interval test5120 256 272 :=
  interval_of_check test5120 256 16 (by decide +kernel)

theorem test5120_block_17 : Interval test5120 272 288 :=
  interval_of_check test5120 272 16 (by decide +kernel)

theorem test5120_block_18 : Interval test5120 288 304 :=
  interval_of_check test5120 288 16 (by decide +kernel)

theorem test5120_block_19 : Interval test5120 304 320 :=
  interval_of_check test5120 304 16 (by decide +kernel)

theorem test5120_block_20 : Interval test5120 320 336 :=
  interval_of_check test5120 320 16 (by decide +kernel)

theorem test5120_block_21 : Interval test5120 336 352 :=
  interval_of_check test5120 336 16 (by decide +kernel)

theorem test5120_block_22 : Interval test5120 352 368 :=
  interval_of_check test5120 352 16 (by decide +kernel)

theorem test5120_block_23 : Interval test5120 368 384 :=
  interval_of_check test5120 368 16 (by decide +kernel)

theorem test5120_block_24 : Interval test5120 384 400 :=
  interval_of_check test5120 384 16 (by decide +kernel)

theorem test5120_block_25 : Interval test5120 400 416 :=
  interval_of_check test5120 400 16 (by decide +kernel)

theorem test5120_block_26 : Interval test5120 416 432 :=
  interval_of_check test5120 416 16 (by decide +kernel)

theorem test5120_block_27 : Interval test5120 432 448 :=
  interval_of_check test5120 432 16 (by decide +kernel)

theorem test5120_block_28 : Interval test5120 448 457 :=
  interval_of_check test5120 448 9 (by decide +kernel)

theorem test5120_complete : Interval test5120 0 457 :=
  (interval_append test5120 0 224 457
  (interval_append test5120 0 112 224
  (interval_append test5120 0 48 112
  (interval_append test5120 0 16 48
  test5120_block_0
  (interval_append test5120 16 32 48
  test5120_block_1
  test5120_block_2))
  (interval_append test5120 48 80 112
  (interval_append test5120 48 64 80
  test5120_block_3
  test5120_block_4)
  (interval_append test5120 80 96 112
  test5120_block_5
  test5120_block_6)))
  (interval_append test5120 112 160 224
  (interval_append test5120 112 128 160
  test5120_block_7
  (interval_append test5120 128 144 160
  test5120_block_8
  test5120_block_9))
  (interval_append test5120 160 192 224
  (interval_append test5120 160 176 192
  test5120_block_10
  test5120_block_11)
  (interval_append test5120 192 208 224
  test5120_block_12
  test5120_block_13))))
  (interval_append test5120 224 336 457
  (interval_append test5120 224 272 336
  (interval_append test5120 224 240 272
  test5120_block_14
  (interval_append test5120 240 256 272
  test5120_block_15
  test5120_block_16))
  (interval_append test5120 272 304 336
  (interval_append test5120 272 288 304
  test5120_block_17
  test5120_block_18)
  (interval_append test5120 304 320 336
  test5120_block_19
  test5120_block_20)))
  (interval_append test5120 336 400 457
  (interval_append test5120 336 368 400
  (interval_append test5120 336 352 368
  test5120_block_21
  test5120_block_22)
  (interval_append test5120 368 384 400
  test5120_block_23
  test5120_block_24))
  (interval_append test5120 400 432 457
  (interval_append test5120 400 416 432
  test5120_block_25
  test5120_block_26)
  (interval_append test5120 432 448 457
  test5120_block_27
  test5120_block_28)))))
theorem nodeInterval5120 : Interval nodeTest 5120 5577 := by
  intro i hlo hhi
  have h := test5120_complete (i-5120) (Nat.zero_le _) (by omega)
  simpa only [test5120, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0309
