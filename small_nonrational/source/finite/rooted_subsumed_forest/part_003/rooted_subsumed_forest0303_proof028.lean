module
prelude
public import RootedSubsumedForest0303Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test17920 (i : Nat) := nodeTest (i+17920)
theorem test17920_block_0 : Interval test17920 0 16 :=
  interval_of_check test17920 0 16 (by decide +kernel)

theorem test17920_block_1 : Interval test17920 16 32 :=
  interval_of_check test17920 16 16 (by decide +kernel)

theorem test17920_block_2 : Interval test17920 32 48 :=
  interval_of_check test17920 32 16 (by decide +kernel)

theorem test17920_block_3 : Interval test17920 48 64 :=
  interval_of_check test17920 48 16 (by decide +kernel)

theorem test17920_block_4 : Interval test17920 64 80 :=
  interval_of_check test17920 64 16 (by decide +kernel)

theorem test17920_block_5 : Interval test17920 80 96 :=
  interval_of_check test17920 80 16 (by decide +kernel)

theorem test17920_block_6 : Interval test17920 96 112 :=
  interval_of_check test17920 96 16 (by decide +kernel)

theorem test17920_block_7 : Interval test17920 112 128 :=
  interval_of_check test17920 112 16 (by decide +kernel)

theorem test17920_block_8 : Interval test17920 128 144 :=
  interval_of_check test17920 128 16 (by decide +kernel)

theorem test17920_block_9 : Interval test17920 144 160 :=
  interval_of_check test17920 144 16 (by decide +kernel)

theorem test17920_block_10 : Interval test17920 160 176 :=
  interval_of_check test17920 160 16 (by decide +kernel)

theorem test17920_block_11 : Interval test17920 176 192 :=
  interval_of_check test17920 176 16 (by decide +kernel)

theorem test17920_block_12 : Interval test17920 192 208 :=
  interval_of_check test17920 192 16 (by decide +kernel)

theorem test17920_block_13 : Interval test17920 208 224 :=
  interval_of_check test17920 208 16 (by decide +kernel)

theorem test17920_block_14 : Interval test17920 224 240 :=
  interval_of_check test17920 224 16 (by decide +kernel)

theorem test17920_block_15 : Interval test17920 240 256 :=
  interval_of_check test17920 240 16 (by decide +kernel)

theorem test17920_block_16 : Interval test17920 256 272 :=
  interval_of_check test17920 256 16 (by decide +kernel)

theorem test17920_block_17 : Interval test17920 272 288 :=
  interval_of_check test17920 272 16 (by decide +kernel)

theorem test17920_block_18 : Interval test17920 288 304 :=
  interval_of_check test17920 288 16 (by decide +kernel)

theorem test17920_block_19 : Interval test17920 304 320 :=
  interval_of_check test17920 304 16 (by decide +kernel)

theorem test17920_block_20 : Interval test17920 320 336 :=
  interval_of_check test17920 320 16 (by decide +kernel)

theorem test17920_block_21 : Interval test17920 336 352 :=
  interval_of_check test17920 336 16 (by decide +kernel)

theorem test17920_block_22 : Interval test17920 352 368 :=
  interval_of_check test17920 352 16 (by decide +kernel)

theorem test17920_block_23 : Interval test17920 368 384 :=
  interval_of_check test17920 368 16 (by decide +kernel)

theorem test17920_block_24 : Interval test17920 384 400 :=
  interval_of_check test17920 384 16 (by decide +kernel)

theorem test17920_block_25 : Interval test17920 400 416 :=
  interval_of_check test17920 400 16 (by decide +kernel)

theorem test17920_block_26 : Interval test17920 416 432 :=
  interval_of_check test17920 416 16 (by decide +kernel)

theorem test17920_block_27 : Interval test17920 432 437 :=
  interval_of_check test17920 432 5 (by decide +kernel)

theorem test17920_complete : Interval test17920 0 437 :=
  (interval_append test17920 0 224 437
  (interval_append test17920 0 112 224
  (interval_append test17920 0 48 112
  (interval_append test17920 0 16 48
  test17920_block_0
  (interval_append test17920 16 32 48
  test17920_block_1
  test17920_block_2))
  (interval_append test17920 48 80 112
  (interval_append test17920 48 64 80
  test17920_block_3
  test17920_block_4)
  (interval_append test17920 80 96 112
  test17920_block_5
  test17920_block_6)))
  (interval_append test17920 112 160 224
  (interval_append test17920 112 128 160
  test17920_block_7
  (interval_append test17920 128 144 160
  test17920_block_8
  test17920_block_9))
  (interval_append test17920 160 192 224
  (interval_append test17920 160 176 192
  test17920_block_10
  test17920_block_11)
  (interval_append test17920 192 208 224
  test17920_block_12
  test17920_block_13))))
  (interval_append test17920 224 336 437
  (interval_append test17920 224 272 336
  (interval_append test17920 224 240 272
  test17920_block_14
  (interval_append test17920 240 256 272
  test17920_block_15
  test17920_block_16))
  (interval_append test17920 272 304 336
  (interval_append test17920 272 288 304
  test17920_block_17
  test17920_block_18)
  (interval_append test17920 304 320 336
  test17920_block_19
  test17920_block_20)))
  (interval_append test17920 336 384 437
  (interval_append test17920 336 352 384
  test17920_block_21
  (interval_append test17920 352 368 384
  test17920_block_22
  test17920_block_23))
  (interval_append test17920 384 416 437
  (interval_append test17920 384 400 416
  test17920_block_24
  test17920_block_25)
  (interval_append test17920 416 432 437
  test17920_block_26
  test17920_block_27)))))
theorem nodeInterval17920 : Interval nodeTest 17920 18357 := by
  intro i hlo hhi
  have h := test17920_complete (i-17920) (Nat.zero_le _) (by omega)
  simpa only [test17920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0303
