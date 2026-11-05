module
prelude
public import RootedSubsumedForest0669Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0669
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test1920 (i : Nat) := nodeTest (i+1920)
theorem test1920_block_0 : Interval test1920 0 16 :=
  interval_of_check test1920 0 16 (by decide +kernel)

theorem test1920_block_1 : Interval test1920 16 32 :=
  interval_of_check test1920 16 16 (by decide +kernel)

theorem test1920_block_2 : Interval test1920 32 48 :=
  interval_of_check test1920 32 16 (by decide +kernel)

theorem test1920_block_3 : Interval test1920 48 64 :=
  interval_of_check test1920 48 16 (by decide +kernel)

theorem test1920_block_4 : Interval test1920 64 80 :=
  interval_of_check test1920 64 16 (by decide +kernel)

theorem test1920_block_5 : Interval test1920 80 96 :=
  interval_of_check test1920 80 16 (by decide +kernel)

theorem test1920_block_6 : Interval test1920 96 112 :=
  interval_of_check test1920 96 16 (by decide +kernel)

theorem test1920_block_7 : Interval test1920 112 128 :=
  interval_of_check test1920 112 16 (by decide +kernel)

theorem test1920_block_8 : Interval test1920 128 144 :=
  interval_of_check test1920 128 16 (by decide +kernel)

theorem test1920_block_9 : Interval test1920 144 160 :=
  interval_of_check test1920 144 16 (by decide +kernel)

theorem test1920_block_10 : Interval test1920 160 176 :=
  interval_of_check test1920 160 16 (by decide +kernel)

theorem test1920_block_11 : Interval test1920 176 192 :=
  interval_of_check test1920 176 16 (by decide +kernel)

theorem test1920_block_12 : Interval test1920 192 208 :=
  interval_of_check test1920 192 16 (by decide +kernel)

theorem test1920_block_13 : Interval test1920 208 224 :=
  interval_of_check test1920 208 16 (by decide +kernel)

theorem test1920_block_14 : Interval test1920 224 240 :=
  interval_of_check test1920 224 16 (by decide +kernel)

theorem test1920_block_15 : Interval test1920 240 256 :=
  interval_of_check test1920 240 16 (by decide +kernel)

theorem test1920_block_16 : Interval test1920 256 272 :=
  interval_of_check test1920 256 16 (by decide +kernel)

theorem test1920_block_17 : Interval test1920 272 288 :=
  interval_of_check test1920 272 16 (by decide +kernel)

theorem test1920_block_18 : Interval test1920 288 304 :=
  interval_of_check test1920 288 16 (by decide +kernel)

theorem test1920_block_19 : Interval test1920 304 320 :=
  interval_of_check test1920 304 16 (by decide +kernel)

theorem test1920_block_20 : Interval test1920 320 336 :=
  interval_of_check test1920 320 16 (by decide +kernel)

theorem test1920_block_21 : Interval test1920 336 352 :=
  interval_of_check test1920 336 16 (by decide +kernel)

theorem test1920_block_22 : Interval test1920 352 358 :=
  interval_of_check test1920 352 6 (by decide +kernel)

theorem test1920_complete : Interval test1920 0 358 :=
  (interval_append test1920 0 176 358
  (interval_append test1920 0 80 176
  (interval_append test1920 0 32 80
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 80
  test1920_block_2
  (interval_append test1920 48 64 80
  test1920_block_3
  test1920_block_4)))
  (interval_append test1920 80 128 176
  (interval_append test1920 80 96 128
  test1920_block_5
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7))
  (interval_append test1920 128 144 176
  test1920_block_8
  (interval_append test1920 144 160 176
  test1920_block_9
  test1920_block_10))))
  (interval_append test1920 176 272 358
  (interval_append test1920 176 224 272
  (interval_append test1920 176 192 224
  test1920_block_11
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13))
  (interval_append test1920 224 240 272
  test1920_block_14
  (interval_append test1920 240 256 272
  test1920_block_15
  test1920_block_16)))
  (interval_append test1920 272 320 358
  (interval_append test1920 272 288 320
  test1920_block_17
  (interval_append test1920 288 304 320
  test1920_block_18
  test1920_block_19))
  (interval_append test1920 320 336 358
  test1920_block_20
  (interval_append test1920 336 352 358
  test1920_block_21
  test1920_block_22)))))
theorem nodeInterval1920 : Interval nodeTest 1920 2278 := by
  intro i hlo hhi
  have h := test1920_complete (i-1920) (Nat.zero_le _) (by omega)
  simpa only [test1920, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0669
