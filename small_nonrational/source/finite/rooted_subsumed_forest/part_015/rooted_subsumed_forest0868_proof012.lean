module
prelude
public import RootedSubsumedForest0868Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test7680 (i : Nat) := nodeTest (i+7680)
theorem test7680_block_0 : Interval test7680 0 16 :=
  interval_of_check test7680 0 16 (by decide +kernel)

theorem test7680_block_1 : Interval test7680 16 32 :=
  interval_of_check test7680 16 16 (by decide +kernel)

theorem test7680_block_2 : Interval test7680 32 48 :=
  interval_of_check test7680 32 16 (by decide +kernel)

theorem test7680_block_3 : Interval test7680 48 64 :=
  interval_of_check test7680 48 16 (by decide +kernel)

theorem test7680_block_4 : Interval test7680 64 80 :=
  interval_of_check test7680 64 16 (by decide +kernel)

theorem test7680_block_5 : Interval test7680 80 96 :=
  interval_of_check test7680 80 16 (by decide +kernel)

theorem test7680_block_6 : Interval test7680 96 112 :=
  interval_of_check test7680 96 16 (by decide +kernel)

theorem test7680_block_7 : Interval test7680 112 128 :=
  interval_of_check test7680 112 16 (by decide +kernel)

theorem test7680_block_8 : Interval test7680 128 144 :=
  interval_of_check test7680 128 16 (by decide +kernel)

theorem test7680_block_9 : Interval test7680 144 160 :=
  interval_of_check test7680 144 16 (by decide +kernel)

theorem test7680_block_10 : Interval test7680 160 176 :=
  interval_of_check test7680 160 16 (by decide +kernel)

theorem test7680_block_11 : Interval test7680 176 192 :=
  interval_of_check test7680 176 16 (by decide +kernel)

theorem test7680_block_12 : Interval test7680 192 208 :=
  interval_of_check test7680 192 16 (by decide +kernel)

theorem test7680_block_13 : Interval test7680 208 224 :=
  interval_of_check test7680 208 16 (by decide +kernel)

theorem test7680_block_14 : Interval test7680 224 240 :=
  interval_of_check test7680 224 16 (by decide +kernel)

theorem test7680_block_15 : Interval test7680 240 256 :=
  interval_of_check test7680 240 16 (by decide +kernel)

theorem test7680_block_16 : Interval test7680 256 272 :=
  interval_of_check test7680 256 16 (by decide +kernel)

theorem test7680_block_17 : Interval test7680 272 288 :=
  interval_of_check test7680 272 16 (by decide +kernel)

theorem test7680_block_18 : Interval test7680 288 304 :=
  interval_of_check test7680 288 16 (by decide +kernel)

theorem test7680_block_19 : Interval test7680 304 320 :=
  interval_of_check test7680 304 16 (by decide +kernel)

theorem test7680_block_20 : Interval test7680 320 336 :=
  interval_of_check test7680 320 16 (by decide +kernel)

theorem test7680_block_21 : Interval test7680 336 352 :=
  interval_of_check test7680 336 16 (by decide +kernel)

theorem test7680_block_22 : Interval test7680 352 368 :=
  interval_of_check test7680 352 16 (by decide +kernel)

theorem test7680_block_23 : Interval test7680 368 377 :=
  interval_of_check test7680 368 9 (by decide +kernel)

theorem test7680_complete : Interval test7680 0 377 :=
  (interval_append test7680 0 192 377
  (interval_append test7680 0 96 192
  (interval_append test7680 0 48 96
  (interval_append test7680 0 16 48
  test7680_block_0
  (interval_append test7680 16 32 48
  test7680_block_1
  test7680_block_2))
  (interval_append test7680 48 64 96
  test7680_block_3
  (interval_append test7680 64 80 96
  test7680_block_4
  test7680_block_5)))
  (interval_append test7680 96 144 192
  (interval_append test7680 96 112 144
  test7680_block_6
  (interval_append test7680 112 128 144
  test7680_block_7
  test7680_block_8))
  (interval_append test7680 144 160 192
  test7680_block_9
  (interval_append test7680 160 176 192
  test7680_block_10
  test7680_block_11))))
  (interval_append test7680 192 288 377
  (interval_append test7680 192 240 288
  (interval_append test7680 192 208 240
  test7680_block_12
  (interval_append test7680 208 224 240
  test7680_block_13
  test7680_block_14))
  (interval_append test7680 240 256 288
  test7680_block_15
  (interval_append test7680 256 272 288
  test7680_block_16
  test7680_block_17)))
  (interval_append test7680 288 336 377
  (interval_append test7680 288 304 336
  test7680_block_18
  (interval_append test7680 304 320 336
  test7680_block_19
  test7680_block_20))
  (interval_append test7680 336 352 377
  test7680_block_21
  (interval_append test7680 352 368 377
  test7680_block_22
  test7680_block_23)))))
theorem nodeInterval7680 : Interval nodeTest 7680 8057 := by
  intro i hlo hhi
  have h := test7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [test7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0868
