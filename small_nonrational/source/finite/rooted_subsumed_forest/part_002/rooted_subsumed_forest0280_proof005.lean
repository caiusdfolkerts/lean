module
prelude
public import RootedSubsumedForest0280Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0280
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3200 (i : Nat) := nodeTest (i+3200)
theorem test3200_block_0 : Interval test3200 0 16 :=
  interval_of_check test3200 0 16 (by decide +kernel)

theorem test3200_block_1 : Interval test3200 16 32 :=
  interval_of_check test3200 16 16 (by decide +kernel)

theorem test3200_block_2 : Interval test3200 32 48 :=
  interval_of_check test3200 32 16 (by decide +kernel)

theorem test3200_block_3 : Interval test3200 48 64 :=
  interval_of_check test3200 48 16 (by decide +kernel)

theorem test3200_block_4 : Interval test3200 64 80 :=
  interval_of_check test3200 64 16 (by decide +kernel)

theorem test3200_block_5 : Interval test3200 80 96 :=
  interval_of_check test3200 80 16 (by decide +kernel)

theorem test3200_block_6 : Interval test3200 96 112 :=
  interval_of_check test3200 96 16 (by decide +kernel)

theorem test3200_block_7 : Interval test3200 112 128 :=
  interval_of_check test3200 112 16 (by decide +kernel)

theorem test3200_block_8 : Interval test3200 128 144 :=
  interval_of_check test3200 128 16 (by decide +kernel)

theorem test3200_block_9 : Interval test3200 144 160 :=
  interval_of_check test3200 144 16 (by decide +kernel)

theorem test3200_block_10 : Interval test3200 160 176 :=
  interval_of_check test3200 160 16 (by decide +kernel)

theorem test3200_block_11 : Interval test3200 176 192 :=
  interval_of_check test3200 176 16 (by decide +kernel)

theorem test3200_block_12 : Interval test3200 192 208 :=
  interval_of_check test3200 192 16 (by decide +kernel)

theorem test3200_block_13 : Interval test3200 208 224 :=
  interval_of_check test3200 208 16 (by decide +kernel)

theorem test3200_block_14 : Interval test3200 224 240 :=
  interval_of_check test3200 224 16 (by decide +kernel)

theorem test3200_block_15 : Interval test3200 240 256 :=
  interval_of_check test3200 240 16 (by decide +kernel)

theorem test3200_block_16 : Interval test3200 256 272 :=
  interval_of_check test3200 256 16 (by decide +kernel)

theorem test3200_block_17 : Interval test3200 272 288 :=
  interval_of_check test3200 272 16 (by decide +kernel)

theorem test3200_block_18 : Interval test3200 288 304 :=
  interval_of_check test3200 288 16 (by decide +kernel)

theorem test3200_block_19 : Interval test3200 304 320 :=
  interval_of_check test3200 304 16 (by decide +kernel)

theorem test3200_block_20 : Interval test3200 320 336 :=
  interval_of_check test3200 320 16 (by decide +kernel)

theorem test3200_block_21 : Interval test3200 336 352 :=
  interval_of_check test3200 336 16 (by decide +kernel)

theorem test3200_block_22 : Interval test3200 352 368 :=
  interval_of_check test3200 352 16 (by decide +kernel)

theorem test3200_block_23 : Interval test3200 368 384 :=
  interval_of_check test3200 368 16 (by decide +kernel)

theorem test3200_block_24 : Interval test3200 384 400 :=
  interval_of_check test3200 384 16 (by decide +kernel)

theorem test3200_block_25 : Interval test3200 400 404 :=
  interval_of_check test3200 400 4 (by decide +kernel)

theorem test3200_complete : Interval test3200 0 404 :=
  (interval_append test3200 0 208 404
  (interval_append test3200 0 96 208
  (interval_append test3200 0 48 96
  (interval_append test3200 0 16 48
  test3200_block_0
  (interval_append test3200 16 32 48
  test3200_block_1
  test3200_block_2))
  (interval_append test3200 48 64 96
  test3200_block_3
  (interval_append test3200 64 80 96
  test3200_block_4
  test3200_block_5)))
  (interval_append test3200 96 144 208
  (interval_append test3200 96 112 144
  test3200_block_6
  (interval_append test3200 112 128 144
  test3200_block_7
  test3200_block_8))
  (interval_append test3200 144 176 208
  (interval_append test3200 144 160 176
  test3200_block_9
  test3200_block_10)
  (interval_append test3200 176 192 208
  test3200_block_11
  test3200_block_12))))
  (interval_append test3200 208 304 404
  (interval_append test3200 208 256 304
  (interval_append test3200 208 224 256
  test3200_block_13
  (interval_append test3200 224 240 256
  test3200_block_14
  test3200_block_15))
  (interval_append test3200 256 272 304
  test3200_block_16
  (interval_append test3200 272 288 304
  test3200_block_17
  test3200_block_18)))
  (interval_append test3200 304 352 404
  (interval_append test3200 304 320 352
  test3200_block_19
  (interval_append test3200 320 336 352
  test3200_block_20
  test3200_block_21))
  (interval_append test3200 352 384 404
  (interval_append test3200 352 368 384
  test3200_block_22
  test3200_block_23)
  (interval_append test3200 384 400 404
  test3200_block_24
  test3200_block_25)))))
theorem nodeInterval3200 : Interval nodeTest 3200 3604 := by
  intro i hlo hhi
  have h := test3200_complete (i-3200) (Nat.zero_le _) (by omega)
  simpa only [test3200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0280
