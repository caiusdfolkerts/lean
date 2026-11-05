module
prelude
public import RootedSubsumedForest0320Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test46720 (i : Nat) := nodeTest (i+46720)
theorem test46720_block_0 : Interval test46720 0 16 :=
  interval_of_check test46720 0 16 (by decide +kernel)

theorem test46720_block_1 : Interval test46720 16 32 :=
  interval_of_check test46720 16 16 (by decide +kernel)

theorem test46720_block_2 : Interval test46720 32 48 :=
  interval_of_check test46720 32 16 (by decide +kernel)

theorem test46720_block_3 : Interval test46720 48 64 :=
  interval_of_check test46720 48 16 (by decide +kernel)

theorem test46720_block_4 : Interval test46720 64 80 :=
  interval_of_check test46720 64 16 (by decide +kernel)

theorem test46720_block_5 : Interval test46720 80 96 :=
  interval_of_check test46720 80 16 (by decide +kernel)

theorem test46720_block_6 : Interval test46720 96 112 :=
  interval_of_check test46720 96 16 (by decide +kernel)

theorem test46720_block_7 : Interval test46720 112 128 :=
  interval_of_check test46720 112 16 (by decide +kernel)

theorem test46720_block_8 : Interval test46720 128 144 :=
  interval_of_check test46720 128 16 (by decide +kernel)

theorem test46720_block_9 : Interval test46720 144 160 :=
  interval_of_check test46720 144 16 (by decide +kernel)

theorem test46720_block_10 : Interval test46720 160 176 :=
  interval_of_check test46720 160 16 (by decide +kernel)

theorem test46720_block_11 : Interval test46720 176 192 :=
  interval_of_check test46720 176 16 (by decide +kernel)

theorem test46720_block_12 : Interval test46720 192 208 :=
  interval_of_check test46720 192 16 (by decide +kernel)

theorem test46720_block_13 : Interval test46720 208 224 :=
  interval_of_check test46720 208 16 (by decide +kernel)

theorem test46720_block_14 : Interval test46720 224 240 :=
  interval_of_check test46720 224 16 (by decide +kernel)

theorem test46720_block_15 : Interval test46720 240 256 :=
  interval_of_check test46720 240 16 (by decide +kernel)

theorem test46720_block_16 : Interval test46720 256 272 :=
  interval_of_check test46720 256 16 (by decide +kernel)

theorem test46720_block_17 : Interval test46720 272 288 :=
  interval_of_check test46720 272 16 (by decide +kernel)

theorem test46720_block_18 : Interval test46720 288 304 :=
  interval_of_check test46720 288 16 (by decide +kernel)

theorem test46720_block_19 : Interval test46720 304 320 :=
  interval_of_check test46720 304 16 (by decide +kernel)

theorem test46720_block_20 : Interval test46720 320 336 :=
  interval_of_check test46720 320 16 (by decide +kernel)

theorem test46720_block_21 : Interval test46720 336 352 :=
  interval_of_check test46720 336 16 (by decide +kernel)

theorem test46720_block_22 : Interval test46720 352 368 :=
  interval_of_check test46720 352 16 (by decide +kernel)

theorem test46720_block_23 : Interval test46720 368 384 :=
  interval_of_check test46720 368 16 (by decide +kernel)

theorem test46720_block_24 : Interval test46720 384 400 :=
  interval_of_check test46720 384 16 (by decide +kernel)

theorem test46720_block_25 : Interval test46720 400 402 :=
  interval_of_check test46720 400 2 (by decide +kernel)

theorem test46720_complete : Interval test46720 0 402 :=
  (interval_append test46720 0 208 402
  (interval_append test46720 0 96 208
  (interval_append test46720 0 48 96
  (interval_append test46720 0 16 48
  test46720_block_0
  (interval_append test46720 16 32 48
  test46720_block_1
  test46720_block_2))
  (interval_append test46720 48 64 96
  test46720_block_3
  (interval_append test46720 64 80 96
  test46720_block_4
  test46720_block_5)))
  (interval_append test46720 96 144 208
  (interval_append test46720 96 112 144
  test46720_block_6
  (interval_append test46720 112 128 144
  test46720_block_7
  test46720_block_8))
  (interval_append test46720 144 176 208
  (interval_append test46720 144 160 176
  test46720_block_9
  test46720_block_10)
  (interval_append test46720 176 192 208
  test46720_block_11
  test46720_block_12))))
  (interval_append test46720 208 304 402
  (interval_append test46720 208 256 304
  (interval_append test46720 208 224 256
  test46720_block_13
  (interval_append test46720 224 240 256
  test46720_block_14
  test46720_block_15))
  (interval_append test46720 256 272 304
  test46720_block_16
  (interval_append test46720 272 288 304
  test46720_block_17
  test46720_block_18)))
  (interval_append test46720 304 352 402
  (interval_append test46720 304 320 352
  test46720_block_19
  (interval_append test46720 320 336 352
  test46720_block_20
  test46720_block_21))
  (interval_append test46720 352 384 402
  (interval_append test46720 352 368 384
  test46720_block_22
  test46720_block_23)
  (interval_append test46720 384 400 402
  test46720_block_24
  test46720_block_25)))))
theorem nodeInterval46720 : Interval nodeTest 46720 47122 := by
  intro i hlo hhi
  have h := test46720_complete (i-46720) (Nat.zero_le _) (by omega)
  simpa only [test46720, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0320
