module
prelude
public import RootedSubsumedForest0655Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0655
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_block_8 : Interval test0 128 144 :=
  interval_of_check test0 128 16 (by decide +kernel)

theorem test0_block_9 : Interval test0 144 160 :=
  interval_of_check test0 144 16 (by decide +kernel)

theorem test0_block_10 : Interval test0 160 176 :=
  interval_of_check test0 160 16 (by decide +kernel)

theorem test0_block_11 : Interval test0 176 192 :=
  interval_of_check test0 176 16 (by decide +kernel)

theorem test0_block_12 : Interval test0 192 208 :=
  interval_of_check test0 192 16 (by decide +kernel)

theorem test0_block_13 : Interval test0 208 224 :=
  interval_of_check test0 208 16 (by decide +kernel)

theorem test0_block_14 : Interval test0 224 240 :=
  interval_of_check test0 224 16 (by decide +kernel)

theorem test0_block_15 : Interval test0 240 256 :=
  interval_of_check test0 240 16 (by decide +kernel)

theorem test0_block_16 : Interval test0 256 272 :=
  interval_of_check test0 256 16 (by decide +kernel)

theorem test0_block_17 : Interval test0 272 288 :=
  interval_of_check test0 272 16 (by decide +kernel)

theorem test0_block_18 : Interval test0 288 304 :=
  interval_of_check test0 288 16 (by decide +kernel)

theorem test0_block_19 : Interval test0 304 320 :=
  interval_of_check test0 304 16 (by decide +kernel)

theorem test0_block_20 : Interval test0 320 336 :=
  interval_of_check test0 320 16 (by decide +kernel)

theorem test0_block_21 : Interval test0 336 352 :=
  interval_of_check test0 336 16 (by decide +kernel)

theorem test0_block_22 : Interval test0 352 368 :=
  interval_of_check test0 352 16 (by decide +kernel)

theorem test0_block_23 : Interval test0 368 376 :=
  interval_of_check test0 368 8 (by decide +kernel)

theorem test0_complete : Interval test0 0 376 :=
  (interval_append test0 0 192 376
  (interval_append test0 0 96 192
  (interval_append test0 0 48 96
  (interval_append test0 0 16 48
  test0_block_0
  (interval_append test0 16 32 48
  test0_block_1
  test0_block_2))
  (interval_append test0 48 64 96
  test0_block_3
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)))
  (interval_append test0 96 144 192
  (interval_append test0 96 112 144
  test0_block_6
  (interval_append test0 112 128 144
  test0_block_7
  test0_block_8))
  (interval_append test0 144 160 192
  test0_block_9
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11))))
  (interval_append test0 192 288 376
  (interval_append test0 192 240 288
  (interval_append test0 192 208 240
  test0_block_12
  (interval_append test0 208 224 240
  test0_block_13
  test0_block_14))
  (interval_append test0 240 256 288
  test0_block_15
  (interval_append test0 256 272 288
  test0_block_16
  test0_block_17)))
  (interval_append test0 288 336 376
  (interval_append test0 288 304 336
  test0_block_18
  (interval_append test0 304 320 336
  test0_block_19
  test0_block_20))
  (interval_append test0 336 352 376
  test0_block_21
  (interval_append test0 352 368 376
  test0_block_22
  test0_block_23)))))
theorem nodeInterval0 : Interval nodeTest 0 376 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0655
