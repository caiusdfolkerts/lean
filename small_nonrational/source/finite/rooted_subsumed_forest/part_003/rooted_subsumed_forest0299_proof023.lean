module
prelude
public import RootedSubsumedForest0299Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test14720 (i : Nat) := nodeTest (i+14720)
theorem test14720_block_0 : Interval test14720 0 16 :=
  interval_of_check test14720 0 16 (by decide +kernel)

theorem test14720_block_1 : Interval test14720 16 32 :=
  interval_of_check test14720 16 16 (by decide +kernel)

theorem test14720_block_2 : Interval test14720 32 48 :=
  interval_of_check test14720 32 16 (by decide +kernel)

theorem test14720_block_3 : Interval test14720 48 64 :=
  interval_of_check test14720 48 16 (by decide +kernel)

theorem test14720_block_4 : Interval test14720 64 80 :=
  interval_of_check test14720 64 16 (by decide +kernel)

theorem test14720_block_5 : Interval test14720 80 96 :=
  interval_of_check test14720 80 16 (by decide +kernel)

theorem test14720_block_6 : Interval test14720 96 112 :=
  interval_of_check test14720 96 16 (by decide +kernel)

theorem test14720_block_7 : Interval test14720 112 128 :=
  interval_of_check test14720 112 16 (by decide +kernel)

theorem test14720_block_8 : Interval test14720 128 144 :=
  interval_of_check test14720 128 16 (by decide +kernel)

theorem test14720_block_9 : Interval test14720 144 160 :=
  interval_of_check test14720 144 16 (by decide +kernel)

theorem test14720_block_10 : Interval test14720 160 176 :=
  interval_of_check test14720 160 16 (by decide +kernel)

theorem test14720_block_11 : Interval test14720 176 192 :=
  interval_of_check test14720 176 16 (by decide +kernel)

theorem test14720_block_12 : Interval test14720 192 208 :=
  interval_of_check test14720 192 16 (by decide +kernel)

theorem test14720_block_13 : Interval test14720 208 224 :=
  interval_of_check test14720 208 16 (by decide +kernel)

theorem test14720_block_14 : Interval test14720 224 240 :=
  interval_of_check test14720 224 16 (by decide +kernel)

theorem test14720_block_15 : Interval test14720 240 256 :=
  interval_of_check test14720 240 16 (by decide +kernel)

theorem test14720_block_16 : Interval test14720 256 272 :=
  interval_of_check test14720 256 16 (by decide +kernel)

theorem test14720_block_17 : Interval test14720 272 288 :=
  interval_of_check test14720 272 16 (by decide +kernel)

theorem test14720_block_18 : Interval test14720 288 304 :=
  interval_of_check test14720 288 16 (by decide +kernel)

theorem test14720_block_19 : Interval test14720 304 320 :=
  interval_of_check test14720 304 16 (by decide +kernel)

theorem test14720_block_20 : Interval test14720 320 336 :=
  interval_of_check test14720 320 16 (by decide +kernel)

theorem test14720_block_21 : Interval test14720 336 352 :=
  interval_of_check test14720 336 16 (by decide +kernel)

theorem test14720_block_22 : Interval test14720 352 368 :=
  interval_of_check test14720 352 16 (by decide +kernel)

theorem test14720_complete : Interval test14720 0 368 :=
  (interval_append test14720 0 176 368
  (interval_append test14720 0 80 176
  (interval_append test14720 0 32 80
  (interval_append test14720 0 16 32
  test14720_block_0
  test14720_block_1)
  (interval_append test14720 32 48 80
  test14720_block_2
  (interval_append test14720 48 64 80
  test14720_block_3
  test14720_block_4)))
  (interval_append test14720 80 128 176
  (interval_append test14720 80 96 128
  test14720_block_5
  (interval_append test14720 96 112 128
  test14720_block_6
  test14720_block_7))
  (interval_append test14720 128 144 176
  test14720_block_8
  (interval_append test14720 144 160 176
  test14720_block_9
  test14720_block_10))))
  (interval_append test14720 176 272 368
  (interval_append test14720 176 224 272
  (interval_append test14720 176 192 224
  test14720_block_11
  (interval_append test14720 192 208 224
  test14720_block_12
  test14720_block_13))
  (interval_append test14720 224 240 272
  test14720_block_14
  (interval_append test14720 240 256 272
  test14720_block_15
  test14720_block_16)))
  (interval_append test14720 272 320 368
  (interval_append test14720 272 288 320
  test14720_block_17
  (interval_append test14720 288 304 320
  test14720_block_18
  test14720_block_19))
  (interval_append test14720 320 336 368
  test14720_block_20
  (interval_append test14720 336 352 368
  test14720_block_21
  test14720_block_22)))))
theorem nodeInterval14720 : Interval nodeTest 14720 15088 := by
  intro i hlo hhi
  have h := test14720_complete (i-14720) (Nat.zero_le _) (by omega)
  simpa only [test14720, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0299
