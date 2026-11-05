module
prelude
public import RootedSubsumedForest0352Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test15360 (i : Nat) := nodeTest (i+15360)
theorem test15360_block_0 : Interval test15360 0 16 :=
  interval_of_check test15360 0 16 (by decide +kernel)

theorem test15360_block_1 : Interval test15360 16 32 :=
  interval_of_check test15360 16 16 (by decide +kernel)

theorem test15360_block_2 : Interval test15360 32 48 :=
  interval_of_check test15360 32 16 (by decide +kernel)

theorem test15360_block_3 : Interval test15360 48 64 :=
  interval_of_check test15360 48 16 (by decide +kernel)

theorem test15360_block_4 : Interval test15360 64 80 :=
  interval_of_check test15360 64 16 (by decide +kernel)

theorem test15360_block_5 : Interval test15360 80 96 :=
  interval_of_check test15360 80 16 (by decide +kernel)

theorem test15360_block_6 : Interval test15360 96 112 :=
  interval_of_check test15360 96 16 (by decide +kernel)

theorem test15360_block_7 : Interval test15360 112 128 :=
  interval_of_check test15360 112 16 (by decide +kernel)

theorem test15360_block_8 : Interval test15360 128 144 :=
  interval_of_check test15360 128 16 (by decide +kernel)

theorem test15360_block_9 : Interval test15360 144 160 :=
  interval_of_check test15360 144 16 (by decide +kernel)

theorem test15360_block_10 : Interval test15360 160 176 :=
  interval_of_check test15360 160 16 (by decide +kernel)

theorem test15360_block_11 : Interval test15360 176 192 :=
  interval_of_check test15360 176 16 (by decide +kernel)

theorem test15360_block_12 : Interval test15360 192 208 :=
  interval_of_check test15360 192 16 (by decide +kernel)

theorem test15360_block_13 : Interval test15360 208 224 :=
  interval_of_check test15360 208 16 (by decide +kernel)

theorem test15360_block_14 : Interval test15360 224 240 :=
  interval_of_check test15360 224 16 (by decide +kernel)

theorem test15360_block_15 : Interval test15360 240 256 :=
  interval_of_check test15360 240 16 (by decide +kernel)

theorem test15360_block_16 : Interval test15360 256 272 :=
  interval_of_check test15360 256 16 (by decide +kernel)

theorem test15360_block_17 : Interval test15360 272 288 :=
  interval_of_check test15360 272 16 (by decide +kernel)

theorem test15360_block_18 : Interval test15360 288 304 :=
  interval_of_check test15360 288 16 (by decide +kernel)

theorem test15360_block_19 : Interval test15360 304 320 :=
  interval_of_check test15360 304 16 (by decide +kernel)

theorem test15360_block_20 : Interval test15360 320 336 :=
  interval_of_check test15360 320 16 (by decide +kernel)

theorem test15360_block_21 : Interval test15360 336 337 :=
  interval_of_check test15360 336 1 (by decide +kernel)

theorem test15360_complete : Interval test15360 0 337 :=
  (interval_append test15360 0 176 337
  (interval_append test15360 0 80 176
  (interval_append test15360 0 32 80
  (interval_append test15360 0 16 32
  test15360_block_0
  test15360_block_1)
  (interval_append test15360 32 48 80
  test15360_block_2
  (interval_append test15360 48 64 80
  test15360_block_3
  test15360_block_4)))
  (interval_append test15360 80 128 176
  (interval_append test15360 80 96 128
  test15360_block_5
  (interval_append test15360 96 112 128
  test15360_block_6
  test15360_block_7))
  (interval_append test15360 128 144 176
  test15360_block_8
  (interval_append test15360 144 160 176
  test15360_block_9
  test15360_block_10))))
  (interval_append test15360 176 256 337
  (interval_append test15360 176 208 256
  (interval_append test15360 176 192 208
  test15360_block_11
  test15360_block_12)
  (interval_append test15360 208 224 256
  test15360_block_13
  (interval_append test15360 224 240 256
  test15360_block_14
  test15360_block_15)))
  (interval_append test15360 256 304 337
  (interval_append test15360 256 272 304
  test15360_block_16
  (interval_append test15360 272 288 304
  test15360_block_17
  test15360_block_18))
  (interval_append test15360 304 320 337
  test15360_block_19
  (interval_append test15360 320 336 337
  test15360_block_20
  test15360_block_21)))))
theorem nodeInterval15360 : Interval nodeTest 15360 15697 := by
  intro i hlo hhi
  have h := test15360_complete (i-15360) (Nat.zero_le _) (by omega)
  simpa only [test15360, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
