module
prelude
public import RootedSubsumedForest0321Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test22400 (i : Nat) := nodeTest (i+22400)
theorem test22400_block_0 : Interval test22400 0 16 :=
  interval_of_check test22400 0 16 (by decide +kernel)

theorem test22400_block_1 : Interval test22400 16 32 :=
  interval_of_check test22400 16 16 (by decide +kernel)

theorem test22400_block_2 : Interval test22400 32 48 :=
  interval_of_check test22400 32 16 (by decide +kernel)

theorem test22400_block_3 : Interval test22400 48 64 :=
  interval_of_check test22400 48 16 (by decide +kernel)

theorem test22400_block_4 : Interval test22400 64 80 :=
  interval_of_check test22400 64 16 (by decide +kernel)

theorem test22400_block_5 : Interval test22400 80 96 :=
  interval_of_check test22400 80 16 (by decide +kernel)

theorem test22400_block_6 : Interval test22400 96 112 :=
  interval_of_check test22400 96 16 (by decide +kernel)

theorem test22400_block_7 : Interval test22400 112 128 :=
  interval_of_check test22400 112 16 (by decide +kernel)

theorem test22400_block_8 : Interval test22400 128 144 :=
  interval_of_check test22400 128 16 (by decide +kernel)

theorem test22400_block_9 : Interval test22400 144 160 :=
  interval_of_check test22400 144 16 (by decide +kernel)

theorem test22400_block_10 : Interval test22400 160 176 :=
  interval_of_check test22400 160 16 (by decide +kernel)

theorem test22400_block_11 : Interval test22400 176 192 :=
  interval_of_check test22400 176 16 (by decide +kernel)

theorem test22400_block_12 : Interval test22400 192 208 :=
  interval_of_check test22400 192 16 (by decide +kernel)

theorem test22400_block_13 : Interval test22400 208 224 :=
  interval_of_check test22400 208 16 (by decide +kernel)

theorem test22400_block_14 : Interval test22400 224 240 :=
  interval_of_check test22400 224 16 (by decide +kernel)

theorem test22400_block_15 : Interval test22400 240 256 :=
  interval_of_check test22400 240 16 (by decide +kernel)

theorem test22400_block_16 : Interval test22400 256 272 :=
  interval_of_check test22400 256 16 (by decide +kernel)

theorem test22400_block_17 : Interval test22400 272 288 :=
  interval_of_check test22400 272 16 (by decide +kernel)

theorem test22400_block_18 : Interval test22400 288 304 :=
  interval_of_check test22400 288 16 (by decide +kernel)

theorem test22400_block_19 : Interval test22400 304 320 :=
  interval_of_check test22400 304 16 (by decide +kernel)

theorem test22400_block_20 : Interval test22400 320 336 :=
  interval_of_check test22400 320 16 (by decide +kernel)

theorem test22400_block_21 : Interval test22400 336 337 :=
  interval_of_check test22400 336 1 (by decide +kernel)

theorem test22400_complete : Interval test22400 0 337 :=
  (interval_append test22400 0 176 337
  (interval_append test22400 0 80 176
  (interval_append test22400 0 32 80
  (interval_append test22400 0 16 32
  test22400_block_0
  test22400_block_1)
  (interval_append test22400 32 48 80
  test22400_block_2
  (interval_append test22400 48 64 80
  test22400_block_3
  test22400_block_4)))
  (interval_append test22400 80 128 176
  (interval_append test22400 80 96 128
  test22400_block_5
  (interval_append test22400 96 112 128
  test22400_block_6
  test22400_block_7))
  (interval_append test22400 128 144 176
  test22400_block_8
  (interval_append test22400 144 160 176
  test22400_block_9
  test22400_block_10))))
  (interval_append test22400 176 256 337
  (interval_append test22400 176 208 256
  (interval_append test22400 176 192 208
  test22400_block_11
  test22400_block_12)
  (interval_append test22400 208 224 256
  test22400_block_13
  (interval_append test22400 224 240 256
  test22400_block_14
  test22400_block_15)))
  (interval_append test22400 256 304 337
  (interval_append test22400 256 272 304
  test22400_block_16
  (interval_append test22400 272 288 304
  test22400_block_17
  test22400_block_18))
  (interval_append test22400 304 320 337
  test22400_block_19
  (interval_append test22400 320 336 337
  test22400_block_20
  test22400_block_21)))))
theorem nodeInterval22400 : Interval nodeTest 22400 22737 := by
  intro i hlo hhi
  have h := test22400_complete (i-22400) (Nat.zero_le _) (by omega)
  simpa only [test22400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
