module
prelude
public import SmallSubsumedForest08Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test61440 (i : Nat) := nodeTest (i+61440)
theorem test61440_block_0 : Interval test61440 0 16 :=
  interval_of_check test61440 0 16 (by decide +kernel)

theorem test61440_block_1 : Interval test61440 16 32 :=
  interval_of_check test61440 16 16 (by decide +kernel)

theorem test61440_block_2 : Interval test61440 32 48 :=
  interval_of_check test61440 32 16 (by decide +kernel)

theorem test61440_block_3 : Interval test61440 48 64 :=
  interval_of_check test61440 48 16 (by decide +kernel)

theorem test61440_block_4 : Interval test61440 64 80 :=
  interval_of_check test61440 64 16 (by decide +kernel)

theorem test61440_block_5 : Interval test61440 80 96 :=
  interval_of_check test61440 80 16 (by decide +kernel)

theorem test61440_block_6 : Interval test61440 96 112 :=
  interval_of_check test61440 96 16 (by decide +kernel)

theorem test61440_block_7 : Interval test61440 112 128 :=
  interval_of_check test61440 112 16 (by decide +kernel)

theorem test61440_block_8 : Interval test61440 128 144 :=
  interval_of_check test61440 128 16 (by decide +kernel)

theorem test61440_block_9 : Interval test61440 144 160 :=
  interval_of_check test61440 144 16 (by decide +kernel)

theorem test61440_block_10 : Interval test61440 160 176 :=
  interval_of_check test61440 160 16 (by decide +kernel)

theorem test61440_block_11 : Interval test61440 176 192 :=
  interval_of_check test61440 176 16 (by decide +kernel)

theorem test61440_block_12 : Interval test61440 192 208 :=
  interval_of_check test61440 192 16 (by decide +kernel)

theorem test61440_block_13 : Interval test61440 208 224 :=
  interval_of_check test61440 208 16 (by decide +kernel)

theorem test61440_block_14 : Interval test61440 224 240 :=
  interval_of_check test61440 224 16 (by decide +kernel)

theorem test61440_block_15 : Interval test61440 240 256 :=
  interval_of_check test61440 240 16 (by decide +kernel)

theorem test61440_block_16 : Interval test61440 256 272 :=
  interval_of_check test61440 256 16 (by decide +kernel)

theorem test61440_block_17 : Interval test61440 272 288 :=
  interval_of_check test61440 272 16 (by decide +kernel)

theorem test61440_block_18 : Interval test61440 288 304 :=
  interval_of_check test61440 288 16 (by decide +kernel)

theorem test61440_block_19 : Interval test61440 304 313 :=
  interval_of_check test61440 304 9 (by decide +kernel)

theorem test61440_complete : Interval test61440 0 313 :=
  (interval_append test61440 0 160 313
  (interval_append test61440 0 80 160
  (interval_append test61440 0 32 80
  (interval_append test61440 0 16 32
  test61440_block_0
  test61440_block_1)
  (interval_append test61440 32 48 80
  test61440_block_2
  (interval_append test61440 48 64 80
  test61440_block_3
  test61440_block_4)))
  (interval_append test61440 80 112 160
  (interval_append test61440 80 96 112
  test61440_block_5
  test61440_block_6)
  (interval_append test61440 112 128 160
  test61440_block_7
  (interval_append test61440 128 144 160
  test61440_block_8
  test61440_block_9))))
  (interval_append test61440 160 240 313
  (interval_append test61440 160 192 240
  (interval_append test61440 160 176 192
  test61440_block_10
  test61440_block_11)
  (interval_append test61440 192 208 240
  test61440_block_12
  (interval_append test61440 208 224 240
  test61440_block_13
  test61440_block_14)))
  (interval_append test61440 240 272 313
  (interval_append test61440 240 256 272
  test61440_block_15
  test61440_block_16)
  (interval_append test61440 272 288 313
  test61440_block_17
  (interval_append test61440 288 304 313
  test61440_block_18
  test61440_block_19)))))
theorem nodeInterval61440 : Interval nodeTest 61440 61753 := by
  intro i hlo hhi
  have h := test61440_complete (i-61440) (Nat.zero_le _) (by omega)
  simpa only [test61440, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest08
