module
prelude
public import SmallSubsumedForest20Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test17280 (i : Nat) := nodeTest (i+17280)
theorem test17280_block_0 : Interval test17280 0 16 :=
  interval_of_check test17280 0 16 (by decide +kernel)

theorem test17280_block_1 : Interval test17280 16 32 :=
  interval_of_check test17280 16 16 (by decide +kernel)

theorem test17280_block_2 : Interval test17280 32 48 :=
  interval_of_check test17280 32 16 (by decide +kernel)

theorem test17280_block_3 : Interval test17280 48 64 :=
  interval_of_check test17280 48 16 (by decide +kernel)

theorem test17280_block_4 : Interval test17280 64 80 :=
  interval_of_check test17280 64 16 (by decide +kernel)

theorem test17280_block_5 : Interval test17280 80 96 :=
  interval_of_check test17280 80 16 (by decide +kernel)

theorem test17280_block_6 : Interval test17280 96 112 :=
  interval_of_check test17280 96 16 (by decide +kernel)

theorem test17280_block_7 : Interval test17280 112 128 :=
  interval_of_check test17280 112 16 (by decide +kernel)

theorem test17280_block_8 : Interval test17280 128 144 :=
  interval_of_check test17280 128 16 (by decide +kernel)

theorem test17280_block_9 : Interval test17280 144 160 :=
  interval_of_check test17280 144 16 (by decide +kernel)

theorem test17280_block_10 : Interval test17280 160 176 :=
  interval_of_check test17280 160 16 (by decide +kernel)

theorem test17280_block_11 : Interval test17280 176 192 :=
  interval_of_check test17280 176 16 (by decide +kernel)

theorem test17280_block_12 : Interval test17280 192 208 :=
  interval_of_check test17280 192 16 (by decide +kernel)

theorem test17280_block_13 : Interval test17280 208 224 :=
  interval_of_check test17280 208 16 (by decide +kernel)

theorem test17280_block_14 : Interval test17280 224 240 :=
  interval_of_check test17280 224 16 (by decide +kernel)

theorem test17280_block_15 : Interval test17280 240 256 :=
  interval_of_check test17280 240 16 (by decide +kernel)

theorem test17280_block_16 : Interval test17280 256 272 :=
  interval_of_check test17280 256 16 (by decide +kernel)

theorem test17280_block_17 : Interval test17280 272 288 :=
  interval_of_check test17280 272 16 (by decide +kernel)

theorem test17280_block_18 : Interval test17280 288 304 :=
  interval_of_check test17280 288 16 (by decide +kernel)

theorem test17280_block_19 : Interval test17280 304 320 :=
  interval_of_check test17280 304 16 (by decide +kernel)

theorem test17280_block_20 : Interval test17280 320 336 :=
  interval_of_check test17280 320 16 (by decide +kernel)

theorem test17280_block_21 : Interval test17280 336 352 :=
  interval_of_check test17280 336 16 (by decide +kernel)

theorem test17280_block_22 : Interval test17280 352 368 :=
  interval_of_check test17280 352 16 (by decide +kernel)

theorem test17280_block_23 : Interval test17280 368 384 :=
  interval_of_check test17280 368 16 (by decide +kernel)

theorem test17280_block_24 : Interval test17280 384 400 :=
  interval_of_check test17280 384 16 (by decide +kernel)

theorem test17280_block_25 : Interval test17280 400 416 :=
  interval_of_check test17280 400 16 (by decide +kernel)

theorem test17280_block_26 : Interval test17280 416 432 :=
  interval_of_check test17280 416 16 (by decide +kernel)

theorem test17280_block_27 : Interval test17280 432 448 :=
  interval_of_check test17280 432 16 (by decide +kernel)

theorem test17280_block_28 : Interval test17280 448 464 :=
  interval_of_check test17280 448 16 (by decide +kernel)

theorem test17280_block_29 : Interval test17280 464 480 :=
  interval_of_check test17280 464 16 (by decide +kernel)

theorem test17280_block_30 : Interval test17280 480 496 :=
  interval_of_check test17280 480 16 (by decide +kernel)

theorem test17280_block_31 : Interval test17280 496 503 :=
  interval_of_check test17280 496 7 (by decide +kernel)

theorem test17280_complete : Interval test17280 0 503 :=
  (interval_append test17280 0 256 503
  (interval_append test17280 0 128 256
  (interval_append test17280 0 64 128
  (interval_append test17280 0 32 64
  (interval_append test17280 0 16 32
  test17280_block_0
  test17280_block_1)
  (interval_append test17280 32 48 64
  test17280_block_2
  test17280_block_3))
  (interval_append test17280 64 96 128
  (interval_append test17280 64 80 96
  test17280_block_4
  test17280_block_5)
  (interval_append test17280 96 112 128
  test17280_block_6
  test17280_block_7)))
  (interval_append test17280 128 192 256
  (interval_append test17280 128 160 192
  (interval_append test17280 128 144 160
  test17280_block_8
  test17280_block_9)
  (interval_append test17280 160 176 192
  test17280_block_10
  test17280_block_11))
  (interval_append test17280 192 224 256
  (interval_append test17280 192 208 224
  test17280_block_12
  test17280_block_13)
  (interval_append test17280 224 240 256
  test17280_block_14
  test17280_block_15))))
  (interval_append test17280 256 384 503
  (interval_append test17280 256 320 384
  (interval_append test17280 256 288 320
  (interval_append test17280 256 272 288
  test17280_block_16
  test17280_block_17)
  (interval_append test17280 288 304 320
  test17280_block_18
  test17280_block_19))
  (interval_append test17280 320 352 384
  (interval_append test17280 320 336 352
  test17280_block_20
  test17280_block_21)
  (interval_append test17280 352 368 384
  test17280_block_22
  test17280_block_23)))
  (interval_append test17280 384 448 503
  (interval_append test17280 384 416 448
  (interval_append test17280 384 400 416
  test17280_block_24
  test17280_block_25)
  (interval_append test17280 416 432 448
  test17280_block_26
  test17280_block_27))
  (interval_append test17280 448 480 503
  (interval_append test17280 448 464 480
  test17280_block_28
  test17280_block_29)
  (interval_append test17280 480 496 503
  test17280_block_30
  test17280_block_31)))))
theorem nodeInterval17280 : Interval nodeTest 17280 17783 := by
  intro i hlo hhi
  have h := test17280_complete (i-17280) (Nat.zero_le _) (by omega)
  simpa only [test17280, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest20
