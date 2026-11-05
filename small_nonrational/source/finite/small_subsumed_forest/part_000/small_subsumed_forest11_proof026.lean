module
prelude
public import SmallSubsumedForest11Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test16640 (i : Nat) := nodeTest (i+16640)
theorem test16640_block_0 : Interval test16640 0 16 :=
  interval_of_check test16640 0 16 (by decide +kernel)

theorem test16640_block_1 : Interval test16640 16 32 :=
  interval_of_check test16640 16 16 (by decide +kernel)

theorem test16640_block_2 : Interval test16640 32 48 :=
  interval_of_check test16640 32 16 (by decide +kernel)

theorem test16640_block_3 : Interval test16640 48 64 :=
  interval_of_check test16640 48 16 (by decide +kernel)

theorem test16640_block_4 : Interval test16640 64 80 :=
  interval_of_check test16640 64 16 (by decide +kernel)

theorem test16640_block_5 : Interval test16640 80 96 :=
  interval_of_check test16640 80 16 (by decide +kernel)

theorem test16640_block_6 : Interval test16640 96 112 :=
  interval_of_check test16640 96 16 (by decide +kernel)

theorem test16640_block_7 : Interval test16640 112 128 :=
  interval_of_check test16640 112 16 (by decide +kernel)

theorem test16640_block_8 : Interval test16640 128 144 :=
  interval_of_check test16640 128 16 (by decide +kernel)

theorem test16640_block_9 : Interval test16640 144 160 :=
  interval_of_check test16640 144 16 (by decide +kernel)

theorem test16640_block_10 : Interval test16640 160 176 :=
  interval_of_check test16640 160 16 (by decide +kernel)

theorem test16640_block_11 : Interval test16640 176 192 :=
  interval_of_check test16640 176 16 (by decide +kernel)

theorem test16640_block_12 : Interval test16640 192 208 :=
  interval_of_check test16640 192 16 (by decide +kernel)

theorem test16640_block_13 : Interval test16640 208 224 :=
  interval_of_check test16640 208 16 (by decide +kernel)

theorem test16640_block_14 : Interval test16640 224 240 :=
  interval_of_check test16640 224 16 (by decide +kernel)

theorem test16640_block_15 : Interval test16640 240 256 :=
  interval_of_check test16640 240 16 (by decide +kernel)

theorem test16640_block_16 : Interval test16640 256 272 :=
  interval_of_check test16640 256 16 (by decide +kernel)

theorem test16640_block_17 : Interval test16640 272 288 :=
  interval_of_check test16640 272 16 (by decide +kernel)

theorem test16640_block_18 : Interval test16640 288 304 :=
  interval_of_check test16640 288 16 (by decide +kernel)

theorem test16640_block_19 : Interval test16640 304 320 :=
  interval_of_check test16640 304 16 (by decide +kernel)

theorem test16640_block_20 : Interval test16640 320 336 :=
  interval_of_check test16640 320 16 (by decide +kernel)

theorem test16640_block_21 : Interval test16640 336 352 :=
  interval_of_check test16640 336 16 (by decide +kernel)

theorem test16640_block_22 : Interval test16640 352 368 :=
  interval_of_check test16640 352 16 (by decide +kernel)

theorem test16640_block_23 : Interval test16640 368 384 :=
  interval_of_check test16640 368 16 (by decide +kernel)

theorem test16640_block_24 : Interval test16640 384 400 :=
  interval_of_check test16640 384 16 (by decide +kernel)

theorem test16640_block_25 : Interval test16640 400 416 :=
  interval_of_check test16640 400 16 (by decide +kernel)

theorem test16640_block_26 : Interval test16640 416 432 :=
  interval_of_check test16640 416 16 (by decide +kernel)

theorem test16640_block_27 : Interval test16640 432 448 :=
  interval_of_check test16640 432 16 (by decide +kernel)

theorem test16640_block_28 : Interval test16640 448 464 :=
  interval_of_check test16640 448 16 (by decide +kernel)

theorem test16640_block_29 : Interval test16640 464 480 :=
  interval_of_check test16640 464 16 (by decide +kernel)

theorem test16640_block_30 : Interval test16640 480 496 :=
  interval_of_check test16640 480 16 (by decide +kernel)

theorem test16640_block_31 : Interval test16640 496 512 :=
  interval_of_check test16640 496 16 (by decide +kernel)

theorem test16640_block_32 : Interval test16640 512 528 :=
  interval_of_check test16640 512 16 (by decide +kernel)

theorem test16640_block_33 : Interval test16640 528 544 :=
  interval_of_check test16640 528 16 (by decide +kernel)

theorem test16640_block_34 : Interval test16640 544 560 :=
  interval_of_check test16640 544 16 (by decide +kernel)

theorem test16640_complete : Interval test16640 0 560 :=
  (interval_append test16640 0 272 560
  (interval_append test16640 0 128 272
  (interval_append test16640 0 64 128
  (interval_append test16640 0 32 64
  (interval_append test16640 0 16 32
  test16640_block_0
  test16640_block_1)
  (interval_append test16640 32 48 64
  test16640_block_2
  test16640_block_3))
  (interval_append test16640 64 96 128
  (interval_append test16640 64 80 96
  test16640_block_4
  test16640_block_5)
  (interval_append test16640 96 112 128
  test16640_block_6
  test16640_block_7)))
  (interval_append test16640 128 192 272
  (interval_append test16640 128 160 192
  (interval_append test16640 128 144 160
  test16640_block_8
  test16640_block_9)
  (interval_append test16640 160 176 192
  test16640_block_10
  test16640_block_11))
  (interval_append test16640 192 224 272
  (interval_append test16640 192 208 224
  test16640_block_12
  test16640_block_13)
  (interval_append test16640 224 240 272
  test16640_block_14
  (interval_append test16640 240 256 272
  test16640_block_15
  test16640_block_16)))))
  (interval_append test16640 272 416 560
  (interval_append test16640 272 336 416
  (interval_append test16640 272 304 336
  (interval_append test16640 272 288 304
  test16640_block_17
  test16640_block_18)
  (interval_append test16640 304 320 336
  test16640_block_19
  test16640_block_20))
  (interval_append test16640 336 368 416
  (interval_append test16640 336 352 368
  test16640_block_21
  test16640_block_22)
  (interval_append test16640 368 384 416
  test16640_block_23
  (interval_append test16640 384 400 416
  test16640_block_24
  test16640_block_25))))
  (interval_append test16640 416 480 560
  (interval_append test16640 416 448 480
  (interval_append test16640 416 432 448
  test16640_block_26
  test16640_block_27)
  (interval_append test16640 448 464 480
  test16640_block_28
  test16640_block_29))
  (interval_append test16640 480 512 560
  (interval_append test16640 480 496 512
  test16640_block_30
  test16640_block_31)
  (interval_append test16640 512 528 560
  test16640_block_32
  (interval_append test16640 528 544 560
  test16640_block_33
  test16640_block_34))))))
theorem nodeInterval16640 : Interval nodeTest 16640 17200 := by
  intro i hlo hhi
  have h := test16640_complete (i-16640) (Nat.zero_le _) (by omega)
  simpa only [test16640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
