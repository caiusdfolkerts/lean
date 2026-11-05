module
prelude
public import RootedSubsumedForest0695Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test19200 (i : Nat) := nodeTest (i+19200)
theorem test19200_block_0 : Interval test19200 0 16 :=
  interval_of_check test19200 0 16 (by decide +kernel)

theorem test19200_block_1 : Interval test19200 16 32 :=
  interval_of_check test19200 16 16 (by decide +kernel)

theorem test19200_block_2 : Interval test19200 32 48 :=
  interval_of_check test19200 32 16 (by decide +kernel)

theorem test19200_block_3 : Interval test19200 48 64 :=
  interval_of_check test19200 48 16 (by decide +kernel)

theorem test19200_block_4 : Interval test19200 64 80 :=
  interval_of_check test19200 64 16 (by decide +kernel)

theorem test19200_block_5 : Interval test19200 80 96 :=
  interval_of_check test19200 80 16 (by decide +kernel)

theorem test19200_block_6 : Interval test19200 96 112 :=
  interval_of_check test19200 96 16 (by decide +kernel)

theorem test19200_block_7 : Interval test19200 112 128 :=
  interval_of_check test19200 112 16 (by decide +kernel)

theorem test19200_block_8 : Interval test19200 128 144 :=
  interval_of_check test19200 128 16 (by decide +kernel)

theorem test19200_block_9 : Interval test19200 144 160 :=
  interval_of_check test19200 144 16 (by decide +kernel)

theorem test19200_block_10 : Interval test19200 160 176 :=
  interval_of_check test19200 160 16 (by decide +kernel)

theorem test19200_block_11 : Interval test19200 176 192 :=
  interval_of_check test19200 176 16 (by decide +kernel)

theorem test19200_block_12 : Interval test19200 192 208 :=
  interval_of_check test19200 192 16 (by decide +kernel)

theorem test19200_block_13 : Interval test19200 208 224 :=
  interval_of_check test19200 208 16 (by decide +kernel)

theorem test19200_block_14 : Interval test19200 224 240 :=
  interval_of_check test19200 224 16 (by decide +kernel)

theorem test19200_block_15 : Interval test19200 240 256 :=
  interval_of_check test19200 240 16 (by decide +kernel)

theorem test19200_block_16 : Interval test19200 256 272 :=
  interval_of_check test19200 256 16 (by decide +kernel)

theorem test19200_block_17 : Interval test19200 272 288 :=
  interval_of_check test19200 272 16 (by decide +kernel)

theorem test19200_block_18 : Interval test19200 288 304 :=
  interval_of_check test19200 288 16 (by decide +kernel)

theorem test19200_block_19 : Interval test19200 304 320 :=
  interval_of_check test19200 304 16 (by decide +kernel)

theorem test19200_block_20 : Interval test19200 320 336 :=
  interval_of_check test19200 320 16 (by decide +kernel)

theorem test19200_block_21 : Interval test19200 336 352 :=
  interval_of_check test19200 336 16 (by decide +kernel)

theorem test19200_block_22 : Interval test19200 352 368 :=
  interval_of_check test19200 352 16 (by decide +kernel)

theorem test19200_block_23 : Interval test19200 368 384 :=
  interval_of_check test19200 368 16 (by decide +kernel)

theorem test19200_block_24 : Interval test19200 384 400 :=
  interval_of_check test19200 384 16 (by decide +kernel)

theorem test19200_block_25 : Interval test19200 400 416 :=
  interval_of_check test19200 400 16 (by decide +kernel)

theorem test19200_block_26 : Interval test19200 416 432 :=
  interval_of_check test19200 416 16 (by decide +kernel)

theorem test19200_block_27 : Interval test19200 432 448 :=
  interval_of_check test19200 432 16 (by decide +kernel)

theorem test19200_block_28 : Interval test19200 448 464 :=
  interval_of_check test19200 448 16 (by decide +kernel)

theorem test19200_block_29 : Interval test19200 464 480 :=
  interval_of_check test19200 464 16 (by decide +kernel)

theorem test19200_block_30 : Interval test19200 480 496 :=
  interval_of_check test19200 480 16 (by decide +kernel)

theorem test19200_block_31 : Interval test19200 496 512 :=
  interval_of_check test19200 496 16 (by decide +kernel)

theorem test19200_block_32 : Interval test19200 512 528 :=
  interval_of_check test19200 512 16 (by decide +kernel)

theorem test19200_block_33 : Interval test19200 528 544 :=
  interval_of_check test19200 528 16 (by decide +kernel)

theorem test19200_block_34 : Interval test19200 544 555 :=
  interval_of_check test19200 544 11 (by decide +kernel)

theorem test19200_complete : Interval test19200 0 555 :=
  (interval_append test19200 0 272 555
  (interval_append test19200 0 128 272
  (interval_append test19200 0 64 128
  (interval_append test19200 0 32 64
  (interval_append test19200 0 16 32
  test19200_block_0
  test19200_block_1)
  (interval_append test19200 32 48 64
  test19200_block_2
  test19200_block_3))
  (interval_append test19200 64 96 128
  (interval_append test19200 64 80 96
  test19200_block_4
  test19200_block_5)
  (interval_append test19200 96 112 128
  test19200_block_6
  test19200_block_7)))
  (interval_append test19200 128 192 272
  (interval_append test19200 128 160 192
  (interval_append test19200 128 144 160
  test19200_block_8
  test19200_block_9)
  (interval_append test19200 160 176 192
  test19200_block_10
  test19200_block_11))
  (interval_append test19200 192 224 272
  (interval_append test19200 192 208 224
  test19200_block_12
  test19200_block_13)
  (interval_append test19200 224 240 272
  test19200_block_14
  (interval_append test19200 240 256 272
  test19200_block_15
  test19200_block_16)))))
  (interval_append test19200 272 416 555
  (interval_append test19200 272 336 416
  (interval_append test19200 272 304 336
  (interval_append test19200 272 288 304
  test19200_block_17
  test19200_block_18)
  (interval_append test19200 304 320 336
  test19200_block_19
  test19200_block_20))
  (interval_append test19200 336 368 416
  (interval_append test19200 336 352 368
  test19200_block_21
  test19200_block_22)
  (interval_append test19200 368 384 416
  test19200_block_23
  (interval_append test19200 384 400 416
  test19200_block_24
  test19200_block_25))))
  (interval_append test19200 416 480 555
  (interval_append test19200 416 448 480
  (interval_append test19200 416 432 448
  test19200_block_26
  test19200_block_27)
  (interval_append test19200 448 464 480
  test19200_block_28
  test19200_block_29))
  (interval_append test19200 480 512 555
  (interval_append test19200 480 496 512
  test19200_block_30
  test19200_block_31)
  (interval_append test19200 512 528 555
  test19200_block_32
  (interval_append test19200 528 544 555
  test19200_block_33
  test19200_block_34))))))
theorem nodeInterval19200 : Interval nodeTest 19200 19755 := by
  intro i hlo hhi
  have h := test19200_complete (i-19200) (Nat.zero_le _) (by omega)
  simpa only [test19200, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
