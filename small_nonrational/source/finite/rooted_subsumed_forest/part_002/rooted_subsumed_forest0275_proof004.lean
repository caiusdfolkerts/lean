module
prelude
public import RootedSubsumedForest0275Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0275
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test2560 (i : Nat) := nodeTest (i+2560)
theorem test2560_block_0 : Interval test2560 0 16 :=
  interval_of_check test2560 0 16 (by decide +kernel)

theorem test2560_block_1 : Interval test2560 16 32 :=
  interval_of_check test2560 16 16 (by decide +kernel)

theorem test2560_block_2 : Interval test2560 32 48 :=
  interval_of_check test2560 32 16 (by decide +kernel)

theorem test2560_block_3 : Interval test2560 48 64 :=
  interval_of_check test2560 48 16 (by decide +kernel)

theorem test2560_block_4 : Interval test2560 64 80 :=
  interval_of_check test2560 64 16 (by decide +kernel)

theorem test2560_block_5 : Interval test2560 80 96 :=
  interval_of_check test2560 80 16 (by decide +kernel)

theorem test2560_block_6 : Interval test2560 96 112 :=
  interval_of_check test2560 96 16 (by decide +kernel)

theorem test2560_block_7 : Interval test2560 112 128 :=
  interval_of_check test2560 112 16 (by decide +kernel)

theorem test2560_block_8 : Interval test2560 128 144 :=
  interval_of_check test2560 128 16 (by decide +kernel)

theorem test2560_block_9 : Interval test2560 144 160 :=
  interval_of_check test2560 144 16 (by decide +kernel)

theorem test2560_block_10 : Interval test2560 160 176 :=
  interval_of_check test2560 160 16 (by decide +kernel)

theorem test2560_block_11 : Interval test2560 176 192 :=
  interval_of_check test2560 176 16 (by decide +kernel)

theorem test2560_block_12 : Interval test2560 192 208 :=
  interval_of_check test2560 192 16 (by decide +kernel)

theorem test2560_block_13 : Interval test2560 208 224 :=
  interval_of_check test2560 208 16 (by decide +kernel)

theorem test2560_block_14 : Interval test2560 224 240 :=
  interval_of_check test2560 224 16 (by decide +kernel)

theorem test2560_block_15 : Interval test2560 240 256 :=
  interval_of_check test2560 240 16 (by decide +kernel)

theorem test2560_block_16 : Interval test2560 256 272 :=
  interval_of_check test2560 256 16 (by decide +kernel)

theorem test2560_block_17 : Interval test2560 272 288 :=
  interval_of_check test2560 272 16 (by decide +kernel)

theorem test2560_block_18 : Interval test2560 288 304 :=
  interval_of_check test2560 288 16 (by decide +kernel)

theorem test2560_block_19 : Interval test2560 304 320 :=
  interval_of_check test2560 304 16 (by decide +kernel)

theorem test2560_block_20 : Interval test2560 320 336 :=
  interval_of_check test2560 320 16 (by decide +kernel)

theorem test2560_block_21 : Interval test2560 336 352 :=
  interval_of_check test2560 336 16 (by decide +kernel)

theorem test2560_block_22 : Interval test2560 352 368 :=
  interval_of_check test2560 352 16 (by decide +kernel)

theorem test2560_block_23 : Interval test2560 368 384 :=
  interval_of_check test2560 368 16 (by decide +kernel)

theorem test2560_block_24 : Interval test2560 384 400 :=
  interval_of_check test2560 384 16 (by decide +kernel)

theorem test2560_block_25 : Interval test2560 400 416 :=
  interval_of_check test2560 400 16 (by decide +kernel)

theorem test2560_block_26 : Interval test2560 416 432 :=
  interval_of_check test2560 416 16 (by decide +kernel)

theorem test2560_block_27 : Interval test2560 432 448 :=
  interval_of_check test2560 432 16 (by decide +kernel)

theorem test2560_block_28 : Interval test2560 448 464 :=
  interval_of_check test2560 448 16 (by decide +kernel)

theorem test2560_block_29 : Interval test2560 464 480 :=
  interval_of_check test2560 464 16 (by decide +kernel)

theorem test2560_block_30 : Interval test2560 480 496 :=
  interval_of_check test2560 480 16 (by decide +kernel)

theorem test2560_block_31 : Interval test2560 496 512 :=
  interval_of_check test2560 496 16 (by decide +kernel)

theorem test2560_block_32 : Interval test2560 512 528 :=
  interval_of_check test2560 512 16 (by decide +kernel)

theorem test2560_block_33 : Interval test2560 528 544 :=
  interval_of_check test2560 528 16 (by decide +kernel)

theorem test2560_block_34 : Interval test2560 544 560 :=
  interval_of_check test2560 544 16 (by decide +kernel)

theorem test2560_block_35 : Interval test2560 560 576 :=
  interval_of_check test2560 560 16 (by decide +kernel)

theorem test2560_block_36 : Interval test2560 576 592 :=
  interval_of_check test2560 576 16 (by decide +kernel)

theorem test2560_block_37 : Interval test2560 592 599 :=
  interval_of_check test2560 592 7 (by decide +kernel)

theorem test2560_complete : Interval test2560 0 599 :=
  (interval_append test2560 0 304 599
  (interval_append test2560 0 144 304
  (interval_append test2560 0 64 144
  (interval_append test2560 0 32 64
  (interval_append test2560 0 16 32
  test2560_block_0
  test2560_block_1)
  (interval_append test2560 32 48 64
  test2560_block_2
  test2560_block_3))
  (interval_append test2560 64 96 144
  (interval_append test2560 64 80 96
  test2560_block_4
  test2560_block_5)
  (interval_append test2560 96 112 144
  test2560_block_6
  (interval_append test2560 112 128 144
  test2560_block_7
  test2560_block_8))))
  (interval_append test2560 144 224 304
  (interval_append test2560 144 176 224
  (interval_append test2560 144 160 176
  test2560_block_9
  test2560_block_10)
  (interval_append test2560 176 192 224
  test2560_block_11
  (interval_append test2560 192 208 224
  test2560_block_12
  test2560_block_13)))
  (interval_append test2560 224 256 304
  (interval_append test2560 224 240 256
  test2560_block_14
  test2560_block_15)
  (interval_append test2560 256 272 304
  test2560_block_16
  (interval_append test2560 272 288 304
  test2560_block_17
  test2560_block_18)))))
  (interval_append test2560 304 448 599
  (interval_append test2560 304 368 448
  (interval_append test2560 304 336 368
  (interval_append test2560 304 320 336
  test2560_block_19
  test2560_block_20)
  (interval_append test2560 336 352 368
  test2560_block_21
  test2560_block_22))
  (interval_append test2560 368 400 448
  (interval_append test2560 368 384 400
  test2560_block_23
  test2560_block_24)
  (interval_append test2560 400 416 448
  test2560_block_25
  (interval_append test2560 416 432 448
  test2560_block_26
  test2560_block_27))))
  (interval_append test2560 448 528 599
  (interval_append test2560 448 480 528
  (interval_append test2560 448 464 480
  test2560_block_28
  test2560_block_29)
  (interval_append test2560 480 496 528
  test2560_block_30
  (interval_append test2560 496 512 528
  test2560_block_31
  test2560_block_32)))
  (interval_append test2560 528 560 599
  (interval_append test2560 528 544 560
  test2560_block_33
  test2560_block_34)
  (interval_append test2560 560 576 599
  test2560_block_35
  (interval_append test2560 576 592 599
  test2560_block_36
  test2560_block_37))))))
theorem nodeInterval2560 : Interval nodeTest 2560 3159 := by
  intro i hlo hhi
  have h := test2560_complete (i-2560) (Nat.zero_le _) (by omega)
  simpa only [test2560, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0275
