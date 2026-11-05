module
prelude
public import RootedSubsumedForest0704Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test7680 (i : Nat) := nodeTest (i+7680)
theorem test7680_block_0 : Interval test7680 0 16 :=
  interval_of_check test7680 0 16 (by decide +kernel)

theorem test7680_block_1 : Interval test7680 16 32 :=
  interval_of_check test7680 16 16 (by decide +kernel)

theorem test7680_block_2 : Interval test7680 32 48 :=
  interval_of_check test7680 32 16 (by decide +kernel)

theorem test7680_block_3 : Interval test7680 48 64 :=
  interval_of_check test7680 48 16 (by decide +kernel)

theorem test7680_block_4 : Interval test7680 64 80 :=
  interval_of_check test7680 64 16 (by decide +kernel)

theorem test7680_block_5 : Interval test7680 80 96 :=
  interval_of_check test7680 80 16 (by decide +kernel)

theorem test7680_block_6 : Interval test7680 96 112 :=
  interval_of_check test7680 96 16 (by decide +kernel)

theorem test7680_block_7 : Interval test7680 112 128 :=
  interval_of_check test7680 112 16 (by decide +kernel)

theorem test7680_block_8 : Interval test7680 128 144 :=
  interval_of_check test7680 128 16 (by decide +kernel)

theorem test7680_block_9 : Interval test7680 144 160 :=
  interval_of_check test7680 144 16 (by decide +kernel)

theorem test7680_block_10 : Interval test7680 160 176 :=
  interval_of_check test7680 160 16 (by decide +kernel)

theorem test7680_block_11 : Interval test7680 176 192 :=
  interval_of_check test7680 176 16 (by decide +kernel)

theorem test7680_block_12 : Interval test7680 192 208 :=
  interval_of_check test7680 192 16 (by decide +kernel)

theorem test7680_block_13 : Interval test7680 208 224 :=
  interval_of_check test7680 208 16 (by decide +kernel)

theorem test7680_block_14 : Interval test7680 224 240 :=
  interval_of_check test7680 224 16 (by decide +kernel)

theorem test7680_block_15 : Interval test7680 240 256 :=
  interval_of_check test7680 240 16 (by decide +kernel)

theorem test7680_block_16 : Interval test7680 256 272 :=
  interval_of_check test7680 256 16 (by decide +kernel)

theorem test7680_block_17 : Interval test7680 272 288 :=
  interval_of_check test7680 272 16 (by decide +kernel)

theorem test7680_block_18 : Interval test7680 288 304 :=
  interval_of_check test7680 288 16 (by decide +kernel)

theorem test7680_block_19 : Interval test7680 304 320 :=
  interval_of_check test7680 304 16 (by decide +kernel)

theorem test7680_block_20 : Interval test7680 320 336 :=
  interval_of_check test7680 320 16 (by decide +kernel)

theorem test7680_block_21 : Interval test7680 336 352 :=
  interval_of_check test7680 336 16 (by decide +kernel)

theorem test7680_block_22 : Interval test7680 352 368 :=
  interval_of_check test7680 352 16 (by decide +kernel)

theorem test7680_block_23 : Interval test7680 368 384 :=
  interval_of_check test7680 368 16 (by decide +kernel)

theorem test7680_block_24 : Interval test7680 384 400 :=
  interval_of_check test7680 384 16 (by decide +kernel)

theorem test7680_block_25 : Interval test7680 400 416 :=
  interval_of_check test7680 400 16 (by decide +kernel)

theorem test7680_block_26 : Interval test7680 416 432 :=
  interval_of_check test7680 416 16 (by decide +kernel)

theorem test7680_block_27 : Interval test7680 432 448 :=
  interval_of_check test7680 432 16 (by decide +kernel)

theorem test7680_block_28 : Interval test7680 448 464 :=
  interval_of_check test7680 448 16 (by decide +kernel)

theorem test7680_block_29 : Interval test7680 464 480 :=
  interval_of_check test7680 464 16 (by decide +kernel)

theorem test7680_block_30 : Interval test7680 480 496 :=
  interval_of_check test7680 480 16 (by decide +kernel)

theorem test7680_block_31 : Interval test7680 496 512 :=
  interval_of_check test7680 496 16 (by decide +kernel)

theorem test7680_block_32 : Interval test7680 512 528 :=
  interval_of_check test7680 512 16 (by decide +kernel)

theorem test7680_block_33 : Interval test7680 528 544 :=
  interval_of_check test7680 528 16 (by decide +kernel)

theorem test7680_block_34 : Interval test7680 544 560 :=
  interval_of_check test7680 544 16 (by decide +kernel)

theorem test7680_block_35 : Interval test7680 560 576 :=
  interval_of_check test7680 560 16 (by decide +kernel)

theorem test7680_block_36 : Interval test7680 576 592 :=
  interval_of_check test7680 576 16 (by decide +kernel)

theorem test7680_block_37 : Interval test7680 592 600 :=
  interval_of_check test7680 592 8 (by decide +kernel)

theorem test7680_complete : Interval test7680 0 600 :=
  (interval_append test7680 0 304 600
  (interval_append test7680 0 144 304
  (interval_append test7680 0 64 144
  (interval_append test7680 0 32 64
  (interval_append test7680 0 16 32
  test7680_block_0
  test7680_block_1)
  (interval_append test7680 32 48 64
  test7680_block_2
  test7680_block_3))
  (interval_append test7680 64 96 144
  (interval_append test7680 64 80 96
  test7680_block_4
  test7680_block_5)
  (interval_append test7680 96 112 144
  test7680_block_6
  (interval_append test7680 112 128 144
  test7680_block_7
  test7680_block_8))))
  (interval_append test7680 144 224 304
  (interval_append test7680 144 176 224
  (interval_append test7680 144 160 176
  test7680_block_9
  test7680_block_10)
  (interval_append test7680 176 192 224
  test7680_block_11
  (interval_append test7680 192 208 224
  test7680_block_12
  test7680_block_13)))
  (interval_append test7680 224 256 304
  (interval_append test7680 224 240 256
  test7680_block_14
  test7680_block_15)
  (interval_append test7680 256 272 304
  test7680_block_16
  (interval_append test7680 272 288 304
  test7680_block_17
  test7680_block_18)))))
  (interval_append test7680 304 448 600
  (interval_append test7680 304 368 448
  (interval_append test7680 304 336 368
  (interval_append test7680 304 320 336
  test7680_block_19
  test7680_block_20)
  (interval_append test7680 336 352 368
  test7680_block_21
  test7680_block_22))
  (interval_append test7680 368 400 448
  (interval_append test7680 368 384 400
  test7680_block_23
  test7680_block_24)
  (interval_append test7680 400 416 448
  test7680_block_25
  (interval_append test7680 416 432 448
  test7680_block_26
  test7680_block_27))))
  (interval_append test7680 448 528 600
  (interval_append test7680 448 480 528
  (interval_append test7680 448 464 480
  test7680_block_28
  test7680_block_29)
  (interval_append test7680 480 496 528
  test7680_block_30
  (interval_append test7680 496 512 528
  test7680_block_31
  test7680_block_32)))
  (interval_append test7680 528 560 600
  (interval_append test7680 528 544 560
  test7680_block_33
  test7680_block_34)
  (interval_append test7680 560 576 600
  test7680_block_35
  (interval_append test7680 576 592 600
  test7680_block_36
  test7680_block_37))))))
theorem nodeInterval7680 : Interval nodeTest 7680 8280 := by
  intro i hlo hhi
  have h := test7680_complete (i-7680) (Nat.zero_le _) (by omega)
  simpa only [test7680, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0704
