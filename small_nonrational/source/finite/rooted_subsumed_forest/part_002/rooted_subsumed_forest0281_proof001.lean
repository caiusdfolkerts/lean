module
prelude
public import RootedSubsumedForest0281Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0281
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test640 (i : Nat) := nodeTest (i+640)
theorem test640_block_0 : Interval test640 0 16 :=
  interval_of_check test640 0 16 (by decide +kernel)

theorem test640_block_1 : Interval test640 16 32 :=
  interval_of_check test640 16 16 (by decide +kernel)

theorem test640_block_2 : Interval test640 32 48 :=
  interval_of_check test640 32 16 (by decide +kernel)

theorem test640_block_3 : Interval test640 48 64 :=
  interval_of_check test640 48 16 (by decide +kernel)

theorem test640_block_4 : Interval test640 64 80 :=
  interval_of_check test640 64 16 (by decide +kernel)

theorem test640_block_5 : Interval test640 80 96 :=
  interval_of_check test640 80 16 (by decide +kernel)

theorem test640_block_6 : Interval test640 96 112 :=
  interval_of_check test640 96 16 (by decide +kernel)

theorem test640_block_7 : Interval test640 112 128 :=
  interval_of_check test640 112 16 (by decide +kernel)

theorem test640_block_8 : Interval test640 128 144 :=
  interval_of_check test640 128 16 (by decide +kernel)

theorem test640_block_9 : Interval test640 144 160 :=
  interval_of_check test640 144 16 (by decide +kernel)

theorem test640_block_10 : Interval test640 160 176 :=
  interval_of_check test640 160 16 (by decide +kernel)

theorem test640_block_11 : Interval test640 176 192 :=
  interval_of_check test640 176 16 (by decide +kernel)

theorem test640_block_12 : Interval test640 192 208 :=
  interval_of_check test640 192 16 (by decide +kernel)

theorem test640_block_13 : Interval test640 208 224 :=
  interval_of_check test640 208 16 (by decide +kernel)

theorem test640_block_14 : Interval test640 224 240 :=
  interval_of_check test640 224 16 (by decide +kernel)

theorem test640_block_15 : Interval test640 240 256 :=
  interval_of_check test640 240 16 (by decide +kernel)

theorem test640_block_16 : Interval test640 256 272 :=
  interval_of_check test640 256 16 (by decide +kernel)

theorem test640_block_17 : Interval test640 272 288 :=
  interval_of_check test640 272 16 (by decide +kernel)

theorem test640_block_18 : Interval test640 288 304 :=
  interval_of_check test640 288 16 (by decide +kernel)

theorem test640_block_19 : Interval test640 304 320 :=
  interval_of_check test640 304 16 (by decide +kernel)

theorem test640_block_20 : Interval test640 320 336 :=
  interval_of_check test640 320 16 (by decide +kernel)

theorem test640_block_21 : Interval test640 336 352 :=
  interval_of_check test640 336 16 (by decide +kernel)

theorem test640_block_22 : Interval test640 352 368 :=
  interval_of_check test640 352 16 (by decide +kernel)

theorem test640_block_23 : Interval test640 368 384 :=
  interval_of_check test640 368 16 (by decide +kernel)

theorem test640_block_24 : Interval test640 384 400 :=
  interval_of_check test640 384 16 (by decide +kernel)

theorem test640_block_25 : Interval test640 400 416 :=
  interval_of_check test640 400 16 (by decide +kernel)

theorem test640_block_26 : Interval test640 416 432 :=
  interval_of_check test640 416 16 (by decide +kernel)

theorem test640_block_27 : Interval test640 432 448 :=
  interval_of_check test640 432 16 (by decide +kernel)

theorem test640_block_28 : Interval test640 448 464 :=
  interval_of_check test640 448 16 (by decide +kernel)

theorem test640_block_29 : Interval test640 464 480 :=
  interval_of_check test640 464 16 (by decide +kernel)

theorem test640_block_30 : Interval test640 480 496 :=
  interval_of_check test640 480 16 (by decide +kernel)

theorem test640_block_31 : Interval test640 496 512 :=
  interval_of_check test640 496 16 (by decide +kernel)

theorem test640_block_32 : Interval test640 512 528 :=
  interval_of_check test640 512 16 (by decide +kernel)

theorem test640_block_33 : Interval test640 528 544 :=
  interval_of_check test640 528 16 (by decide +kernel)

theorem test640_block_34 : Interval test640 544 560 :=
  interval_of_check test640 544 16 (by decide +kernel)

theorem test640_block_35 : Interval test640 560 576 :=
  interval_of_check test640 560 16 (by decide +kernel)

theorem test640_block_36 : Interval test640 576 592 :=
  interval_of_check test640 576 16 (by decide +kernel)

theorem test640_block_37 : Interval test640 592 602 :=
  interval_of_check test640 592 10 (by decide +kernel)

theorem test640_complete : Interval test640 0 602 :=
  (interval_append test640 0 304 602
  (interval_append test640 0 144 304
  (interval_append test640 0 64 144
  (interval_append test640 0 32 64
  (interval_append test640 0 16 32
  test640_block_0
  test640_block_1)
  (interval_append test640 32 48 64
  test640_block_2
  test640_block_3))
  (interval_append test640 64 96 144
  (interval_append test640 64 80 96
  test640_block_4
  test640_block_5)
  (interval_append test640 96 112 144
  test640_block_6
  (interval_append test640 112 128 144
  test640_block_7
  test640_block_8))))
  (interval_append test640 144 224 304
  (interval_append test640 144 176 224
  (interval_append test640 144 160 176
  test640_block_9
  test640_block_10)
  (interval_append test640 176 192 224
  test640_block_11
  (interval_append test640 192 208 224
  test640_block_12
  test640_block_13)))
  (interval_append test640 224 256 304
  (interval_append test640 224 240 256
  test640_block_14
  test640_block_15)
  (interval_append test640 256 272 304
  test640_block_16
  (interval_append test640 272 288 304
  test640_block_17
  test640_block_18)))))
  (interval_append test640 304 448 602
  (interval_append test640 304 368 448
  (interval_append test640 304 336 368
  (interval_append test640 304 320 336
  test640_block_19
  test640_block_20)
  (interval_append test640 336 352 368
  test640_block_21
  test640_block_22))
  (interval_append test640 368 400 448
  (interval_append test640 368 384 400
  test640_block_23
  test640_block_24)
  (interval_append test640 400 416 448
  test640_block_25
  (interval_append test640 416 432 448
  test640_block_26
  test640_block_27))))
  (interval_append test640 448 528 602
  (interval_append test640 448 480 528
  (interval_append test640 448 464 480
  test640_block_28
  test640_block_29)
  (interval_append test640 480 496 528
  test640_block_30
  (interval_append test640 496 512 528
  test640_block_31
  test640_block_32)))
  (interval_append test640 528 560 602
  (interval_append test640 528 544 560
  test640_block_33
  test640_block_34)
  (interval_append test640 560 576 602
  test640_block_35
  (interval_append test640 576 592 602
  test640_block_36
  test640_block_37))))))
theorem nodeInterval640 : Interval nodeTest 640 1242 := by
  intro i hlo hhi
  have h := test640_complete (i-640) (Nat.zero_le _) (by omega)
  simpa only [test640, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0281
