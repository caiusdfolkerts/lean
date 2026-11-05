module
prelude
public import RootedSubsumedForest0339Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test14080 (i : Nat) := nodeTest (i+14080)
theorem test14080_block_0 : Interval test14080 0 16 :=
  interval_of_check test14080 0 16 (by decide +kernel)

theorem test14080_block_1 : Interval test14080 16 32 :=
  interval_of_check test14080 16 16 (by decide +kernel)

theorem test14080_block_2 : Interval test14080 32 48 :=
  interval_of_check test14080 32 16 (by decide +kernel)

theorem test14080_block_3 : Interval test14080 48 64 :=
  interval_of_check test14080 48 16 (by decide +kernel)

theorem test14080_block_4 : Interval test14080 64 80 :=
  interval_of_check test14080 64 16 (by decide +kernel)

theorem test14080_block_5 : Interval test14080 80 96 :=
  interval_of_check test14080 80 16 (by decide +kernel)

theorem test14080_block_6 : Interval test14080 96 112 :=
  interval_of_check test14080 96 16 (by decide +kernel)

theorem test14080_block_7 : Interval test14080 112 128 :=
  interval_of_check test14080 112 16 (by decide +kernel)

theorem test14080_block_8 : Interval test14080 128 144 :=
  interval_of_check test14080 128 16 (by decide +kernel)

theorem test14080_block_9 : Interval test14080 144 160 :=
  interval_of_check test14080 144 16 (by decide +kernel)

theorem test14080_block_10 : Interval test14080 160 176 :=
  interval_of_check test14080 160 16 (by decide +kernel)

theorem test14080_block_11 : Interval test14080 176 192 :=
  interval_of_check test14080 176 16 (by decide +kernel)

theorem test14080_block_12 : Interval test14080 192 208 :=
  interval_of_check test14080 192 16 (by decide +kernel)

theorem test14080_block_13 : Interval test14080 208 224 :=
  interval_of_check test14080 208 16 (by decide +kernel)

theorem test14080_block_14 : Interval test14080 224 240 :=
  interval_of_check test14080 224 16 (by decide +kernel)

theorem test14080_block_15 : Interval test14080 240 256 :=
  interval_of_check test14080 240 16 (by decide +kernel)

theorem test14080_block_16 : Interval test14080 256 272 :=
  interval_of_check test14080 256 16 (by decide +kernel)

theorem test14080_block_17 : Interval test14080 272 288 :=
  interval_of_check test14080 272 16 (by decide +kernel)

theorem test14080_block_18 : Interval test14080 288 304 :=
  interval_of_check test14080 288 16 (by decide +kernel)

theorem test14080_block_19 : Interval test14080 304 320 :=
  interval_of_check test14080 304 16 (by decide +kernel)

theorem test14080_block_20 : Interval test14080 320 336 :=
  interval_of_check test14080 320 16 (by decide +kernel)

theorem test14080_block_21 : Interval test14080 336 352 :=
  interval_of_check test14080 336 16 (by decide +kernel)

theorem test14080_block_22 : Interval test14080 352 368 :=
  interval_of_check test14080 352 16 (by decide +kernel)

theorem test14080_block_23 : Interval test14080 368 384 :=
  interval_of_check test14080 368 16 (by decide +kernel)

theorem test14080_block_24 : Interval test14080 384 400 :=
  interval_of_check test14080 384 16 (by decide +kernel)

theorem test14080_block_25 : Interval test14080 400 416 :=
  interval_of_check test14080 400 16 (by decide +kernel)

theorem test14080_block_26 : Interval test14080 416 432 :=
  interval_of_check test14080 416 16 (by decide +kernel)

theorem test14080_block_27 : Interval test14080 432 448 :=
  interval_of_check test14080 432 16 (by decide +kernel)

theorem test14080_block_28 : Interval test14080 448 464 :=
  interval_of_check test14080 448 16 (by decide +kernel)

theorem test14080_block_29 : Interval test14080 464 480 :=
  interval_of_check test14080 464 16 (by decide +kernel)

theorem test14080_block_30 : Interval test14080 480 496 :=
  interval_of_check test14080 480 16 (by decide +kernel)

theorem test14080_block_31 : Interval test14080 496 512 :=
  interval_of_check test14080 496 16 (by decide +kernel)

theorem test14080_block_32 : Interval test14080 512 528 :=
  interval_of_check test14080 512 16 (by decide +kernel)

theorem test14080_block_33 : Interval test14080 528 544 :=
  interval_of_check test14080 528 16 (by decide +kernel)

theorem test14080_block_34 : Interval test14080 544 560 :=
  interval_of_check test14080 544 16 (by decide +kernel)

theorem test14080_block_35 : Interval test14080 560 576 :=
  interval_of_check test14080 560 16 (by decide +kernel)

theorem test14080_block_36 : Interval test14080 576 592 :=
  interval_of_check test14080 576 16 (by decide +kernel)

theorem test14080_block_37 : Interval test14080 592 608 :=
  interval_of_check test14080 592 16 (by decide +kernel)

theorem test14080_block_38 : Interval test14080 608 619 :=
  interval_of_check test14080 608 11 (by decide +kernel)

theorem test14080_complete : Interval test14080 0 619 :=
  (interval_append test14080 0 304 619
  (interval_append test14080 0 144 304
  (interval_append test14080 0 64 144
  (interval_append test14080 0 32 64
  (interval_append test14080 0 16 32
  test14080_block_0
  test14080_block_1)
  (interval_append test14080 32 48 64
  test14080_block_2
  test14080_block_3))
  (interval_append test14080 64 96 144
  (interval_append test14080 64 80 96
  test14080_block_4
  test14080_block_5)
  (interval_append test14080 96 112 144
  test14080_block_6
  (interval_append test14080 112 128 144
  test14080_block_7
  test14080_block_8))))
  (interval_append test14080 144 224 304
  (interval_append test14080 144 176 224
  (interval_append test14080 144 160 176
  test14080_block_9
  test14080_block_10)
  (interval_append test14080 176 192 224
  test14080_block_11
  (interval_append test14080 192 208 224
  test14080_block_12
  test14080_block_13)))
  (interval_append test14080 224 256 304
  (interval_append test14080 224 240 256
  test14080_block_14
  test14080_block_15)
  (interval_append test14080 256 272 304
  test14080_block_16
  (interval_append test14080 272 288 304
  test14080_block_17
  test14080_block_18)))))
  (interval_append test14080 304 464 619
  (interval_append test14080 304 384 464
  (interval_append test14080 304 336 384
  (interval_append test14080 304 320 336
  test14080_block_19
  test14080_block_20)
  (interval_append test14080 336 352 384
  test14080_block_21
  (interval_append test14080 352 368 384
  test14080_block_22
  test14080_block_23)))
  (interval_append test14080 384 416 464
  (interval_append test14080 384 400 416
  test14080_block_24
  test14080_block_25)
  (interval_append test14080 416 432 464
  test14080_block_26
  (interval_append test14080 432 448 464
  test14080_block_27
  test14080_block_28))))
  (interval_append test14080 464 544 619
  (interval_append test14080 464 496 544
  (interval_append test14080 464 480 496
  test14080_block_29
  test14080_block_30)
  (interval_append test14080 496 512 544
  test14080_block_31
  (interval_append test14080 512 528 544
  test14080_block_32
  test14080_block_33)))
  (interval_append test14080 544 576 619
  (interval_append test14080 544 560 576
  test14080_block_34
  test14080_block_35)
  (interval_append test14080 576 592 619
  test14080_block_36
  (interval_append test14080 592 608 619
  test14080_block_37
  test14080_block_38))))))
theorem nodeInterval14080 : Interval nodeTest 14080 14699 := by
  intro i hlo hhi
  have h := test14080_complete (i-14080) (Nat.zero_le _) (by omega)
  simpa only [test14080, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0339
