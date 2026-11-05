module
prelude
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test57600 (i : Nat) := nodeTest (i+57600)
theorem test57600_block_0 : Interval test57600 0 16 :=
  interval_of_check test57600 0 16 (by decide +kernel)

theorem test57600_block_1 : Interval test57600 16 32 :=
  interval_of_check test57600 16 16 (by decide +kernel)

theorem test57600_block_2 : Interval test57600 32 48 :=
  interval_of_check test57600 32 16 (by decide +kernel)

theorem test57600_block_3 : Interval test57600 48 64 :=
  interval_of_check test57600 48 16 (by decide +kernel)

theorem test57600_block_4 : Interval test57600 64 80 :=
  interval_of_check test57600 64 16 (by decide +kernel)

theorem test57600_block_5 : Interval test57600 80 96 :=
  interval_of_check test57600 80 16 (by decide +kernel)

theorem test57600_block_6 : Interval test57600 96 112 :=
  interval_of_check test57600 96 16 (by decide +kernel)

theorem test57600_block_7 : Interval test57600 112 128 :=
  interval_of_check test57600 112 16 (by decide +kernel)

theorem test57600_block_8 : Interval test57600 128 144 :=
  interval_of_check test57600 128 16 (by decide +kernel)

theorem test57600_block_9 : Interval test57600 144 160 :=
  interval_of_check test57600 144 16 (by decide +kernel)

theorem test57600_block_10 : Interval test57600 160 176 :=
  interval_of_check test57600 160 16 (by decide +kernel)

theorem test57600_block_11 : Interval test57600 176 192 :=
  interval_of_check test57600 176 16 (by decide +kernel)

theorem test57600_block_12 : Interval test57600 192 208 :=
  interval_of_check test57600 192 16 (by decide +kernel)

theorem test57600_block_13 : Interval test57600 208 224 :=
  interval_of_check test57600 208 16 (by decide +kernel)

theorem test57600_block_14 : Interval test57600 224 240 :=
  interval_of_check test57600 224 16 (by decide +kernel)

theorem test57600_block_15 : Interval test57600 240 256 :=
  interval_of_check test57600 240 16 (by decide +kernel)

theorem test57600_block_16 : Interval test57600 256 272 :=
  interval_of_check test57600 256 16 (by decide +kernel)

theorem test57600_block_17 : Interval test57600 272 288 :=
  interval_of_check test57600 272 16 (by decide +kernel)

theorem test57600_block_18 : Interval test57600 288 304 :=
  interval_of_check test57600 288 16 (by decide +kernel)

theorem test57600_block_19 : Interval test57600 304 320 :=
  interval_of_check test57600 304 16 (by decide +kernel)

theorem test57600_block_20 : Interval test57600 320 336 :=
  interval_of_check test57600 320 16 (by decide +kernel)

theorem test57600_block_21 : Interval test57600 336 352 :=
  interval_of_check test57600 336 16 (by decide +kernel)

theorem test57600_block_22 : Interval test57600 352 368 :=
  interval_of_check test57600 352 16 (by decide +kernel)

theorem test57600_block_23 : Interval test57600 368 384 :=
  interval_of_check test57600 368 16 (by decide +kernel)

theorem test57600_block_24 : Interval test57600 384 400 :=
  interval_of_check test57600 384 16 (by decide +kernel)

theorem test57600_block_25 : Interval test57600 400 416 :=
  interval_of_check test57600 400 16 (by decide +kernel)

theorem test57600_block_26 : Interval test57600 416 432 :=
  interval_of_check test57600 416 16 (by decide +kernel)

theorem test57600_block_27 : Interval test57600 432 448 :=
  interval_of_check test57600 432 16 (by decide +kernel)

theorem test57600_block_28 : Interval test57600 448 464 :=
  interval_of_check test57600 448 16 (by decide +kernel)

theorem test57600_block_29 : Interval test57600 464 480 :=
  interval_of_check test57600 464 16 (by decide +kernel)

theorem test57600_block_30 : Interval test57600 480 496 :=
  interval_of_check test57600 480 16 (by decide +kernel)

theorem test57600_block_31 : Interval test57600 496 512 :=
  interval_of_check test57600 496 16 (by decide +kernel)

theorem test57600_block_32 : Interval test57600 512 528 :=
  interval_of_check test57600 512 16 (by decide +kernel)

theorem test57600_block_33 : Interval test57600 528 544 :=
  interval_of_check test57600 528 16 (by decide +kernel)

theorem test57600_block_34 : Interval test57600 544 560 :=
  interval_of_check test57600 544 16 (by decide +kernel)

theorem test57600_block_35 : Interval test57600 560 576 :=
  interval_of_check test57600 560 16 (by decide +kernel)

theorem test57600_block_36 : Interval test57600 576 592 :=
  interval_of_check test57600 576 16 (by decide +kernel)

theorem test57600_block_37 : Interval test57600 592 608 :=
  interval_of_check test57600 592 16 (by decide +kernel)

theorem test57600_block_38 : Interval test57600 608 609 :=
  interval_of_check test57600 608 1 (by decide +kernel)

theorem test57600_complete : Interval test57600 0 609 :=
  (interval_append test57600 0 304 609
  (interval_append test57600 0 144 304
  (interval_append test57600 0 64 144
  (interval_append test57600 0 32 64
  (interval_append test57600 0 16 32
  test57600_block_0
  test57600_block_1)
  (interval_append test57600 32 48 64
  test57600_block_2
  test57600_block_3))
  (interval_append test57600 64 96 144
  (interval_append test57600 64 80 96
  test57600_block_4
  test57600_block_5)
  (interval_append test57600 96 112 144
  test57600_block_6
  (interval_append test57600 112 128 144
  test57600_block_7
  test57600_block_8))))
  (interval_append test57600 144 224 304
  (interval_append test57600 144 176 224
  (interval_append test57600 144 160 176
  test57600_block_9
  test57600_block_10)
  (interval_append test57600 176 192 224
  test57600_block_11
  (interval_append test57600 192 208 224
  test57600_block_12
  test57600_block_13)))
  (interval_append test57600 224 256 304
  (interval_append test57600 224 240 256
  test57600_block_14
  test57600_block_15)
  (interval_append test57600 256 272 304
  test57600_block_16
  (interval_append test57600 272 288 304
  test57600_block_17
  test57600_block_18)))))
  (interval_append test57600 304 464 609
  (interval_append test57600 304 384 464
  (interval_append test57600 304 336 384
  (interval_append test57600 304 320 336
  test57600_block_19
  test57600_block_20)
  (interval_append test57600 336 352 384
  test57600_block_21
  (interval_append test57600 352 368 384
  test57600_block_22
  test57600_block_23)))
  (interval_append test57600 384 416 464
  (interval_append test57600 384 400 416
  test57600_block_24
  test57600_block_25)
  (interval_append test57600 416 432 464
  test57600_block_26
  (interval_append test57600 432 448 464
  test57600_block_27
  test57600_block_28))))
  (interval_append test57600 464 544 609
  (interval_append test57600 464 496 544
  (interval_append test57600 464 480 496
  test57600_block_29
  test57600_block_30)
  (interval_append test57600 496 512 544
  test57600_block_31
  (interval_append test57600 512 528 544
  test57600_block_32
  test57600_block_33)))
  (interval_append test57600 544 576 609
  (interval_append test57600 544 560 576
  test57600_block_34
  test57600_block_35)
  (interval_append test57600 576 592 609
  test57600_block_36
  (interval_append test57600 592 608 609
  test57600_block_37
  test57600_block_38))))))
theorem nodeInterval57600 : Interval nodeTest 57600 58209 := by
  intro i hlo hhi
  have h := test57600_complete (i-57600) (Nat.zero_le _) (by omega)
  simpa only [test57600, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
