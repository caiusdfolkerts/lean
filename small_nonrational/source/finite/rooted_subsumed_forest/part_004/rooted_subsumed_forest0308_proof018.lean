module
prelude
public import RootedSubsumedForest0308Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test11520 (i : Nat) := nodeTest (i+11520)
theorem test11520_block_0 : Interval test11520 0 16 :=
  interval_of_check test11520 0 16 (by decide +kernel)

theorem test11520_block_1 : Interval test11520 16 32 :=
  interval_of_check test11520 16 16 (by decide +kernel)

theorem test11520_block_2 : Interval test11520 32 48 :=
  interval_of_check test11520 32 16 (by decide +kernel)

theorem test11520_block_3 : Interval test11520 48 64 :=
  interval_of_check test11520 48 16 (by decide +kernel)

theorem test11520_block_4 : Interval test11520 64 80 :=
  interval_of_check test11520 64 16 (by decide +kernel)

theorem test11520_block_5 : Interval test11520 80 96 :=
  interval_of_check test11520 80 16 (by decide +kernel)

theorem test11520_block_6 : Interval test11520 96 112 :=
  interval_of_check test11520 96 16 (by decide +kernel)

theorem test11520_block_7 : Interval test11520 112 128 :=
  interval_of_check test11520 112 16 (by decide +kernel)

theorem test11520_block_8 : Interval test11520 128 144 :=
  interval_of_check test11520 128 16 (by decide +kernel)

theorem test11520_block_9 : Interval test11520 144 160 :=
  interval_of_check test11520 144 16 (by decide +kernel)

theorem test11520_block_10 : Interval test11520 160 176 :=
  interval_of_check test11520 160 16 (by decide +kernel)

theorem test11520_block_11 : Interval test11520 176 192 :=
  interval_of_check test11520 176 16 (by decide +kernel)

theorem test11520_block_12 : Interval test11520 192 208 :=
  interval_of_check test11520 192 16 (by decide +kernel)

theorem test11520_block_13 : Interval test11520 208 224 :=
  interval_of_check test11520 208 16 (by decide +kernel)

theorem test11520_block_14 : Interval test11520 224 240 :=
  interval_of_check test11520 224 16 (by decide +kernel)

theorem test11520_block_15 : Interval test11520 240 256 :=
  interval_of_check test11520 240 16 (by decide +kernel)

theorem test11520_block_16 : Interval test11520 256 272 :=
  interval_of_check test11520 256 16 (by decide +kernel)

theorem test11520_block_17 : Interval test11520 272 288 :=
  interval_of_check test11520 272 16 (by decide +kernel)

theorem test11520_block_18 : Interval test11520 288 304 :=
  interval_of_check test11520 288 16 (by decide +kernel)

theorem test11520_block_19 : Interval test11520 304 320 :=
  interval_of_check test11520 304 16 (by decide +kernel)

theorem test11520_block_20 : Interval test11520 320 336 :=
  interval_of_check test11520 320 16 (by decide +kernel)

theorem test11520_block_21 : Interval test11520 336 352 :=
  interval_of_check test11520 336 16 (by decide +kernel)

theorem test11520_block_22 : Interval test11520 352 368 :=
  interval_of_check test11520 352 16 (by decide +kernel)

theorem test11520_block_23 : Interval test11520 368 384 :=
  interval_of_check test11520 368 16 (by decide +kernel)

theorem test11520_block_24 : Interval test11520 384 400 :=
  interval_of_check test11520 384 16 (by decide +kernel)

theorem test11520_block_25 : Interval test11520 400 416 :=
  interval_of_check test11520 400 16 (by decide +kernel)

theorem test11520_block_26 : Interval test11520 416 432 :=
  interval_of_check test11520 416 16 (by decide +kernel)

theorem test11520_block_27 : Interval test11520 432 448 :=
  interval_of_check test11520 432 16 (by decide +kernel)

theorem test11520_block_28 : Interval test11520 448 464 :=
  interval_of_check test11520 448 16 (by decide +kernel)

theorem test11520_block_29 : Interval test11520 464 480 :=
  interval_of_check test11520 464 16 (by decide +kernel)

theorem test11520_block_30 : Interval test11520 480 496 :=
  interval_of_check test11520 480 16 (by decide +kernel)

theorem test11520_block_31 : Interval test11520 496 512 :=
  interval_of_check test11520 496 16 (by decide +kernel)

theorem test11520_block_32 : Interval test11520 512 528 :=
  interval_of_check test11520 512 16 (by decide +kernel)

theorem test11520_block_33 : Interval test11520 528 544 :=
  interval_of_check test11520 528 16 (by decide +kernel)

theorem test11520_block_34 : Interval test11520 544 560 :=
  interval_of_check test11520 544 16 (by decide +kernel)

theorem test11520_block_35 : Interval test11520 560 576 :=
  interval_of_check test11520 560 16 (by decide +kernel)

theorem test11520_block_36 : Interval test11520 576 578 :=
  interval_of_check test11520 576 2 (by decide +kernel)

theorem test11520_complete : Interval test11520 0 578 :=
  (interval_append test11520 0 288 578
  (interval_append test11520 0 144 288
  (interval_append test11520 0 64 144
  (interval_append test11520 0 32 64
  (interval_append test11520 0 16 32
  test11520_block_0
  test11520_block_1)
  (interval_append test11520 32 48 64
  test11520_block_2
  test11520_block_3))
  (interval_append test11520 64 96 144
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)
  (interval_append test11520 96 112 144
  test11520_block_6
  (interval_append test11520 112 128 144
  test11520_block_7
  test11520_block_8))))
  (interval_append test11520 144 208 288
  (interval_append test11520 144 176 208
  (interval_append test11520 144 160 176
  test11520_block_9
  test11520_block_10)
  (interval_append test11520 176 192 208
  test11520_block_11
  test11520_block_12))
  (interval_append test11520 208 240 288
  (interval_append test11520 208 224 240
  test11520_block_13
  test11520_block_14)
  (interval_append test11520 240 256 288
  test11520_block_15
  (interval_append test11520 256 272 288
  test11520_block_16
  test11520_block_17)))))
  (interval_append test11520 288 432 578
  (interval_append test11520 288 352 432
  (interval_append test11520 288 320 352
  (interval_append test11520 288 304 320
  test11520_block_18
  test11520_block_19)
  (interval_append test11520 320 336 352
  test11520_block_20
  test11520_block_21))
  (interval_append test11520 352 384 432
  (interval_append test11520 352 368 384
  test11520_block_22
  test11520_block_23)
  (interval_append test11520 384 400 432
  test11520_block_24
  (interval_append test11520 400 416 432
  test11520_block_25
  test11520_block_26))))
  (interval_append test11520 432 512 578
  (interval_append test11520 432 464 512
  (interval_append test11520 432 448 464
  test11520_block_27
  test11520_block_28)
  (interval_append test11520 464 480 512
  test11520_block_29
  (interval_append test11520 480 496 512
  test11520_block_30
  test11520_block_31)))
  (interval_append test11520 512 544 578
  (interval_append test11520 512 528 544
  test11520_block_32
  test11520_block_33)
  (interval_append test11520 544 560 578
  test11520_block_34
  (interval_append test11520 560 576 578
  test11520_block_35
  test11520_block_36))))))
theorem nodeInterval11520 : Interval nodeTest 11520 12098 := by
  intro i hlo hhi
  have h := test11520_complete (i-11520) (Nat.zero_le _) (by omega)
  simpa only [test11520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0308
