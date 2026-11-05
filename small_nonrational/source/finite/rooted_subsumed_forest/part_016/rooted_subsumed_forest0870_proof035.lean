module
prelude
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test22400 (i : Nat) := nodeTest (i+22400)
theorem test22400_block_0 : Interval test22400 0 16 :=
  interval_of_check test22400 0 16 (by decide +kernel)

theorem test22400_block_1 : Interval test22400 16 32 :=
  interval_of_check test22400 16 16 (by decide +kernel)

theorem test22400_block_2 : Interval test22400 32 48 :=
  interval_of_check test22400 32 16 (by decide +kernel)

theorem test22400_block_3 : Interval test22400 48 64 :=
  interval_of_check test22400 48 16 (by decide +kernel)

theorem test22400_block_4 : Interval test22400 64 80 :=
  interval_of_check test22400 64 16 (by decide +kernel)

theorem test22400_block_5 : Interval test22400 80 96 :=
  interval_of_check test22400 80 16 (by decide +kernel)

theorem test22400_block_6 : Interval test22400 96 112 :=
  interval_of_check test22400 96 16 (by decide +kernel)

theorem test22400_block_7 : Interval test22400 112 128 :=
  interval_of_check test22400 112 16 (by decide +kernel)

theorem test22400_block_8 : Interval test22400 128 144 :=
  interval_of_check test22400 128 16 (by decide +kernel)

theorem test22400_block_9 : Interval test22400 144 160 :=
  interval_of_check test22400 144 16 (by decide +kernel)

theorem test22400_block_10 : Interval test22400 160 176 :=
  interval_of_check test22400 160 16 (by decide +kernel)

theorem test22400_block_11 : Interval test22400 176 192 :=
  interval_of_check test22400 176 16 (by decide +kernel)

theorem test22400_block_12 : Interval test22400 192 208 :=
  interval_of_check test22400 192 16 (by decide +kernel)

theorem test22400_block_13 : Interval test22400 208 224 :=
  interval_of_check test22400 208 16 (by decide +kernel)

theorem test22400_block_14 : Interval test22400 224 240 :=
  interval_of_check test22400 224 16 (by decide +kernel)

theorem test22400_block_15 : Interval test22400 240 256 :=
  interval_of_check test22400 240 16 (by decide +kernel)

theorem test22400_block_16 : Interval test22400 256 272 :=
  interval_of_check test22400 256 16 (by decide +kernel)

theorem test22400_block_17 : Interval test22400 272 288 :=
  interval_of_check test22400 272 16 (by decide +kernel)

theorem test22400_block_18 : Interval test22400 288 304 :=
  interval_of_check test22400 288 16 (by decide +kernel)

theorem test22400_block_19 : Interval test22400 304 320 :=
  interval_of_check test22400 304 16 (by decide +kernel)

theorem test22400_block_20 : Interval test22400 320 336 :=
  interval_of_check test22400 320 16 (by decide +kernel)

theorem test22400_block_21 : Interval test22400 336 352 :=
  interval_of_check test22400 336 16 (by decide +kernel)

theorem test22400_block_22 : Interval test22400 352 368 :=
  interval_of_check test22400 352 16 (by decide +kernel)

theorem test22400_block_23 : Interval test22400 368 384 :=
  interval_of_check test22400 368 16 (by decide +kernel)

theorem test22400_block_24 : Interval test22400 384 400 :=
  interval_of_check test22400 384 16 (by decide +kernel)

theorem test22400_block_25 : Interval test22400 400 416 :=
  interval_of_check test22400 400 16 (by decide +kernel)

theorem test22400_block_26 : Interval test22400 416 432 :=
  interval_of_check test22400 416 16 (by decide +kernel)

theorem test22400_block_27 : Interval test22400 432 448 :=
  interval_of_check test22400 432 16 (by decide +kernel)

theorem test22400_block_28 : Interval test22400 448 464 :=
  interval_of_check test22400 448 16 (by decide +kernel)

theorem test22400_block_29 : Interval test22400 464 480 :=
  interval_of_check test22400 464 16 (by decide +kernel)

theorem test22400_block_30 : Interval test22400 480 496 :=
  interval_of_check test22400 480 16 (by decide +kernel)

theorem test22400_block_31 : Interval test22400 496 512 :=
  interval_of_check test22400 496 16 (by decide +kernel)

theorem test22400_block_32 : Interval test22400 512 528 :=
  interval_of_check test22400 512 16 (by decide +kernel)

theorem test22400_block_33 : Interval test22400 528 544 :=
  interval_of_check test22400 528 16 (by decide +kernel)

theorem test22400_block_34 : Interval test22400 544 560 :=
  interval_of_check test22400 544 16 (by decide +kernel)

theorem test22400_block_35 : Interval test22400 560 576 :=
  interval_of_check test22400 560 16 (by decide +kernel)

theorem test22400_block_36 : Interval test22400 576 583 :=
  interval_of_check test22400 576 7 (by decide +kernel)

theorem test22400_complete : Interval test22400 0 583 :=
  (interval_append test22400 0 288 583
  (interval_append test22400 0 144 288
  (interval_append test22400 0 64 144
  (interval_append test22400 0 32 64
  (interval_append test22400 0 16 32
  test22400_block_0
  test22400_block_1)
  (interval_append test22400 32 48 64
  test22400_block_2
  test22400_block_3))
  (interval_append test22400 64 96 144
  (interval_append test22400 64 80 96
  test22400_block_4
  test22400_block_5)
  (interval_append test22400 96 112 144
  test22400_block_6
  (interval_append test22400 112 128 144
  test22400_block_7
  test22400_block_8))))
  (interval_append test22400 144 208 288
  (interval_append test22400 144 176 208
  (interval_append test22400 144 160 176
  test22400_block_9
  test22400_block_10)
  (interval_append test22400 176 192 208
  test22400_block_11
  test22400_block_12))
  (interval_append test22400 208 240 288
  (interval_append test22400 208 224 240
  test22400_block_13
  test22400_block_14)
  (interval_append test22400 240 256 288
  test22400_block_15
  (interval_append test22400 256 272 288
  test22400_block_16
  test22400_block_17)))))
  (interval_append test22400 288 432 583
  (interval_append test22400 288 352 432
  (interval_append test22400 288 320 352
  (interval_append test22400 288 304 320
  test22400_block_18
  test22400_block_19)
  (interval_append test22400 320 336 352
  test22400_block_20
  test22400_block_21))
  (interval_append test22400 352 384 432
  (interval_append test22400 352 368 384
  test22400_block_22
  test22400_block_23)
  (interval_append test22400 384 400 432
  test22400_block_24
  (interval_append test22400 400 416 432
  test22400_block_25
  test22400_block_26))))
  (interval_append test22400 432 512 583
  (interval_append test22400 432 464 512
  (interval_append test22400 432 448 464
  test22400_block_27
  test22400_block_28)
  (interval_append test22400 464 480 512
  test22400_block_29
  (interval_append test22400 480 496 512
  test22400_block_30
  test22400_block_31)))
  (interval_append test22400 512 544 583
  (interval_append test22400 512 528 544
  test22400_block_32
  test22400_block_33)
  (interval_append test22400 544 560 583
  test22400_block_34
  (interval_append test22400 560 576 583
  test22400_block_35
  test22400_block_36))))))
theorem nodeInterval22400 : Interval nodeTest 22400 22983 := by
  intro i hlo hhi
  have h := test22400_complete (i-22400) (Nat.zero_le _) (by omega)
  simpa only [test22400, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
