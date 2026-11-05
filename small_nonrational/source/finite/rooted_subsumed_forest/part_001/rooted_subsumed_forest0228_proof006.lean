module
prelude
public import RootedSubsumedForest0228Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0228
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test3840 (i : Nat) := nodeTest (i+3840)
theorem test3840_block_0 : Interval test3840 0 16 :=
  interval_of_check test3840 0 16 (by decide +kernel)

theorem test3840_block_1 : Interval test3840 16 32 :=
  interval_of_check test3840 16 16 (by decide +kernel)

theorem test3840_block_2 : Interval test3840 32 48 :=
  interval_of_check test3840 32 16 (by decide +kernel)

theorem test3840_block_3 : Interval test3840 48 64 :=
  interval_of_check test3840 48 16 (by decide +kernel)

theorem test3840_block_4 : Interval test3840 64 80 :=
  interval_of_check test3840 64 16 (by decide +kernel)

theorem test3840_block_5 : Interval test3840 80 96 :=
  interval_of_check test3840 80 16 (by decide +kernel)

theorem test3840_block_6 : Interval test3840 96 112 :=
  interval_of_check test3840 96 16 (by decide +kernel)

theorem test3840_block_7 : Interval test3840 112 128 :=
  interval_of_check test3840 112 16 (by decide +kernel)

theorem test3840_block_8 : Interval test3840 128 144 :=
  interval_of_check test3840 128 16 (by decide +kernel)

theorem test3840_block_9 : Interval test3840 144 160 :=
  interval_of_check test3840 144 16 (by decide +kernel)

theorem test3840_block_10 : Interval test3840 160 176 :=
  interval_of_check test3840 160 16 (by decide +kernel)

theorem test3840_block_11 : Interval test3840 176 192 :=
  interval_of_check test3840 176 16 (by decide +kernel)

theorem test3840_block_12 : Interval test3840 192 208 :=
  interval_of_check test3840 192 16 (by decide +kernel)

theorem test3840_block_13 : Interval test3840 208 224 :=
  interval_of_check test3840 208 16 (by decide +kernel)

theorem test3840_block_14 : Interval test3840 224 240 :=
  interval_of_check test3840 224 16 (by decide +kernel)

theorem test3840_block_15 : Interval test3840 240 256 :=
  interval_of_check test3840 240 16 (by decide +kernel)

theorem test3840_block_16 : Interval test3840 256 272 :=
  interval_of_check test3840 256 16 (by decide +kernel)

theorem test3840_block_17 : Interval test3840 272 288 :=
  interval_of_check test3840 272 16 (by decide +kernel)

theorem test3840_block_18 : Interval test3840 288 304 :=
  interval_of_check test3840 288 16 (by decide +kernel)

theorem test3840_block_19 : Interval test3840 304 320 :=
  interval_of_check test3840 304 16 (by decide +kernel)

theorem test3840_block_20 : Interval test3840 320 336 :=
  interval_of_check test3840 320 16 (by decide +kernel)

theorem test3840_block_21 : Interval test3840 336 352 :=
  interval_of_check test3840 336 16 (by decide +kernel)

theorem test3840_block_22 : Interval test3840 352 368 :=
  interval_of_check test3840 352 16 (by decide +kernel)

theorem test3840_block_23 : Interval test3840 368 384 :=
  interval_of_check test3840 368 16 (by decide +kernel)

theorem test3840_block_24 : Interval test3840 384 400 :=
  interval_of_check test3840 384 16 (by decide +kernel)

theorem test3840_block_25 : Interval test3840 400 416 :=
  interval_of_check test3840 400 16 (by decide +kernel)

theorem test3840_block_26 : Interval test3840 416 432 :=
  interval_of_check test3840 416 16 (by decide +kernel)

theorem test3840_block_27 : Interval test3840 432 448 :=
  interval_of_check test3840 432 16 (by decide +kernel)

theorem test3840_block_28 : Interval test3840 448 464 :=
  interval_of_check test3840 448 16 (by decide +kernel)

theorem test3840_block_29 : Interval test3840 464 480 :=
  interval_of_check test3840 464 16 (by decide +kernel)

theorem test3840_block_30 : Interval test3840 480 496 :=
  interval_of_check test3840 480 16 (by decide +kernel)

theorem test3840_block_31 : Interval test3840 496 512 :=
  interval_of_check test3840 496 16 (by decide +kernel)

theorem test3840_block_32 : Interval test3840 512 520 :=
  interval_of_check test3840 512 8 (by decide +kernel)

theorem test3840_complete : Interval test3840 0 520 :=
  (interval_append test3840 0 256 520
  (interval_append test3840 0 128 256
  (interval_append test3840 0 64 128
  (interval_append test3840 0 32 64
  (interval_append test3840 0 16 32
  test3840_block_0
  test3840_block_1)
  (interval_append test3840 32 48 64
  test3840_block_2
  test3840_block_3))
  (interval_append test3840 64 96 128
  (interval_append test3840 64 80 96
  test3840_block_4
  test3840_block_5)
  (interval_append test3840 96 112 128
  test3840_block_6
  test3840_block_7)))
  (interval_append test3840 128 192 256
  (interval_append test3840 128 160 192
  (interval_append test3840 128 144 160
  test3840_block_8
  test3840_block_9)
  (interval_append test3840 160 176 192
  test3840_block_10
  test3840_block_11))
  (interval_append test3840 192 224 256
  (interval_append test3840 192 208 224
  test3840_block_12
  test3840_block_13)
  (interval_append test3840 224 240 256
  test3840_block_14
  test3840_block_15))))
  (interval_append test3840 256 384 520
  (interval_append test3840 256 320 384
  (interval_append test3840 256 288 320
  (interval_append test3840 256 272 288
  test3840_block_16
  test3840_block_17)
  (interval_append test3840 288 304 320
  test3840_block_18
  test3840_block_19))
  (interval_append test3840 320 352 384
  (interval_append test3840 320 336 352
  test3840_block_20
  test3840_block_21)
  (interval_append test3840 352 368 384
  test3840_block_22
  test3840_block_23)))
  (interval_append test3840 384 448 520
  (interval_append test3840 384 416 448
  (interval_append test3840 384 400 416
  test3840_block_24
  test3840_block_25)
  (interval_append test3840 416 432 448
  test3840_block_26
  test3840_block_27))
  (interval_append test3840 448 480 520
  (interval_append test3840 448 464 480
  test3840_block_28
  test3840_block_29)
  (interval_append test3840 480 496 520
  test3840_block_30
  (interval_append test3840 496 512 520
  test3840_block_31
  test3840_block_32))))))
theorem nodeInterval3840 : Interval nodeTest 3840 4360 := by
  intro i hlo hhi
  have h := test3840_complete (i-3840) (Nat.zero_le _) (by omega)
  simpa only [test3840, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0228
