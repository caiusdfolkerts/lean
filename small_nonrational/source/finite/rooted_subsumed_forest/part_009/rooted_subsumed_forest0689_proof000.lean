module
prelude
public import RootedSubsumedForest0689Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0689
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test0 (i : Nat) := nodeTest (i+0)
theorem test0_block_0 : Interval test0 0 16 :=
  interval_of_check test0 0 16 (by decide +kernel)

theorem test0_block_1 : Interval test0 16 32 :=
  interval_of_check test0 16 16 (by decide +kernel)

theorem test0_block_2 : Interval test0 32 48 :=
  interval_of_check test0 32 16 (by decide +kernel)

theorem test0_block_3 : Interval test0 48 64 :=
  interval_of_check test0 48 16 (by decide +kernel)

theorem test0_block_4 : Interval test0 64 80 :=
  interval_of_check test0 64 16 (by decide +kernel)

theorem test0_block_5 : Interval test0 80 96 :=
  interval_of_check test0 80 16 (by decide +kernel)

theorem test0_block_6 : Interval test0 96 112 :=
  interval_of_check test0 96 16 (by decide +kernel)

theorem test0_block_7 : Interval test0 112 128 :=
  interval_of_check test0 112 16 (by decide +kernel)

theorem test0_block_8 : Interval test0 128 144 :=
  interval_of_check test0 128 16 (by decide +kernel)

theorem test0_block_9 : Interval test0 144 160 :=
  interval_of_check test0 144 16 (by decide +kernel)

theorem test0_block_10 : Interval test0 160 176 :=
  interval_of_check test0 160 16 (by decide +kernel)

theorem test0_block_11 : Interval test0 176 192 :=
  interval_of_check test0 176 16 (by decide +kernel)

theorem test0_block_12 : Interval test0 192 208 :=
  interval_of_check test0 192 16 (by decide +kernel)

theorem test0_block_13 : Interval test0 208 224 :=
  interval_of_check test0 208 16 (by decide +kernel)

theorem test0_block_14 : Interval test0 224 240 :=
  interval_of_check test0 224 16 (by decide +kernel)

theorem test0_block_15 : Interval test0 240 256 :=
  interval_of_check test0 240 16 (by decide +kernel)

theorem test0_block_16 : Interval test0 256 272 :=
  interval_of_check test0 256 16 (by decide +kernel)

theorem test0_block_17 : Interval test0 272 288 :=
  interval_of_check test0 272 16 (by decide +kernel)

theorem test0_block_18 : Interval test0 288 304 :=
  interval_of_check test0 288 16 (by decide +kernel)

theorem test0_block_19 : Interval test0 304 320 :=
  interval_of_check test0 304 16 (by decide +kernel)

theorem test0_block_20 : Interval test0 320 336 :=
  interval_of_check test0 320 16 (by decide +kernel)

theorem test0_block_21 : Interval test0 336 352 :=
  interval_of_check test0 336 16 (by decide +kernel)

theorem test0_block_22 : Interval test0 352 368 :=
  interval_of_check test0 352 16 (by decide +kernel)

theorem test0_block_23 : Interval test0 368 384 :=
  interval_of_check test0 368 16 (by decide +kernel)

theorem test0_block_24 : Interval test0 384 400 :=
  interval_of_check test0 384 16 (by decide +kernel)

theorem test0_block_25 : Interval test0 400 416 :=
  interval_of_check test0 400 16 (by decide +kernel)

theorem test0_block_26 : Interval test0 416 432 :=
  interval_of_check test0 416 16 (by decide +kernel)

theorem test0_block_27 : Interval test0 432 448 :=
  interval_of_check test0 432 16 (by decide +kernel)

theorem test0_block_28 : Interval test0 448 464 :=
  interval_of_check test0 448 16 (by decide +kernel)

theorem test0_block_29 : Interval test0 464 480 :=
  interval_of_check test0 464 16 (by decide +kernel)

theorem test0_block_30 : Interval test0 480 496 :=
  interval_of_check test0 480 16 (by decide +kernel)

theorem test0_block_31 : Interval test0 496 512 :=
  interval_of_check test0 496 16 (by decide +kernel)

theorem test0_block_32 : Interval test0 512 524 :=
  interval_of_check test0 512 12 (by decide +kernel)

theorem test0_complete : Interval test0 0 524 :=
  (interval_append test0 0 256 524
  (interval_append test0 0 128 256
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  (interval_append test0 0 16 32
  test0_block_0
  test0_block_1)
  (interval_append test0 32 48 64
  test0_block_2
  test0_block_3))
  (interval_append test0 64 96 128
  (interval_append test0 64 80 96
  test0_block_4
  test0_block_5)
  (interval_append test0 96 112 128
  test0_block_6
  test0_block_7)))
  (interval_append test0 128 192 256
  (interval_append test0 128 160 192
  (interval_append test0 128 144 160
  test0_block_8
  test0_block_9)
  (interval_append test0 160 176 192
  test0_block_10
  test0_block_11))
  (interval_append test0 192 224 256
  (interval_append test0 192 208 224
  test0_block_12
  test0_block_13)
  (interval_append test0 224 240 256
  test0_block_14
  test0_block_15))))
  (interval_append test0 256 384 524
  (interval_append test0 256 320 384
  (interval_append test0 256 288 320
  (interval_append test0 256 272 288
  test0_block_16
  test0_block_17)
  (interval_append test0 288 304 320
  test0_block_18
  test0_block_19))
  (interval_append test0 320 352 384
  (interval_append test0 320 336 352
  test0_block_20
  test0_block_21)
  (interval_append test0 352 368 384
  test0_block_22
  test0_block_23)))
  (interval_append test0 384 448 524
  (interval_append test0 384 416 448
  (interval_append test0 384 400 416
  test0_block_24
  test0_block_25)
  (interval_append test0 416 432 448
  test0_block_26
  test0_block_27))
  (interval_append test0 448 480 524
  (interval_append test0 448 464 480
  test0_block_28
  test0_block_29)
  (interval_append test0 480 496 524
  test0_block_30
  (interval_append test0 496 512 524
  test0_block_31
  test0_block_32))))))
theorem nodeInterval0 : Interval nodeTest 0 524 := by
  intro i hlo hhi
  have h := test0_complete (i-0) (Nat.zero_le _) (by omega)
  simpa only [test0, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0689
