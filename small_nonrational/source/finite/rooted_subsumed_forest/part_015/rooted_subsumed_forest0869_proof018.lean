module
prelude
public import RootedSubsumedForest0869Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
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

theorem test11520_block_32 : Interval test11520 512 521 :=
  interval_of_check test11520 512 9 (by decide +kernel)

theorem test11520_complete : Interval test11520 0 521 :=
  (interval_append test11520 0 256 521
  (interval_append test11520 0 128 256
  (interval_append test11520 0 64 128
  (interval_append test11520 0 32 64
  (interval_append test11520 0 16 32
  test11520_block_0
  test11520_block_1)
  (interval_append test11520 32 48 64
  test11520_block_2
  test11520_block_3))
  (interval_append test11520 64 96 128
  (interval_append test11520 64 80 96
  test11520_block_4
  test11520_block_5)
  (interval_append test11520 96 112 128
  test11520_block_6
  test11520_block_7)))
  (interval_append test11520 128 192 256
  (interval_append test11520 128 160 192
  (interval_append test11520 128 144 160
  test11520_block_8
  test11520_block_9)
  (interval_append test11520 160 176 192
  test11520_block_10
  test11520_block_11))
  (interval_append test11520 192 224 256
  (interval_append test11520 192 208 224
  test11520_block_12
  test11520_block_13)
  (interval_append test11520 224 240 256
  test11520_block_14
  test11520_block_15))))
  (interval_append test11520 256 384 521
  (interval_append test11520 256 320 384
  (interval_append test11520 256 288 320
  (interval_append test11520 256 272 288
  test11520_block_16
  test11520_block_17)
  (interval_append test11520 288 304 320
  test11520_block_18
  test11520_block_19))
  (interval_append test11520 320 352 384
  (interval_append test11520 320 336 352
  test11520_block_20
  test11520_block_21)
  (interval_append test11520 352 368 384
  test11520_block_22
  test11520_block_23)))
  (interval_append test11520 384 448 521
  (interval_append test11520 384 416 448
  (interval_append test11520 384 400 416
  test11520_block_24
  test11520_block_25)
  (interval_append test11520 416 432 448
  test11520_block_26
  test11520_block_27))
  (interval_append test11520 448 480 521
  (interval_append test11520 448 464 480
  test11520_block_28
  test11520_block_29)
  (interval_append test11520 480 496 521
  test11520_block_30
  (interval_append test11520 496 512 521
  test11520_block_31
  test11520_block_32))))))
theorem nodeInterval11520 : Interval nodeTest 11520 12041 := by
  intro i hlo hhi
  have h := test11520_complete (i-11520) (Nat.zero_le _) (by omega)
  simpa only [test11520, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedSubsumedForest0869
