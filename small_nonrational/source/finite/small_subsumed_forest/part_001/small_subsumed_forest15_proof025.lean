module
prelude
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def test16000 (i : Nat) := nodeTest (i+16000)
theorem test16000_block_0 : Interval test16000 0 16 :=
  interval_of_check test16000 0 16 (by decide +kernel)

theorem test16000_block_1 : Interval test16000 16 32 :=
  interval_of_check test16000 16 16 (by decide +kernel)

theorem test16000_block_2 : Interval test16000 32 48 :=
  interval_of_check test16000 32 16 (by decide +kernel)

theorem test16000_block_3 : Interval test16000 48 64 :=
  interval_of_check test16000 48 16 (by decide +kernel)

theorem test16000_block_4 : Interval test16000 64 80 :=
  interval_of_check test16000 64 16 (by decide +kernel)

theorem test16000_block_5 : Interval test16000 80 96 :=
  interval_of_check test16000 80 16 (by decide +kernel)

theorem test16000_block_6 : Interval test16000 96 112 :=
  interval_of_check test16000 96 16 (by decide +kernel)

theorem test16000_block_7 : Interval test16000 112 128 :=
  interval_of_check test16000 112 16 (by decide +kernel)

theorem test16000_block_8 : Interval test16000 128 144 :=
  interval_of_check test16000 128 16 (by decide +kernel)

theorem test16000_block_9 : Interval test16000 144 160 :=
  interval_of_check test16000 144 16 (by decide +kernel)

theorem test16000_block_10 : Interval test16000 160 176 :=
  interval_of_check test16000 160 16 (by decide +kernel)

theorem test16000_block_11 : Interval test16000 176 192 :=
  interval_of_check test16000 176 16 (by decide +kernel)

theorem test16000_block_12 : Interval test16000 192 208 :=
  interval_of_check test16000 192 16 (by decide +kernel)

theorem test16000_block_13 : Interval test16000 208 224 :=
  interval_of_check test16000 208 16 (by decide +kernel)

theorem test16000_block_14 : Interval test16000 224 240 :=
  interval_of_check test16000 224 16 (by decide +kernel)

theorem test16000_block_15 : Interval test16000 240 256 :=
  interval_of_check test16000 240 16 (by decide +kernel)

theorem test16000_block_16 : Interval test16000 256 272 :=
  interval_of_check test16000 256 16 (by decide +kernel)

theorem test16000_block_17 : Interval test16000 272 288 :=
  interval_of_check test16000 272 16 (by decide +kernel)

theorem test16000_block_18 : Interval test16000 288 304 :=
  interval_of_check test16000 288 16 (by decide +kernel)

theorem test16000_block_19 : Interval test16000 304 320 :=
  interval_of_check test16000 304 16 (by decide +kernel)

theorem test16000_block_20 : Interval test16000 320 336 :=
  interval_of_check test16000 320 16 (by decide +kernel)

theorem test16000_block_21 : Interval test16000 336 352 :=
  interval_of_check test16000 336 16 (by decide +kernel)

theorem test16000_block_22 : Interval test16000 352 368 :=
  interval_of_check test16000 352 16 (by decide +kernel)

theorem test16000_block_23 : Interval test16000 368 384 :=
  interval_of_check test16000 368 16 (by decide +kernel)

theorem test16000_block_24 : Interval test16000 384 400 :=
  interval_of_check test16000 384 16 (by decide +kernel)

theorem test16000_block_25 : Interval test16000 400 416 :=
  interval_of_check test16000 400 16 (by decide +kernel)

theorem test16000_block_26 : Interval test16000 416 432 :=
  interval_of_check test16000 416 16 (by decide +kernel)

theorem test16000_block_27 : Interval test16000 432 448 :=
  interval_of_check test16000 432 16 (by decide +kernel)

theorem test16000_block_28 : Interval test16000 448 464 :=
  interval_of_check test16000 448 16 (by decide +kernel)

theorem test16000_block_29 : Interval test16000 464 480 :=
  interval_of_check test16000 464 16 (by decide +kernel)

theorem test16000_block_30 : Interval test16000 480 496 :=
  interval_of_check test16000 480 16 (by decide +kernel)

theorem test16000_block_31 : Interval test16000 496 512 :=
  interval_of_check test16000 496 16 (by decide +kernel)

theorem test16000_block_32 : Interval test16000 512 528 :=
  interval_of_check test16000 512 16 (by decide +kernel)

theorem test16000_block_33 : Interval test16000 528 544 :=
  interval_of_check test16000 528 16 (by decide +kernel)

theorem test16000_block_34 : Interval test16000 544 560 :=
  interval_of_check test16000 544 16 (by decide +kernel)

theorem test16000_block_35 : Interval test16000 560 576 :=
  interval_of_check test16000 560 16 (by decide +kernel)

theorem test16000_block_36 : Interval test16000 576 592 :=
  interval_of_check test16000 576 16 (by decide +kernel)

theorem test16000_block_37 : Interval test16000 592 608 :=
  interval_of_check test16000 592 16 (by decide +kernel)

theorem test16000_block_38 : Interval test16000 608 624 :=
  interval_of_check test16000 608 16 (by decide +kernel)

theorem test16000_block_39 : Interval test16000 624 640 :=
  interval_of_check test16000 624 16 (by decide +kernel)

theorem test16000_complete : Interval test16000 0 640 :=
  (interval_append test16000 0 320 640
  (interval_append test16000 0 160 320
  (interval_append test16000 0 80 160
  (interval_append test16000 0 32 80
  (interval_append test16000 0 16 32
  test16000_block_0
  test16000_block_1)
  (interval_append test16000 32 48 80
  test16000_block_2
  (interval_append test16000 48 64 80
  test16000_block_3
  test16000_block_4)))
  (interval_append test16000 80 112 160
  (interval_append test16000 80 96 112
  test16000_block_5
  test16000_block_6)
  (interval_append test16000 112 128 160
  test16000_block_7
  (interval_append test16000 128 144 160
  test16000_block_8
  test16000_block_9))))
  (interval_append test16000 160 240 320
  (interval_append test16000 160 192 240
  (interval_append test16000 160 176 192
  test16000_block_10
  test16000_block_11)
  (interval_append test16000 192 208 240
  test16000_block_12
  (interval_append test16000 208 224 240
  test16000_block_13
  test16000_block_14)))
  (interval_append test16000 240 272 320
  (interval_append test16000 240 256 272
  test16000_block_15
  test16000_block_16)
  (interval_append test16000 272 288 320
  test16000_block_17
  (interval_append test16000 288 304 320
  test16000_block_18
  test16000_block_19)))))
  (interval_append test16000 320 480 640
  (interval_append test16000 320 400 480
  (interval_append test16000 320 352 400
  (interval_append test16000 320 336 352
  test16000_block_20
  test16000_block_21)
  (interval_append test16000 352 368 400
  test16000_block_22
  (interval_append test16000 368 384 400
  test16000_block_23
  test16000_block_24)))
  (interval_append test16000 400 432 480
  (interval_append test16000 400 416 432
  test16000_block_25
  test16000_block_26)
  (interval_append test16000 432 448 480
  test16000_block_27
  (interval_append test16000 448 464 480
  test16000_block_28
  test16000_block_29))))
  (interval_append test16000 480 560 640
  (interval_append test16000 480 512 560
  (interval_append test16000 480 496 512
  test16000_block_30
  test16000_block_31)
  (interval_append test16000 512 528 560
  test16000_block_32
  (interval_append test16000 528 544 560
  test16000_block_33
  test16000_block_34)))
  (interval_append test16000 560 592 640
  (interval_append test16000 560 576 592
  test16000_block_35
  test16000_block_36)
  (interval_append test16000 592 608 640
  test16000_block_37
  (interval_append test16000 608 624 640
  test16000_block_38
  test16000_block_39))))))
theorem nodeInterval16000 : Interval nodeTest 16000 16640 := by
  intro i hlo hhi
  have h := test16000_complete (i-16000) (Nat.zero_le _) (by omega)
  simpa only [test16000, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
