module
prelude
public import RootedSevenPure037OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure037.Outside.Verified
open Papers.RationalityTen.FiniteChecks
def fastGenerator1 (i : Nat) := fastCellTest 1 i
theorem fastGenerator1_block_0 : Interval fastGenerator1 0 16 :=
  interval_of_check fastGenerator1 0 16 (by decide +kernel)

theorem fastGenerator1_block_1 : Interval fastGenerator1 16 32 :=
  interval_of_check fastGenerator1 16 16 (by decide +kernel)

theorem fastGenerator1_block_2 : Interval fastGenerator1 32 48 :=
  interval_of_check fastGenerator1 32 16 (by decide +kernel)

theorem fastGenerator1_block_3 : Interval fastGenerator1 48 64 :=
  interval_of_check fastGenerator1 48 16 (by decide +kernel)

theorem fastGenerator1_block_4 : Interval fastGenerator1 64 80 :=
  interval_of_check fastGenerator1 64 16 (by decide +kernel)

theorem fastGenerator1_block_5 : Interval fastGenerator1 80 96 :=
  interval_of_check fastGenerator1 80 16 (by decide +kernel)

theorem fastGenerator1_block_6 : Interval fastGenerator1 96 112 :=
  interval_of_check fastGenerator1 96 16 (by decide +kernel)

theorem fastGenerator1_block_7 : Interval fastGenerator1 112 128 :=
  interval_of_check fastGenerator1 112 16 (by decide +kernel)

theorem fastGenerator1_block_8 : Interval fastGenerator1 128 144 :=
  interval_of_check fastGenerator1 128 16 (by decide +kernel)

theorem fastGenerator1_block_9 : Interval fastGenerator1 144 160 :=
  interval_of_check fastGenerator1 144 16 (by decide +kernel)

theorem fastGenerator1_block_10 : Interval fastGenerator1 160 176 :=
  interval_of_check fastGenerator1 160 16 (by decide +kernel)

theorem fastGenerator1_block_11 : Interval fastGenerator1 176 192 :=
  interval_of_check fastGenerator1 176 16 (by decide +kernel)

theorem fastGenerator1_block_12 : Interval fastGenerator1 192 208 :=
  interval_of_check fastGenerator1 192 16 (by decide +kernel)

theorem fastGenerator1_block_13 : Interval fastGenerator1 208 224 :=
  interval_of_check fastGenerator1 208 16 (by decide +kernel)

theorem fastGenerator1_block_14 : Interval fastGenerator1 224 240 :=
  interval_of_check fastGenerator1 224 16 (by decide +kernel)

theorem fastGenerator1_block_15 : Interval fastGenerator1 240 256 :=
  interval_of_check fastGenerator1 240 16 (by decide +kernel)

theorem fastGenerator1_block_16 : Interval fastGenerator1 256 272 :=
  interval_of_check fastGenerator1 256 16 (by decide +kernel)

theorem fastGenerator1_block_17 : Interval fastGenerator1 272 288 :=
  interval_of_check fastGenerator1 272 16 (by decide +kernel)

theorem fastGenerator1_block_18 : Interval fastGenerator1 288 304 :=
  interval_of_check fastGenerator1 288 16 (by decide +kernel)

theorem fastGenerator1_block_19 : Interval fastGenerator1 304 320 :=
  interval_of_check fastGenerator1 304 16 (by decide +kernel)

theorem fastGenerator1_block_20 : Interval fastGenerator1 320 336 :=
  interval_of_check fastGenerator1 320 16 (by decide +kernel)

theorem fastGenerator1_block_21 : Interval fastGenerator1 336 352 :=
  interval_of_check fastGenerator1 336 16 (by decide +kernel)

theorem fastGenerator1_block_22 : Interval fastGenerator1 352 368 :=
  interval_of_check fastGenerator1 352 16 (by decide +kernel)

theorem fastGenerator1_block_23 : Interval fastGenerator1 368 384 :=
  interval_of_check fastGenerator1 368 16 (by decide +kernel)

theorem fastGenerator1_block_24 : Interval fastGenerator1 384 400 :=
  interval_of_check fastGenerator1 384 16 (by decide +kernel)

theorem fastGenerator1_block_25 : Interval fastGenerator1 400 416 :=
  interval_of_check fastGenerator1 400 16 (by decide +kernel)

theorem fastGenerator1_block_26 : Interval fastGenerator1 416 432 :=
  interval_of_check fastGenerator1 416 16 (by decide +kernel)

theorem fastGenerator1_block_27 : Interval fastGenerator1 432 448 :=
  interval_of_check fastGenerator1 432 16 (by decide +kernel)

theorem fastGenerator1_block_28 : Interval fastGenerator1 448 464 :=
  interval_of_check fastGenerator1 448 16 (by decide +kernel)

theorem fastGenerator1_block_29 : Interval fastGenerator1 464 480 :=
  interval_of_check fastGenerator1 464 16 (by decide +kernel)

theorem fastGenerator1_block_30 : Interval fastGenerator1 480 496 :=
  interval_of_check fastGenerator1 480 16 (by decide +kernel)

theorem fastGenerator1_block_31 : Interval fastGenerator1 496 512 :=
  interval_of_check fastGenerator1 496 16 (by decide +kernel)

theorem fastGenerator1_block_32 : Interval fastGenerator1 512 528 :=
  interval_of_check fastGenerator1 512 16 (by decide +kernel)

theorem fastGenerator1_block_33 : Interval fastGenerator1 528 544 :=
  interval_of_check fastGenerator1 528 16 (by decide +kernel)

theorem fastGenerator1_block_34 : Interval fastGenerator1 544 560 :=
  interval_of_check fastGenerator1 544 16 (by decide +kernel)

theorem fastGenerator1_block_35 : Interval fastGenerator1 560 576 :=
  interval_of_check fastGenerator1 560 16 (by decide +kernel)

theorem fastGenerator1_block_36 : Interval fastGenerator1 576 586 :=
  interval_of_check fastGenerator1 576 10 (by decide +kernel)

theorem fastGenerator1_complete : Interval fastGenerator1 0 586 :=
  (interval_append fastGenerator1 0 288 586
  (interval_append fastGenerator1 0 144 288
  (interval_append fastGenerator1 0 64 144
  (interval_append fastGenerator1 0 32 64
  (interval_append fastGenerator1 0 16 32
  fastGenerator1_block_0
  fastGenerator1_block_1)
  (interval_append fastGenerator1 32 48 64
  fastGenerator1_block_2
  fastGenerator1_block_3))
  (interval_append fastGenerator1 64 96 144
  (interval_append fastGenerator1 64 80 96
  fastGenerator1_block_4
  fastGenerator1_block_5)
  (interval_append fastGenerator1 96 112 144
  fastGenerator1_block_6
  (interval_append fastGenerator1 112 128 144
  fastGenerator1_block_7
  fastGenerator1_block_8))))
  (interval_append fastGenerator1 144 208 288
  (interval_append fastGenerator1 144 176 208
  (interval_append fastGenerator1 144 160 176
  fastGenerator1_block_9
  fastGenerator1_block_10)
  (interval_append fastGenerator1 176 192 208
  fastGenerator1_block_11
  fastGenerator1_block_12))
  (interval_append fastGenerator1 208 240 288
  (interval_append fastGenerator1 208 224 240
  fastGenerator1_block_13
  fastGenerator1_block_14)
  (interval_append fastGenerator1 240 256 288
  fastGenerator1_block_15
  (interval_append fastGenerator1 256 272 288
  fastGenerator1_block_16
  fastGenerator1_block_17)))))
  (interval_append fastGenerator1 288 432 586
  (interval_append fastGenerator1 288 352 432
  (interval_append fastGenerator1 288 320 352
  (interval_append fastGenerator1 288 304 320
  fastGenerator1_block_18
  fastGenerator1_block_19)
  (interval_append fastGenerator1 320 336 352
  fastGenerator1_block_20
  fastGenerator1_block_21))
  (interval_append fastGenerator1 352 384 432
  (interval_append fastGenerator1 352 368 384
  fastGenerator1_block_22
  fastGenerator1_block_23)
  (interval_append fastGenerator1 384 400 432
  fastGenerator1_block_24
  (interval_append fastGenerator1 400 416 432
  fastGenerator1_block_25
  fastGenerator1_block_26))))
  (interval_append fastGenerator1 432 512 586
  (interval_append fastGenerator1 432 464 512
  (interval_append fastGenerator1 432 448 464
  fastGenerator1_block_27
  fastGenerator1_block_28)
  (interval_append fastGenerator1 464 480 512
  fastGenerator1_block_29
  (interval_append fastGenerator1 480 496 512
  fastGenerator1_block_30
  fastGenerator1_block_31)))
  (interval_append fastGenerator1 512 544 586
  (interval_append fastGenerator1 512 528 544
  fastGenerator1_block_32
  fastGenerator1_block_33)
  (interval_append fastGenerator1 544 560 586
  fastGenerator1_block_34
  (interval_append fastGenerator1 560 576 586
  fastGenerator1_block_35
  fastGenerator1_block_36))))))
end Papers.RationalityTen.FacetUniverses.RootedSevenPure037.Outside.Verified
