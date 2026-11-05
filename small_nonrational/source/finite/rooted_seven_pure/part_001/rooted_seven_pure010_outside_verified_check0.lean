module
prelude
public import RootedSevenPure010OutsideVerifiedLookup

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenPure010.Outside.Verified
open Papers.RationalityTen.FiniteChecks
def fastGenerator0 (i : Nat) := fastCellTest 0 i
theorem fastGenerator0_block_0 : Interval fastGenerator0 0 16 :=
  interval_of_check fastGenerator0 0 16 (by decide +kernel)

theorem fastGenerator0_block_1 : Interval fastGenerator0 16 32 :=
  interval_of_check fastGenerator0 16 16 (by decide +kernel)

theorem fastGenerator0_block_2 : Interval fastGenerator0 32 48 :=
  interval_of_check fastGenerator0 32 16 (by decide +kernel)

theorem fastGenerator0_block_3 : Interval fastGenerator0 48 64 :=
  interval_of_check fastGenerator0 48 16 (by decide +kernel)

theorem fastGenerator0_block_4 : Interval fastGenerator0 64 80 :=
  interval_of_check fastGenerator0 64 16 (by decide +kernel)

theorem fastGenerator0_block_5 : Interval fastGenerator0 80 96 :=
  interval_of_check fastGenerator0 80 16 (by decide +kernel)

theorem fastGenerator0_block_6 : Interval fastGenerator0 96 112 :=
  interval_of_check fastGenerator0 96 16 (by decide +kernel)

theorem fastGenerator0_block_7 : Interval fastGenerator0 112 128 :=
  interval_of_check fastGenerator0 112 16 (by decide +kernel)

theorem fastGenerator0_block_8 : Interval fastGenerator0 128 144 :=
  interval_of_check fastGenerator0 128 16 (by decide +kernel)

theorem fastGenerator0_block_9 : Interval fastGenerator0 144 160 :=
  interval_of_check fastGenerator0 144 16 (by decide +kernel)

theorem fastGenerator0_block_10 : Interval fastGenerator0 160 176 :=
  interval_of_check fastGenerator0 160 16 (by decide +kernel)

theorem fastGenerator0_block_11 : Interval fastGenerator0 176 192 :=
  interval_of_check fastGenerator0 176 16 (by decide +kernel)

theorem fastGenerator0_block_12 : Interval fastGenerator0 192 208 :=
  interval_of_check fastGenerator0 192 16 (by decide +kernel)

theorem fastGenerator0_block_13 : Interval fastGenerator0 208 224 :=
  interval_of_check fastGenerator0 208 16 (by decide +kernel)

theorem fastGenerator0_block_14 : Interval fastGenerator0 224 240 :=
  interval_of_check fastGenerator0 224 16 (by decide +kernel)

theorem fastGenerator0_block_15 : Interval fastGenerator0 240 256 :=
  interval_of_check fastGenerator0 240 16 (by decide +kernel)

theorem fastGenerator0_block_16 : Interval fastGenerator0 256 272 :=
  interval_of_check fastGenerator0 256 16 (by decide +kernel)

theorem fastGenerator0_block_17 : Interval fastGenerator0 272 288 :=
  interval_of_check fastGenerator0 272 16 (by decide +kernel)

theorem fastGenerator0_block_18 : Interval fastGenerator0 288 304 :=
  interval_of_check fastGenerator0 288 16 (by decide +kernel)

theorem fastGenerator0_block_19 : Interval fastGenerator0 304 320 :=
  interval_of_check fastGenerator0 304 16 (by decide +kernel)

theorem fastGenerator0_block_20 : Interval fastGenerator0 320 336 :=
  interval_of_check fastGenerator0 320 16 (by decide +kernel)

theorem fastGenerator0_block_21 : Interval fastGenerator0 336 352 :=
  interval_of_check fastGenerator0 336 16 (by decide +kernel)

theorem fastGenerator0_block_22 : Interval fastGenerator0 352 368 :=
  interval_of_check fastGenerator0 352 16 (by decide +kernel)

theorem fastGenerator0_block_23 : Interval fastGenerator0 368 384 :=
  interval_of_check fastGenerator0 368 16 (by decide +kernel)

theorem fastGenerator0_block_24 : Interval fastGenerator0 384 400 :=
  interval_of_check fastGenerator0 384 16 (by decide +kernel)

theorem fastGenerator0_block_25 : Interval fastGenerator0 400 416 :=
  interval_of_check fastGenerator0 400 16 (by decide +kernel)

theorem fastGenerator0_block_26 : Interval fastGenerator0 416 432 :=
  interval_of_check fastGenerator0 416 16 (by decide +kernel)

theorem fastGenerator0_block_27 : Interval fastGenerator0 432 448 :=
  interval_of_check fastGenerator0 432 16 (by decide +kernel)

theorem fastGenerator0_block_28 : Interval fastGenerator0 448 464 :=
  interval_of_check fastGenerator0 448 16 (by decide +kernel)

theorem fastGenerator0_block_29 : Interval fastGenerator0 464 480 :=
  interval_of_check fastGenerator0 464 16 (by decide +kernel)

theorem fastGenerator0_block_30 : Interval fastGenerator0 480 496 :=
  interval_of_check fastGenerator0 480 16 (by decide +kernel)

theorem fastGenerator0_block_31 : Interval fastGenerator0 496 512 :=
  interval_of_check fastGenerator0 496 16 (by decide +kernel)

theorem fastGenerator0_block_32 : Interval fastGenerator0 512 528 :=
  interval_of_check fastGenerator0 512 16 (by decide +kernel)

theorem fastGenerator0_block_33 : Interval fastGenerator0 528 544 :=
  interval_of_check fastGenerator0 528 16 (by decide +kernel)

theorem fastGenerator0_block_34 : Interval fastGenerator0 544 560 :=
  interval_of_check fastGenerator0 544 16 (by decide +kernel)

theorem fastGenerator0_block_35 : Interval fastGenerator0 560 576 :=
  interval_of_check fastGenerator0 560 16 (by decide +kernel)

theorem fastGenerator0_block_36 : Interval fastGenerator0 576 586 :=
  interval_of_check fastGenerator0 576 10 (by decide +kernel)

theorem fastGenerator0_complete : Interval fastGenerator0 0 586 :=
  (interval_append fastGenerator0 0 288 586
  (interval_append fastGenerator0 0 144 288
  (interval_append fastGenerator0 0 64 144
  (interval_append fastGenerator0 0 32 64
  (interval_append fastGenerator0 0 16 32
  fastGenerator0_block_0
  fastGenerator0_block_1)
  (interval_append fastGenerator0 32 48 64
  fastGenerator0_block_2
  fastGenerator0_block_3))
  (interval_append fastGenerator0 64 96 144
  (interval_append fastGenerator0 64 80 96
  fastGenerator0_block_4
  fastGenerator0_block_5)
  (interval_append fastGenerator0 96 112 144
  fastGenerator0_block_6
  (interval_append fastGenerator0 112 128 144
  fastGenerator0_block_7
  fastGenerator0_block_8))))
  (interval_append fastGenerator0 144 208 288
  (interval_append fastGenerator0 144 176 208
  (interval_append fastGenerator0 144 160 176
  fastGenerator0_block_9
  fastGenerator0_block_10)
  (interval_append fastGenerator0 176 192 208
  fastGenerator0_block_11
  fastGenerator0_block_12))
  (interval_append fastGenerator0 208 240 288
  (interval_append fastGenerator0 208 224 240
  fastGenerator0_block_13
  fastGenerator0_block_14)
  (interval_append fastGenerator0 240 256 288
  fastGenerator0_block_15
  (interval_append fastGenerator0 256 272 288
  fastGenerator0_block_16
  fastGenerator0_block_17)))))
  (interval_append fastGenerator0 288 432 586
  (interval_append fastGenerator0 288 352 432
  (interval_append fastGenerator0 288 320 352
  (interval_append fastGenerator0 288 304 320
  fastGenerator0_block_18
  fastGenerator0_block_19)
  (interval_append fastGenerator0 320 336 352
  fastGenerator0_block_20
  fastGenerator0_block_21))
  (interval_append fastGenerator0 352 384 432
  (interval_append fastGenerator0 352 368 384
  fastGenerator0_block_22
  fastGenerator0_block_23)
  (interval_append fastGenerator0 384 400 432
  fastGenerator0_block_24
  (interval_append fastGenerator0 400 416 432
  fastGenerator0_block_25
  fastGenerator0_block_26))))
  (interval_append fastGenerator0 432 512 586
  (interval_append fastGenerator0 432 464 512
  (interval_append fastGenerator0 432 448 464
  fastGenerator0_block_27
  fastGenerator0_block_28)
  (interval_append fastGenerator0 464 480 512
  fastGenerator0_block_29
  (interval_append fastGenerator0 480 496 512
  fastGenerator0_block_30
  fastGenerator0_block_31)))
  (interval_append fastGenerator0 512 544 586
  (interval_append fastGenerator0 512 528 544
  fastGenerator0_block_32
  fastGenerator0_block_33)
  (interval_append fastGenerator0 544 560 586
  fastGenerator0_block_34
  (interval_append fastGenerator0 560 576 586
  fastGenerator0_block_35
  fastGenerator0_block_36))))))
end Papers.RationalityTen.FacetUniverses.RootedSevenPure010.Outside.Verified
